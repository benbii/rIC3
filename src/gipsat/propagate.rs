use super::{
    DagCnfSolver,
    cdb::{CREF_NONE, CRef, Clause},
};
use logicrs::{Lbool, Lit, LitMap, Var};
use nix::libc;
use std::{io, mem::size_of, ptr};

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Watcher {
    pub clause: CRef,
    pub blocker: Lit,
}

impl Watcher {
    #[inline]
    pub fn new(clause: CRef, blocker: Lit) -> Self {
        Self { clause, blocker }
    }
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct WatchRange {
    begin: u32,
    end: u32,
    cap_end: u32,
}

const _: () = assert!(size_of::<Watcher>() == 8);
const _: () = assert!(size_of::<WatchRange>() == 12);

pub(super) struct WatchArena {
    ranges: LitMap<WatchRange>,
    pool: *mut Watcher,
    cursor: usize,
    next_compact: usize,
}

#[inline(never)]
fn grow(range: *mut WatchRange, pool: *mut Watcher, cursor: *mut usize, watcher: Watcher) {
    let old = unsafe { *range };
    let len = old.end - old.begin;
    let cap = old.cap_end - old.begin;
    let new_cap = cap + (cap >> 1) + 1;
    let old_cursor = unsafe { *cursor };
    if cap != 0 && old.cap_end as usize == old_cursor {
        unsafe {
            pool.add(old.end as usize).write(watcher);
            (*range).end += 1;
            (*range).cap_end = old.begin + new_cap;
            *cursor += (new_cap - cap) as usize;
        }
        return;
    }
    let begin = old_cursor as u32;
    unsafe {
        let dst = pool.add(old_cursor);
        ptr::copy_nonoverlapping(pool.add(old.begin as usize), dst, len as usize);
        dst.add(len as usize).write(watcher);
        *range = WatchRange {
            begin,
            end: begin + len + 1,
            cap_end: begin + new_cap,
        };
        *cursor += new_cap as usize;
    }
}

fn push(
    ranges: *mut WatchRange,
    pool: *mut Watcher,
    cursor: *mut usize,
    lit: Lit,
    watcher: Watcher,
) {
    let range = unsafe { &mut *ranges.add(u32::from(lit) as usize) };
    let end = range.end;
    if end != range.cap_end {
        unsafe {
            pool.add(end as usize).write(watcher);
        }
        range.end = end + 1;
        return;
    }
    grow(range, pool, cursor, watcher)
}


impl WatchArena {
    // The hot insertion path intentionally has no global bound check. The inaccessible
    // 12MB catches a runaway bump cursor before it can reach an unrelated mapping.
    const USABLE_BYTES: usize = 500 * 1024 * 1024;
    const GUARD_BYTES: usize = 12 * 1024 * 1024;
    const MAPPING_BYTES: usize = Self::USABLE_BYTES + Self::GUARD_BYTES;
    const MIN_COMPACT: usize = 2 * 1024 * 1024 / size_of::<Watcher>();

    fn map_pool() -> *mut Watcher {
        let mapping = unsafe {
            libc::mmap(
                ptr::null_mut(),
                Self::MAPPING_BYTES,
                libc::PROT_NONE,
                libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        if mapping == libc::MAP_FAILED {
            let error = io::Error::last_os_error();
            panic!("failed to reserve watcher arena: {error}");
        }
        if unsafe {
            libc::mprotect(
                mapping,
                Self::USABLE_BYTES,
                libc::PROT_READ | libc::PROT_WRITE,
            )
        } != 0
        {
            let error = io::Error::last_os_error();
            panic!("failed to enable watcher arena: {error}");
        }
        mapping.cast()
    }

    pub(super) fn new_with(var: Var) -> Self {
        Self {
            ranges: LitMap::new_with(var),
            pool: Self::map_pool(),
            cursor: 0,
            next_compact: Self::MIN_COMPACT,
        }
    }

    #[inline]
    pub(super) fn reserve(&mut self, var: Var) {
        self.ranges.reserve(var)
    }

    pub(super) fn attach(&mut self, cref: CRef, cls: Clause) {
        let ranges = self.ranges.as_mut_ptr();
        let pool = self.pool;
        let cursor = &mut self.cursor;
        push(ranges, pool, cursor, !cls[0], Watcher::new(cref, cls[1]));
        push(ranges, pool, cursor, !cls[1], Watcher::new(cref, cls[0]));
    }

    pub(super) fn detach(&mut self, cref: CRef, cls: Clause) {
        for l in 0..2 {
            let lit = !cls[l];
            let range = &mut self.ranges[lit];
            for i in (range.begin..range.end).rev() {
                if unsafe { (*self.pool.add(i as usize)).clause == cref } {
                    range.end -= 1;
                    unsafe {
                        *self.pool.add(i as usize) = *self.pool.add(range.end as usize);
                    }
                    break;
                }
            }
        }
    }

    pub(super) fn for_each_mut(&mut self, mut f: impl FnMut(&mut Watcher)) {
        for range in self.ranges.iter() {
            for i in range.begin..range.end {
                unsafe {
                    f(&mut *self.pool.add(i as usize));
                }
            }
        }
    }

    fn capacity_for(len: u32) -> u32 {
        let mut cap = 0;
        while cap < len {
            cap += (cap >> 1) + 1;
        }
        cap
    }

    pub(super) fn maybe_compact(&mut self) {
        if self.cursor < self.next_compact {
            return;
        }

        let mut live = Vec::new();
        for (index, range) in self.ranges.iter().enumerate() {
            if range.begin != range.end {
                live.push((range.begin, index as u32));
            }
        }
        live.sort_unstable_by_key(|&(begin, _)| begin);

        let mut cursor = 0usize;
        for (_, index) in live {
            let lit = Lit::new(Var(index >> 1), index & 1 == 0);
            let old = self.ranges[lit];
            let len = old.end - old.begin;
            let cap = Self::capacity_for(len);
            debug_assert!(cap <= old.cap_end - old.begin);
            debug_assert!(cursor <= old.begin as usize);
            unsafe {
                ptr::copy(
                    self.pool.add(old.begin as usize),
                    self.pool.add(cursor),
                    len as usize,
                );
            }
            let begin = cursor as u32;
            self.ranges[lit] = WatchRange {
                begin,
                end: begin + len,
                cap_end: begin + cap,
            };
            cursor += cap as usize;
        }
        for range in self.ranges.iter_mut() {
            if range.begin == range.end {
                *range = WatchRange::default();
            }
        }
        self.cursor = cursor;
        self.next_compact = Self::MIN_COMPACT.max(cursor.saturating_mul(2));

        let page_size =
            usize::try_from(unsafe { libc::sysconf(libc::_SC_PAGESIZE) }).unwrap_or(4096);
        let used = cursor * size_of::<Watcher>();
        let discard = used.div_ceil(page_size) * page_size;
        if discard < Self::USABLE_BYTES {
            unsafe {
                libc::madvise(
                    self.pool.cast::<u8>().add(discard).cast(),
                    Self::USABLE_BYTES - discard,
                    libc::MADV_DONTNEED,
                );
            }
        }
    }
}

impl Clone for WatchArena {
    fn clone(&self) -> Self {
        let mut cloned = Self {
            ranges: self.ranges.clone(),
            pool: Self::map_pool(),
            cursor: 0,
            next_compact: Self::MIN_COMPACT,
        };
        for range in cloned.ranges.iter_mut() {
            let old = *range;
            let len = old.end - old.begin;
            if len == 0 {
                *range = WatchRange::default();
                continue;
            }
            let cap = Self::capacity_for(len);
            unsafe {
                ptr::copy_nonoverlapping(
                    self.pool.add(old.begin as usize),
                    cloned.pool.add(cloned.cursor),
                    len as usize,
                );
            }
            let begin = cloned.cursor as u32;
            *range = WatchRange {
                begin,
                end: begin + len,
                cap_end: begin + cap,
            };
            cloned.cursor += cap as usize;
        }
        cloned.next_compact = Self::MIN_COMPACT.max(cloned.cursor.saturating_mul(2));
        cloned
    }
}

impl Drop for WatchArena {
    fn drop(&mut self) {
        unsafe {
            libc::munmap(self.pool.cast(), Self::MAPPING_BYTES);
        }
    }
}

impl DagCnfSolver {
    fn propagate_full(&mut self) -> CRef {
        let ranges = self.watchers.ranges.as_mut_ptr();
        let pool = self.watchers.pool;
        let cursor = &mut self.watchers.cursor as *mut usize;
        while self.propagated < self.trail.len() as u32 {
            let p = self.trail[self.propagated];
            self.propagated += 1;
            let range = unsafe { ranges.add(u32::from(p) as usize) };
            let mut w = unsafe { (*range).begin };
            let mut end = unsafe { (*range).end };
            'next_cls: while w < end {
                let watcher = unsafe { pool.add(w as usize) };
                let blocker = unsafe { (*watcher).blocker };
                let blocker_value = self.state.lit_value(blocker);
                if blocker_value == Lbool::TRUE {
                    w += 1;
                    continue;
                }
                let cid = unsafe { (*watcher).clause };
                let mut cref = self.cdb.get(cid);
                if cref[0] == !p {
                    cref.swap(0, 1);
                }
                let cref0 = cref[0];
                let mut cref0_value = blocker_value;
                if cref0 != blocker {
                    cref0_value = self.state.lit_value(cref0);
                    if cref0_value == Lbool::TRUE {
                        unsafe {
                            (*watcher).blocker = cref0;
                        }
                        w += 1;
                        continue;
                    }
                }
                let cref_len = cref.len();
                for i in 2..cref_len {
                    let lit = cref[i];
                    if !self.state.lit_value(lit).is_false() {
                        cref.swap(1, i);
                        end -= 1;
                        unsafe {
                            *watcher = *pool.add(end as usize);
                        }
                        push(ranges, pool, cursor, !lit, Watcher::new(cid, cref0));
                        continue 'next_cls;
                    }
                }
                unsafe {
                    (*watcher).blocker = cref0;
                }
                if cref0_value.is_false() {
                    unsafe {
                        (*range).end = end;
                    }
                    return cid;
                }
                self.assign(cref0, cid);
                w += 1;
            }
            unsafe {
                (*range).end = end;
            }
        }
        CREF_NONE
    }

    fn propagate_domain(&mut self) -> CRef {
        // Collect "stable" variables from faraway addresses into stack
        let cdb_data = self.cdb.allocator.data.as_mut_ptr();
        let ranges = self.watchers.ranges.as_mut_ptr();
        let pool = self.watchers.pool;
        let cursor = &mut self.watchers.cursor as *mut usize;
        let mut propagated = self.propagated as usize;

        while propagated < self.trail.len() {
            let p = self.trail[propagated];
            propagated += 1;
            let range = unsafe { ranges.add(u32::from(p) as usize) };
            let mut w = unsafe { (*range).begin };
            let mut end = unsafe { (*range).end };
            'next_cls: while w < end {
                let watcher = unsafe { pool.add(w as usize) };
                let blocker = unsafe { (*watcher).blocker };
                let blocker_state = self.state.get(blocker.var());
                let (skip, v) = blocker_state.domain_value(blocker);
                if skip {
                    w += 1;
                    continue;
                }
                let cid = unsafe { (*watcher).clause };
                let mut cref = Clause { data: unsafe { cdb_data.add(cid.0 as usize) } };
                if cref[0] == !p {
                    cref.swap(0, 1);
                }
                let cref0 = cref[0];
                let mut cref0_value = v;
                if cref0 != blocker {
                    let cref0_state = self.state.get(cref0.var());
                    let (skip, value) = cref0_state.domain_value(cref0);
                    cref0_value = value;
                    if skip {
                        unsafe {
                            (*watcher).blocker = cref0;
                        }
                        w += 1;
                        continue;
                    }
                }
                let cref_len = cref.len();
                for i in 2..cref_len {
                    let lit = cref[i];
                    if !self.state.lit_value(lit).is_false() {
                        cref.swap(1, i);
                        end -= 1;
                        unsafe {
                            *watcher = *pool.add(end as usize);
                        }
                        push(ranges, pool, cursor, !lit, Watcher::new(cid, cref0));
                        continue 'next_cls;
                    }
                }
                unsafe {
                    (*watcher).blocker = cref0;
                }
                if cref0_value.is_false() {
                    unsafe {
                        (*range).end = end;
                    }
                    self.propagated = propagated as u32;
                    return cid;
                }
                self.assign(cref0, cid);
                w += 1;
            }
            unsafe {
                (*range).end = end;
            }
        }
        self.propagated = propagated as u32;
        CREF_NONE
    }

    #[inline]
    pub(super) fn propagate(&mut self) -> CRef {
        if self.highest_level() == 0 {
            self.propagate_full()
        } else {
            self.propagate_domain()
        }
    }

    pub(super) fn flip_to_none_inner(&mut self, var: Var) -> bool {
        if self.level[var] == 0 {
            return false;
        }
        let l = var.lit();
        let l = match self.state.lit_value(l) {
            Lbool::TRUE => l,
            Lbool::FALSE => !l,
            _ => return true,
        };
        self.state.set_none(var);
        let source = !l;
        let ranges = self.watchers.ranges.as_mut_ptr();
        let range = unsafe { ranges.add(u32::from(source) as usize) };
        let pool = self.watchers.pool;
        let cursor = &mut self.watchers.cursor as *mut usize;
        let mut w = unsafe { (*range).begin };
        let mut end = unsafe { (*range).end };
        'next_cls: while w < end {
            let watcher = unsafe { pool.add(w as usize) };
            let cid = unsafe { (*watcher).clause };
            let mut cref = self.cdb.get(cid);
            if cref[0] == l {
                cref.swap(0, 1);
            }
            debug_assert!(cref[1] == l);
            let new_watcher = Watcher::new(cid, cref[0]);
            let cref0_state = self.state.get(cref[0].var());
            let v = cref0_state.lit_value(cref[0]);
            if v == Lbool::TRUE || (v != Lbool::FALSE && !cref0_state.in_domain()) {
                unsafe {
                    (*watcher).blocker = cref[0];
                }
                w += 1;
                continue;
            }
            for i in 2..cref.len() {
                let lit = cref[i];
                let state = self.state.get(lit.var());
                let v = state.lit_value(lit);
                if v.is_true() || (v.is_none() && !state.in_domain()) {
                    cref.swap(1, i);
                    end -= 1;
                    unsafe {
                        *watcher = *pool.add(end as usize);
                    }
                    push(ranges, pool, cursor, !lit, new_watcher);
                    continue 'next_cls;
                }
            }
            unsafe {
                (*range).end = end;
            }
            self.state.set(l);
            return false;
        }
        unsafe {
            (*range).end = end;
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn contents(arena: &WatchArena, lit: Lit) -> Vec<(u32, u32)> {
        let range = arena.ranges[lit];
        (range.begin..range.end)
            .map(|i| unsafe {
                let watcher = *arena.pool.add(i as usize);
                (watcher.clause.0, watcher.blocker.into())
            })
            .collect()
    }

    #[test]
    fn arena_growth_compaction_and_clone_preserve_lists() {
        let max_var = Var(127);
        let mut arena = WatchArena::new_with(max_var);
        let num_lit = u32::from(max_var.lit()) + 2;
        let mut expected: Vec<_> = (0..num_lit)
            .map(|index| (Lit::new(Var(index >> 1), index & 1 == 0), Vec::new()))
            .collect();
        for item in 0..19 {
            for index in 0..num_lit {
                if item >= index % 19 {
                    continue;
                }
                let lit = expected[index as usize].0;
                let watcher = Watcher::new(CRef(index * 100 + item), lit.not_if(item & 1 != 0));
                push(arena.ranges.as_mut_ptr(), arena.pool, &mut arena.cursor, lit, watcher);
                expected[index as usize]
                    .1
                    .push((watcher.clause.0, watcher.blocker.into()));
            }
        }

        for (lit, list) in &expected {
            assert_eq!(&contents(&arena, *lit), list);
        }
        let before = arena.cursor;
        arena.next_compact = 0;
        arena.maybe_compact();
        assert!(arena.cursor < before);
        for (lit, list) in &expected {
            assert_eq!(&contents(&arena, *lit), list);
        }

        let cloned = arena.clone();
        for (lit, list) in &expected {
            assert_eq!(&contents(&cloned, *lit), list);
        }
    }
}
