#!/usr/bin/env python3
import argparse
import struct
import sys


def read_records(path):
    with open(path, "rb") as f:
        while True:
            header = f.read(4)
            if not header:
                return
            if len(header) != 4:
                raise RuntimeError("truncated header")
            (nlits,) = struct.unpack("<I", header)
            if nlits == 0:
                yield []
                continue
            data = f.read(nlits * 4)
            if len(data) != nlits * 4:
                raise RuntimeError("truncated record")
            lits = list(struct.unpack("<" + "i" * nlits, data))
            yield lits


def subsume_filter(records):
    kept = []
    kept_sets = []
    for lits in records:
        s = set(lits)
        # skip if subsumed by existing
        if any(k.issubset(s) for k in kept_sets):
            continue
        kept.append(lits)
        kept_sets.append(s)
        yield lits


def offline_minimize(records):
    items = []
    seen = set()
    for idx, lits in enumerate(records):
        t = tuple(lits)
        if t in seen:
            continue
        seen.add(t)
        items.append((idx, lits, set(lits)))
    items.sort(key=lambda x: (len(x[1]), x[0]))
    kept = []
    kept_sets = []
    kept_idx = []
    for idx, lits, s in items:
        if any(ks.issubset(s) for ks in kept_sets):
            continue
        kept.append(lits)
        kept_sets.append(s)
        kept_idx.append(idx)
    for _, lits in sorted(zip(kept_idx, kept), key=lambda x: x[0]):
        yield lits


def main():
    ap = argparse.ArgumentParser(
        description="Pretty-print IC3 invariant binary dump (little-endian records)."
    )
    ap.add_argument("dump", help="Path to binary invariant dump file")
    ap.add_argument(
        "--subsume",
        action="store_true",
        help="Filter lemmas subsumed by already-kept ones (streaming/monotone)",
    )
    ap.add_argument(
        "--minimize",
        action="store_true",
        help="Offline subsumption minimization (loads full dump into memory)",
    )
    ap.add_argument(
        "--dimacs",
        action="store_true",
        help="Print DIMACS-like lines ending with 0",
    )
    args = ap.parse_args()

    try:
        if args.subsume and args.minimize:
            raise RuntimeError("use only one of --subsume or --minimize")
        records = read_records(args.dump)
        if args.minimize:
            records = offline_minimize(records)
        elif args.subsume:
            records = subsume_filter(records)
        for lits in records:
            if args.dimacs:
                line = " ".join(str(l) for l in lits) + " 0"
            else:
                line = " ".join(str(l) for l in lits)
            print(line)
    except Exception as e:
        print(f"error: {e}", file=sys.stderr)
        sys.exit(2)


if __name__ == "__main__":
    main()
