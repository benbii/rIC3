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
        # drop existing lemmas subsumed by new
        new_kept = []
        new_sets = []
        for k, ks in zip(kept, kept_sets):
            if not s.issubset(ks):
                new_kept.append(k)
                new_sets.append(ks)
        kept, kept_sets = new_kept, new_sets
        kept.append(lits)
        kept_sets.append(s)
        yield lits


def main():
    ap = argparse.ArgumentParser(
        description="Pretty-print IC3 invariant binary dump (little-endian records)."
    )
    ap.add_argument("dump", help="Path to binary invariant dump file")
    ap.add_argument("--subsume", action="store_true", help="Filter subsumed lemmas")
    ap.add_argument(
        "--dimacs",
        action="store_true",
        help="Print DIMACS-like lines ending with 0",
    )
    args = ap.parse_args()

    try:
        records = read_records(args.dump)
        if args.subsume:
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
