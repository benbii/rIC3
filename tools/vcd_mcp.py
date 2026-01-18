from __future__ import annotations

import argparse
import re
import sys
from bisect import bisect_right
from typing import Dict, List, Sequence, Tuple
from mcp.server.fastmcp import FastMCP
from vcdvcd import VCDVCD


def _strip_end_prefix(name: str) -> str:
    """Remove '$end.' prefix from signal name if present."""
    if name.startswith("$end."):
        return name[5:]
    return name


def _load_vcd_signals(vcd_path: str) -> List[str]:
    vcd = VCDVCD(vcd_path, only_sigs=True)
    signals = [_strip_end_prefix(s) for s in getattr(vcd, "signals", [])]
    return sorted(signals)


def _resolve_signal_name(available: Sequence[str], name: str) -> str:
    if name in available:
        return name
    if name.startswith("/") and name[1:] in available:
        return name[1:]
    if not name.startswith("/") and ("/" + name) in available:
        return "/" + name

    lower_map = {sig.lower(): sig for sig in available}
    if name.lower() in lower_map:
        return lower_map[name.lower()]

    raise ValueError(f"Signal not found: {name}")


def _expand_signal_names(
    available: Sequence[str], requested: Sequence[str]
) -> Tuple[List[str], List[str]]:
    resolved: List[str] = []
    missing: List[str] = []
    for name in requested:
        try:
            resolved.append(_resolve_signal_name(available, name))
            continue
        except ValueError:
            pass

        # Suffix match, like the reference script (e.g. "clock" matches "uut.clock")
        # Prefer '.' hierarchy but also accept '/' separators.
        suffix_matches = [
            sig
            for sig in available
            if sig.endswith("." + name) or sig.endswith("/" + name)
        ]
        if not suffix_matches:
            missing.append(name)
            continue

        # Deterministic order, while still respecting the user's requested ordering.
        resolved.extend(sorted(suffix_matches))

    # De-duplicate while preserving order.
    seen: set[str] = set()
    out: List[str] = []
    for s in resolved:
        if s in seen:
            continue
        seen.add(s)
        out.append(s)
    return out, missing


def _extract_time_markers(vcd_path: str) -> List[int]:
    """Return all VCD time markers (#<time>) in file order, after $enddefinitions."""
    times: List[int] = []
    start_parsing = False
    with open(vcd_path, "r", encoding="utf-8", errors="replace") as f:
        for raw in f:
            line = raw.strip()
            if not start_parsing:
                if line.startswith("$enddefinitions"):
                    start_parsing = True
                continue

            if line.startswith("#"):
                try:
                    times.append(int(line[1:]))
                except ValueError:
                    # Ignore malformed time markers.
                    continue
    return times


def _sample_times(vcd_path: str) -> List[int]:
    times = _extract_time_markers(vcd_path)
    if not times:
        raise ValueError("No timepoints found in VCD")
    times = times[:-1]
    return times


def _build_tv_index(tv: Sequence[Tuple[int, str]]) -> Tuple[List[int], List[str]]:
    times: List[int] = []
    values: List[str] = []
    for t, v in tv:
        times.append(int(t))
        values.append(v)
    return times, values


def _value_at(times: Sequence[int], values: Sequence[str], t: int) -> str:
    # Rightmost index where times[idx] <= t
    idx = bisect_right(times, t) - 1
    if idx < 0:
        return "x"
    return values[idx]


def _strip_inner_ws(s: str) -> str:
    return "".join(s.split())


def _format_hex(val: str) -> str:
    if val is None or val == "x":
        return "X"

    s = _strip_inner_ws(str(val).strip())
    if not s:
        return s

    # vcdvcd may return vectors as "0101" or "b0101"; normalize.
    if (s.startswith("b") or s.startswith("B")) and len(s) > 1:
        s_bits = s[1:]
    elif s.startswith("0b") or s.startswith("0B"):
        s_bits = s[2:]
    else:
        s_bits = s

    lowered = s_bits.lower()

    if any(c in lowered for c in ("x", "z")):
        # Compact to hex; any nibble containing X/Z becomes x or z.
        pad = (-len(s_bits)) % 4
        bits = ("0" * pad) + lowered
        out_digits: List[str] = []
        for i in range(0, len(bits), 4):
            nib = bits[i : i + 4]
            if any(c in nib for c in ("x", "z")):
                if all(c == "z" for c in nib):
                    out_digits.append("z")
                    continue
                if all(c in ("x", "z") for c in nib):
                    out_digits.append("x")
                    continue
                # Mixed known/unknown: treat X/Z as 0 to preserve known bits.
                nib_bits = "".join("0" if c in ("x", "z") else c for c in nib)
                out_digits.append(format(int(nib_bits, 2), "x"))
                continue
            out_digits.append(format(int(nib, 2), "x"))
        return "0x_" + "".join(out_digits)

    if s_bits and all(c in "01" for c in s_bits):
        h = hex(int(s_bits, 2))
        if h.startswith("0x"):
            return "0x_" + h[2:]
        return h

    return s


def _normalize_raw_value_for_const(v: str) -> str:
    s = _strip_inner_ws(str(v).strip())
    if not s:
        return s

    if (s.startswith("b") or s.startswith("B")) and len(s) > 1:
        return s[1:]
    if s.startswith("0b") or s.startswith("0B"):
        return s[2:]
    return s


def _steps_text(
    vcd_path: str,
    signals: Sequence[str],
) -> Tuple[str, List[str]]:
    if not signals:
        raise ValueError("signals must be a non-empty list")

    vcd = VCDVCD(vcd_path, only_sigs=False)
    raw_signals = getattr(vcd, "signals", [])
    stripped_to_raw: Dict[str, str] = {_strip_end_prefix(s): s for s in raw_signals}
    available = sorted(stripped_to_raw.keys())
    signal_names, missing = _expand_signal_names(available, signals)
    step_times = _sample_times(vcd_path)

    if not step_times:
        raise ValueError("No steps found (no sampled timepoints)")

    sig_indexes: Dict[str, Tuple[List[int], List[str]]] = {}
    for s in signal_names:
        raw_name = stripped_to_raw.get(s)
        if raw_name is None:
            continue
        tv = getattr(vcd[raw_name], "tv", None)
        if tv is None:
            missing.append(s)
            continue
        sig_indexes[s] = _build_tv_index(tv)

    lines: List[str] = []
    for s in signal_names:
        idx = sig_indexes.get(s)
        if idx is None:
            continue
        times, values = idx
        raw_row_vals = [_value_at(times, values, t) for t in step_times]

        # If the value is constant across all sampled steps, compress output.
        # Use raw values for the const check to avoid false constants caused by
        # lossy formatting (e.g. nibble-level X compaction).
        if len(raw_row_vals) > 1:
            normalized = [_normalize_raw_value_for_const(v) for v in raw_row_vals]
            if normalized and all(n == normalized[0] for n in normalized[1:]):
                lines.append(
                    f"{s} constant {_format_hex(raw_row_vals[0])}"
                )
                continue

        row_vals = [_format_hex(v) for v in raw_row_vals]
        lines.append(f"{s} " + " ".join(row_vals))

    text = "\n".join(lines)
    return text, missing


mcp = FastMCP("vcd-tools")


@mcp.tool(
    name="search_signals",
    description=(
        "Search signals in a VCD file by regex pattern. "
        "Include values (one signal per line) if few results found. Otherwise "
        "show names only. Path must be absolute."
    ),
)
def search_signals(vcd_path: str, pattern: str) -> str:
    signals = _load_vcd_signals(vcd_path)
    regex = re.compile(pattern)
    matches = [s for s in signals if regex.search(s)]

    step_times = _sample_times(vcd_path)
    trans_nr = len(step_times)
    found_sig_nr = len(matches)

    if found_sig_nr * trans_nr <= 40 and matches:
        text, _missing = _steps_text(vcd_path, matches)
        return text

    if not matches:
        return "Found 0 signals:"

    return "Found {} signals:\n{}".format(len(matches), "\n".join(matches))


@mcp.tool(
    name="signal_values",
    description=(
        "Prints values of selected signals, one per line. "
        "Path must be absolute."
    ),
)
def signal_values(
    vcd_path: str,
    signals: List[str],
) -> str:
    text, missing = _steps_text(
        vcd_path,
        signals,
    )
    lines: List[str] = []
    if missing:
        lines.append("Not found: " + " ".join(missing))
    if text:
        lines.append(text)
    return "\n".join(lines)


def _run_cli(argv: Sequence[str]) -> int:
    parser = argparse.ArgumentParser(description="VCD tools")
    parser.add_argument(
        "--cli",
        action="store_true",
        help="Enable CLI mode instead of MCP server",
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    search_p = subparsers.add_parser("search", help="Search signals by regex")
    search_p.add_argument("--vcd", required=True, help="Absolute path to VCD")
    search_p.add_argument("--pattern", required=True, help="Regex pattern")

    values_p = subparsers.add_parser("values", help="Print values for signals")
    values_p.add_argument("--vcd", required=True, help="Absolute path to VCD")
    values_p.add_argument(
        "--signal",
        action="append",
        dest="signals",
        required=True,
        help="Signal name (repeatable)",
    )

    args = parser.parse_args(argv)

    if args.command == "search":
        print(search_signals(args.vcd, args.pattern))
        return 0
    if args.command == "values":
        print(signal_values(args.vcd, args.signals))
        return 0
    return 2


if __name__ == "__main__":
    if "--cli" in sys.argv[1:]:
        sys.exit(_run_cli(sys.argv[1:]))
    mcp.run()
