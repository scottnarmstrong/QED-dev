#!/usr/bin/env python3
"""Render the effort-weighted three-loop meter into README.md (HQ).

Data: docs/campaign/three-loop-meter.json. Each item has the worker-sessions spent and a
lo-hi range for the remaining effort; completion = spent / (spent + midpoint remaining).
Usage: three_loop_meter.py [--check] [-v]. This is not a Lean proof checker."""

from __future__ import annotations

import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/campaign/three-loop-meter.json"
README = ROOT / "README.md"
START = "<!-- HQ:threeloop:start -->"
END = "<!-- HQ:threeloop:end -->"
NAMES = {"a": "Set (a)", "b": "Set (b)", "c": "Set (c)", "d": "Set (d)", "e": "Set (e)",
         "asm": "Model link and assembly"}


def pct(spent: float, rest: float) -> float:
    return 100 * spent / (spent + rest) if spent + rest else 100.0


def bar(p: float, width: int = 20) -> str:
    n = round(p / 100 * width)
    return "█" * n + "░" * (width - n)


def render(data: dict) -> str:
    lines = [
        f"**Updated:** {data['updated']}. Unit: {data['unit']}. "
        "Completion = spent / (spent + midpoint of the remaining range); the range column "
        "uses the two ends of that range. These are estimates, not milestone counts.",
        "",
        "| Part | Spent | Remaining | Estimate | Range | Meter |",
        "| --- | ---: | ---: | ---: | ---: | --- |",
    ]
    tot = [0, 0, 0]
    for key, name in NAMES.items():
        items = [i for i in data["items"] if i["set"] == key]
        s = sum(i["spent"] for i in items)
        lo = sum(i["lo"] for i in items)
        hi = sum(i["hi"] for i in items)
        tot = [tot[0] + s, tot[1] + lo, tot[2] + hi]
        p = pct(s, (lo + hi) / 2)
        lines.append(f"| {name} | {s} | {lo}–{hi} | {p:.0f}% | "
                     f"{pct(s, hi):.0f}–{pct(s, lo):.0f}% | `{bar(p)}` |")
    s, lo, hi = tot
    p = pct(s, (lo + hi) / 2)
    lines.append(f"| **Total** | {s} | {lo}–{hi} | **{p:.0f}%** | "
                 f"{pct(s, hi):.0f}–{pct(s, lo):.0f}% | `{bar(p)}` |")
    lines += ["", "Open items (remaining range, part, item):", ""]
    for i in data["items"]:
        if i["hi"]:
            lines.append(f"- {i['lo']}–{i['hi']} ({NAMES[i['set']]}): {i['item']}")
    return "\n".join(lines)


def main() -> int:
    data = json.loads(DATA.read_text())
    block = f"{START}\n{render(data)}\n{END}"
    text = README.read_text()
    if START not in text or END not in text:
        print("README lacks the three-loop meter markers", file=sys.stderr)
        return 1
    head, rest = text.split(START, 1)
    _, tail = rest.split(END, 1)
    new = head + block + tail
    if "--check" in sys.argv:
        if new != text:
            print("Three-loop meter out of date: run scripts/three_loop_meter.py",
                  file=sys.stderr)
            return 1
        print("Three-loop meter in sync.")
        return 0
    README.write_text(new)
    if "-v" in sys.argv:
        print(render(data))
    return 0


if __name__ == "__main__":
    sys.exit(main())
