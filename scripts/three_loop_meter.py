#!/usr/bin/env python3
"""Render the effort-weighted three-loop meter into README.md (HQ).

Data: docs/campaign/three-loop-meter.json. Each item has the worker-sessions spent and a
lo-hi range for the remaining effort; completion = spent / (spent + midpoint remaining).
It also writes the three-loop status bullet of "Where things stand" (between the HQ:tlstatus
markers) from the per-set notes in the same file, so the two cannot drift apart.
Usage: three_loop_meter.py [--check] [-v]. This is not a Lean proof checker."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import textwrap

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "docs/campaign/three-loop-meter.json"
README = ROOT / "README.md"
START = "<!-- HQ:threeloop:start -->"
END = "<!-- HQ:threeloop:end -->"
S_START = "<!-- HQ:tlstatus:start -->"
S_END = "<!-- HQ:tlstatus:end -->"
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


def set_pct(data: dict, key: str) -> tuple[float, int]:
    items = [i for i in data["items"] if i["set"] == key]
    s = sum(i["spent"] for i in items)
    hi = sum(i["hi"] for i in items)
    return pct(s, sum(i["lo"] + i["hi"] for i in items) / 2), hi


def plural(n: int) -> str:
    return f"{n} diagram" + ("" if n == 1 else "s")


WORDS = ["no", "one", "two", "three", "four", "five", "six", "seven", "eight", "nine"]


def render_status(data: dict) -> str:
    s = sum(i["spent"] for i in data["items"])
    total = pct(s, sum(i["lo"] + i["hi"] for i in data["items"]) / 2)
    sets = data["sets"]
    done = [k for k in sets if set_pct(data, k)[1] == 0]
    todo = [k for k in sets if k not in done]
    n = sum(v["diagrams"] for v in sets.values())
    out = [f"The target is the exact result of Laporta and Remiddi (1996), which sums {n} "
           f"Feynman diagrams in {WORDS[len(sets)]} groups."]
    if done:
        names = [f"{sets[k]['name']} ({plural(sets[k]['diagrams'])}"
                 + (f"; {sets[k]['note']})" if sets[k]["note"] else ")") for k in done]
        out.append(f"{WORDS[len(done)].capitalize()} "
                   f"{'group is' if len(done) == 1 else 'groups are'} proved: "
                   f"{', '.join(names[:-1]) + ' and ' if len(names) > 1 else ''}{names[-1]}.")
    for k in todo:
        info = sets[k]
        name = info["name"][0].upper() + info["name"][1:]
        out.append(f"{name} ({plural(info['diagrams'])}) {info['verb']} about "
                   f"{set_pct(data, k)[0]:.0f}% done{info['note']}.")
    out.append(f"Overall, about {total:.0f}% of the estimated work is done "
               "([meter](#three-loop-effort-meter)).")
    lines = textwrap.wrap(" ".join(out), 96, break_on_hyphens=False, break_long_words=False)
    return "\n".join("  " + ln for ln in lines)


def splice(text: str, start: str, end: str, body: str) -> str | None:
    if start not in text or end not in text:
        return None
    head, rest = text.split(start, 1)
    _, tail = rest.split(end, 1)
    return head + start + body + end + tail


def main() -> int:
    data = json.loads(DATA.read_text())
    text = README.read_text()
    new = splice(text, START, END, f"\n{render(data)}\n")
    new = new and splice(new, S_START, S_END, f"\n{render_status(data)}\n  ")
    if new is None:
        print("README lacks the three-loop meter or status markers", file=sys.stderr)
        return 1
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
