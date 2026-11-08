#!/usr/bin/env python3
"""Render campaign milestone meters. This is not a Lean proof checker."""

from __future__ import annotations

import argparse
from datetime import date
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "docs/campaign/progress.json"
README = ROOT / "README.md"
START = "<!-- HQ:progress:start -->"
END = "<!-- HQ:progress:end -->"
STATUSES = {"planned", "in_progress", "done"}
KINDS = {"setup", "preparation", "formal", "comparison"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def evidence_path(value: str) -> Path:
    require(isinstance(value, str) and bool(value), "Empty evidence path")
    path = (ROOT / value).resolve()
    require(path.is_relative_to(ROOT), f"Evidence leaves repository: {value}")
    require(path.is_file(), f"Missing evidence file: {value}")
    return path


def validate(data: dict) -> None:
    require(data.get("schema_version") == 1, "Unsupported ledger schema")
    date.fromisoformat(data["updated"])
    require(bool(data.get("history")), "A scope history is required")
    require(bool(data.get("tracks")), "No campaign tracks")
    identifiers: set[str] = set()
    for track in data["tracks"]:
        require(track["kind"] in KINDS, f"Unknown track kind: {track['kind']}")
        require(bool(track["items"]), f"Empty track: {track['id']}")
        for entry in [track, *track["items"]]:
            key = entry["id"]
            require(isinstance(key, str) and bool(key), "Missing identifier")
            require(key not in identifiers, f"Duplicate identifier: {key}")
            identifiers.add(key)
            title = entry["title"]
            require(isinstance(title, str) and bool(title), f"Missing title: {key}")
            require("|" not in title and "\n" not in title, f"Invalid title: {key}")
        for item in track["items"]:
            key = item["id"]
            require(item["status"] in STATUSES, f"Unknown status: {key}")
            require(isinstance(item["evidence"], list), f"Invalid evidence: {key}")
            paths = [evidence_path(value) for value in item["evidence"]]
            if item["status"] != "done":
                continue
            require(bool(paths), f"Completed item lacks evidence: {key}")
            if track["kind"] == "formal":
                require(any(path.suffix == ".lean" for path in paths),
                        f"Completed formal item lacks Lean evidence: {key}")
                require(bool(item.get("validation")),
                        f"Completed formal item lacks validation record: {key}")
                evidence_path(item["validation"])


def render(data: dict) -> str:
    lines = [
        f"**Ledger updated:** {data['updated']}. "
        "Only milestones marked `done` contribute to the meters.",
        "",
        "| Workstream | Complete | Milestone meter | State |",
        "| --- | ---: | --- | --- |",
    ]
    for track in data["tracks"]:
        items = track["items"]
        done = sum(item["status"] == "done" for item in items)
        total = len(items)
        filled = 10 * done // total
        meter = "█" * filled + "░" * (10 - filled)
        state = ("Complete" if done == total else
                 "In progress" if any(item["status"] != "planned" for item in items)
                 else "Planned")
        lines.append(
            f"| {track['title']} | {done}/{total} | "
            f"`{meter}` {100 * done / total:.0f}% | {state} |"
        )
    tracked = subprocess.run(
        ["git", "ls-files", "-z", "--", "*.lean"], cwd=ROOT,
        check=True, capture_output=True, text=True,
    ).stdout
    lean_paths = [path for path in tracked.split("\0") if path]
    lean_lines = sum(len((ROOT / path).read_text(encoding="utf-8").splitlines())
                     for path in lean_paths)
    lines.extend(["", f"**Tracked Lean source files:** {len(lean_paths)}. "
                  f"**Total lines of Lean code:** {lean_lines:,}."])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="fail if the ledger is invalid or HQ is stale")
    args = parser.parse_args()
    try:
        data = json.loads(LEDGER.read_text(encoding="utf-8"))
        validate(data)
        current = README.read_text(encoding="utf-8")
        require(current.count(START) == current.count(END) == 1,
                "Expected one pair of HQ progress markers")
        before, rest = current.split(START, 1)
        _, after = rest.split(END, 1)
        expected = before + START + "\n" + render(data) + "\n" + END + after
        if args.check:
            require(current == expected,
                    "HQ is stale; run python3 scripts/update_hq.py")
            print("HQ check passed: ledger, evidence paths, and meters agree.")
        else:
            if current != expected:
                README.write_text(expected, encoding="utf-8")
            print("HQ progress meters updated from the campaign ledger.")
        return 0
    except (KeyError, TypeError, ValueError, OSError,
            subprocess.CalledProcessError) as error:
        print(f"HQ check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
