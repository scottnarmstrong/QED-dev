#!/usr/bin/env python3
"""Verify (and optionally fetch) the pinned source documents.

The manifest is sources/manifest.json. Bytes live in the untracked directory
sources/cache/<id>.pdf (decision D-2). A hash mismatch is reported and the
file is left in place for inspection; it never replaces a verified file.
This script checks bytes only; it says nothing about mathematical content.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "sources" / "manifest.json"
CACHE = ROOT / "sources" / "cache"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true",
                        help="download sources missing from the cache")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    CACHE.mkdir(parents=True, exist_ok=True)
    failures = 0
    for entry in manifest["sources"]:
        path = CACHE / f"{entry['id']}.pdf"
        if not path.exists() and args.fetch:
            request = urllib.request.Request(
                entry["url"], headers={"User-Agent": "qed-dev-source-fetch"})
            with urllib.request.urlopen(request, timeout=120) as response:
                path.write_bytes(response.read())
        if not path.exists():
            print(f"MISSING  {entry['id']}  (run with --fetch)")
            failures += 1
            continue
        size, digest = path.stat().st_size, sha256(path)
        if size == entry["bytes"] and digest == entry["sha256"]:
            print(f"OK       {entry['id']}  {digest}")
        else:
            print(f"MISMATCH {entry['id']}  bytes={size} sha256={digest}")
            failures += 1
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
