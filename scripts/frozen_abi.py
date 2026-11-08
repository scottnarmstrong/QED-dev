#!/usr/bin/env python3
"""Compute elaborated ABI hashes of frozen exports (QED/Frozen/manifest.json `abi_sha256`).

For each export, a transient untracked Lean file imports the export's frozen module and
prints it with `set_option pp.all true`: `#print` for a definition (type and body) and
`#check @export` for a theorem (statement only, so sealing the proof does not move the
hash). The SHA-256 of the printed message text is the ABI hash. The printed form depends
on the pinned toolchain, so the hashes are only comparable at the same Lean/Mathlib pin.

Usage: python3 scripts/frozen_abi.py [--check]
With --check, compare against the manifest and exit nonzero on any mismatch.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "QED" / "Frozen" / "manifest.json"


def abi(module: str, export: str, kind: str) -> str:
    scratch = ROOT / ".scratch" / "abi"
    scratch.mkdir(parents=True, exist_ok=True)
    command = f"#print {export}" if kind == "definition" else f"#check @{export}"
    source = f"module\nimport {module}\nset_option pp.all true in\n{command}\n"
    path = scratch / "Abi.lean"
    path.write_text(source, encoding="utf-8")
    try:
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                capture_output=True, text=True, check=False)
    finally:
        shutil.rmtree(ROOT / ".scratch", ignore_errors=True)
    if result.returncode != 0:
        raise RuntimeError(f"elaboration failed for {export}:\n{result.stdout}{result.stderr}")
    return hashlib.sha256(result.stdout.encode("utf-8")).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    bad = 0
    for anchor in data["anchors"]:
        module = anchor["path"].removesuffix(".lean").replace("/", ".")
        digest = abi(module, anchor["export"], anchor["kind"])
        status = "OK" if digest == anchor["abi_sha256"] else "MISMATCH"
        if args.check and status != "OK":
            bad += 1
        print(f"{status if args.check else 'ABI'} {anchor['export']} {digest}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
