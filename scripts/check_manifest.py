#!/usr/bin/env python3
"""Check release hashes, dependency revisions, or actual Lean axiom output."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def check_files() -> None:
    manifest = ROOT / "SHA256SUMS"
    entries: dict[str, str] = {}
    for line_no, line in enumerate(manifest.read_text(encoding="utf-8").splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if match is None:
            raise ValueError(f"SHA256SUMS:{line_no}: malformed entry")
        digest, name = match.groups()
        relative = Path(name)
        if relative.is_absolute() or ".." in relative.parts or name in entries:
            raise ValueError(f"SHA256SUMS:{line_no}: unsafe or duplicate path {name!r}")
        path = ROOT / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(ROOT):
            raise ValueError(f"SHA256SUMS:{line_no}: missing or unsafe file {name!r}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != digest:
            raise ValueError(f"SHA256 mismatch for {name}: {actual} != {digest}")
        entries[name] = digest
    if not entries:
        raise ValueError("SHA256SUMS contains no entries")
    # Proof and verification additions must not silently bypass the release manifest.
    required = {"lean-toolchain", "lakefile.toml", "lake-manifest.json", "Erdos1092.lean"}
    for directory, suffix in (("Erdos1092", ".lean"), ("verification", ".lean"),
                              ("scripts", ".sh"), ("scripts", ".py"),
                              (".github/workflows", ".yml")):
        required.update(str(path.relative_to(ROOT)) for path in (ROOT / directory).rglob(f"*{suffix}"))
    missing = required - entries.keys()
    if missing:
        raise ValueError(f"Files absent from SHA256SUMS: {', '.join(sorted(missing))}")
    print(f"SHA256SUMS verified: {len(entries)} files")


def git_output(directory: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "--no-pager", "-C", str(directory), *args], text=True
    ).strip()


def check_dependencies() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages_dir = ROOT / manifest["packagesDir"]
    packages = manifest["packages"]
    if not packages:
        raise ValueError("The Lake manifest contains no dependencies")
    for package in packages:
        if package["type"] != "git" or not re.fullmatch(r"[0-9a-f]{40}", package["rev"]):
            raise ValueError(f"Dependency {package['name']} is not pinned to a Git commit")
        directory = packages_dir / package["name"]
        actual = git_output(directory, "rev-parse", "HEAD")
        if actual != package["rev"]:
            raise ValueError(f"Dependency {package['name']}: {actual} != {package['rev']}")
        if git_output(directory, "status", "--porcelain", "--untracked-files=no"):
            raise ValueError(f"Dependency {package['name']} has tracked changes")
        print(f"Dependency verified: {package['name']} {actual}")


def check_axioms(source: Path, log: Path, expected_count: int | None) -> None:
    expected = re.findall(r"^#print axioms ([A-Za-z_][A-Za-z_0-9.]*)\s*$",
                          source.read_text(encoding="utf-8"), re.MULTILINE)
    if not expected or len(expected) != len(set(expected)):
        raise ValueError(f"{source}: empty or duplicate axiom-query list")
    if expected_count is not None and len(expected) != expected_count:
        raise ValueError(f"{source}: expected {expected_count} queries, found {len(expected)}")
    actual: dict[str, set[str]] = {}
    for line in log.read_text(encoding="utf-8").splitlines():
        match = re.fullmatch(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", line)
        if match is None:
            continue
        name, axioms_text = match.groups()
        if name in actual:
            raise ValueError(f"{log}: duplicate axiom result for {name}")
        axioms = set() if not axioms_text else {item.strip() for item in axioms_text.split(",")}
        unexpected = axioms - STANDARD_AXIOMS
        if unexpected:
            raise ValueError(f"{name} uses non-standard axioms: {', '.join(sorted(unexpected))}")
        actual[name] = axioms
    if set(actual) != set(expected):
        missing = set(expected) - actual.keys()
        extra = actual.keys() - set(expected)
        raise ValueError(f"Axiom results mismatch: missing={sorted(missing)}, extra={sorted(extra)}")
    print(f"Actual Lean axiom output verified: {len(actual)} declarations; standard foundations only")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--dependencies", action="store_true")
    modes.add_argument("--axioms", nargs=2, metavar=("SOURCE", "LOG"), type=Path)
    parser.add_argument("--expected-count", type=int)
    args = parser.parse_args()
    if args.expected_count is not None and args.axioms is None:
        parser.error("--expected-count requires --axioms")
    try:
        if args.dependencies:
            check_dependencies()
        elif args.axioms is not None:
            check_axioms(*args.axioms, args.expected_count)
        else:
            check_files()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
