#!/usr/bin/env python3
"""Check release Lean source bytes and reject extra project Lean files."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys

# These contain downloaded dependencies, toolchains or generated products.
IGNORED_ANYWHERE = {".git", ".lake", "__pycache__"}
IGNORED_AT_ROOT = {".elan", "artifacts", "build", "toolchains"}
ENVIRONMENT_FILES = {
    "lean-toolchain", "lakefile.toml", "lake-manifest.json",
    "third_party/dkgm-topology-source/lakefile.toml",
    "third_party/dkgm-topology-source/lean-toolchain",
}


def check_file_bytes(root, entry, issues):
    name, digest = entry["path"], entry["sha256"]
    if not isinstance(name, str) or not isinstance(digest, str):
        raise ValueError("manifest paths and SHA-256 digests must be strings")
    relative = PurePosixPath(name)
    if (not relative.parts or relative.is_absolute() or ".." in relative.parts
            or relative.as_posix() != name or "\\" in name):
        raise ValueError(f"unsafe/noncanonical manifest path: {name!r}")
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError(f"invalid SHA-256 digest for {name}")
    path = root.joinpath(*relative.parts)
    if any(part.is_symlink() for part in [path, *path.parents] if part != root and root in part.parents):
        issues.append(f"symlink in manifest path: {name}")
    elif not path.is_file():
        issues.append(f"missing file: {name}")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != digest:
        issues.append(f"file bytes differ: {name}")
    return name


def check(root):
    root = root.resolve()
    metadata = json.loads((root / "verification/source-files.json").read_text(encoding="utf-8"))
    entries = metadata["files"]
    if not isinstance(entries, list) or len(entries) != 459:
        raise ValueError("source manifest must contain 456 accepted proof files, 2 facades and 1 statement challenge")
    if metadata.get("accepted_closure_files") != 456:
        raise ValueError("accepted_closure_files must be 456")
    if (root / "lean-toolchain").read_text(encoding="utf-8").strip() != metadata["lean"]:
        raise ValueError("lean-toolchain differs from the source manifest")

    expected = set()
    origins = {}
    issues = []
    for entry in entries:
        name = check_file_bytes(root, entry, issues)
        if PurePosixPath(name).suffix != ".lean":
            raise ValueError(f"non-Lean file in source manifest: {name}")
        if name in expected:
            raise ValueError(f"duplicate source manifest path: {name}")
        expected.add(name)
        origin = entry.get("origin")
        origins[origin] = origins.get(origin, 0) + 1
    if origins != {
        "successful-round-4-proof-closure": 456,
        "release-import-facade": 1,
        "frozen-vendored-package-entrypoint": 1,
        "release-statement-challenge-not-a-proof": 1,
    }:
        raise ValueError("source manifest origin counts differ from the release")

    environment = json.loads((root / "verification/environment-files.json").read_text(encoding="utf-8"))
    environment_entries = environment["files"]
    if not isinstance(environment_entries, list) or len(environment_entries) != len(ENVIRONMENT_FILES):
        raise ValueError("environment manifest must contain exactly the five pinned configuration files")
    environment_names = set()
    for entry in environment_entries:
        name = check_file_bytes(root, entry, issues)
        if name in environment_names:
            raise ValueError(f"duplicate environment manifest path: {name}")
        environment_names.add(name)
    if environment_names != ENVIRONMENT_FILES:
        raise ValueError("environment manifest paths differ from the five pinned configuration files")

    def walk_error(error):
        issues.append(f"cannot scan source tree: {error}")

    found = set()
    for directory, subdirs, files in os.walk(root, followlinks=False, onerror=walk_error):
        directory = Path(directory)
        kept = []
        for name in subdirs:
            if name in IGNORED_ANYWHERE or (directory == root and name in IGNORED_AT_ROOT):
                continue
            child = directory / name
            if child.is_symlink():
                issues.append(f"unscanned symlink directory: {child.relative_to(root)}")
            else:
                kept.append(name)
        subdirs[:] = kept
        for name in files:
            if name.endswith(".lean"):
                found.add((directory / name).relative_to(root).as_posix())
    for name in sorted(found - expected):
        issues.append(f"extra Lean source: {name}")
    for name in sorted(expected - found):
        issues.append(f"manifest source absent from scanned project: {name}")
    if issues:
        raise ValueError("\n".join(issues))
    print("Source integrity OK: all 459 Lean files and 5 pinned configuration files match SHA-256; no extra project Lean sources.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    try:
        check(args.root)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"Source integrity FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
