#!/usr/bin/env python3
"""Check a fresh CertificateAudit log against the 47 release endpoints."""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"'([^'\r\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|"
    r"does not depend on any axioms)",
    re.MULTILINE,
)
ANSI = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")


def check(log_path, expected_path):
    expected = json.loads(expected_path.read_text(encoding="utf-8"))
    if (not isinstance(expected, list) or len(expected) != 47
            or any(not isinstance(name, str) or not name for name in expected)
            or len(set(expected)) != 47):
        raise ValueError("expected-endpoints.json must contain 47 distinct names")

    text = ANSI.sub("", log_path.read_text(encoding="utf-8"))
    reports = list(REPORT.finditer(text))
    counts = Counter(match.group(1) for match in reports)
    issues = []
    for name in expected:
        if counts[name] != 1:
            issues.append(f"{name}: expected one report, found {counts[name]}")
    for name in sorted(counts.keys() - set(expected)):
        issues.append(f"unexpected endpoint: {name}")
    for match in reports:
        body = match.group(2)
        axioms = [] if body is None or not body.strip() else [
            axiom.strip() for axiom in body.split(",")
        ]
        bad = sorted(set(axioms) - ALLOWED_AXIOMS)
        if bad:
            issues.append(f"{match.group(1)}: unapproved axioms: {', '.join(bad)}")
    remainder = REPORT.sub("", text)
    if "depends on axioms" in remainder or "does not depend on any axioms" in remainder:
        issues.append("malformed or truncated axiom report")
    if re.search(r"^.*\berror(?:\([^\n)]*\))?:", text, re.MULTILINE):
        issues.append("audit log contains a compiler error")
    if issues:
        raise ValueError("\n".join(issues))
    print("Axiom audit OK: all 47 expected endpoints; only propext, Classical.choice, Quot.sound.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, help="fresh output of CertificateAudit.lean")
    parser.add_argument(
        "--expected", type=Path,
        default=Path(__file__).resolve().parents[1] / "verification/expected-endpoints.json",
    )
    args = parser.parse_args()
    try:
        check(args.log, args.expected)
    except (OSError, ValueError) as error:
        print(f"Axiom audit FAILED: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
