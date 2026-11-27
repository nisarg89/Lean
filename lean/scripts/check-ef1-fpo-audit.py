#!/usr/bin/env python3
"""Check that Lean gave one complete transitive axiom report for the main result."""
import argparse
import json
from pathlib import Path
import re
import sys

from check_axioms import ALLOWED_AXIOMS, ANSI, REPORT

ENDPOINT = "EF1FPO.ef1_fpo_polynomial"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--expected", type=Path, required=True)
    args = parser.parse_args()
    if json.loads(args.expected.read_text()) != [ENDPOINT]:
        raise ValueError("Expected exactly " + ENDPOINT)
    text = ANSI.sub("", args.log.read_text())
    if re.search(r"\berror(?:\([^\n)]*\))?:", text, re.MULTILINE):
        raise ValueError("Lean reported an error")
    reports = list(REPORT.finditer(text))
    if len(reports) != 1 or reports[0][1] != ENDPOINT:
        raise ValueError("Expected exactly one Lean axiom report for " + ENDPOINT)
    remainder = REPORT.sub("", text)
    if re.search(r"depend(?:s)? on (?:any )?axioms", remainder):
        raise ValueError("Malformed axiom report")
    entries = [] if reports[0][2] is None else [ax.strip() for ax in reports[0][2].split(",")]
    if any(not re.fullmatch(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*", ax) for ax in entries):
        raise ValueError("Malformed transitive axiom list")
    axioms = set(entries)
    if len(entries) != len(axioms):
        raise ValueError("Duplicate axiom in Lean report")
    extra = axioms - ALLOWED_AXIOMS
    if extra:
        raise ValueError("Unapproved transitive axioms: " + ", ".join(sorted(extra)))
    print(f"{ENDPOINT} passed. Transitive axioms: {', '.join(sorted(axioms)) or '(none)'}.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit("EF1 and fractional Pareto optimality audit failed: " + str(error))
