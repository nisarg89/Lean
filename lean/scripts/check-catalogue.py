#!/usr/bin/env python3
"""Validate targets and prevent removal of prior protected paper contracts."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]

def read_json(path):
    return json.loads((ROOT / path).read_text())

def old_bytes(ref, path):
    return subprocess.check_output(['git', 'show', ref + ':' + path], cwd=ROOT)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base-ref', help='Compare protected catalogue entries to this Git ref')
    parser.add_argument('--matrix', action='store_true')
    args = parser.parse_args()
    catalogue = read_json('certificates.json')
    assert catalogue['schema_version'] == 1
    papers = catalogue['papers']
    targets = []
    for name, paper in papers.items():
        if not re.fullmatch(r'[A-Za-z0-9_-]+', name):
            raise ValueError('Invalid paper identifier: ' + name)
        assert (ROOT / paper['reader']).is_file(), name + ': missing reader guide'
        if paper['regression_required']:
            assert paper['target'] and paper['audit_file'], name + ': missing executable target/audit'
            assert (ROOT / 'lean' / paper['audit_file']).is_file()
            assert (ROOT / paper['audit_checker']).is_file()
            endpoints = read_json(paper['endpoints'])
            assert endpoints and len(set(endpoints)) == len(endpoints)
            regression = read_json('lean/ComparatorChallenges/' + name + 'Regression.json')
            assert regression['theorem_names'] == endpoints, name + ': incomplete regression endpoint list'
            assert not regression['definition_names'], name + ': definition holes are not permitted'
            assert set(regression['permitted_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}
            targets.append(name)
        if paper['status'] == 'certified':
            assert paper['regression_required'], name + ': certified entry excluded from regressions'
            assert paper['semantic_baseline'], name + ': no sealed baseline'
        if paper['semantic_baseline']:
            baseline = read_json(paper['semantic_baseline'])
            for key in ['export_sha256', 'comparator_config_sha256', 'endpoints_sha256']:
                assert re.fullmatch(r'[0-9a-f]{64}', baseline[key]), name + ': invalid hash ' + key
            assert re.fullmatch(r'[0-9a-f]{40}', baseline['source_commit']), name + ': invalid commit'
            assert baseline['export_url'].startswith('https://'), name + ': baseline must use HTTPS'
            for key, path in [('comparator_config_sha256', 'lean/ComparatorChallenges/' + name + 'Regression.json'),
                              ('endpoints_sha256', paper['endpoints'])]:
                assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == baseline[key]
    if args.base_ref:
        old = json.loads(old_bytes(args.base_ref, 'certificates.json'))
        for name, previous in old['papers'].items():
            if not previous['regression_required']:
                continue
            assert name in papers and papers[name]['regression_required'], name + ': prior regression removed'
            current = papers[name]
            assert current['target'] == previous['target'], name + ': existing build target changed'
            if previous['status'] != 'certified':
                continue
            assert current['status'] == 'certified', name + ': certified status removed'
            for key in ['semantic_baseline', 'endpoints']:
                assert current[key] == previous[key], name + ': protected contract path changed'
                assert (ROOT / current[key]).read_bytes() == old_bytes(args.base_ref, previous[key]), name + ': protected contract changed'
            config = 'lean/ComparatorChallenges/' + name + 'Regression.json'
            assert (ROOT / config).read_bytes() == old_bytes(args.base_ref, config), name + ': protected comparator config changed'
    print(json.dumps(targets) if args.matrix else 'Catalogue valid: ' + ', '.join(targets))

if __name__ == '__main__':
    try:
        main()
    except (AssertionError, KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('Catalogue rejected: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
