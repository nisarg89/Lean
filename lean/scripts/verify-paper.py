#!/usr/bin/env python3
"""Build one catalogue target, audit its endpoints, compare a sealed baseline."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[2]
WORKSPACE = ROOT / 'lean'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(command, log=None):
    print('+ ' + ' '.join(map(str, command)), flush=True)
    if log is None:
        subprocess.run(command, cwd=WORKSPACE, check=True)
    else:
        with log.open('w') as out:
            subprocess.run(command, cwd=WORKSPACE, stdout=out, stderr=subprocess.STDOUT, check=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paper')
    parser.add_argument('--skip-cache', action='store_true')
    parser.add_argument('--skip-comparator', action='store_true', help='Local build/audit only; not a release gate')
    args = parser.parse_args()
    catalogue = json.loads((ROOT / 'certificates.json').read_text())
    paper = catalogue['papers'][args.paper]
    if not paper['regression_required'] or not paper['target']:
        parser.error('This paper is not an executable certificate target')
    logs = WORKSPACE / 'artifacts/verification' / args.paper
    logs.mkdir(parents=True, exist_ok=True)
    # No previous success-looking reports survive a failed new invocation.
    for name in ['build.log', 'axioms.log', 'comparator.log', 'cache.log']:
        (logs / name).unlink(missing_ok=True)
    lock = WORKSPACE / 'lake-manifest.json'
    before = lock.read_bytes()
    try:
        if not args.skip_cache:
            run(['lake', 'exe', 'cache', 'get'], logs / 'cache.log')
        run(['lake', 'build', '+' + paper['target']], logs / 'build.log')
        run(['lake', 'env', 'lean', paper['audit_file']], logs / 'axioms.log')
        run([sys.executable, str(ROOT / paper['audit_checker']), str(logs / 'axioms.log'),
             '--expected', str(ROOT / paper['endpoints'])])
        baseline_ref = paper['semantic_baseline']
        if baseline_ref is None:
            if paper['status'] == 'certified':
                raise ValueError('Certified entry has no sealed semantic baseline')
            print('Certificate build and axiom audit passed; no cross-commit semantic baseline configured.')
        elif args.skip_comparator:
            print('LOCAL CHECK ONLY: sealed semantic comparison explicitly skipped.')
        else:
            baseline = json.loads((ROOT / baseline_ref).read_text())
            config = WORKSPACE / 'ComparatorChallenges' / (args.paper + 'Regression.json')
            if digest(config) != baseline['comparator_config_sha256']:
                raise ValueError('Comparator config differs from sealed baseline')
            if digest(ROOT / paper['endpoints']) != baseline['endpoints_sha256']:
                raise ValueError('Endpoint list differs from sealed baseline')
            if (WORKSPACE / 'lean-toolchain').read_text().strip() != baseline['toolchain']:
                raise ValueError('Toolchain differs from sealed baseline; use reviewed upgrade process')
            export = logs / 'baseline.ndjson'
            if not export.exists() or digest(export) != baseline['export_sha256']:
                partial = export.with_suffix('.partial')
                partial.unlink(missing_ok=True)
                with urllib.request.urlopen(baseline['export_url'], timeout=60) as source, partial.open('wb') as out:
                    while True:
                        block = source.read(1024 * 1024)
                        if not block:
                            break
                        out.write(block)
                if digest(partial) != baseline['export_sha256']:
                    partial.unlink(missing_ok=True)
                    raise ValueError('Downloaded baseline SHA256 mismatch')
                partial.replace(export)
            run(['lake', 'comparator', '--config=' + str(config),
                 '--challenge-from-export=' + str(export)], logs / 'comparator.log')
    finally:
        if lock.read_bytes() != before:
            raise ValueError('Dependency lock changed during verification; run rejected')
    print('Checks completed for ' + args.paper + '; logs: ' + str(logs))

if __name__ == '__main__':
    try:
        main()
    except (KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
        print('Verification failed: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
