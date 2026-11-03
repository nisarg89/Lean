#!/usr/bin/env python3
"""Export a previously checked certificate and prepare immutable baseline metadata.

Run only after a clean package build and endpoint audit. This tool does not
certify the catalogue entry or publish its artifact.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
WORKSPACE = ROOT / 'lean'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paper')
    parser.add_argument('--artifact-url', required=True, help='Planned immutable HTTPS release-asset URL')
    args = parser.parse_args()
    if not args.artifact_url.startswith('https://'):
        parser.error('Artifact URL must use HTTPS')
    paper = json.loads((ROOT / 'certificates.json').read_text())['papers'][args.paper]
    if not paper['regression_required']:
        parser.error('No certificate target for this entry')
    if subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT).strip():
        parser.error('Commit the checked source snapshot first; the working tree must be clean')
    commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
    config_path = WORKSPACE / 'ComparatorChallenges' / (args.paper + 'Regression.json')
    config = json.loads(config_path.read_text())
    targets = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind'] + config['theorem_names'] + config['permitted_axioms']
    output_dir = WORKSPACE / 'artifacts/verification' / args.paper
    output_dir.mkdir(parents=True, exist_ok=True)
    output = output_dir / 'baseline.ndjson'
    partial = output.with_suffix('.partial')
    try:
        with partial.open('wb') as out:
            subprocess.run(['lake', 'env', 'leanexport', paper['target'], '--', *targets],
                           cwd=WORKSPACE, stdout=out, check=True)
        if not partial.stat().st_size:
            raise ValueError('Empty export')
        partial.replace(output)
    finally:
        partial.unlink(missing_ok=True)
    baseline = {
        'source_commit': commit,
        'toolchain': (WORKSPACE / 'lean-toolchain').read_text().strip(),
        'export_url': args.artifact_url,
        'export_sha256': sha(output),
        'comparator_config_sha256': sha(config_path),
        'endpoints_sha256': sha(ROOT / paper['endpoints'])
    }
    metadata = output_dir / 'baseline-metadata.json'
    metadata.write_text(json.dumps(baseline, indent=2) + '\n')
    print('Export: ' + str(output))
    print('Draft metadata: ' + str(metadata))
    print('Next: compare this export, upload it at the exact URL, then seal the catalogue in a reviewed change.')

if __name__ == '__main__':
    main()
