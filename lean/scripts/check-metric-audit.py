#!/usr/bin/env python3
"""Check coverage of the Lean metric-distortion audit invoked by verify-paper.py.

Lean itself checks each contract, all transitive axioms, and provider closure.
This script checks the expected audit commands remain present and the *already
successful* Lean subprocess left no error in its log; it is not a proof oracle.
"""
import argparse
import json
from pathlib import Path
import re
import sys

WORKSPACE = Path(__file__).resolve().parents[1]
AUDIT = WORKSPACE / '../manuscripts/RandomSizeMetricDistortion/CertificateAudit.lean'
CONTRACTS = WORKSPACE / 'verification/metric-distortion-contracts.json'
SHARED_SPECS = WORKSPACE / 'verification/voting-audits.json'
COMMAND = re.compile(r'^#metric_distortion_audit\s+(\S+)\s*:\s*(\S+)\s*$', re.M)
DEFINITION_COMMAND = re.compile(r'^#metric_distortion_audit_def\s+(\S+)\s*:\s*(\S+)\s*$', re.M)
EXPECTED_DEFINITIONS = [
    ('MetricDistortion.starLaw', 'MetricDistortion.Audit.Star.lawType'),
    ('MetricDistortion.starCertificateFor', 'MetricDistortion.Audit.Star.certificateForType'),
    ('MetricDistortion.starCertificate', 'MetricDistortion.Audit.Star.certificateType'),
]
ANSI = re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('log', type=Path)
    p.add_argument('--expected', type=Path, required=True)
    p.add_argument('--additional-log', type=Path, action='append', default=[])
    args = p.parse_args()
    endpoints = json.loads(args.expected.read_text())
    contracts = json.loads(CONTRACTS.read_text())
    if (not isinstance(endpoints, list) or len(endpoints) != 151 or
        any(not isinstance(name, str) or not name for name in endpoints) or
        len(set(endpoints)) != len(endpoints)):
        raise ValueError('expected 151 distinct audited theorems')
    if not isinstance(contracts, dict) or list(contracts) != endpoints:
        raise ValueError('contract mapping does not match expected endpoint order')
    audit_source = AUDIT.read_text()
    actual = COMMAND.findall(audit_source)
    if actual != list(contracts.items()):
        raise ValueError('Lean audit command names, contracts, or order differ from expected')
    if DEFINITION_COMMAND.findall(audit_source) != EXPECTED_DEFINITIONS:
        raise ValueError('expected paper-specific definition audits are missing or changed')
    log = ANSI.sub('', args.log.read_text())
    if re.search(r'^.*\berror(?:\([^\n)]*\))?:', log, re.M):
        raise ValueError('Lean audit log contains an error')
    shared = json.loads(SHARED_SPECS.read_text())
    if not isinstance(shared, list) or len(shared) != 2 or len(args.additional_log) != 2:
        raise ValueError('two expected shared audits and logs are required')
    required = [('../Library/Voting/Audit.lean', 'voting_audit'),
                ('../Library/Voting/Distortion/Audit.lean', 'distortion_audit')]
    count = 0
    for spec, (source, command), extra_log in zip(shared, required, args.additional_log):
        if not isinstance(spec, dict) or spec.get('source') != source or spec.get('command') != command:
            raise ValueError('unexpected shared audit source or command')
        contracts = spec.get('contracts')
        if not isinstance(contracts, dict) or not contracts:
            raise ValueError('shared audit expected contracts are missing')
        pattern = re.compile(r'^#'+re.escape(command)+r'[ \t]+(\S+)[ \t]*:[ \t]*(.+)$', re.M)
        if pattern.findall((WORKSPACE/source).read_text()) != list(contracts.items()):
            raise ValueError('shared Lean audit names, contracts, or order differ from expected')
        content = ANSI.sub('', extra_log.read_text())
        if re.search(r'^.*\berror(?:\([^\n)]*\))?:', content, re.M):
            raise ValueError('shared Lean audit log contains an error')
        count += len(contracts)
    print(f'Lean audit coverage OK: 151 paper theorems, 3 paper definitions and {count} shared theorems.')

if __name__ == '__main__':
    try:
        main()
    except (KeyError, OSError, ValueError) as error:
        print('Metric audit coverage FAILED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
