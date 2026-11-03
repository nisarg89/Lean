#!/usr/bin/env bash
# Compatibility entry point for the BF reader; new papers use verify-paper.py.
set -euo pipefail
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
args=()
case "${BF_SKIP_CACHE:-0}" in
  0) ;;
  1) args+=(--skip-cache) ;;
  *) echo 'BF_SKIP_CACHE must be 0 or 1.' >&2; exit 2 ;;
esac
exec python3 "$script_dir/verify-paper.py" BF "${args[@]}" "$@"
