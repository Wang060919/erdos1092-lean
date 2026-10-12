#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/runtime.sh"
exec timeout --signal=TERM --kill-after=10s 900 "${task_runtime_bin}/lake" "$@"
