#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/runtime.sh"
exec timeout --signal=TERM --kill-after=10s 300 "${task_runtime_bin}/lake" env lean -j 2 \
  -DautoImplicit=false -DmaxHeartbeats=1000000 -DmaxRecDepth=2048 "$@"
