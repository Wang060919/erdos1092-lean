#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/runtime.sh"
mapfile -t task_imports < <(awk '$1 == "import" && $2 ~ /^Mathlib\./ { print $2 }' Erdos1092/*.lean | sort -u)
if (( ${#task_imports[@]} == 0 )); then
  printf 'No Mathlib imports were found.\n' >&2
  exit 1
fi
export MATHLIB_NO_CACHE_ON_UPDATE=1
exec "${task_project_dir}/scripts/lake.sh" exe cache get \
  --repo=leanprover-community/mathlib4 --cache-from=master,legacy "${task_imports[@]}"
