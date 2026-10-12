#!/usr/bin/env bash
# Shared runtime selection for the pinned project. Source this file from Bash.
set -euo pipefail

task_project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "${task_project_dir}"

task_expected_toolchain="leanprover/lean4:v4.33.0"
if [[ "$(<lean-toolchain)" != "${task_expected_toolchain}" ]]; then
  printf 'Unexpected lean-toolchain; expected %s\n' "${task_expected_toolchain}" >&2
  exit 1
fi

if [[ -n "${ERDOS1092_LEAN_BIN:-}" ]]; then
  if [[ ! -d "${ERDOS1092_LEAN_BIN}" ]]; then
    printf 'ERDOS1092_LEAN_BIN must name a directory containing lean, lake and leanchecker.\n' >&2
    exit 1
  fi
  task_runtime_bin="$(cd -- "${ERDOS1092_LEAN_BIN}" && pwd)"
else
  if ! task_path_lean="$(command -v lean)"; then
    printf 'Lean is not on PATH. Install the pinned Elan toolchain or set ERDOS1092_LEAN_BIN.\n' >&2
    exit 1
  fi
  task_runtime_prefix="$("${task_path_lean}" --print-prefix)"
  task_runtime_bin="${task_runtime_prefix}/bin"
fi

for task_program in lean lake leanchecker; do
  if [[ ! -x "${task_runtime_bin}/${task_program}" ]]; then
    printf 'Missing executable: %s/%s\n' "${task_runtime_bin}" "${task_program}" >&2
    exit 1
  fi
done

if [[ "$("${task_runtime_bin}/lean" --short-version)" != '4.33.0' ]]; then
  printf 'The selected Lean runtime is not version 4.33.0.\n' >&2
  exit 1
fi
if [[ "$("${task_runtime_bin}/lean" --githash)" != 'd8b18978322de05a8f3dba51ef03cf5461676c17' ]]; then
  printf 'The selected Lean runtime does not match the pinned 4.33.0 release commit.\n' >&2
  exit 1
fi
if [[ "$("${task_runtime_bin}/lake" --version)" != *'(Lean version 4.33.0)' ]]; then
  printf 'The selected Lake executable was not built with Lean 4.33.0.\n' >&2
  exit 1
fi
export PATH="${task_runtime_bin}:${PATH}"
