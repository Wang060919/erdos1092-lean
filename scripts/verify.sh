#!/usr/bin/env bash
set -euo pipefail
source "$(dirname -- "${BASH_SOURCE[0]}")/runtime.sh"
task_log_dir="${task_project_dir}/.lake/verification"
mkdir -p -- "${task_log_dir}"
python3 scripts/check_manifest.py
python3 scripts/check_manifest.py --dependencies
"${task_runtime_bin}/lean" --version | tee "${task_log_dir}/lean-version.log"
"${task_runtime_bin}/lake" --version | tee "${task_log_dir}/lake-version.log"
"${task_project_dir}/scripts/lake.sh" --wfail build 2>&1 | tee "${task_log_dir}/build.log"
"${task_project_dir}/scripts/lean.sh" verification/CheckScope.lean 2>&1 | tee "${task_log_dir}/scope.log"
python3 scripts/check_manifest.py --axioms verification/CheckScope.lean "${task_log_dir}/scope.log" --expected-count 4
"${task_project_dir}/scripts/lean.sh" verification/CheckAxioms.lean 2>&1 | tee "${task_log_dir}/axioms.log"
python3 scripts/check_manifest.py --axioms verification/CheckAxioms.lean "${task_log_dir}/axioms.log" --expected-count 68
for task_module in Basic Parameters Transport Winding Cuts Outer Main; do
  "${task_project_dir}/scripts/lake.sh" env leanchecker --verbose "Erdos1092.${task_module}" 2>&1 \
    | tee "${task_log_dir}/kernel-${task_module}.log"
done
python3 scripts/check_manifest.py
python3 scripts/check_manifest.py --dependencies
printf 'Build, original-scope checks, 68 declaration axiom checks and seven proof-module kernel replays passed.\n'
