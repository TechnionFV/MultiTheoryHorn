#!/bin/bash
#SBATCH --job-name bench_run
set -euo pipefail

# Expected environment variables (exported by get_files.cmd via sbatch --export):
#   OUTDIR         → target output directory (has tool/, stats/, slurm/, specs.list)
#   REPODIR        → repo root (contains ext/brunch.py and build/bin/benchmarks)
#   TIMEOUT        → CPU time limit (seconds)
#   MEMOUT         → memory limit (MB)
#   FORMAT_FIELDS  → colon-separated header for CSV (e.g., base:bench:size:result:Cpu:Status)

: "${OUTDIR:?OUTDIR not set}"
: "${REPODIR:?REPODIR not set}"
: "${TIMEOUT:?TIMEOUT not set}"
: "${MEMOUT:?MEMOUT not set}"
: "${FORMAT_FIELDS:?FORMAT_FIELDS not set}"

SPECS_FILE="${OUTDIR}/specs.list"
BRUNCH="${REPODIR}/ext/brunch.py"
BENCHBIN="${REPODIR}/build/bin/benchmarks"

echo "Array meta:"
echo "  SLURM_ARRAY_JOB_ID  = ${SLURM_ARRAY_JOB_ID:-n/a}"
echo "  SLURM_ARRAY_TASK_ID = ${SLURM_ARRAY_TASK_ID:-n/a}"
echo "  OUTDIR              = ${OUTDIR}"
echo "  REPODIR             = ${REPODIR}"

# Get this task's spec (1-based sed index)
IDX=$(( SLURM_ARRAY_TASK_ID + 1 ))
SPEC="$(sed -n "${IDX}p" "${SPECS_FILE}")"

if [[ -z "${SPEC}" ]]; then
  echo "error: empty spec for task id ${SLURM_ARRAY_TASK_ID}" >&2
  exit 3
fi

echo "Spec: ${SPEC}"

# Run through brunch.py; placeholders expanded per spec
# NOTE: brunch.py will:
#   - record per-run .stats in ${OUTDIR}/stats/<bench>-<size>.stats
#   - append to unified CSV at ${OUTDIR}/stats/benchmarks_results.csv
#   - capture tool stdout into ${OUTDIR}/tool/<bench>-<size>.stdout
python3 "${BRUNCH}" \
  --out "${OUTDIR}" \
  --cpu "${TIMEOUT}" \
  --mem "${MEMOUT}" \
  --format "${FORMAT_FIELDS}" \
  "${SPEC}" \
  -- "${BENCHBIN}" --bench "{bench}" --size "{size}" --brunch