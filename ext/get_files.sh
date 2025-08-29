#!/bin/bash
set -euo pipefail

# CONTROL THE SWEEP HERE
# =======================
TIMEOUT=900 # 15 minutes
MEMOUT=8192 # 8 GB
SIZE_MIN=4
SIZE_MAX=4
SIZE_STEP=1
# =======================

# Where this repo lives; resolved relative to this script (../)
REPODIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Build output location (binary expected at $REPODIR/build/bin/benchmarks)
BENCHBIN="${REPODIR}/build/bin/benchmarks"

# Output root; a timestamped subdir will be created
OUTPUT_ROOT="${REPODIR}/out"

# CSV fields (must match what brunch.py can populate)
FORMAT_FIELDS="base:bench:size:result:Cpu:Status"

# Job name prefix (for SLURM)
JOBNAME_PREFIX="bench_sweep"

# =======================
# Derived paths
# =======================
TS="$(date +%F_%H-%M-%S)"
OUTDIR="${OUTPUT_ROOT}/benchmarks_${TS}"
SLURM_DIR="${OUTDIR}/slurm"
TOOL_DIR="${OUTDIR}/tool"
STATS_DIR="${OUTDIR}/stats"
SPECS_FILE="${OUTDIR}/specs.list"

# =======================
# Prep dirs
# =======================
mkdir -p "${SLURM_DIR}" "${TOOL_DIR}" "${STATS_DIR}"

# =======================
# Discover enabled benchmarks
# =======================
if [[ ! -x "${BENCHBIN}" ]]; then
  echo "error: benchmarks binary not found or not executable at: ${BENCHBIN}" >&2
  exit 1
fi

echo "# Generating specs from enabled benchmarks and size sweep..."
BENCHES=()
while IFS= read -r line; do
  [[ -n "$line" ]] && BENCHES+=("$line")
done < <("${BENCHBIN}" --list)

if [[ ${#BENCHES[@]} -eq 0 ]]; then
  echo "error: no enabled benchmarks returned by '${BENCHBIN} --list'" >&2
  exit 1
fi

# =======================
# Generate specs.list (bench:size)
# =======================
: > "${SPECS_FILE}"  # truncate/create
for b in "${BENCHES[@]}"; do
  # skip blanks just in case
  [[ -z "$b" ]] && continue
  for (( sz=SIZE_MIN; sz<=SIZE_MAX; sz+=SIZE_STEP )); do
    echo "${b}:${sz}" >> "${SPECS_FILE}"
  done
done

NUMSPECS=$(wc -l < "${SPECS_FILE}" | tr -d ' ')
if [[ "${NUMSPECS}" -eq 0 ]]; then
  echo "No specs generated (check SIZE_* bounds?)" >&2
  exit 1
fi

ZBMAX=$((NUMSPECS - 1))
echo "# Specs generated: ${NUMSPECS}"
echo "# Output dir: ${OUTDIR}"

# =======================
# Submit SLURM array
# =======================
JOBNAME="${JOBNAME_PREFIX}_${TS}"
echo "# Submitting array: 0..${ZBMAX} (job-name: ${JOBNAME})"

sbatch \
  --job-name "${JOBNAME}" \
  --array=0-"${ZBMAX}" \
  --output="${SLURM_DIR}/slurm_%A_%a.out" \
  --export=ALL,OUTDIR="${OUTDIR}",REPODIR="${REPODIR}",TIMEOUT="${TIMEOUT}",MEMOUT="${MEMOUT}",FORMAT_FIELDS="${FORMAT_FIELDS}" \
  "${REPODIR}/ext/run_files.cmd"

echo "# Submitted."