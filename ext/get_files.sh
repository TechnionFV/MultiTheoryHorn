#!/bin/bash
set -euo pipefail

# ==========================================================
# CONTROL THE SWEEP HERE (no CLI args; edit this section)
# ==========================================================

TIMEOUT=7200   # CPU time limit in seconds (2 hours)
MEMOUT=16384   # Memory limit in MB (16 GB)
SIZE_MIN=4
SIZE_MAX=63    # inclusive
SIZE_STEP=1

# Benchmark type filter (all/multi/bv)
TYPE="all"

# debug mode (true/false) - adds more logging
# It is recommended to keep this false as it may clutter output files
# and slow down the runs.
DEBUG=true

# Use SLURM (true) or run locally (false).
# If set to true but `sbatch` is not found, we automatically fall back to local mode.
USE_SLURM=true

# ==========================================================
# Paths and derived locations
# ==========================================================

# Check if Z3_ROOT is defined in the environment if it's not exit
if [[ -z "${Z3_ROOT:-}" ]]; then
  echo "error: Z3_ROOT environment variable is not set" >&2
  exit 1
fi

export LD_LIBRARY_PATH=${Z3_ROOT}/build

# Repo root (resolve relative to this script)
REPODIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Benchmarks binary
BENCHBIN="${REPODIR}/build/bin/benchmarks"

# Output root; a timestamped subdir will be created
OUTPUT_ROOT="${REPODIR}/out"

# CSV fields (must match what brunch.py can populate)
FORMAT_FIELDS="base:bench:type:size:result:Cpu:Status"

# Job name prefix (for SLURM)
JOBNAME_PREFIX="bench_sweep"

# Derived paths
TS="$(date +%F_%H-%M-%S)"
OUTDIR="${OUTPUT_ROOT}/benchmarks_${TS}"
SLURM_DIR="${OUTDIR}/slurm"
TOOL_DIR="${OUTDIR}/tool"
STATS_DIR="${OUTDIR}/stats"
SPECS_FILE="${OUTDIR}/specs.list"

# Ensure dirs
mkdir -p "${OUTDIR}" "${SLURM_DIR}" "${TOOL_DIR}" "${STATS_DIR}"

# ==========================================================
# Discover enabled benchmarks
# ==========================================================
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

# ==========================================================
# Generate specs.list (bench:size)
# ==========================================================
: > "${SPECS_FILE}"  # truncate/create
for (( sz=SIZE_MIN; sz<=SIZE_MAX; sz+=SIZE_STEP )); do
  for b in "${BENCHES[@]}"; do
    [[ -z "$b" ]] && continue
    # Concatenate :multi or :bv to the spec based on TYPE
    if [[ "${TYPE}" == "multi" ]]; then
      echo "${b}:${sz}:multi" >> "${SPECS_FILE}"
    elif [[ "${TYPE}" == "bv" ]]; then
      echo "${b}:${sz}:bv" >> "${SPECS_FILE}"
    else
      echo "${b}:${sz}:multi" >> "${SPECS_FILE}"
      echo "${b}:${sz}:bv" >> "${SPECS_FILE}"
    fi
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

# ==========================================================
# Decide mode: SLURM vs Local
# ==========================================================
if [[ "${USE_SLURM}" == "true" ]] && command -v sbatch >/dev/null 2>&1; then
  # -------------------------
  # SLURM ARRAY SUBMISSION
  # -------------------------
  JOBNAME="${JOBNAME_PREFIX}_${TS}"
  echo "# Submitting SLURM array: 0..${ZBMAX} (job-name: ${JOBNAME})"

  sbatch \
    --job-name "${JOBNAME}" \
    --array=0-"${ZBMAX}" \
    --output="${SLURM_DIR}/slurm_%A_%a.out" \
    --export=ALL,OUTDIR="${OUTDIR}",REPODIR="${REPODIR}",TIMEOUT="${TIMEOUT}",MEMOUT="${MEMOUT}",FORMAT_FIELDS="${FORMAT_FIELDS}",DEBUG="${DEBUG}" \
    "${REPODIR}/ext/run_files.sh"

  echo "# Submitted."
else
  # -------------------------
  # LOCAL FALLBACK MODE
  # -------------------------
  echo "# Running locally (no SLURM)."
  echo "# This may take a while if NUMSPECS is large."

  BRUNCH="${REPODIR}/ext/brunch.py"

  if [[ ! -f "${BRUNCH}" ]]; then
    echo "error: brunch.py not found at ${BRUNCH}" >&2
    exit 1
  fi

  # We want the whole sweep even if one run fails; temporarily relax -e
  set +e
  i=0
  while IFS= read -r SPEC; do
    ((i++))
    [[ -z "${SPEC}" ]] && continue
    echo "[$i/${NUMSPECS}] Spec: ${SPEC}"

    # Invoke brunch.py, which will:
    #  - capture tool stdout to ${OUTDIR}/tool/<bench>-<size>.stdout
    #  - write per-run .stats and append to unified CSV in ${OUTDIR}/stats
    python3 "${BRUNCH}" \
      --out "${OUTDIR}" \
      --cpu "${TIMEOUT}" \
      --mem "${MEMOUT}" \
      --format "${FORMAT_FIELDS}" \
      "${SPEC}" \
      -- "${BENCHBIN}" --bench "{bench}" --size "{size}" "{multi}" --brunch $( [[ "${DEBUG}" == "true" ]] && echo "--debug" )

    rc=$? # capture return code of the python call
    if [[ $rc -ne 0 ]]; then
      echo "WARN: run failed for spec '${SPEC}' (rc=${rc}); continuing..." >&2
    fi
  done < "${SPECS_FILE}"
  set -e

  echo "# Local sweep complete. Results in: ${OUTDIR}"
fi
