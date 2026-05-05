#! /bin/bash

set -euo pipefail


usage() {
    cat <<'EOF'
Run TLC model checking locally on this machine.

Usage:
  ./tla+/tlc_local_check.sh -s <SPEC_DIR> -n <SPEC_NAME> [OPTIONS]

Options:
  -s, --spec-dir <DIR>        spec folder under tla+/ (required)
  -n, --spec-name <NAME>      e.g. MultiPaxos (required)
  -c, --cfg-suffix <SUFFIX>   e.g. small -> MultiPaxos_MC_small.cfg
      --fpmem-ratio <F>       TLC -fpmem value, 0<F<=1 (default 0.25)
      --jvm-max-heap <SIZE>   JVM -Xmx max heap, e.g. 450G (default: 90% of system RAM)
      --states-dir <DIR>      TLC -metadir path (default /tmp/tlc-<SPEC_DIR>/states)
  -h, --help                  show this help

Example:
  ./tla+/tlc_local_check.sh -s multipaxos_smr_style -n MultiPaxos -c small
EOF
}


if [ "$(id -u)" -eq 0 ]; then
    echo "Please run this script as normal user!" >&2
    exit 1
fi


default_jvm_max_heap() {
    local total_kb mem_mb
    if [[ -r /proc/meminfo ]]; then
        total_kb="$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)"
        mem_mb=$(( total_kb * 9 / 10 / 1024 ))
    elif command -v sysctl >/dev/null 2>&1 && sysctl -n hw.memsize >/dev/null 2>&1; then
        mem_mb=$(( $(sysctl -n hw.memsize) * 9 / 10 / 1024 / 1024 ))
    else
        echo "ERROR: cannot detect system RAM; pass --jvm-max-heap explicitly" >&2
        exit 1
    fi
    echo "${mem_mb}M"
}

SPEC_DIR=""
SPEC_NAME=""
CFG_SUFFIX=""
FPMEM_RATIO="0.5"
XMX=""
STATES_DIR=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        -s|--spec-dir)    SPEC_DIR="$2"; shift 2 ;;
        -n|--spec-name)   SPEC_NAME="$2"; shift 2 ;;
        -c|--cfg-suffix)  CFG_SUFFIX="$2"; shift 2 ;;
        --fpmem-ratio)    FPMEM_RATIO="$2"; shift 2 ;;
        --jvm-max-heap)   XMX="$2"; shift 2 ;;
        --states-dir)     STATES_DIR="$2"; shift 2 ;;
        -h|--help)        usage; exit 0 ;;
        --)               shift; break ;;
        *)                echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if [[ -z "$SPEC_DIR" || -z "$SPEC_NAME" ]]; then
    echo "--spec-dir and --spec-name are required" >&2
    usage >&2
    exit 2
fi

[[ -z "$XMX" ]] && XMX="$(default_jvm_max_heap)"
[[ -z "$STATES_DIR" ]] && STATES_DIR="/tmp/tlc-${SPEC_DIR}/states"


SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

cfg_tag=""
[[ -n "$CFG_SUFFIX" ]] && cfg_tag="_${CFG_SUFFIX}"

cd "${SCRIPT_DIR}/${SPEC_DIR}" || { echo "ERROR: folder tla+/${SPEC_DIR} not found" >&2; exit 1; }

exec java -XX:+UseParallelGC -Xmx"${XMX}" \
     -jar "${REPO_ROOT}/../tla2tools.jar" \
     -cleanup \
     -difftrace \
     -fpmem "$FPMEM_RATIO" \
     -workers auto \
     -metadir "$STATES_DIR" \
     -config "${SPEC_NAME}_MC${cfg_tag}.cfg" \
     "${SPEC_NAME}_MC.tla"
