#! /bin/bash

set -euo pipefail


usage() {
    cat <<'EOF'
Run a distributed TLC worker (optionally with a fingerprint-set shard).

Usage:
  ./tla+/tlc_distr_worker.sh -r <worker|worker-fp> -m <HOST> [OPTIONS]

Options:
  -r, --role <ROLE>           worker | worker-fp (required)
  -m, --master <HOST>         master hostname/IP (required)
      --hostname <HOST>       value for -Djava.rmi.server.hostname (default: $(hostname -f))
      --worker-threads <N>    worker thread count (default: one per core)
      --jvm-max-heap <SIZE>   JVM max heap, e.g. 8G (default: 90% of system RAM)
  -h, --help                  show this help

'worker'     runs tlc2.tool.distributed.TLCWorker (compute only).
'worker-fp'  runs tlc2.tool.distributed.fp.TLCWorkerAndFPSet
             (compute + a shard of the fingerprint set).
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

ROLE=""
MASTER_HOST=""
WORKER_THREADS=""
RMI_HOST=""
XMX=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        -r|--role)          ROLE="$2"; shift 2 ;;
        -m|--master)        MASTER_HOST="$2"; shift 2 ;;
        --worker-threads)   WORKER_THREADS="$2"; shift 2 ;;
        --hostname)         RMI_HOST="$2"; shift 2 ;;
        --jvm-max-heap)     XMX="$2"; shift 2 ;;
        -h|--help)          usage; exit 0 ;;
        --)                 shift; break ;;
        *)                  echo "unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if [[ -z "$ROLE" || -z "$MASTER_HOST" ]]; then
    echo "--role and --master are required" >&2
    usage >&2
    exit 2
fi

case "$ROLE" in
    worker)     MAIN_CLASS="tlc2.tool.distributed.TLCWorker" ;;
    worker-fp)  MAIN_CLASS="tlc2.tool.distributed.fp.TLCWorkerAndFPSet" ;;
    *)          echo "--role must be 'worker' or 'worker-fp'" >&2; exit 2 ;;
esac

[[ -z "$XMX" ]] && XMX="$(default_jvm_max_heap)"


SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
JAR_PATH="${REPO_ROOT}/../tla2tools.jar"

[[ -z "$RMI_HOST" ]] && RMI_HOST="$(hostname -f)"

jvm_props=(-Djava.rmi.server.hostname="$RMI_HOST")
if [[ -n "$WORKER_THREADS" ]]; then
    jvm_props+=(-Dtlc2.tool.distributed.TLCWorker.threadCount="$WORKER_THREADS")
fi

echo "TLC ${ROLE} on ${RMI_HOST} -> master ${MASTER_HOST}"

exec java -XX:+UseParallelGC "-Xmx${XMX}" \
     "${jvm_props[@]}" \
     -cp "$JAR_PATH" "$MAIN_CLASS" \
     "$MASTER_HOST"
