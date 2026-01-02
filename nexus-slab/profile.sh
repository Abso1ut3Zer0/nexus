#!/bin/bash
# Perf profiling script for nexus-slab
#
# Usage: ./profile.sh [-r REPEATS] [-c CPU] [-t] [BENCHMARK]
#
# Benchmarks:
#   insert, get, churn, indexing    - nexus-slab only (for perf record/stat)
#   insert-cmp, get-cmp, churn-cmp, indexing-cmp
#                                   - cycle-accurate comparison vs slab crate
#   all                             - all nexus-slab benchmarks
#   compare                         - all comparison benchmarks
#
# Options:
#   -r REPEATS   Number of times to run each benchmark (default: 10)
#                perf stat will show mean ± stddev with -r > 1
#   -c CPU       CPU core to pin to (default: 0)
#   -t           Toggle turbo boost on/off (requires sudo)
#
# Examples:
#   ./profile.sh -t             # Toggle turbo boost (disable if on, enable if off)
#   ./profile.sh compare        # Run all cycle-accurate comparisons
#   ./profile.sh insert-cmp     # Compare insert: nexus-slab vs slab
#   ./profile.sh -r 50 churn    # Run churn 50 times with perf stat
#   ./profile.sh -c 2 insert    # Pin to CPU 2
#
# For best results:
#   1. Run with -t first to disable turbo
#   2. Close other applications
#   3. Use -r 10 or higher for stable measurements
#   4. Run with -t again to re-enable turbo when done
#
# Requires: perf (linux-tools-common)

set -e

# Parse options
REPEATS=10
CPU=0
TOGGLE=0

while getopts "r:c:t" opt; do
    case $opt in
        r)
            REPEATS=$OPTARG
            ;;
        c)
            CPU=$OPTARG
            ;;
        t)
            TOGGLE=1
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
    esac
done
shift $((OPTIND-1))

# Toggle turbo boost
if [ $TOGGLE -eq 1 ]; then
    if [ -f /sys/devices/system/cpu/intel_pstate/no_turbo ]; then
        current=$(cat /sys/devices/system/cpu/intel_pstate/no_turbo)
        if [ "$current" = "1" ]; then
            echo 0 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null
            echo "Turbo boost ENABLED"
        else
            echo 1 | sudo tee /sys/devices/system/cpu/intel_pstate/no_turbo > /dev/null
            echo "Turbo boost DISABLED (for stable benchmarks)"
        fi
    elif [ -d /sys/devices/system/cpu/cpufreq ]; then
        current=$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor)
        if [ "$current" = "powersave" ]; then
            for gov in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
                echo "performance" | sudo tee "$gov" > /dev/null
            done
            echo "CPU governor set to PERFORMANCE (turbo enabled)"
        else
            for gov in /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor; do
                echo "powersave" | sudo tee "$gov" > /dev/null
            done
            echo "CPU governor set to POWERSAVE (turbo disabled)"
        fi
    else
        echo "Error: Could not find turbo boost control"
        exit 1
    fi
    exit 0
fi

BENCH=${1:-all}

# Check turbo status
get_turbo_status() {
    if [ -f /sys/devices/system/cpu/intel_pstate/no_turbo ]; then
        local status=$(cat /sys/devices/system/cpu/intel_pstate/no_turbo)
        if [ "$status" = "0" ]; then
            echo "ON (noisy)"
        else
            echo "OFF (stable)"
        fi
    else
        echo "unknown"
    fi
}

# Build release binaries
echo "Building release binaries..."
cargo build --release \
    --bin perf_nexus_slab_insert \
    --bin perf_nexus_slab_get \
    --bin perf_nexus_slab_churn \
    --bin perf_nexus_slab_indexing \
    --example perf_insert_cycles \
    --example perf_get_cycles \
    --example perf_churn_cycles \
    --example perf_indexing_cycles \
    2>/dev/null

TURBO_STATUS=$(get_turbo_status)
echo "Configuration: CPU=$CPU, REPEATS=$REPEATS, Turbo=$TURBO_STATUS"
if [ "$TURBO_STATUS" = "ON (noisy)" ]; then
    echo "TIP: Run './profile.sh -t' to disable turbo for stable results"
fi
echo ""

# Common perf events
EVENTS="cycles,instructions,cache-references,cache-misses,L1-dcache-loads,L1-dcache-load-misses,branches,branch-misses"

run_perf() {
    local name=$1
    local bin=$2
    
    echo ""
    echo "=========================================="
    echo "Profiling: $name (repeats: $REPEATS, CPU: $CPU)"
    echo "=========================================="
    
    echo ""
    echo "--- perf stat ---"
    taskset -c $CPU perf stat -r $REPEATS -e $EVENTS ./target/release/$bin 2>&1 | tail -25
    
    echo ""
    echo "To get detailed profile:"
    echo "  taskset -c $CPU perf record -g ./target/release/$bin"
    echo "  perf report"
}

run_cycles() {
    local name=$1
    local example=$2
    
    echo ""
    echo "=========================================="
    echo "Cycle comparison: $name (CPU: $CPU)"
    echo "=========================================="
    echo ""
    
    taskset -c $CPU ./target/release/examples/$example
}

case $BENCH in
    # nexus-slab only (for perf stat/record)
    insert)
        run_perf "INSERT" "perf_nexus_slab_insert"
        ;;
    get)
        run_perf "GET (sequential)" "perf_nexus_slab_get"
        ;;
    churn)
        run_perf "CHURN (insert+remove)" "perf_nexus_slab_churn"
        ;;
    indexing)
        run_perf "INDEXING (random access)" "perf_nexus_slab_indexing"
        ;;
    all)
        run_perf "INSERT" "perf_nexus_slab_insert"
        run_perf "GET (sequential)" "perf_nexus_slab_get"
        run_perf "CHURN (insert+remove)" "perf_nexus_slab_churn"
        run_perf "INDEXING (random access)" "perf_nexus_slab_indexing"
        ;;
    
    # Cycle-accurate comparisons (nexus-slab vs slab crate)
    insert-cmp)
        run_cycles "INSERT" "perf_insert_cycles"
        ;;
    get-cmp)
        run_cycles "GET" "perf_get_cycles"
        ;;
    churn-cmp)
        run_cycles "CHURN" "perf_churn_cycles"
        ;;
    indexing-cmp)
        run_cycles "INDEXING" "perf_indexing_cycles"
        ;;
    compare)
        run_cycles "INSERT" "perf_insert_cycles"
        run_cycles "GET" "perf_get_cycles"
        run_cycles "CHURN" "perf_churn_cycles"
        run_cycles "INDEXING" "perf_indexing_cycles"
        ;;
    
    *)
        echo "Usage: $0 [-r REPEATS] [-c CPU] [-t] [BENCHMARK]"
        echo ""
        echo "Benchmarks (nexus-slab only, for perf stat/record):"
        echo "  insert, get, churn, indexing, all"
        echo ""
        echo "Comparisons (cycle-accurate, nexus-slab vs slab crate):"
        echo "  insert-cmp, get-cmp, churn-cmp, indexing-cmp, compare"
        echo ""
        echo "Options:"
        echo "  -r REPEATS   Number of times to run perf stat (default: 10)"
        echo "  -c CPU       CPU core to pin to (default: 0)"
        echo "  -t           Toggle turbo boost on/off (requires sudo)"
        echo ""
        echo "Workflow:"
        echo "  $0 -t                    # Disable turbo boost"
        echo "  $0 compare               # Run all cycle comparisons"
        echo "  $0 -t                    # Re-enable turbo boost when done"
        exit 1
        ;;
esac

echo ""
echo "=========================================="
echo "Key metrics to look for:"
echo "=========================================="
echo "- IPC (instructions per cycle): Higher is better, >2 is good"
echo "- Cache miss rate: Lower is better"
echo "- L1 miss rate: (L1-dcache-load-misses / L1-dcache-loads)"
echo "- Branch miss rate: (branch-misses / branches)"
echo ""
echo "Results pinned to CPU $CPU."
echo "Don't forget: './profile.sh -t' to re-enable turbo when done!"
