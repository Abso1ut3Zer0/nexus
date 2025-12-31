#!/bin/bash
# Run all SPSC benchmarks pinned to specific CPU cores
# Usage: sudo ./perf_compare.sh [core_mask]
# Example: sudo ./perf_compare.sh 0,2   (pins to cores 0 and 2)

CORES="${1:-0,2}"
EVENTS="cycles,instructions,cache-references,cache-misses,L1-dcache-load-misses"

echo "========================================"
echo "SPSC Performance Comparison"
echo "Pinned to cores: $CORES"
echo "========================================"
echo ""

# Build all benchmarks first
echo "Building benchmarks..."
cargo build --release --bench perf_raw --bench perf_minimal --bench perf_rtrb --bench perf_rtrb_clone 2>/dev/null

echo ""
echo "Running 3 iterations each, pinned to cores $CORES"
echo ""

for i in 1 2 3; do
    echo "========== Iteration $i =========="
    echo ""
    
    echo "--- nexus_raw ---"
    taskset -c $CORES perf stat -e $EVENTS ./target/release/deps/perf_raw-* 2>&1 | grep -E "(iterations|cycles|instructions|cache|time elapsed)"
    echo ""
    
    echo "--- nexus_minimal ---"
    taskset -c $CORES perf stat -e $EVENTS ./target/release/deps/perf_minimal-* 2>&1 | grep -E "(iterations|cycles|instructions|cache|time elapsed)"
    echo ""
    
    echo "--- rtrb_clone ---"
    taskset -c $CORES perf stat -e $EVENTS ./target/release/deps/perf_rtrb_clone-* 2>&1 | grep -E "(iterations|cycles|instructions|cache|time elapsed)"
    echo ""
    
    echo "--- rtrb (original) ---"
    taskset -c $CORES perf stat -e $EVENTS ./target/release/deps/perf_rtrb-* 2>&1 | grep -E "(iterations|cycles|instructions|cache|time elapsed)"
    echo ""
done

echo "========================================"
echo "Done!"
echo "========================================"
