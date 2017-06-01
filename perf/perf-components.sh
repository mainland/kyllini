#!/bin/sh
. "$(dirname "$0")/perf.sh"

WIFIDIR=../examples/wifi-sid

GITREV=$(githash .)
FILE="components-$(date '+%Y-%m-%d')-$GITREV.csv"

truncate -s 0 "$FILE"

record_perf_tests() {        
    echo "platform,gitRev,test,nsamples,cpuTime,realTime,branchInstructions,branchMisses,cacheMisses,cpuCycles,instructions,contextSwitches,cpuMigrations,pageFaults"
    
    PLATFORM="base" run_perf_test "IFFT" transmitter/perf test_ifft 100000000 $N "-fno-autolut -fno-lut -fno-peval"
    PLATFORM="base" run_perf_test "FFT" receiver/perf testFFT 100000000 $N "-fno-autolut -fno-lut -fno-peval"
    PLATFORM="base" run_perf_test "Viterbi" receiver/perf testViterbi 100000000 $N "-fno-autolut -fno-lut -fno-peval"
    
    PLATFORM="lut" run_perf_test "IFFT" transmitter/perf test_ifft 100000000 $N "-fautolut -flut -fno-peval"
    PLATFORM="lut" run_perf_test "FFT" receiver/perf testFFT 100000000 $N "-fautolut -flut -fno-peval"
    PLATFORM="lut" run_perf_test "Viterbi" receiver/perf testViterbi 100000000 $N "-fautolut -flut -fno-peval"
    
    PLATFORM="peval" run_perf_test "IFFT" transmitter/perf test_ifft 100000000 $N
    PLATFORM="peval" run_perf_test "FFT" receiver/perf testFFT 100000000 $N
    PLATFORM="peval" run_perf_test "Viterbi" receiver/perf testViterbi 100000000 $N
    
    PLATFORM="peval-pure-ziria" run_perf_test "IFFT" transmitter/perf test_ifft 100000000 $N "-DPURE_ZIRIA"
    PLATFORM="peval-pure-ziria" run_perf_test "FFT" receiver/perf testFFT 100000000 $N "-DPURE_ZIRIA"
    PLATFORM="peval-pure-ziria" run_perf_test "Viterbi" receiver/perf testViterbi 100000000 $N "-DPURE_ZIRIA"
}

(record_perf_tests wifi "$GITREV" "$WIFIDIR") >>"$FILE"
