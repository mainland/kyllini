#!/bin/sh
set -e

# Number of runs per benchmark
N=100

githash() {
    DIR=$1
    shift

    BRANCH="$(cd $DIR && git symbolic-ref HEAD 2>/dev/null)" || BRANCH="detached-head"
    BRANCH=${BRANCH##refs/heads/}

    REV=$(cd $DIR && git rev-parse --short=8 HEAD)

    echo $BRANCH-$REV
}

run_perf_test() {
    TESTNAME=$1
    SUBDIR=$2
    TESTBIN=$3
    NSAMPLES=$4
    NRUNS=$5
    KZCFLAGS=$6
    CCFLAGS=$7

    if [ "$PLATFORM" = "ziria" ] ; then
        EXE=out
        ARGS="--input=dummy --output=dummy --dummy-samples=$NSAMPLES"
    else
        EXE=exe
        ARGS="--input-dev=dummy --output-dev=dummy --dummy-samples=$NSAMPLES"
    fi
    
    (cd "$WIFIDIR/$SUBDIR" && make clean && KZCFLAGS="$KZCFLAGS" CFLAGS="$CFLAGS" COMPILER=gcc make -B "$TESTBIN.$EXE") >/dev/null 2>&1

    for i in `seq 1 $NRUNS`; do
        perf stat -x ' ' -e branch-instructions,branch-misses,cache-misses,cpu-cycles,instructions,context-switches,cpu-migrations,page-faults \
             "$WIFIDIR/$SUBDIR/$TESTBIN.$EXE" $ARGS 2>&1 | \
            awk -v platform="$PLATFORM" -v gitRev="$GITREV" -v test="$TESTNAME" -v nsamples="$NSAMPLES" -f perf.awk
    done
    
    (cd "$WIFIDIR/$SUBDIR" && make clean) >/dev/null 2>&1
}

run_all_perf_tests() {
    run_perf_test "RX 6Mbps"  perf testRX6Mbps  100000000 $N
    run_perf_test "RX 9Mbps"  perf testRX9Mbps  100000000 $N
    run_perf_test "RX 12Mbps" perf testRX12Mbps 100000000 $N
    run_perf_test "RX 18Mbps" perf testRX18Mbps 100000000 $N
    run_perf_test "RX 24Mbps" perf testRX24Mbps 100000000 $N
    run_perf_test "RX 36Mbps" perf testRX36Mbps 100000000 $N
    run_perf_test "RX 48Mbps" perf testRX48Mbps 100000000 $N
    run_perf_test "RX 54Mbps" perf testRX54Mbps 100000000 $N

    run_perf_test "RX CCA" perf testRXCCA 100000000 $N

    run_perf_test "TX 6Mbps"  perf testTX6Mbps  100000000 $N
    run_perf_test "TX 9Mbps"  perf testTX9Mbps  100000000 $N
    run_perf_test "TX 12Mbps" perf testTX12Mbps 100000000 $N
    run_perf_test "TX 18Mbps" perf testTX18Mbps 100000000 $N
    run_perf_test "TX 24Mbps" perf testTX24Mbps 100000000 $N
    run_perf_test "TX 36Mbps" perf testTX36Mbps 100000000 $N
    run_perf_test "TX 48Mbps" perf testTX48Mbps 100000000 $N
    run_perf_test "TX 54Mbps" perf testTX54Mbps 100000000 $N

    run_perf_test "Encoding 12" transmitter/perf test_encoding_12_perf 100000000 $N
    run_perf_test "Encoding 23" transmitter/perf test_encoding_23_perf 100000000 $N
    run_perf_test "Encoding 34" transmitter/perf test_encoding_34_perf 100000000 $N

    run_perf_test "IFFT" transmitter/perf test_ifft 100000000 $N

    run_perf_test "Interleaving BPSK" transmitter/perf test_interleaving_bpsk_perf 100000000 $N
    run_perf_test "Interleaving QPSK" transmitter/perf test_interleaving_qpsk_perf 100000000 $N
    run_perf_test "Interleaving 16QAM" transmitter/perf test_interleaving_16qam_perf 100000000 $N
    run_perf_test "Interleaving 64QAM" transmitter/perf test_interleaving_64qam_perf 100000000 $N

    run_perf_test "Modulating BPSK" transmitter/perf test_modulating_bpsk_perf 10000000000 $N
    run_perf_test "Modulating QPSK" transmitter/perf test_modulating_qpsk_perf 10000000000 $N
    run_perf_test "Modulating 16QAM" transmitter/perf test_modulating_16qam_perf 10000000000 $N
    run_perf_test "Modulating 64QAM" transmitter/perf test_modulating_64qam_perf 10000000000 $N

    run_perf_test "Map OFDM" transmitter/perf test_map_ofdm_perf 100000000 $N

    run_perf_test "Scramble" transmitter/perf test_scramble_perf 100000000 $N

    run_perf_test "CCA" receiver/perf testCCA 100000000 $N
    run_perf_test "Channel Equalization" receiver/perf testChannelEqualization 100000000 $N
    run_perf_test "Data symbol" receiver/perf testDataSymbol 10000000000 $N
    run_perf_test "Down-sample" receiver/perf testDownSample 10000000000 $N
    run_perf_test "Pilot tracking" receiver/perf testPilotTrack 100000000 $N
    run_perf_test "Remove DC" receiver/perf testRemoveDC 100000000 $N
    run_perf_test "FFT" receiver/perf testFFT 100000000 $N
    run_perf_test "LTS" receiver/perf testLTS 100000000 $N
    run_perf_test "Viterbi" receiver/perf testViterbi 100000000 $N

    run_perf_test "De-interleave BPSK" receiver/perf testDeinterleaveBPSK 100000000 $N
    run_perf_test "De-interleave QPSK" receiver/perf testDeinterleaveQPSK 100000000 $N
    run_perf_test "De-interleave QAM16" receiver/perf testDeinterleaveQAM16 100000000 $N
    run_perf_test "De-interleave QAM64" receiver/perf testDeinterleaveQAM64 100000000 $N

    run_perf_test "De-map BPSK" receiver/perf testDemapBPSK 100000000 $N
    run_perf_test "De-map QPSK" receiver/perf testDemapQPSK 100000000 $N
    run_perf_test "De-map QAM16" receiver/perf testDemapQAM16 100000000 $N
    run_perf_test "De-map QAM64" receiver/perf testDemapQAM64 100000000 $N
}

record_perf_tests() {
    echo "platform,gitRev,test,nsamples,cpuTime,realTime,branchInstructions,branchMisses,cacheMisses,cpuCycles,instructions,contextSwitches,cpuMigrations,pageFaults"

    while [ "$#" -ne 0 ]; do
        PLATFORM=$1
        GITREV=$2
        WIFIDIR=$3
        shift
        shift
        shift

        run_all_perf_tests
    done
}
