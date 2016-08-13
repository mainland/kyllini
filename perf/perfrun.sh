#!/bin/sh
set -e

# Number of runs per benchmark
N=10

perf_run() {
    TESTNAME=$1
    SUBDIR=$2
    TESTBIN=$3
    NSAMPLES=$4
    NRUNS=$5

    if [ "$PLATFORM" = "ziria" ] ; then
        EXE=out
        ARGS="--input=dummy --output=dummy --dummy-samples=$NSAMPLES"
    else
        EXE=exe
        ARGS="--input-dev=dummy --output-dev=dummy --dummy-samples=$NSAMPLES"
    fi
    
    (cd "$WIFIDIR/$SUBDIR" && make clean && COMPILER=gcc make -B "$TESTBIN.$EXE") >/dev/null 2>&1

    for i in `seq 1 $NRUNS`; do
        perf stat -x ' ' -e branch-instructions,branch-misses,cache-misses,cpu-cycles,instructions,context-switches,cpu-migrations,page-faults \
             "$WIFIDIR/$SUBDIR/$TESTBIN.$EXE" $ARGS 2>&1 | \
            awk -v platform="$PLATFORM" -v gitRev="$GITREV" -v test="$TESTNAME" -v nsamples="$NSAMPLES" -f perf.awk
    done
    
    (cd "$WIFIDIR/$SUBDIR" && make clean) >/dev/null 2>&1
}

platform_perf() {
    perf_run "RX 6Mbps"  perf testRX6Mbps  100000000 $N
    perf_run "RX 9Mbps"  perf testRX9Mbps  100000000 $N
    perf_run "RX 12Mbps" perf testRX12Mbps 100000000 $N
    perf_run "RX 18Mbps" perf testRX18Mbps 100000000 $N
    perf_run "RX 24Mbps" perf testRX24Mbps 100000000 $N
    perf_run "RX 36Mbps" perf testRX36Mbps 100000000 $N
    perf_run "RX 48Mbps" perf testRX48Mbps 100000000 $N
    perf_run "RX 54Mbps" perf testRX54Mbps 100000000 $N

    perf_run "RX CCA" perf testRXCCA 100000000 $N

    perf_run "TX 6Mbps"  perf testTX6Mbps  100000000 $N
    perf_run "TX 9Mbps"  perf testTX9Mbps  100000000 $N
    perf_run "TX 12Mbps" perf testTX12Mbps 100000000 $N
    perf_run "TX 18Mbps" perf testTX18Mbps 100000000 $N
    perf_run "TX 24Mbps" perf testTX24Mbps 100000000 $N
    perf_run "TX 36Mbps" perf testTX36Mbps 100000000 $N
    perf_run "TX 48Mbps" perf testTX48Mbps 100000000 $N
    perf_run "TX 54Mbps" perf testTX54Mbps 100000000 $N

    perf_run "Encoding 12" transmitter/perf test_encoding_12_perf 100000000 $N
    perf_run "Encoding 23" transmitter/perf test_encoding_23_perf 100000000 $N
    perf_run "Encoding 34" transmitter/perf test_encoding_34_perf 100000000 $N

    perf_run "IFFT" transmitter/perf test_ifft 100000000 $N

    perf_run "Interleaving BPSK" transmitter/perf test_interleaving_bpsk_perf 100000000 $N
    perf_run "Interleaving QPSK" transmitter/perf test_interleaving_qpsk_perf 100000000 $N
    perf_run "Interleaving 16QAM" transmitter/perf test_interleaving_16qam_perf 100000000 $N
    perf_run "Interleaving 64QAM" transmitter/perf test_interleaving_64qam_perf 100000000 $N

    perf_run "Modulating BPSK" transmitter/perf test_modulating_bpsk_perf 10000000000 $N
    perf_run "Modulating QPSK" transmitter/perf test_modulating_qpsk_perf 10000000000 $N
    perf_run "Modulating 16QAM" transmitter/perf test_modulating_16qam_perf 10000000000 $N
    perf_run "Modulating 64QAM" transmitter/perf test_modulating_64qam_perf 10000000000 $N

    perf_run "Map OFDM" transmitter/perf test_map_ofdm_perf 100000000 $N

    perf_run "Scramble" transmitter/perf test_scramble_perf 100000000 $N

    perf_run "CCA" receiver/perf testCCA 100000000 $N
    perf_run "Channel Equalization" receiver/perf testChannelEqualization 100000000 $N
    perf_run "Data symbol" receiver/perf testDataSymbol 10000000000 $N
    perf_run "Down-sample" receiver/perf testDownSample 10000000000 $N
    perf_run "Pilot tracking" receiver/perf testPilotTrack 100000000 $N
    perf_run "Remove DC" receiver/perf testRemoveDC 100000000 $N
    perf_run "FFT" receiver/perf testFFT 100000000 $N
    perf_run "LTS" receiver/perf testLTS 100000000 $N
    perf_run "Viterbi" receiver/perf testViterbi 100000000 $N

    perf_run "De-interleave BPSK" receiver/perf testDeinterleaveBPSK 100000000 $N
    perf_run "De-interleave QPSK" receiver/perf testDeinterleaveQPSK 100000000 $N
    perf_run "De-interleave QAM16" receiver/perf testDeinterleaveQAM16 100000000 $N
    perf_run "De-interleave QAM64" receiver/perf testDeinterleaveQAM64 100000000 $N

    perf_run "De-map BPSK" receiver/perf testDemapBPSK 100000000 $N
    perf_run "De-map QPSK" receiver/perf testDemapQPSK 100000000 $N
    perf_run "De-map QAM16" receiver/perf testDemapQAM16 100000000 $N
    perf_run "De-map QAM64" receiver/perf testDemapQAM64 100000000 $N
}

echo "platform,gitRev,test,nsamples,cpuTime,realTime,branchInstructions,branchMisses,cacheMisses,cpuCycles,instructions,contextSwitches,cpuMigrations,pageFaults"

while [ "$#" -ne 0 ]; do
    PLATFORM=$1
    GITREV=$2
    WIFIDIR=$3
    shift
    shift
    shift
    
    platform_perf
done
