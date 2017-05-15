#!/bin/sh
. "$(dirname "$0")/perf.sh"

ZIRIADIR=../ziria/code/WiFi
ZIRIAREV=$(githash $ZIRIADIR)

WIFIDIR=../examples/wifi
REV=$(githash .)

# Number of runs per benchmark
N=10

(record_perf_tests ziria "$ZIRIAREV" "$ZIRIADIR" kzc "$REV" "$WIFIDIR") >"icfp17.csv"
