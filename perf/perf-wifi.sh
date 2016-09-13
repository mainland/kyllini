#!/bin/sh
. "$(dirname "$0")/perf.sh"

WIFIDIR=../examples/wifi

REV=$(githash .)
FILE="wifi-$(date '+%Y-%m-%d')-$REV.csv"

truncate -s 0 "$FILE"

(record_perf_tests wifi "$REV" "$WIFIDIR") >>"$FILE"
