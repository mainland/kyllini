#!/bin/sh
. "$(dirname "$0")/perf.sh"

WIFIDIR=../examples/wifi-sid

REV=$(githash .)
FILE="wifi-sid-$(date '+%Y-%m-%d')-$REV.csv"

truncate -s 0 "$FILE"

(record_perf_tests wifi-sid "$REV" "$WIFIDIR") >>"$FILE"
