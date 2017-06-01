#!/bin/sh
. "$(dirname "$0")/perf.sh"

WIFIBRANCH=$1
shift

WIFIDIR="../examples/$WIFIBRANCH"

REV=$(githash .)
FILE="$WIFIBRANCH-$(date '+%Y-%m-%d')-$REV.csv"

truncate -s 0 "$FILE"

(record_perf_tests "$WIFIBRANCH" "$REV" "$WIFIDIR") >>"$FILE"
