#!/bin/sh
. "$(dirname "$0")/perf.sh"

ZIRIADIR=$1
shift

ZIRIAREV=$(githash $ZIRIADIR)
FILE="ziria-$(date '+%Y-%m-%d')-$ZIRIAREV.csv"

truncate -s 0 "$FILE"

(record_perf_tests ziria "$ZIRIAREV" "$ZIRIADIR") >>"$FILE"
