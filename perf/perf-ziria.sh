#!/bin/sh
. "$(dirname "$0")/perf.sh"

ZIRIADIR=$1
shift

ZIRIAREV=$(githash $ZIRIADIR)
FILE="ziria-$(date '+%Y-%m-%d')-$ZIRIAREV.csv"

truncate -s 0 "$FILE"

if [ ! -f "$ZIRIADIR/../../wplc" ]; then
    echo "Can't find wplc" && exit 1
fi

(record_perf_tests ziria "$ZIRIAREV" "$ZIRIADIR") >>"$FILE"
