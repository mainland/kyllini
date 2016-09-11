#!/bin/sh
WIFIDIR=../examples/wifi

githash() {
    DIR=$1
    shift

    BRANCH="$(cd $DIR && git symbolic-ref HEAD 2>/dev/null)" || BRANCH="detached-head"
    BRANCH=${BRANCH##refs/heads/}

    REV=$(cd $DIR && git rev-parse --short=8 HEAD)

    echo $BRANCH-$REV
}

REV=$(githash $WIFIDIR)

FILE="$REV.csv"

truncate -s 0 "$FILE"

if [ "$#" != 0 ]; then
    ZIRIADIR=$1
    shift

    ZIRIAREV=$(githash $ZIRIADIR)
fi

if [ -n "ZIRIADIR" ]; then
    ./perfrun.sh \
        kzc "$REV" "$WIFIDIR" \
        ziria "$ZIRIAREV" "$ZIRIADIR" \
        >>"$FILE"
else
    ./perfrun.sh \
        kzc "$REV" "$WIFIDIR" \
        >>"$FILE"
fi
