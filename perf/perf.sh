#!/bin/sh
WIFIDIR=../testsuite/code/WiFi

BRANCH="$(git symbolic-ref HEAD 2>/dev/null)" || BRANCH="detached-head"
BRANCH=${BRANCH##refs/heads/}

REV=$(git rev-parse --short=8 HEAD)

FILE=$BRANCH-$REV-perf.txt

truncate -s 0 "$FILE"

for DIR in receiver/perf transmitter/perf perf; do
    (cd $WIFIDIR/$DIR && make all) | awk -v category=$DIR -f perf.awk | sort >>"$FILE"
    (cd $WIFIDIR/$DIR && make clean)
done
