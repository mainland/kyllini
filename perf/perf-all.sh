#!/bin/sh
set -e
./perf-ziria.sh ~/projects/ziria/Ziria/code/WiFi/
./perf-wifi.sh wifi
./perf-wifi.sh wifi-sid
./perf-components.sh
