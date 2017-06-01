# Running performance tests

There are a number of scripts that will automatically run the WiFi performance
tests, generating a CSV file performance data.

## Prerequisites

The performance tests use `perf` to collect statistics for each run. You
therefore may need to install and enable non-privileged access to `perf`. You can enable non-privileged access access to `perf` as follows:

```
sudo sh -c 'echo 0 >/proc/sys/kernel/perf_event_paranoid'
```

### Disabling dynamic CPU frequency scaling

Disabling dynamic CPU frequency scaling is recommended during benchmarking. Frequency scaling can be disabled using `cpufreq-set`. On Ubuntu, you can install `cpufreq-set` as follows:

```
sudo apt install cpufrequtils
```

Then, disable frequency scaling with the following command.

```
sudo cpufreq-set -g performance
```

## Benchmarking the various implementations

### Ziria performance tests
Performance tests can be run for Ziria by invoking the `perf-ziria.sh` script
with the path to the Ziria WiFi implementation, e.g.,

```
./perf-ziria.sh ~/projects/ziria/Ziria/code/WiFi/
```

### WiFi performance tests

Performance tests for WiFi can be run be invoking the `perf-wifi.sh` script with the name of the WiFi branch to run. The branch should be a subdirectory of examples, i.e., `wifi` or `wifi-sid`. For example:

```
./perf-wifi.sh wifi
```

### Component tests

The `perf-components.sh` will run WiFI Viterbi/FFT/IFFT component tests to compare the `wifi` and `wifi-sid` branches.

### Running all performance tests

All tests can be run by invoking the `perf-all.sh` script. It assumes that the
path to the Ziria WiFi implementation is ``~/projects/ziria/Ziria/code/WiFi/`.`

## Plotting 

The `plot.R` R script can be used to plot CSV data generated from the various performance scripts. Use the `--help` to see the available options.
