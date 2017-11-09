#!/usr/bin/env python
import argparse
import logging
import os
import re
from subprocess import (Popen, PIPE)
import sys
import traceback

def execute(cmd, cwd=None, errmsg=None):
    """Return 'True' if command executes successfully"""
    logging.debug(" ".join(cmd))
    p = Popen(cmd, stdout=PIPE, stderr=PIPE, cwd=cwd)
    (out, err) = p.communicate()
    if p.returncode != 0:
        if errmsg:
            raise Exception(errmsg)
        else:
            raise Exception("Could not execute command: %s %s %s" % (" ".join(cmd), out, err))
    return (out, err)

def find_source(path):
    """Find source code for a performance test"""
    (dir, file) = os.path.split(path)
    (root, _) = os.path.splitext(file)

    for ext in ['.blk', '.wpl', '.zr', '.kz']:
        source = os.path.join(dir, root + ext)
        if os.path.exists(source):
            return (dir, root, root + ext)

    raise Exception("Can't find source for %s" % path)

STATS = ['Time elapsed (usec)',
         'Elapsed cpu time (sec)',
         'Elapsed real time (sec)',
         'Elapsed cycles']

def mean(xs):
    """Return mean of sequence data."""
    return sum(xs) / len(xs)

#
# See:
#   https://stackoverflow.com/questions/10797819/finding-the-mode-of-a-list
#
def mode(xs):
    """Return mode of sequence data."""
    return max(set(xs), key=xs.count)

#
# See:
#   https://stackoverflow.com/questions/24101524/finding-median-of-list-in-python
#
def median(xs):
    """Return median of sequence data."""
    n = len(xs)

    if n < 1:
        return None
    elif n % 2 == 1:
        return sorted(xs)[n//2]
    else:
        return sum(sorted(xs)[n//2-1:n//2+1])/2.0

#
# See:
#   https://stackoverflow.com/questions/15389768/standard-deviation-of-a-list
#
def _ss(data):
    """Return sum of square deviations of sequence data."""
    c = mean(data)
    ss = sum((x-c)**2 for x in data)
    return ss

def stddev(data, ddof=0):
    """Calculates the population standard deviation
    by default; specify ddof=1 to compute the sample
    standard deviation."""
    n = len(data)
    if n < 2:
        raise ValueError('variance requires at least two data points')
    ss = _ss(data)
    pvar = ss/(n-ddof)
    return pvar**0.5

def perftest(path):
    global args

    (dir, root, source) = find_source(path)

    cPath = root + '.c'
    exePath = root + '.exe'

    if args.noclean:
        cmd = ['make', exePath]
    else:
        cmd = ['make', '-B', exePath]

    execute(cmd, cwd=dir)

    stats = {}

    for i in range(0, args.ntrials):
        cmd = ['./' + exePath, '--input-dev=dummy', '--output-dev=dummy', '--dummy-samples=100000000']
        (out, _) = execute(cmd, cwd=dir)
        for s in STATS:
            m = re.search('^' + re.escape(s + ':') + '\s+(.*)$', out, re.M)
            if m:
                stats[s] = stats.get(s, []) + [float(m.group(1))]

    for s in STATS:
        if s in stats:
          xs = stats[s]

          if args.verbose:
              print "%s: %02f +/- %02f range [%02f, %02f] mode %02f median %02f" % (s,  mean(xs), stddev(xs), min(xs), max(xs), mode(xs), median(xs))
          else:
              print "%s: %02f +/- %02f" % (s,  mean(xs), stddev(xs))

    if not args.noclean:
        if os.path.isfile(os.path.join(dir, cPath)):
            os.remove(os.path.join(dir, cPath))

        if os.path.isfile(os.path.join(dir, exePath)):
            os.remove(os.path.join(dir, exePath))

    return True

#
# Main driver
#
def main():
    global args

    parser = argparse.ArgumentParser(description='Run testsuite.')
    parser.add_argument('paths', help='a test to run', metavar='PATH',
                        type=str, nargs='+')
    parser.add_argument('--verbose', '-v', action='count', default=0)
    parser.add_argument('-d', '--debug', help='print debug output',
                        action='store_true', dest='debug')
    parser.add_argument('--ntrials', help='number of trials',
                        default=10, type=int,
                        action='store', dest='ntrials')
    parser.add_argument('--no-clean', help='don\'t clean before make',
                        action='store_true', dest='noclean')
    args = parser.parse_args()

    if args.debug:
       level = logging.DEBUG
    else:
       level = logging.ERROR

    logging.basicConfig(format='%(asctime)s %(levelname)s %(message)s',
                        level=level)

    #
    # Iterate over ways and tests
    #
    def visit(root, path):
        if os.path.isfile(path):
            try:
                perftest(path)
            except Exception, err:
                print err
                traceback.print_exc()
        else:
            return None

    for path in args.paths:
        if os.path.isfile(path):
            visit(path, path)
        else:
            for root, dirs, files in os.walk(path):
                for filename in files:
                    visit(path, os.path.join(root, filename))

    sys.exit(0)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        os._exit(1)
