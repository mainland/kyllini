#!/usr/bin/env python
import argparse
import logging
import os
import re
from subprocess import (Popen, PIPE)
import sys
import threading
from threading import Thread
import tempfile
import traceback
from Queue import Queue

threadLocal = threading.local()

ioLock = threading.RLock()

WAY_FLAGS = { "normal"          : [],
              "simpl"           : ['-fsimpl'],
              "simpl-inline"    : ['-fsimpl', '-finline'],
              "fuse"            : ['-ffuse'],
              "peval"           : ['-fpeval'],
              "simpl-peval"     : ['-fsimpl', '-fpeval'],
              "fuse-peval"      : ['-ffuse', '-fpeval'],
              "lut"             : ['-fautolut', '-flut'],
              "lut-peval"       : ['-fautolut', '-flut', '-fpeval'],
              "simpl-lut-peval" : ['-fsimpl', '-finline', '-fautolut', '-flut', '-fpeval'],
              "O3"              : ['-O3'],
              "perf"            : ['-ftimers',
                                   '-finline', '-fsimpl', '-fautolut', '-flut', '-ffuse', '-fpeval',
                                   '-fcoalesce', '-fcoalesce-top', '-fmax-top-coalesce-rate=288',
                                   '-Wno-unsafe-auto-cast',
                                   '-dlint',
                                   '-dprint-uniques',
                                   '-fno-line-pragmas']
            }

ALL_WAYS = ["normal",
            "simpl",
            "simpl-inline",
            "fuse",
            "peval",
            "simpl-peval",
            "fuse-peval",
            "lut",
            "lut-peval",
            "simpl-lut-peval",
            "O3"]

def way_flags(way):
    if way:
        return WAY_FLAGS[way]
    else:
        return None

class Config(object):
    def __init__(self):
        self.kzc = None
        self.args = []
        self.lib = None
        self.verbose = 0
        self.way = None
        self.ground = False
        self.unexpected_passes = {}
        self.unexpected_failures = {}
        self.diffs = {}

class Test(object):
    def __init__(self, name):
        self.name = name
        self.cwd = None
        self.lib = None
        self.cmd = None
        self.args = []
        # By default, we compare in text mode
        self.blink_args = ['-d']
        # By default, do text input/output
        self.binary = False
        self.skip_compile = False
        self.make_args = []
        self.should_fail = False
        self.returncode = 0
        self.skip = False

#
# Setup functions
#
def should_fail(test, way):
    test.should_fail = True

def skip_way(way_to_skip):
    def f(test, way):
        if way == way_to_skip:
            test.skip = True

    return f

def only_way(the_way):
    def f(test, way):
        if way != the_way:
            test.skip = True

    return f

def flags(flags):
    """Hard-code KZC flags"""
    def f(test, way):
        test.way = None
        test.args += flags

    return f

def add_flags(flags):
    """Add KZC flags"""
    def f(test, way):
        test.args += flags

    return f

def blinkdiff(flags):
    """Add BlinkDiff flags"""
    def f(test, way):
        test.blink_args += flags

    return f

def binary(test, way):
    """Do binary input/output and comparison"""
    test.blink_args = [f for f in test.blink_args if f != '-d']
    test.binary = True

def skip_compile(test, way):
    """Skip compilation"""
    test.skip_compile = True

def wantStats(stats):
    """Check statistics"""
    def f(test, way):
        test.stats = stats

    return f

#
# Helper functions
#
def find_source(test):
    """Find source code for a test"""
    if test.source:
        test.basename = test.source
    else:
        test.basename = test.name

    for ext in ['.blk', '.wpl', '.zr', '.kz']:
        path = os.path.join(test.cwd, test.basename + ext)
        if os.path.exists(path):
            return path

    raise Exception("Can't find source for test %s" % test.name)

#
# Helpers
#
def recordTestDiff(test, diff):
    test_desc = "%s(%s)" % (test.name, config.way)
    config.diffs[test_desc] = config.diffs.get(test_desc, "") + diff

def cleanup(test):
    source = find_source(test)

    cPath =  os.path.splitext(source)[0] + '.c'
    exePath = '%s.exe' % test.basename

    os.remove(cPath)
    os.remove(os.path.join(test.cwd, exePath))

    return True

def parseStats(data):
    stats = {}

    for m in re.finditer(r'^\s+(.*): ([\d\.]*)$', data, re.M):
        stats[m.group(1)] = float(m.group(2))

    return stats

def checkStats(test, out):
    stats = parseStats(out)

    for (k, v) in test.stats.iteritems():
        if callable(v):
            if not v(stats[k]):
                recordTestDiff(test, "Unexpected value of %d for statistic %s" % (stats[k], k))
                return False
        else:
            if stats[k] != v:
                recordTestDiff(test, "Expected statistic %s value of %d but got %d" % (k, v, stats[k]))
                return False

    return True

#
# Test functions
#
def compile(test, way, args):
    source = find_source(test)

    exePath = '%s.exe' % test.basename

    cmd = [config.kzc] + test.args + way_flags(way) + args + [source]
    execute_and_compare_stdouterr(test, cmd)

    cmd = ['make', exePath] + test.make_args
    try:
        execute(cmd, cwd=test.cwd)
        return True
    except:
        return False

def compile_stats(test, way, args):
    source = find_source(test)

    cPath =  os.path.splitext(source)[0] + '.c'

    cmd = [config.kzc] + test.args + way_flags(way) + args + ['-s'] + [source]
    (out, err) = execute(cmd)

    os.remove(cPath)

    return checkStats(test, out)

def compile_and_make(test, way, args):
    source = find_source(test)

    exePath = '%s.exe' % test.basename

    cmd = [config.kzc] + test.args + way_flags(way) + args + [source]
    execute_and_compare_stdouterr(test, cmd)

    cmd = ['make', exePath] + test.make_args
    execute(cmd, cwd=test.cwd)

    return True

def compile_and_run(test, way, args):
    source = find_source(test)

    cPath =  os.path.splitext(source)[0] + '.c'
    exePath = '%s.exe' % test.basename
    infilePath = '%s.infile' % test.name
    outfilePath = '%s.outfile' % test.name
    outfileGroundPath = '%s.outfile.ground' % test.name

    if not test.skip_compile:
        cmd = [config.kzc] + test.args + way_flags(way) + args + [source]
        execute(cmd)

        cmd = ['make', exePath] + test.make_args
        execute(cmd, cwd=test.cwd)

    if config.ground:
        outfilePath = outfileGroundPath

    cmd = ['./' + exePath,
           '--input=%s' % infilePath,
           '--output=%s' % outfilePath]
    if test.binary:
        cmd += ['--input-mode=bin', '--output-mode=bin']

    try:
        if not execute_and_compare_stdouterr(test, cmd, test.cwd):
            return False

        if config.ground:
            return True
        else:
            return blinkdiff_compare(test)
    finally:
        if not test.skip_compile:
            os.remove(cPath)
            os.remove(os.path.join(test.cwd, exePath))

        if not config.ground:
            os.remove(os.path.join(test.cwd, outfilePath))

#
# Main test driver
#
def find_lib(path):
    path = os.path.abspath(path)

    while True:
        if path == "":
            return None

        lib = os.path.join(path, "lib")
        if os.path.isdir(lib):
            return lib

        path = os.path.dirname(path)

def test(testname, setup=None, testfn=compile_and_run, source=None, args=[]):
    global config

    try:
        # Create the Test object
        test = Test(testname)
        test.cwd = threadLocal.cwd
        test.lib = find_lib(threadLocal.cwd)
        test.cmd = config.kzc
        test.args = list(config.args)
        test.source = source

        if test.lib:
            test.args.append('-i'+os.path.dirname(test.lib))
            test.args.append('-i'+test.lib)
            test.args.append('-I'+test.lib)

        # Apply setup function(s)
        if setup:
            if type(setup) == list:
                for f in setup:
                    f(test, config.way)
            else:
                setup(test, config.way)

        if not test.skip:
            with ioLock:
                print "Running %s (%s)" % (test.name, config.way)

            if testfn(test, config.way, args):
                if test.should_fail:
                    config.unexpected_passes[test.name] = config.unexpected_passes.get(test.name, []) + [config.way]
            else:
                if not test.should_fail:
                    config.unexpected_failures[test.name] = config.unexpected_failures.get(test.name, []) + [config.way]

        return test
    except Exception, err:
        config.unexpected_failures[test.name] = config.unexpected_failures.get(test.name, []) + [config.way]
        print err
        traceback.print_exc()

#
# Running a test and comparing output
#
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

def execute_and_compare_stdouterr(test, cmd, cwd=None):
    """Run a command and compare stdout/stderr against expected results"""
    global config

    # Determine paths to files containing stdin/stdout/stderr
    stdin_path = os.path.join(test.cwd, test.name + ".in")
    if not os.path.exists(stdin_path):
        stdin_path = None

    if config.ground:
        stdout_path = os.path.join(test.cwd, test.name + ".out.ground")
        stderr_path = os.path.join(test.cwd, test.name + ".err.ground")
    else:
        stdout_path = os.path.join(test.cwd, test.name + ".out")
        stderr_path = os.path.join(test.cwd, test.name + ".err")

    # Open stdin
    if stdin_path:
        f_stdin = open(stdin_path, "r")
    else:
        f_stdin = PIPE

    # Run the command
    logging.debug(" ".join(cmd))
    p = Popen(cmd,
              stdin=f_stdin,
              stdout=PIPE,
              stderr=PIPE,
              close_fds=True,
              cwd=cwd)

    (out, err) = p.communicate()
    test.returncode = p.returncode

    # Close stdin
    if stdin_path:
        close(f_stdin)

    # If we're constructing ground truth, then we are by definition successful
    if config.ground:
        return True

    # Test return code
    if test.returncode != 0:
        recordTestDiff(test,
            "Return code: got %d but expected %d\n" %
            (test.returncode, 0))

    # Diff stdout
    ground_stdout_path = os.path.join(test.cwd, test.name + ".out.ground")

    if os.path.exists(ground_stdout_path):
        with open(stdout_path, "w") as f:
            f.write(out)

    if os.path.exists(ground_stdout_path):
        stdout_same = diff_files(test, ground_stdout_path, stdout_path)
    else:
        stdout_same = True

    # Diff stderr
    ground_stderr_path = os.path.join(test.cwd, test.name + ".err.ground")

    if os.path.exists(ground_stderr_path):
        with open(stderr_path, "w") as f:
            f.write(err)

    if os.path.exists(ground_stderr_path):
        stderr_same = diff_files(test, ground_stderr_path, stderr_path)
    else:
        stderr_same = True

    return test.returncode == 0 and stdout_same and stderr_same

#
# Output comparison
#
def normalize_paths(text):
    def f(m):
        return re.sub(r'\\', r'/', m.group(0))

    return re.sub(r'testsuite[^\s]+', f, text, re.M)

def normalize_line_endings(text):
    # Replace Windows line endings with UNIX line endings
    text = re.sub(r'\r\n', r'\n', text)

    # Replace Mac line endings with UNIX line endings
    text = re.sub(r'\r', r'\n', text)

    return text

def normalize(text):
    return normalize_paths(normalize_line_endings(text))

def diff_files(test, ground_path, result_path):
    global config

    with open(ground_path, "r") as f:
        ground = normalize(f.read())

    with open(result_path, "r") as f:
        result = normalize(f.read())

    if result == ground:
        return True
    else:
        proc = Popen("diff -u %s %s" % (ground_path, result_path),
                     shell=True,
                     stdout=PIPE, stderr=PIPE)
        (out, err) = proc.communicate()
        recordTestDiff(test, out)
        return False

def blinkdiff_compare(test):
    global config

    result_path = os.path.join(test.cwd, '%s.outfile' % test.name)
    ground_path = os.path.join(test.cwd, '%s.outfile.ground' % test.name)

    # -O3 turns on coalescing, so we
    if config.way == 'O3':
        test.blink_args += ['-p']

    cmd = "bin/BlinkDiff -f %s -g %s -v" % (result_path, ground_path) + " " + " ".join(test.blink_args)

    logging.debug(cmd)
    p = Popen(cmd,
              shell=True,
              stdout=PIPE, stderr=PIPE)
    (out, err) = p.communicate()

    if p.returncode == 0:
        return True
    else:
        recordTestDiff(test, out)
        return False

#
# Main driver
#
def main():
    global config

    parser = argparse.ArgumentParser(description='Run testsuite.')
    parser.add_argument('paths', help='a test to run', metavar='PATH',
                        type=str, nargs='+')
    parser.add_argument('--verbose', '-v', action='count', default=0)
    parser.add_argument('-d', '--debug', help='print debug output',
                        action='store_true', dest='debug')
    parser.add_argument('--kzc', help='path to kzc',
                        default='bin/kzc', metavar='PATH',
                        action='store', dest='kzc')
    parser.add_argument('--dump-all', help='dump all',
                        action='store_true', dest='dump_all')
    parser.add_argument('--no-lint', help='don\'t lint',
                        action='store_true', dest='no_lint')
    parser.add_argument('--ground', help='use test results as ground truth',
                        action='store_true', dest='ground')
    parser.add_argument('--diff', help='show test result difference',
                        action='store_true', dest='diff')
    parser.add_argument('--nthreads', help='number of threads to use to run tests',
                        default=10, type=int,
                        action='store', dest='nthreads')
    parser.add_argument('--ways', help='define ways to run the test',
                        type=str, action='append')
    parser.add_argument('--all-ways', help='run all ways',
                        action='store_true', dest='all_ways')
    args = parser.parse_args()

    if args.debug:
       level = logging.DEBUG
    else:
       level = logging.ERROR

    logging.basicConfig(format='%(asctime)s %(levelname)s %(message)s',
                        level=level)

    config = Config()

    config.kzc = os.path.abspath(args.kzc)
    config.verbose = args.verbose

    if args.dump_all:
        config.args += ['-ddump-all']

    if not args.no_lint:
        config.args += ['-dlint']

    if args.all_ways:
        ways = ALL_WAYS
    elif not args.ways:
        ways = ['normal']
    else:
        ways = args.ways

    config.ground = args.ground

    # Start worker threads
    def testRunner():
        while True:
            (root, path) = q.get(True)

            logging.debug("Running %s" % path)
            threadLocal.cwd = os.path.dirname(path)
            execfile(path)

            q.task_done()

    q = Queue(-1)

    for i in range(args.nthreads):
        t = Thread(target=testRunner)
        t.daemon = True
        t.start()

    #
    # Iterate over ways and tests
    #
    def visit(root, way, path):
        if os.path.isfile(path) and re.match(r'.*\.T$', path):
            q.put((root, path), True)
        else:
            return None

    for way in ways:
        q.join()
        config.way = way

        for path in args.paths:
            if os.path.isfile(path):
                visit(path, way, path)
            else:
                for root, dirs, files in os.walk(path):
                    for filename in files:
                        visit(path, way, os.path.join(root, filename))

    q.join()

    #
    # Output results
    #
    def print_failures(failures):
        print ", ".join([test + " (" + ", ".join(failures[test]) + ")" for test in failures.keys()])

    if len(config.unexpected_failures) != 0:
        print "Unexpected failures:",
        print_failures(config.unexpected_failures)
    else:
        print "No unexpected failures"

    if len(config.unexpected_passes) != 0:
        print "Unexpected passes:",
        print_failures(config.unexpected_passes)
    else:
        print "No unexpected passes"

    if args.diff:
        for test_desc in config.diffs:
            print
            print test_desc
            print config.diffs[test_desc]

    if len(config.unexpected_failures) != 0 or len(config.unexpected_passes) != 0:
        sys.exit(1)
    else:
        sys.exit(0)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        os._exit(1)
