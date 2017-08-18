stats = {'For loops': 0,
         'Takes': 1,
         'Emits': 1
        }

test("issue44", [flags(['-Iexamples/wifi', '-O3', '-fcoalesce-top']), wantStats(stats)], compile_stats)
