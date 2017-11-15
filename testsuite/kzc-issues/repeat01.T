stats = {'Fusion failures': 0}

test("repeat01-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat01")

test("repeat01", blinkdiff(['-p']))
