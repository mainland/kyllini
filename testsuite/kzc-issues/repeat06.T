stats = {'Fusion failures': 0}

test("repeat06-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat06")

test("repeat06", blinkdiff(['-p']))
