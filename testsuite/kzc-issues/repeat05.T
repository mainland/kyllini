stats = {'Fusion failures': 0}

test("repeat05-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat05")

test("repeat05", blinkdiff(['-p']))
