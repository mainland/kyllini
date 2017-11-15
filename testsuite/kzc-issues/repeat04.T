stats = {'Fusion failures': 0}

test("repeat04-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat04")

test("repeat04", blinkdiff(['-p']))
