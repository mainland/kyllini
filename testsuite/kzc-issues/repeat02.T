stats = {'Fusion failures': 0}

test("repeat02-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat02")

test("repeat02", blinkdiff(['-p']))
