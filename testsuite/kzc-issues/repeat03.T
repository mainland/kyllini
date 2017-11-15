stats = {'Fusion failures': 0}

test("repeat03-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat03")

test("repeat03", blinkdiff(['-p']))
