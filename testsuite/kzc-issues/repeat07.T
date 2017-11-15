stats = {'Fusion failures': 0}

test("repeat07-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="repeat07")

test("repeat07")
