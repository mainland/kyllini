stats = {'Fusion failures': 0}

test("fuse04")
test("fuse04-fusion", [only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse04")
