stats = {'Fusion failures': 0}

test("fuse02")
test("fuse02-fusion", [should_fail, only_flag('-ffuse'), wantStats(stats)], compile_stats, source="fuse02")
