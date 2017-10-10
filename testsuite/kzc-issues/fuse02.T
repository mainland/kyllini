stats = {'Fusion failures': 0}

test("fuse02", [only_way('fuse-simpl')], compile_and_run)
test("fuse02-fusion", [should_fail, only_way('fuse-simpl'), wantStats(stats)], compile_stats, source="fuse02")
