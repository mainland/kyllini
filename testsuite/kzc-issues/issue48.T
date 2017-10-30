t = test("issue48", [add_flags(['-fpipeline'])], compile_and_make)
cleanup(t)
