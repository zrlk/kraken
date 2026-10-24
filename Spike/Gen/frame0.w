-- main returns 42 with no `+`: no IR register and no call, so its x64 frame
-- is 0 bytes (the prologue's `subq $0, %rsp`); one thread, no allocation.
def main(u : Unit) : Int = ret 42
