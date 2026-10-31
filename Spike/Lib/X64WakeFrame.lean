/-
**wake.w's frames and stack regions on x86-64**, beside the AArch64 ones:
the numbers every `X64Wake*` file and every x64 twin of the wake.w runtime
pieces uses, in one place. The listing is `scc -S Scc/Test/wake.w` (AArch64:
`scc --arch arm -S Scc/Test/wake.w`).

## The ABI, x86-64 against AArch64

* x86-64: `call` pushes the return address; the prologue is
  `pushq %rbp; movq %rsp, %rbp`, then (stack-checked functions)
  `leaq -N(%rsp), %rax; movq %fs:8, %r11; cmpq %r11, %rax; jb .Lf.stk`,
  `subq $N, %rsp` and the parameters stored at `-8(%rbp)`, `-16(%rbp)`, ….
  The epilogue is `movq %rbp, %rsp; popq %rbp; ret`, a tail call the same
  with `jmp f` for `ret`.
* AArch64: `bl` leaves the return address in `x30`; the frame of `N` bytes
  is below the entry `sp` (frame record at its base), `N` a multiple of 16.

A function's **region** is based at its entry `%rsp` (`sp` on AArch64): on
x86-64 the return address is at offset `0` (so `hi = 8`), the saved `%rbp`
at `-8`, the frame below; on AArch64 `hi = 0`. Inside the frame the static
offsets are `⟨-(N + 8), [(.rbp, -8)]⟩`. A callee called with `%rsp` at
offset `s` of its caller's region is entered at `s - 8` (the return address
pushed), so its region is `R.callee (s - 8) (-D) 8`; on AArch64 `R.callee s
(-D) 0`. No x86-64 segment asks a 16-aligned base.

## Frames and depths

`N` is the `subq` (AArch64: the frame); "need" the bytes the function and
its callees touch below its entry `%rsp`, the pushed return addresses and
`%rbp`s included, `scc_rt_morestack` and the abort chain excluded.

| function | x64 `N` | x64 need | A64 frame | A64 need |
|---|---|---|---|---|
| `scc_rt_main` | 32 | 376 | 48 | 384 |
| `wc_main` | 64 | 328 | 80 | 336 |
| `wc_waitLoop` | 16 | 88 | 32 | 96 |
| `wc_worker` | 16 | 72 | 32 | 80 |
| `scc_rt_thr_worker` | 32 | 120 | 48 | 128 |
| `scc_rt_park` | 48 | 56 | 64 | 64 |
| `scc_rt_unpark` | 32 | 40 | 48 | 48 |
| `scc_rt_thread_reserve` | 32 | 40 | 48 | 48 |
| `scc_rt_alloc` | 144 | 152 (region `-160`) | 160 | 160 |
| `scc_rt_alloc_tcb` | 176 | 184 | 192 | 192 |
| `scc_rt_thread_init` | 32 | 248 | 48 | 256 |
| `scc_rt_stack_take` | 192 | 200 | 208 | 208 |
| `scc_rt_abort` | 16 | 24 (`hi = 16`) | 32 | 32 |
| abort stubs | 32 | 40 | 48 | 48 |

The region bounds the existing x64 segment lemmas ask: `seg_alloc`
`lo ≤ -160`, `hi ≥ 8`; alloc_tcb `-184`; stack_take `-200`; thread_init
`-248`; abort `lo ≤ -24`, `hi ≥ 16` (entered at its region's offset `8`,
`RtDepthX64.abortAt`); print `-40`.

## The derived constants

* `wcK = -48`: `scc_rt_main` (frame 32) calls `wc_main` with `%rsp` at its
  region's `-40`, so `wc_main` is entered at `-48`; `wcR R D` its region
  (AArch64 `WakeM.wR R D = R.callee (-48) (-D) 0`: frame 48, no push).
  This is `X64Main`'s `-8 - Z - 8 - 0` for `Z = 32`.
* `callK = -80`: `wc_main` (frame 64) calls with `%rsp` at `-72`, its
  callees entered at `-80` (AArch64: frame 80, callees at `-80`).
* `wcD = 328`: `wc_main`'s deepest callee is `scc_rt_thread_init`
  (`-80 - 248`; AArch64 `-80 - 256 = -336`). `scc_rt_alloc` needs only
  `-80 - 160 = -240`, the AArch64 glue's `240 ≤ D` (`wcDmin`) on both ISAs.
* `swL = 384`: the switched-to region `swR v (-L) 0` holds `scc_rt_main`'s
  return address at `-8` and its region `mainR v L = (swR v (-L) 0).callee
  (-8) (8 - L) 8` must reach `wcK - wcD = -376`: `8 + 48 + D ≤ L`
  (AArch64 `48 + D ≤ L`). `D = 328`, `L = 384` meet it (`swL_ok`); the
  AArch64 pair `336`, `384` is `dLsw_ok`.
* The stack-check limits after the switch at `v` are the AArch64 ones:
  `scc_rt_main` compares `v - 8 - 8 - 32 = v - 48`, `wc_main`
  `v - 56 - 8 - 64 = v - 128` (`hlim48`, `hlim128`), `wc_waitLoop`
  (tail-jumped to at `wc_main`'s entry `v - 56`) `v - 80`.
* `wc_waitLoop` (frame 16) calls `scc_rt_park` with `%rsp` at `-24`:
  `parkR R = R.callee (-32) (-56) 8`, `wc_waitLoop`'s own `lo ≤ -88`
  (`waitD`; AArch64 `R.callee (-32) (-64) 0`, `-96`). Its tail jump back to
  itself and `wc_main`'s to it are in `wc_main`'s region, `-88 ≥ -wcD`.
* `wc_worker` (frame 16) calls `scc_rt_unpark` likewise: `unparkR R =
  R.callee (-32) (-40) 8`, `wc_worker`'s `lo ≤ -72` (`workerD`).
* `scc_rt_thr_worker` (frame 32) calls `wc_worker` with `%rsp` at `-40`:
  `workerR R = R.callee (-48) (-72) 8`, its own `lo ≤ -120` (`thrD`). The
  child's stack top `v'` is reached by `call scc_rt_thr_worker` on the new
  `%rsp`, so its region is `(swR v' (-L') 0).callee (-8) (8 - L') 8` with
  `128 ≤ L'` (`thrL`); its limits are `v' - 48` and (`wc_worker`)
  `v' - 80`, as on AArch64.
* `scc_rt_abort` from `wc_main`'s spawn failure is entered at `callK`:
  `RtDepthX64.abortAt R callK = R.callee (-88) (-24) 16`, lowest `-112`;
  from `scc_rt_thread_reserve` (frame 32, call at `-40`) at `-48`, lowest
  `-80`. These exits are nodes of the callers' segments (as on AArch64),
  not part of their `lo`.

The constants are `abbrev`s, so `omega` and `decide` see the numbers.
-/
import Spike.Lib.Region

namespace Spike.Lib.X64.WakeFrame

open Spike.Lib

/-! ## Frames (`subq`) -/

/-- `scc_rt_main`'s frame. -/
abbrev mainN : Int := 32
/-- `wc_main`'s frame. -/
abbrev wcN : Int := 64
/-- `wc_waitLoop`'s frame. -/
abbrev waitN : Int := 16
/-- `wc_worker`'s frame. -/
abbrev workerN : Int := 16
/-- `scc_rt_thr_worker`'s frame. -/
abbrev thrN : Int := 32
/-- `scc_rt_park`'s frame. -/
abbrev parkN : Int := 48
/-- `scc_rt_unpark`'s frame. -/
abbrev unparkN : Int := 32
/-- `scc_rt_thread_reserve`'s frame. -/
abbrev reserveN : Int := 32

/-- **A callee's entry offset** in its caller's region: the caller of frame
`n` calls with `%rsp` at `-8 - n`, the `call` pushes. -/
abbrev callAt (n : Int) : Int := -8 - n - 8

/-! ## Offsets and depths -/

/-- `wc_main`'s entry offset in `scc_rt_main`'s region. -/
abbrev wcK : Int := callAt mainN
/-- The entry offset of `wc_main`'s callees in its region. -/
abbrev callK : Int := callAt wcN
/-- `scc_rt_park`'s entry offset in `wc_waitLoop`'s region. -/
abbrev parkK : Int := callAt waitN
/-- `scc_rt_unpark`'s entry offset in `wc_worker`'s region. -/
abbrev unparkK : Int := callAt workerN
/-- `wc_worker`'s entry offset in `scc_rt_thr_worker`'s region. -/
abbrev workerK : Int := callAt thrN
/-- `scc_rt_abort`'s entry offset in `scc_rt_thread_reserve`'s region. -/
abbrev reserveAbK : Int := callAt reserveN

/-- `scc_rt_park`'s region depth (its `seg_park`'s `lo`). -/
abbrev parkD : Int := 56
/-- `scc_rt_unpark`'s region depth. -/
abbrev unparkD : Int := 40
/-- `scc_rt_thread_reserve`'s region depth (without the abort chain). -/
abbrev reserveD : Int := 40
/-- `scc_rt_alloc`'s region depth (`seg_alloc`'s `lo`). -/
abbrev allocD : Int := 160
/-- `scc_rt_alloc_tcb`'s region depth. -/
abbrev tcbD : Int := 184
/-- `scc_rt_thread_init`'s region depth. -/
abbrev tiD : Int := 248
/-- `scc_rt_stack_take`'s region depth. -/
abbrev takeD : Int := 200

/-- `wc_waitLoop`'s region depth: the park call's. -/
abbrev waitD : Int := -(parkK - parkD)
/-- `wc_worker`'s region depth: the unpark call's. -/
abbrev workerD : Int := -(unparkK - unparkD)
/-- `scc_rt_thr_worker`'s region depth: `wc_worker`'s call. -/
abbrev thrD : Int := -(workerK - workerD)
/-- **`wc_main`'s region depth**: `scc_rt_thread_init`'s call. -/
abbrev wcD : Int := -(callK - tiD)
/-- The least `wc_main` depth covering `scc_rt_alloc`'s call (the AArch64
glue's `240 ≤ D`). -/
abbrev wcDmin : Int := -(callK - allocD)
/-- **The depth of the region after the switch**. -/
abbrev swL : Int := 384
/-- The least depth of a worker thread's region after its `clone`. -/
abbrev thrL : Int := 128

/-! ## Regions -/

/-- **`wc_main`'s region** `D` deep in `scc_rt_main`'s region `R`. -/
abbrev wcR (R : Region) (D : Int) : Region := R.callee wcK (-D) 8
/-- A callee of `wc_main` of depth `d`, in `wc_main`'s region `R`. -/
abbrev wcCallR (R : Region) (d : Int) : Region := R.callee callK (-d) 8
/-- `scc_rt_park`'s region in `wc_waitLoop`'s region `R`. -/
abbrev parkR (R : Region) : Region := R.callee parkK (-parkD) 8
/-- `scc_rt_unpark`'s region in `wc_worker`'s region `R`. -/
abbrev unparkR (R : Region) : Region := R.callee unparkK (-unparkD) 8
/-- `wc_worker`'s region in `scc_rt_thr_worker`'s region `R`. -/
abbrev workerR (R : Region) : Region := R.callee workerK (-workerD) 8
/-- **The callee's region of a `call` from a new stack's top** `swR v (-L) 0`
(`scc_rt_main`'s after the switch, `scc_rt_thr_worker`'s after the
`clone`), as the x64 hello's `mainR`. -/
abbrev topR (S : Region) (L : Int) : Region := S.callee (-8) (8 - L) 8

/-! ## Checks -/

theorem frames_val : wcK = -48 ∧ callK = -80 ∧ parkK = -32 ∧ unparkK = -32 ∧ workerK = -48 ∧
    reserveAbK = -48 := by decide

theorem depths_val : waitD = 88 ∧ workerD = 72 ∧ thrD = 120 ∧ wcD = 328 ∧ wcDmin = 240 := by decide

/-- **`wcD`, `swL` meet the switch's depth premise** (x64: `8 + 48 + D ≤
L`), the region fits a 16 KiB stack, and every `wc_main` callee and
`wc_waitLoop` (tail-called in `wc_main`'s region) fit `wcD`. -/
theorem swL_ok : 8 + -wcK + wcD ≤ swL ∧ swL % 8 = 0 ∧ wcD % 8 = 0 ∧ swL ≤ 16384 ∧ wcDmin ≤ wcD ∧
    callK - allocD ≥ -wcD ∧ callK - tcbD ≥ -wcD ∧ callK - reserveD ≥ -wcD ∧ -waitD ≥ -wcD := by decide

/-- A worker thread's region of depth `thrL` covers `scc_rt_thr_worker`. -/
theorem thrL_ok : 8 - thrL ≤ -thrD ∧ thrL % 8 = 0 := by decide

/-- `scc_rt_main`'s region after the switch reaches `wc_main`'s at depth
`wcD`. -/
theorem wcR_lo (S : Region) : (wcR (topR S swL) wcD).lo = -328 ∧ (topR S swL).lo ≤ wcK - wcD := by
  simp only [Region.callee]; decide

/-- The stack-check limits below the switched-to top: `scc_rt_main`'s,
`wc_main`'s, `wc_waitLoop`'s (and on the worker's stack
`scc_rt_thr_worker`'s, `wc_worker`'s). -/
theorem limits_val : -8 - 8 - mainN = -48 ∧ -8 + wcK - 8 - wcN = -128 ∧ -8 + wcK - 8 - waitN = -80 ∧
    -8 - 8 - thrN = -48 ∧ -8 + workerK - 8 - workerN = -80 := by decide

end Spike.Lib.X64.WakeFrame

/-- info: 'Spike.Lib.X64.WakeFrame.swL_ok' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeFrame.swL_ok
