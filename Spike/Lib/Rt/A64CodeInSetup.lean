/-
**`scc_rt_main` after a setup block, light** (`rtCodeOkS`, `mainPhTabS`):
the code and phase facts A11 (`Scc/Cert/PlaceOKA64.lean`) checks of a
`.setup` tail, next to the bare shape's (`MainCode`, `rtCodeOk`,
`mainPhTab` in `Spike/Lib/Rt/A64CodeIn.lean`, `A64RtPhTab.lean`).

With a setup block (`main(a : S * Ptr pub Void)`, `rodata(u : Unit) : S`,
`Runtime.mainThreadF` at `EntryArg.setupTid`), scc's `scc_rt_main` keeps
the bare shape's stack-checked prologue (`x0`, the TCB, at the frame's base)
and its `exit_group` tail, but calls twice: `bl rodata` at `.0_entry`;
then at `.sp0` the `sw` setup words `x0`…`x(sw-1)` go to the frame at
`8`…`8 sw` and back (`marshal`), the TCB to `x(sw)`, and `bl main`; the tail
at `.sp1` spills the result at `8 (1 + sw)`. The frame is
`Scc.Lower.A64.mainFrame` at `sw` (`main` returning an `Int`, no outgoing
area): `align16 (8 (sw + 3) + 16)`.

- `SetupCode`: the frame, the spill, the two callees, `sw` and the labels;
  `setupMC sw` today's emitter's at `sw` words (`hello1.w`: `sw = 4`, frame
  80, spill 40).
- `mainSGrps sc`: `scc_rt_main`'s groups; `rtCodeTabS`/`rtCodeOkS` the
  runtime's code with them in place of `mainUGrps`, in one pass (`rtIn`).
- `mainPhTabS sc`: `scc_rt_main`'s phase facts (each block's check, the
  two single steps).
- `setupOk prog lo Λ`: some `sw < 8` (the setup words and the TCB in
  `x0`–`x7`) passes both; the placement data does not record `sw`, the
  frame's check picks it.
-/
import Spike.Lib.Rt.A64RtPhTab

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Scc.Cert.Rt.A64 (RGrp PhFact rtIn)

/-- **What `scc_rt_main` after a setup block reads of the program**: its
frame `Z`, the spill offset `k` of the exit value, the setup block `setup`,
the user function `fn`, the number `sw` of setup words, and its labels (the
prologue's check `sc`, the grow stub `grow`, the body's entry `e0`, the two
calls' return points `sp0`, `sp1`). -/
structure SetupCode where
  Z : Int64
  k : Int64
  setup : Label
  fn : Label
  sw : Nat
  sc : Label
  grow : Label
  e0 : Label
  sp0 : Label
  sp1 : Label

/-- The argument registers `x0`–`x7`. -/
def argXs : List XReg := [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7]

/-- The `i`th argument register (`x0` past the eighth). -/
def argX (i : Nat) : XReg := argXs.getD i .X0

/-- `ldr Xr, [sp, #o]`. -/
def spLdr (r : XReg) (o : Int64) : Directive := RW.dir r (.slot o)

/-- **`.sp0`'s block at `sw` words**: the setup words `x0`…`x(sw-1)` stored
at `8`…`8 sw` and loaded back, the TCB from `[sp]` into `x(sw)`, `bl fn`. -/
def marshal (sw : Nat) (fn : Label) : List Directive :=
  (List.range sw).map (fun i => spStr (argX i) (Int64.ofNat (8 * (i + 1)))) ++
    (List.range sw).map (fun i => spLdr (argX i) (Int64.ofNat (8 * (i + 1)))) ++ [spLdr (argX sw) 0, blD fn]

/-- **`scc_rt_main` after a setup block of `sw` words**, as today's emitter
writes it: the frame `mainFrame` at `sw`, the result spilled at `8 (1 + sw)`,
`bl wc_rodata` then `bl wc_main`, its labels. -/
def setupMC (sw : Nat) : SetupCode :=
  ⟨Int64.ofNat ((8 * (sw + 3) + 16 + 15) / 16 * 16), Int64.ofNat (8 * (1 + sw)), "wc_rodata", "wc_main", sw,
    ".L1_scc_rt_main.stack_check", ".L1_scc_rt_main.stack_grow", ".L1_scc_rt_main.0_entry",
    ".L1_scc_rt_main.sp0", ".L1_scc_rt_main.sp1"⟩

/-- `scc_rt_main`'s groups at `sc`: the fall-through into the check, the
check and the frame's setup and the fall-through into the body, `bl setup`
and the return point after it, the marshalling and `bl fn` and the return
point after it, the `exit_group` tail there. -/
def mainSGrps (sc : SetupCode) : List RGrp := [
  ⟨"scc_rt_main", [], some (0, sc.sc)⟩,
  ⟨sc.sc, [(0, chkHead sc.Z), (2, [ldrDir .X10 .X10 8]), (3, chkBr sc.grow), (5, frameSet sc.Z [(.X0, 0)])],
    some (10, sc.e0)⟩,
  ⟨sc.e0, [(0, [blD sc.setup])], some (1, sc.sp0)⟩,
  ⟨sc.sp0, [(0, marshal sc.sw sc.fn)], some (2 * sc.sw + 2, sc.sp1)⟩,
  ⟨sc.sp1, [(0, exitTail sc.k), (3, [svcDir])], none⟩]

/-- **The runtime's code after a setup block**, in program order: as
`rtCodeTab` with `scc_rt_main`'s groups at `sc`. -/
def rtCodeTabS (sc : SetupCode) : List RGrp := startGrps ++ mainSGrps sc ++ tcbGrps ++ tiGrps ++ takeGrps

/-- **The runtime's code after a setup block in `prog`**, in one pass. -/
def rtCodeOkS (prog : List Directive) (sc : SetupCode) : Bool := rtIn prog (rtCodeTabS sc)

/-- **`scc_rt_main`'s facts at `sc`**: each block's phase check, the limit's
load and the system call single steps. -/
def mainPhTabS (sc : SetupCode) : List PhFact :=
  [.blk sc.sc 0 (chkHead sc.Z) none none, .step sc.sc 2, .blk sc.sc 3 (chkBr sc.grow) none none,
    .blk sc.sc 5 (frameSet sc.Z [(.X0, 0)]) none none, .blk sc.e0 0 [blD sc.setup] none none,
    .blk sc.sp0 0 (marshal sc.sw sc.fn) none none, .blk sc.sp1 0 (exitTail sc.k) none none, .step sc.sp1 3]

/-- **A11 at a `.setup` tail**: at some `sw < 8`, the runtime's code with
`scc_rt_main` at `setupMC sw` (`rtCodeOkS`) and its phase facts
(`mainPhTabS`), the code at `lo`, the sites of `Λ`. -/
def setupOk (prog : List Directive) (lo : Nat) (Λ : Scc.Sem.Layout) : Bool :=
  (List.range 8).any fun sw =>
    rtCodeOkS prog (setupMC sw) && Scc.Cert.Rt.A64.rtPhOk lo prog Λ (mainPhTabS (setupMC sw))

/-- info: [(80, 40), (48, 8), (96, 64)] -/
#guard_msgs in
#eval [4, 0, 7].map fun sw => ((setupMC sw).Z.toInt, (setupMC sw).k.toInt)

/-- info: 10 -/
#guard_msgs in
#eval (marshal 4 "wc_main").length

end Spike.Lib.A64.Rt
