/-
**`scc_rt_main` after a setup block, light** (x86-64; `rtCodeOkS`,
`mainPhTabS`): the code and phase facts A11 (`Scc/Cert/PlaceOKX64.lean`)
checks of a `.setup` tail, next to the bare shape's (`MainCode`, `rtCodeOk`,
`mainPhTab` in `Spike/Lib/Rt/X64CodeIn.lean`, `X64RtPhTab.lean`). The twin
of `Spike/Lib/Rt/A64CodeInSetup.lean`.

With a setup block (`main(a : S * Ptr pub Void)`, `rodata(u : Unit) : S`,
`Runtime.mainThreadF` at `EntryArg.setupTid`), scc's `scc_rt_main` keeps
the bare shape's stack-checked prologue (`%rdi`, the TCB, stored at
`-8(%rbp)`) and its `exit_group` tail, but calls twice: `call rodata` at
`.entry`; then at `.x2` the `sw` setup words come back in `%rax`, `%rdx`,
`%rcx`, `%rsi`, `%rdi`, `%r8` (`Scc.Emit.X64.retRegs`), go to the frame at
`-16`, …, `-(8 sw + 8)` and back into `%rdi`, `%rsi`, … (`argRegs`), the
TCB into the next argument register (`marshal`), and `call main`; the tail
at `.x3` spills the result at `-8 (sw + 2)`. The frame holds `sw + 3`
slots (the TCB, the words, the result, the system call's), 16-aligned.

The emitter numbers the `.x` labels with one counter over the whole program
(`Scc.Emit.X64.freshL`), so the setup call shifts every later one by one:
`scc_rt_thread_init`'s return point is `.Lscc_rt_thread_init.x8` here and
`.x7` after a bare `scc_rt_main` (`tiGrpsAt`, `SetupCode.ti`). The other
runtime groups name no `.x` label after `scc_rt_main`'s.

- `SetupCode`: the frame, the spill, the two callees, `sw` and the labels;
  `setupMC sw` today's emitter's at `sw` words (`hello1.w`: `sw = 4`, frame
  64, spill `-48`).
- `mainSGrps sc`: `scc_rt_main`'s groups; `rtCodeTabS`/`rtCodeOkS` the
  runtime's code with them in place of `mainUGrps` and
  `scc_rt_thread_init`'s at `sc.ti`, in one pass (`rtIn`).
- `mainPhTabS sc`: `scc_rt_main`'s phase facts (each block's check, the
  limit's load and the system call's single steps).
- `setupOk cells lo Λ`: some `sw < 6` (the setup words and the TCB in the
  six argument registers) passes both; the placement data does not record
  `sw`, the frame's check picks it.
-/
import Spike.Lib.Rt.X64RtPhTab

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Kraken.X64.Parser
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (RGrp PhFact rtIn)

/-- **What `scc_rt_main` after a setup block reads of the program**: its
frame `Z`, the spill offset `k` of the exit value (from `%rbp`), the setup
block `setup`, the user function `fn`, the number `sw` of setup words, its
labels (the prologue's check `sc`, the grow stub `grow`, the body's entry
`e0`, the two calls' return points `sp0`, `sp1`), and
`scc_rt_thread_init`'s return point `ti` as the program numbers it. -/
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
  ti : Label

/-- The result registers (`Scc.Emit.X64.retRegs`). -/
def retXs : List Reg64 := [.rax, .rdx, .rcx, .rsi, .rdi, .r8]

/-- The argument registers (`Scc.Emit.X64.argRegs`). -/
def argXs : List Reg64 := [.rdi, .rsi, .rdx, .rcx, .r8, .r9]

/-- `movq n(%rbp), %r`, `z` bytes (`p = (r, n, z)`). -/
def xLd (p : Reg64 × Int64 × Nat) : Directive × Nat :=
  (op64 (.mov (.reg (.low p.1 .W64))
    (.regOrMem (.mem { base := some (.reg .rbp), idx := none, disp := .int64 p.2.1 }))), p.2.2)

/-- The slot of setup word `i`, `-(16 + 8 i)(%rbp)`. -/
def swOff (i : Nat) : Int64 := -Int64.ofNat (16 + 8 * i)

/-- **`.x2`'s block at `sw` words**: the setup words from the result
registers stored at their slots and loaded back into the argument
registers, the TCB from `-8(%rbp)` into the next one, `call fn`; each move
four bytes. -/
def marshal (sw : Nat) (fn : Label) : List (Directive × Nat) :=
  (List.range sw).map (fun i => xSt (retXs.getD i .rax, swOff i, 4)) ++
    (List.range sw).map (fun i => xLd (argXs.getD i .rdi, swOff i, 4)) ++
    [xLd (argXs.getD sw .rdi, -8, 4)] ++ callB fn

/-- `marshal`'s size in bytes. -/
def marshalSz (sw : Nat) : Nat := 4 * (2 * sw + 1) + 5

/-- **`scc_rt_main` after a setup block of `sw` words**, as today's emitter
writes it: the frame of `sw + 3` slots, the result spilled at
`-8 (sw + 2)`, `call wc_rodata` then `call wc_main`, its labels, and
`scc_rt_thread_init`'s return point `.x8`. -/
def setupMC (sw : Nat) : SetupCode :=
  ⟨Int64.ofNat ((8 * (sw + 3) + 15) / 16 * 16), -Int64.ofNat (8 * (sw + 2)), "wc_rodata", "wc_main", sw,
    ".Lscc_rt_main.chk", ".Lscc_rt_main.stk", ".Lscc_rt_main.entry", ".Lscc_rt_main.x2", ".Lscc_rt_main.x3",
    ".Lscc_rt_thread_init.x8"⟩

/-- The prologue's frame block at `sc`: `subq $Z, %rsp`, `%rdi` (the TCB)
stored at `-8(%rbp)`. -/
def setupFr (sc : SetupCode) : List (Directive × Nat) := xFr sc.Z 4 [(.rdi, -8, 4)]

/-- `scc_rt_main`'s groups at `sc`: the prologue's head and its
fall-through into the check, the check and the frame and the fall-through
into the body, `call setup` and the return point after it, the marshalling
and `call fn` and the return point after it, the `exit_group` tail there. -/
def mainSGrps (sc : SetupCode) : List RGrp := [
  ⟨"scc_rt_main", [(0, xHead)], some (4, sc.sc)⟩,
  ⟨sc.sc, [(0, xLea sc.Z 5), (5, [(fsDir .r11 8, 9)]), (14, xCmp sc.grow 3 2), (19, setupFr sc)],
    some (27, sc.e0)⟩,
  ⟨sc.e0, [(0, callB sc.setup)], some (5, sc.sp0)⟩,
  ⟨sc.sp0, [(0, marshal sc.sw sc.fn)], some (marshalSz sc.sw, sc.sp1)⟩,
  ⟨sc.sp1, [(0, xExit sc.k 4 4 5), (13, [(op64 .syscall, 2)])], none⟩]

section Ti

open Code.Ti

/-- `scc_rt_thread_init`'s groups with its return point at `x`
(`tiGrps` at `.x7`). -/
def tiGrpsAt (x : Label) : List RGrp := [
  ⟨fnL, [(0, tiPro)], some (12, entryL)⟩,
  ⟨entryL, [(0, tiArg), (7, callBlk)], some (12, x)⟩,
  ⟨x, [(0, tiSp), (51, tiF1), (63, tiZ), (78, tiZ), (93, tiF4), (105, tiF5), (117, tiRet)] ++
    storeOff.zip storeBlks, none⟩]

theorem tiGrpsAt_x7 : tiGrpsAt x7L = tiGrps := rfl

end Ti

/-- **The runtime's code after a setup block**, in program order: as
`rtCodeTab` with `scc_rt_main`'s groups at `sc` and `scc_rt_thread_init`'s
return point at `sc.ti`. -/
def rtCodeTabS (sc : SetupCode) : List RGrp :=
  startGrps ++ mainSGrps sc ++ tcbGrps ++ tiGrpsAt sc.ti ++ takeGrps

/-- **The runtime's code after a setup block in `cells`**, in one pass. -/
def rtCodeOkS (cells : List (Directive × Nat)) (sc : SetupCode) : Bool := rtIn cells (rtCodeTabS sc)

/-- **`scc_rt_main`'s facts at `sc`**: each block's phase check, the
limit's load and the system call single steps. -/
def mainPhTabS (sc : SetupCode) : List PhFact :=
  [.blk "scc_rt_main" 0 xHead none none, .blk sc.sc 0 (xLea sc.Z 5) none none, .step sc.sc 5 9,
    .blk sc.sc 14 (xCmp sc.grow 3 2) none none, .blk sc.sc 19 (setupFr sc) none none,
    .blk sc.e0 0 (callB sc.setup) none none, .blk sc.sp0 0 (marshal sc.sw sc.fn) none none,
    .blk sc.sp1 0 (xExit sc.k 4 4 5) none none, .step sc.sp1 13 2]

/-- **A11 at a `.setup` tail**: at some `sw < 6`, the runtime's code with
`scc_rt_main` at `setupMC sw` (`rtCodeOkS`) and its phase facts
(`mainPhTabS`), the code at `lo`, the sites of `Λ`. -/
def setupOk (cells : List (Directive × Nat)) (lo : Nat) (Λ : Scc.Sem.Layout) : Bool :=
  (List.range 6).any fun sw =>
    rtCodeOkS cells (setupMC sw) && Scc.Cert.Rt.X64.rtPhOk lo cells Λ (mainPhTabS (setupMC sw))

/-- info: [(64, -48), (32, -16), (64, -56)] -/
#guard_msgs in
#eval [4, 0, 5].map fun sw => ((setupMC sw).Z.toInt, (setupMC sw).k.toInt)

/-- `marshal` at four words is the parser's form of `hello1.w`'s `.x2`. -/
example : marshal 4 "wc_main" = (parse("movq %rax, -16(%rbp)
movq %rdx, -24(%rbp)
movq %rcx, -32(%rbp)
movq %rsi, -40(%rbp)
movq -16(%rbp), %rdi
movq -24(%rbp), %rsi
movq -32(%rbp), %rdx
movq -40(%rbp), %rcx
movq -8(%rbp), %r8
call wc_main")).zip [4, 4, 4, 4, 4, 4, 4, 4, 4, 5] := by decide

/-- The frame block at four words is the listing's. -/
example : setupFr (setupMC 4) = (parse("subq $64, %rsp
movq %rdi, -8(%rbp)")).zip [4, 4] := by decide

end Spike.Lib.X64.Rt
