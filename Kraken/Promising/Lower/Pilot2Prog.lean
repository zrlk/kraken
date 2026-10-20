/-
**The lowering pilot with a real `dmem` stack
frame.**

`Lower/PilotProg.lean`'s hand-lowered Treiber client with the draft convention's stack
discipline: a private 16-byte-aligned stack per thread in `dmem`; the non-leaf
`main` saves `x30` in a 16-byte frame (`str x30, [sp, #-16]!` /
`ldr x30, [sp], #16`) instead of the first lowering pilot's `x19`; `push`/`pop` are leaves (no
stack, `x30` kept). No `stp`/`ldp` (one saved register), no frame pointer,
results in registers, nothing live across a call is spilled.

Contents: `pilot2` (40 directives), the layout `pLayout2`, the stack builder
`stackMem`, two start states with disjoint stacks, a `#guard_msgs` explorer run
with `pilotRun`'s finals, and the static EnvG checks (`rmwLive`, `Phase1TreeF`;
`DirsNoFault` fails statically, see below).
-/
import Kraken.Promising.Lower.PilotProg

namespace Kraken.Promising.Lower.Pilot2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- **The hand-lowered program with a `dmem` frame** (one text, three
functions; `main` differs from `Pilot.pilot` only in its prologue and
epilogue). -/
def pilot2 : Program := parseAArch64("
main:
    str x30, [sp, #-16]!
    mov x1, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi oom
    str w9, [x1]
    mov x0, x21
    bl push
    mov x0, x21
    bl pop
ret_pop:
    cbz x0, empty
    mov x10, x0
    ldr w11, [x10]
empty:
    ldr x30, [sp], #16
    ret
oom:
    b oom
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
    ret
pop:
    ldar x2, [x0]
    cbz x2, pop_done
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne pop
pop_done:
    mov x0, x2
    ret
done:
")

/-- info: 40 -/
#guard_msgs in
#eval pilot2.length

/-! ## The runner-style layout, the stacks and two start states -/

/-- Text at `0x100000`, each directive its `fakeSize` (labels `0`). -/
@[reducible] def pLayout2 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize pilot2

instance pValid2 : Executable.ValidLayout (pLayout2 pilot2) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- `k` zeroed 8-byte words from `lo`: a private stack region `[lo, lo + 8k)`. -/
def stackMem (lo : BitVec 64) : Nat → Mem 64
  | 0 => {}
  | k + 1 => Mem.storeInt (stackMem lo k) (lo + BitVec.ofNat 64 (8 * k)) 8 0

/-- Thread `i`'s start: as `Pilot.thread`, plus a 64-byte stack
`[sp - 64, sp)` in `dmem` with `sp` 16-byte aligned. -/
def thread2 (base v sp : UInt64) : AArch64.State where
  exe := pLayout2 pilot2
  endPc := Pilot.endA
  st := ({ regs := { X21 := 0x1000, X27 := base, X28 := base + 0x100, X9 := v, X30 := 0x100000 + 128, SP := sp }
           dmem := stackMem (sp.toBitVec - 64) 8 }, 0x100000)

/-- The explorer under `isa`: per final configuration, each thread's
`(x10, w11, x27, sp)` (popped node, its payload, the bumped arena pointer, the
restored stack pointer). -/
def exploreFinals2 (o : ExploreOpts) : List (List (Nat × Nat × Nat × Nat)) × Bool × List String :=
  let proj := fun (ts : List AArch64.State) => ts.map fun s =>
      (s.st.1.regs.X10.toBitVec.toNat, s.st.1.regs.X11.toBitVec.toNat, s.st.1.regs.X27.toBitVec.toNat,
        s.st.1.regs.SP.toBitVec.toNat)
  let r := explore Arch.armv8
    (Config.init [thread2 0x2000 1 0x8040, thread2 0x3000 2 0x9040] Pilot.initMem : Config isa)
    (fun c => proj (c.threads.toList.map (·.st))) o
  (r.finals, r.boundHit, r.faults)

/-! ## The static checks of the EnvG link -/

section Static

variable [layout : _root_.Layout]

/-- The `casal`s return into a register (`x3`). -/
theorem pilot2_rmwLive : (layout pilot2).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

/-- Every cell is a phase-1 tree (the frame `str`/`ldr` included). -/
theorem pilot2_phase1F [Executable.ValidLayout (layout pilot2)] : Phase1TreeF (layout pilot2) :=
  phase1TreeF_of_dirs (by dirs_phase1F pilot2)

/- `DirsNoFault (layout pilot2)` does not hold: the frame cells `str x30, [sp, #-16]!` and
`ldr x30, [sp], #16` fault when `sp` is not 16-byte aligned (`checkSPAlignment`). The alignment
is a state invariant (the private stack is 16-byte aligned), not a static property of the cells, so
the static no-fault check of `Pilot.pilot_noFault` has no `pilot2` counterpart. -/

end Static

/-- **The program terminates with the pilot's results** (`isa`, promise-free
exploration, `boundHit = true` as for `Pilot.pilotRun`): in every final
configuration each thread popped one of the two nodes (`0x2000`, `0x3000`)
with its payload (`1`, `2`), the nodes are distinct, each arena pointer moved
by one node, and each `sp` is back at its start (`0x8040`, `0x9040`); no
fault. The frame accesses are private (no events), so the finals are
`pilotRun`'s. -/
def pilot2Run : List (List (Nat × Nat × Nat × Nat)) × Bool × List String :=
  exploreFinals2 { fuel := 32, maxPromises := some 0 }

/--
info: ([[(12288, 2, 8208, 32832), (8192, 1, 12304, 36928)], [(8192, 1, 8208, 32832), (12288, 2, 12304, 36928)]], true, [])
-/
#guard_msgs in
#eval pilot2Run

end Kraken.Promising.Lower.Pilot2
