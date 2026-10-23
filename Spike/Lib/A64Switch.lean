/-
**AArch64 stack switches as nodes of a function**: a register operation
that sets `sp` to a value of unknown static offset.

A function's nodes (`Spike/Lib/A64Cfg.lean`) relate the thread's registers
to one region `R` through static offsets (`SO`), and `sp` must stay at a
known offset (`SO.write` refuses `sp`, so `okBlk` rejects such a write). scc
switches stacks twice: `_start` moves to the thread's stack (`add sp, x9,
#0`, `x9` loaded from a frame slot), and `scc_rt_morestack` moves to the
grown stack (`add sp, x29, #0` after `add x29, x29, x0`). After the switch
`sp` is in another region.

- `swR v lo hi`: the region a switch enters, based at the new `sp` value
  `v`, cells `[lo, hi)`; `SO.entry`: `sp` at offset 0, no register offsets.
- `SwAt exe endPc lo hi F' n'`: node `n'` in the region `swR v lo hi` for
  some 16-aligned, non-wrapping `v`, with frame condition `F' v`.
- `sw_nd`: a node at a register operation (`RegOnly`, any destination; the
  stack switches are the ones writing `sp`) lands at `SwAt`, after a local
  run of the source. The obligation is on the abstract step
  (`AI.step … (.reg w op)`, whose closed form `block_spec`'s simp set
  computes) and on the memory at the node: the new region's cells, the new
  frame condition.
- `sw_seg`, `sw_seq`: segments from the switched-to node, one for each `v`, make one
  segment from `SwAt` (`Seg.exists_pre`), so a function graph in the new
  region (`fn_seg` at `swR v lo hi`) continues the switch.
-/
import Spike.Lib.A64Cfg
import Kraken.AArch64.Parser

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-! ## The region after a switch -/

/-- **The region a switch enters**: based at the new `sp` value `v`, cells
`[lo, hi)`. -/
def swR (v : BitVec 64) (lo hi : Int) : Region := ⟨v, lo, hi⟩

/-- The static offsets at a switch's target: `sp` at offset 0, no register
offsets (the registers' old offsets are relative to the old region). -/
def SO.entry : SO := ⟨0, []⟩

/-- `sp` is at offset 0 of the region based at its value. -/
theorem soRel_entry {regs : Reg64s} (lo hi : Int) : SORel (swR regs.SP.toBitVec lo hi) SO.entry regs := by
  intro r k h
  rcases r with x | _
  · simp [SO.entry, SO.get, lk] at h
  · simp only [SO.entry, SO.get, Option.some.injEq] at h
    subst h
    simp [swR, Region.addr, Reg64s.getRegOrSp64]

/-- **Node `n'` after a switch**: in the region `swR v lo hi` for some
16-aligned, non-wrapping `v`, with frame condition `F' v`. -/
def SwAt (exe : _root_.Executable) (endPc : Int64) (lo hi : Int) (F' : BitVec 64 → MachineData → Prop)
    (n' : ND) : Frag isaLSE2 :=
  fun s c => ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v lo hi).OK ∧ At exe endPc (swR v lo hi) (F' v) n' s c

/-! ## Kraken's step -/

/-- A register operation's machine data, from the abstract state the
machine data is: the abstract step's registers and flags, the memory as it
was. -/
theorem regRes_abs {w : RegWidth} {op : Operation w} (h : RegOnly op = true) {R : Region} {o : SO}
    {m : MachineData} {σ : AS} (hA : Abs R o m σ) (fall : Int64) :
    regRes op m = { m with regs := (AI.step o fall (.reg w op) σ).regs,
                           status := (AI.step o fall (.reg w op) σ).status } := by
  rw [regRes_eq h m]
  obtain ⟨r, st, d⟩ := m
  obtain ⟨hr, hs, -, -⟩ := hA
  simp only at hr hs
  subst hr hs
  rfl

/-! ## A node at a switch -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A node at a stack switch**: a register operation at node `n` (in
region `R`) lands at node `n'` in the region based at the new `sp`, after a
local run of the source. From every state of `n`'s invariant (with its
machine data `m`), the new `sp` value `v` is 16-aligned and the region
`swR v lo hi` does not wrap, the new frame condition holds of the machine
data after the step, the new region's cells hold some slot file `sl` in
`m`'s memory, and the source reaches `n'`'s invariant at the abstract state
after the step with slot file `sl`. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem sw_ndW {W : Frag isaLSE2} {K : State → State → Prop} {n n' : ND} {w : RegWidth} {op : Operation w}
    {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hop : RegOnly op = true)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨w, op⟩])
    (hpc : n'.pc = n.pc + Int64.ofNat 4) (ho : n'.o = SO.entry)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec.toNat % 16 = 0 ∧
      (swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).OK ∧
      F' (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec
        { m with regs := (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs,
                 status := (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).status } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k, (swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).Off k →
          ∃ j, Mem.loadInt m.dmem
            ((swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).addr k) 8 = some j ∧
            BitVec.ofInt 64 j = sl k) ∧
        ∃ c', LocalRun p c c' ∧ n'.J { AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ with slot := sl } c') :
    SegW W K p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc0, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr ⟨w, op⟩) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc0]; simp)
  obtain ⟨h16, hok, hF', sl, hsl, c', hr, hJ'⟩ := hedge _ σ c hA hD hJ
  refine .silent _ c' (exec_reg hop hc) hr ?_
  have hm := regRes_abs hop hA (n.pc + Int64.ofNat 4)
  refine ⟨_, h16, hok, he, hn, hdc, by simp only [hpc0, hpc], _, ⟨?_, ?_, ?_, ?_⟩, ?_, hJ'⟩
  · simp only [hm]
  · simp only [hm]
  · rw [ho]; exact soRel_entry lo hi
  · intro k hk
    simp only [regRes_dmem hop]
    exact hsl k hk
  · simp only [hm]; exact hF'

/-- **`sw_ndW` inside the trivial predicate**, with no outside moves. -/
theorem sw_nd {n n' : ND} {w : RegWidth} {op : Operation w} {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hop : RegOnly op = true)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [.instr ⟨w, op⟩])
    (hpc : n'.pc = n.pc + Int64.ofNat 4) (ho : n'.o = SO.entry)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec.toNat % 16 = 0 ∧
      (swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).OK ∧
      F' (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec
        { m with regs := (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs,
                 status := (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).status } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k, (swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).Off k →
          ∃ j, Mem.loadInt m.dmem
            ((swR (AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ).regs.SP.toBitVec lo hi).addr k) 8 = some j ∧
            BitVec.ofInt 64 j = sl k) ∧
        ∃ c', LocalRun p c c' ∧ n'.J { AI.step n.o (n.pc + Int64.ofNat 4) (.reg w op) σ with slot := sl } c') :
    Seg p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') :=
  (sw_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hop hcode hpc ho hedge).toSeg

end Fn

/-- **Continuing after a switch**: a segment from the switched-to node for
every 16-aligned, non-wrapping `v` is a segment from `SwAt`. -/
theorem sw_seg {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : Frag isaLSE2}
    (h : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v lo hi).OK → Seg p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    Seg p lbl ms (SwAt exe endPc lo hi F' n') X :=
  (Seg.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v lo hi).OK} =>
      At exe endPc (swR g.1 lo hi) (F' g.1) n') fun g => h g.1 g.2.1 g.2.2).mono_pre
    fun _ _ ⟨v, h1, h2, hA⟩ => ⟨⟨v, h1, h2⟩, hA⟩

/-- **A switch, then the code in the new region**: a segment into `SwAt`,
continued by a segment from the switched-to node for every admissible `v`. -/
theorem sw_seq {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {P X : Frag isaLSE2}
    (h : Seg p lbl ms P (SwAt exe endPc lo hi F' n'))
    (h' : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v lo hi).OK →
      Seg p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    Seg p lbl ms P X :=
  h.seq (sw_seg h')

/-- **Continuing after a switch**, inside `W` with outside moves `K`
(`sw_seg` over `SegW`). -/
theorem sw_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : Frag isaLSE2}
    (h : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v lo hi).OK →
      SegW W K p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    SegW W K p lbl ms (SwAt exe endPc lo hi F' n') X :=
  (SegW.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v lo hi).OK} =>
      At exe endPc (swR g.1 lo hi) (F' g.1) n') fun g => h g.1 g.2.1 g.2.2).mono_pre
    fun _ _ ⟨v, h1, h2, hA⟩ => ⟨⟨v, h1, h2⟩, hA⟩

/-- **A switch, then the code in the new region**, inside `W` with outside
moves `K` (`sw_seq` over `SegW`). -/
theorem sw_seqW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {P X : Frag isaLSE2}
    (h : SegW W K p lbl ms P (SwAt exe endPc lo hi F' n'))
    (h' : ∀ v : BitVec 64, v.toNat % 16 = 0 → (swR v lo hi).OK →
      SegW W K p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    SegW W K p lbl ms P X :=
  h.seq (sw_segW h')

/-! ## The parser's forms -/

section Parse

open Kraken.AArch64.Parser

/-- The switch directive `add sp, Xs, #0`. -/
def swDir (s : XReg) : Directive :=
  .instr ⟨.W64, .ADD_e (.low .SP .W64) (.low (.reg s) .W64) (.imm ⟨.int64 0, .S0⟩)⟩

/-- `swDir` is what Kraken's parser makes of scc's two switches. -/
example : parseAArch64("add sp, x9, #0
add sp, x29, #0") = [swDir .X9, swDir .X29] := by
  decide

/-- Both are register operations. -/
example (s : XReg) : RegOnly (w := .W64) (.ADD_e (.low .SP .W64) (.low (.reg s) .W64) (.imm ⟨.int64 0, .S0⟩)) = true :=
  rfl

end Parse

end Spike.Lib.A64.Flow
