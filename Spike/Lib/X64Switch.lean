/-
**x64 stack switches as nodes of a function**: an instruction that sets
`%rsp` to a value of unknown static offset.

A function's nodes (`Spike/Lib/X64Cfg.lean`) relate the thread's registers
to one region `R` through static offsets (`SO`), and `%rsp` must stay at a
known offset (`SO.write` refuses `%rsp`, so `okBlk` rejects such a write).
scc switches stacks twice: `_start` aligns the kernel's stack (`andq $-16,
%rsp`, an `and` whose `AF` is undefined, so Kraken's tree is a choice), and
`scc_rt_start` moves to the thread's stack (`movq %rax, %rsp`, `%rax`
loaded from a frame slot). After the switch `%rsp` is in another region.

- `swR v lo hi`: the region a switch enters, based at the new `%rsp` value
  `v`, cells `[lo, hi)`; `SO.entry`: `%rsp` at offset 0, no register
  offsets.
- `SwAt exe endPc lo hi F' n'`: node `n'` in the region `swR v lo hi` for
  some non-wrapping `v`, with frame condition `F' v`.
- `sw_nd`: a node at a register operation (`RegOnly`, any destination; the
  switch `movq %r, %rsp` is the one writing `%rsp`) lands at `SwAt`, after a
  local run of the source. The obligation is on the abstract step
  (`AI.step … (.reg w op)`, whose closed form `block_spec`'s simp set
  computes) and on the memory at the node: the new region's cells, the new
  frame condition.
- `swand_nd`: the same for `andq $k, %rsp` (`andRsp k`), for every value of
  the flags (Kraken's row `exec_and_ri`, a choice of `AF`).
- `sw_seg`, `sw_seq`: segments from the switched-to node, one for each `v`, make one
  segment from `SwAt` (`Seg.exists_pre`), so a function graph in the new
  region (`fn_seg` at `swR v lo hi`) continues the switch.
-/
import Spike.Lib.X64Cfg
import Kraken.Promising.Lower.EventsX64Flags
import Kraken.X64.Parser

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64

/-! ## The region after a switch -/

/-- **The region a switch enters**: based at the new `%rsp` value `v`,
cells `[lo, hi)`. -/
def swR (v : BitVec 64) (lo hi : Int) : Region := ⟨v, lo, hi⟩

/-- The static offsets at a switch's target: `%rsp` at offset 0, no register
offsets (the registers' old offsets are relative to the old region). -/
def SO.entry : SO := ⟨0, []⟩

/-- `%rsp` is at offset 0 of the region based at its value. -/
theorem soRel_entry {regs : Reg64s} (lo hi : Int) : SORel (swR (regs.get64 .rsp) lo hi) SO.entry regs := by
  intro r k h
  by_cases hr : r = .rsp
  · subst hr
    simp only [SO.entry, SO.get, ↓reduceIte, Option.some.injEq] at h
    subst h
    simp [swR, Region.addr]
  · simp [SO.entry, SO.get, hr, lk] at h

/-- **Node `n'` after a switch**: in the region `swR v lo hi` for some
non-wrapping `v`, with frame condition `F' v`. -/
def SwAt (exe : _root_.Executable) (endPc : Int64) (lo hi : Int) (F' : BitVec 64 → MachineData → Prop)
    (n' : ND) : Frag isa :=
  fun s c => ∃ v : BitVec 64, (swR v lo hi).OK ∧ At exe endPc (swR v lo hi) (F' v) n' s c

/-! ## Kraken's steps -/

/-- A register operation's machine data, from the abstract state the
machine data is: the abstract step's registers and flags, the vector
registers and memory as they were. -/
theorem regRes_abs {w : Width} {op : Operation w} (h : RegOnly op = true) {R : Region} {o : SO}
    {m : MachineData} {σ : AS} (hA : Abs R o m σ) (fall : Int64) :
    regRes op m = { m with regs := (AI.step o fall (.reg w op) σ).regs,
                           status := (AI.step o fall (.reg w op) σ).status } := by
  rw [regRes_eq h m]
  obtain ⟨r, z, st, d⟩ := m
  obtain ⟨hr, hz, hs, -, -⟩ := hA
  simp only at hr hz hs
  subst hr hz hs
  rfl

/-- The directive `andq $k, %rsp`. -/
def andRsp (k : Int64) : Directive := op64 (.and (.reg (.low .rsp .W64)) (.imm (.int64 k)))

/-- The registers after `andq $k, %rsp`. -/
def andRegs (k : Int64) (r : Reg64s) : Reg64s := r.set64 .rsp (r.get64 .rsp &&& k.toBitVec)

/-- **Kraken's step at `andq $k, %rsp`**: a silent tree whose every leaf is
the registers `andRegs k` and some flags. -/
theorem exec_andRsp {st : State} {k : Int64} {z : Nat} (hc : CellAt st (andRsp k) z) :
    ∃ t, isa.exec st = some t ∧
      SilentTree (fun s' => ∃ fl, s' = after st z { st.st.1 with regs := andRegs k st.st.1.regs, status := fl }) t :=
  ⟨_, exec_and_ri hc, (silentTree_choose2 _).mono fun _ ⟨_, h⟩ => ⟨_, by
    rw [h]; simp only [logicPost, Reg64s.get_low64]; rfl⟩⟩

/-! ## Nodes at a switch -/

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A node at a stack switch** by a register operation: node `n` (in
region `R`) lands at node `n'` in the region based at the new `%rsp`, after
a local run of the source. From every state of `n`'s invariant (with its
machine data `m`), the region `swR v lo hi` at the new `%rsp` value `v` does
not wrap, the new frame condition holds of the machine data after the step,
the new region's cells hold some slot file `sl` in `m`'s memory, and the
source reaches `n'`'s invariant at the abstract state after the step with
slot file `sl`. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem sw_ndW {W : Frag isa} {K : State → State → Prop}
    {n n' : ND} {z : Nat} {w : Width} {op : Operation w} {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hop : RegOnly op = true)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(.instr (.regular .W64 w op), z)])
    (hpc : n'.pc = n.pc + Int64.ofNat z) (ho : n'.o = SO.entry)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).OK ∧
      F' ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp)
        { m with regs := (AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs,
                 status := (AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).status } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k, (swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).Off k →
          ∃ j, Mem.loadInt m.dmem
            ((swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).addr k) 8 = some j ∧
            BitVec.ofInt 64 j = sl k) ∧
        ∃ c', LocalRun p c c' ∧ n'.J { AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ with slot := sl } c') :
    SegW W K p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc0, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (.instr (.regular .W64 w op)) z := (hcode s he hn).cell0 rfl rfl hpc0
  obtain ⟨hok, hF', sl, hsl, c', hr, hJ'⟩ := hedge _ σ c hA hD hJ
  refine .silent _ c' (exec_reg hop hc) hr ?_
  have hm := regRes_abs hop hA (n.pc + Int64.ofNat z)
  refine ⟨_, hok, he, hn, hdc, by simp only [hpc0, hpc], _, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hJ'⟩
  · simp only [hm]
  · simp only [hm]; exact hA.zmms
  · simp only [hm]
  · rw [ho]; exact soRel_entry lo hi
  · intro k hk
    simp only [hm]
    exact hsl k hk
  · simp only [hm]; exact hF'

/-- **`sw_ndW` inside the trivial predicate**, with no outside moves. -/
theorem sw_nd {n n' : ND} {z : Nat} {w : Width} {op : Operation w} {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hop : RegOnly op = true)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(.instr (.regular .W64 w op), z)])
    (hpc : n'.pc = n.pc + Int64.ofNat z) (ho : n'.o = SO.entry)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).OK ∧
      F' ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp)
        { m with regs := (AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs,
                 status := (AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).status } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k, (swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).Off k →
          ∃ j, Mem.loadInt m.dmem
            ((swR ((AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ).regs.get64 .rsp) lo hi).addr k) 8 = some j ∧
            BitVec.ofInt 64 j = sl k) ∧
        ∃ c', LocalRun p c c' ∧ n'.J { AI.step n.o (n.pc + Int64.ofNat z) (.reg w op) σ with slot := sl } c') :
    Seg p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') :=
  (sw_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hop hcode hpc ho hedge).toSeg

/-- **A node at `andq $k, %rsp`**: node `n` (in region `R`) lands at node
`n'` in the region based at the new `%rsp`, for every value of the flags,
after a local run of the source; the obligation as for `sw_nd`, at the
registers `andRegs k` and flags `fl`. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem swand_ndW {W : Frag isa} {K : State → State → Prop}
    {n n' : ND} {z : Nat} {k : Int64} {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(andRsp k, z)])
    (hpc : n'.pc = n.pc + Int64.ofNat z) (ho : n'.o = SO.entry)
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c → ∀ fl : StatusFlags,
      (swR ((andRegs k σ.regs).get64 .rsp) lo hi).OK ∧
      F' ((andRegs k σ.regs).get64 .rsp) { m with regs := andRegs k σ.regs, status := fl } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k', (swR ((andRegs k σ.regs).get64 .rsp) lo hi).Off k' →
          ∃ j, Mem.loadInt m.dmem ((swR ((andRegs k σ.regs).get64 .rsp) lo hi).addr k') 8 = some j ∧
            BitVec.ofInt 64 j = sl k') ∧
        ∃ c', LocalRun p c c' ∧ n'.J { σ with regs := andRegs k σ.regs, status := fl, slot := sl } c') :
    SegW W K p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc0, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (andRsp k) z := (hcode s he hn).cell0 rfl rfl hpc0
  obtain ⟨t, hex, hs⟩ := exec_andRsp hc
  refine .choice _ t hex hs fun s' ⟨fl, hs'⟩ => ?_
  obtain ⟨hok, hF', sl, hsl, c', hr, hJ'⟩ := hedge _ σ c hA hD hJ fl
  refine ⟨c', hr, ?_⟩
  subst hs'
  rw [hA.regs]
  refine ⟨_, hok, he, hn, hdc, by simp only [hpc0, hpc], { σ with regs := andRegs k σ.regs, status := fl, slot := sl },
    ⟨rfl, hA.zmms, rfl, ?_, hsl⟩, hF', hJ'⟩
  rw [ho]; exact soRel_entry lo hi

/-- **`swand_ndW` inside the trivial predicate**, with no outside moves. -/
theorem swand_nd {n n' : ND} {z : Nat} {k : Int64} {lo hi : Int} {F' : BitVec 64 → MachineData → Prop}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(andRsp k, z)])
    (hpc : n'.pc = n.pc + Int64.ofNat z) (ho : n'.o = SO.entry)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c → ∀ fl : StatusFlags,
      (swR ((andRegs k σ.regs).get64 .rsp) lo hi).OK ∧
      F' ((andRegs k σ.regs).get64 .rsp) { m with regs := andRegs k σ.regs, status := fl } ∧
      ∃ sl : Int → BitVec 64,
        (∀ k', (swR ((andRegs k σ.regs).get64 .rsp) lo hi).Off k' →
          ∃ j, Mem.loadInt m.dmem ((swR ((andRegs k σ.regs).get64 .rsp) lo hi).addr k') 8 = some j ∧
            BitVec.ofInt 64 j = sl k') ∧
        ∃ c', LocalRun p c c' ∧ n'.J { σ with regs := andRegs k σ.regs, status := fl, slot := sl } c') :
    Seg p lbl ms (At exe endPc R F n) (SwAt exe endPc lo hi F' n') :=
  (swand_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hcode hpc ho hedge).toSeg

end Fn

/-- **Continuing after a switch**: a segment from the switched-to node for
every non-wrapping `v` is a segment from `SwAt`. -/
theorem sw_seg {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : Frag isa}
    (h : ∀ v : BitVec 64, (swR v lo hi).OK → Seg p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    Seg p lbl ms (SwAt exe endPc lo hi F' n') X :=
  (Seg.exists_pre (P := fun g : {v : BitVec 64 // (swR v lo hi).OK} =>
      At exe endPc (swR g.1 lo hi) (F' g.1) n') fun g => h g.1 g.2).mono_pre
    fun _ _ ⟨v, h1, hA⟩ => ⟨⟨v, h1⟩, hA⟩

/-- **A switch, then the code in the new region**: a segment into `SwAt`,
continued by a segment from the switched-to node for every admissible `v`. -/
theorem sw_seq {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {P X : Frag isa}
    (h : Seg p lbl ms P (SwAt exe endPc lo hi F' n'))
    (h' : ∀ v : BitVec 64, (swR v lo hi).OK → Seg p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    Seg p lbl ms P X :=
  h.seq (sw_seg h')

/-- **Continuing after a switch**, inside `W` with outside moves `K`
(`sw_seg` over `SegW`). -/
theorem sw_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {X : Frag isa}
    (h : ∀ v : BitVec 64, (swR v lo hi).OK → SegW W K p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    SegW W K p lbl ms (SwAt exe endPc lo hi F' n') X :=
  (SegW.exists_pre (P := fun g : {v : BitVec 64 // (swR v lo hi).OK} =>
      At exe endPc (swR g.1 lo hi) (F' g.1) n') fun g => h g.1 g.2).mono_pre
    fun _ _ ⟨v, h1, hA⟩ => ⟨⟨v, h1⟩, hA⟩

/-- **A switch, then the code in the new region**, inside `W` with outside
moves `K` (`sw_seq` over `SegW`). -/
theorem sw_seqW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {lo hi : Int}
    {F' : BitVec 64 → MachineData → Prop} {n' : ND} {P X : Frag isa}
    (h : SegW W K p lbl ms P (SwAt exe endPc lo hi F' n'))
    (h' : ∀ v : BitVec 64, (swR v lo hi).OK → SegW W K p lbl ms (At exe endPc (swR v lo hi) (F' v) n') X) :
    SegW W K p lbl ms P X :=
  h.seq (sw_segW h')

/-! ## The parser's forms -/

section Parse

open Kraken.X64.Parser

/-- The switch directive `movq %s, %rsp`. -/
def swDir (s : Reg64) : Directive := op64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low s .W64))))

/-- `swDir` and `andRsp` are what Kraken's parser makes of scc's two
switches. -/
example : parse("andq $-16, %rsp
movq %rax, %rsp") = [andRsp (-16), swDir .rax] := by
  decide

/-- The `movq` switch is a register operation. -/
example (s : Reg64) : RegOnly (w := .W64) (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low s .W64)))) = true :=
  rfl

end Parse

end Spike.Lib.X64
