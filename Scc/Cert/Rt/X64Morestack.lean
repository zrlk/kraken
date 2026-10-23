import Spike.Lib.X64Switch
import Kraken.X64.Parser

/-!
# `scc_rt_morestack` on x64

The trampoline between a grow stub and the runtime's `scc_rt_grow`
(`Scc.Emit.X64`, the protocol in `Scc.IR.StackMap`), the x64 twin of
`Scc/Cert/Rt/A64Morestack.lean`:

    scc_rt_morestack(need = rdi):
      push rbp; rbp := rsp                         -- the frame record
      (delta, ob, osz) := scc_rt_grow(rbp, need)   -- in rax, rdx, rcx: copies the stack
      rbp := rbp + delta; rsp := rbp               -- the stack switch
      scc_rt_stack_release(ob, osz)                -- on the new stack
      pop rbp; ret

`seg_morestack` proves it one segment from its entry in the region `R` of
the old stack (`%rsp` at offset 8, the return address `ra` in the cell
`[8, 16)`, cells `[-8, 16)` its frame record and the call's return
address, `%rbp = fp`) to its return in the region `swR v (-8) 16` based at
the moved frame record `v`, with `%rsp` at offset 16, `%rbp` the moved
frame record's saved `%rbp`, `fp + (v - R.addr 0)` (the caller's frame
pointer moved by the same distance), and the frame condition `F' v`.

Given nodes (hypotheses), as on AArch64:

- `hgrow`, the call to `scc_rt_grow`, from its entry (`%rdi` the frame
  record, `%rsi` the frame size `need`, the return address into the
  trampoline at `-8`, `ra` at `8`) back to the trampoline, for some new
  frame record address `v` and old range `(ob, osz)`: `%rbp` kept, `%rax`
  the distance `v - %rbp`, `(%rdx, %rcx) = (ob, osz)`, and the memory
  `Moved R ra fp F' v`: the region `swR v (-8) 16` not wrapping and
  outside `R`, its cells mapped with the saved `%rbp` moved,
  `fp + (v - R.addr 0)`, at `v` and `ra` at `v + 8`, and `F' v`.
- `hrel`, the call to `scc_rt_stack_release`, on the new stack: from its
  entry (`(%rdi, %rsi) = (ob, osz)`) back, keeping the frame record.

The stack switch `movq %rbp, %rsp` is `sw_nd`. The code is a hypothesis
(`Code`): every block at its node's pc. Each block is zipped with its
instructions' sizes in bytes (the assembler's); a node's pc is
`scc_rt_morestack` plus the sizes of the instructions before it: `+ 15`,
`+ 18`, `+ 21` and `+ 32`.
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

/-! ## The blocks -/

def b0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
movq %rdi, %rsi
movq %rbp, %rdi
call scc_rt_grow")).zip [1, 3, 3, 3, 5]
def b1 : List (Directive × Nat) := (parse("addq %rax, %rbp")).zip [3]
def b2 : List (Directive × Nat) := (parse("movq %rdx, %rdi
movq %rcx, %rsi
call scc_rt_stack_release")).zip [3, 3, 5]
def b3 : List (Directive × Nat) := (parse("popq %rbp
ret")).zip [1, 1]

/-- The stack switch (3 bytes). -/
theorem bs_eq : parse("movq %rbp, %rsp") = [swDir .rbp] := by decide

/-- The offsets at entry. -/
abbrev oE : SO := ⟨8, []⟩
/-- The offsets in the frame on the old stack. -/
abbrev oF : SO := ⟨0, [(.rbp, 0)]⟩
/-- The offsets at the call to `scc_rt_grow`. -/
abbrev oG : SO := ⟨-8, [(.rbp, 0)]⟩
/-- The offsets at the switch, and at its target. -/
abbrev oS : SO := ⟨0, []⟩
/-- The offsets at the call to `scc_rt_stack_release`. -/
abbrev oR : SO := ⟨-8, []⟩

block_spec b0 (-8) 16 oE b0
block_spec b1 (-8) 16 oF b1
block_spec b2 (-8) 16 oS b2
block_spec b3 (-8) 16 oS b3

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (R : Region) (c0 : Ctl) (ra need fp : BitVec 64)

/-- The trampoline's address. -/
abbrev pc0 : Int64 := lab "scc_rt_morestack"

/-- The region after the switch, at the moved frame record `v`. -/
abbrev rN (v : BitVec 64) : Region := swR v (-8) 16

/-- **The memory after `scc_rt_grow`** for the new frame record at `v`: the
region `rN v` not wrapping and outside `R`, its cells mapped with the saved
`%rbp` moved by the stack's distance, `fp + (v - R.addr 0)`, at `v` and the
return address `ra` at `v + 8`, and `F' v`. -/
def Moved (F' : BitVec 64 → MachineData → Prop) (v : BitVec 64) (m : MachineData) : Prop :=
  (rN v).OK ∧
  ((v.toNat : Int) + 16 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ v.toNat - 8) ∧
  (∀ k, (rN v).Off k → ∃ j, Mem.loadInt m.dmem ((rN v).addr k) 8 = some j) ∧
  (∃ j, Mem.loadInt m.dmem ((rN v).addr 0) 8 = some j ∧ BitVec.ofInt 64 j = fp + (v - R.addr 0)) ∧
  (∃ j, Mem.loadInt m.dmem ((rN v).addr 8) 8 = some j ∧ BitVec.ofInt 64 j = ra) ∧
  F' v m

/-- The entry: `%rsp` at offset 8, `ra` in its cell, `%rdi` the frame
size, `%rbp = fp`. -/
def nE : ND := ⟨pc0 lab, oE, fun σ c => c = c0 ∧ σ.regs.get64 .rsp = R.addr 8 ∧ σ.slot 8 = ra ∧
  σ.regs.get64 .rdi = need ∧ σ.regs.get64 .rbp = fp⟩

/-- The return from `scc_rt_grow`, the stack moved to `v`, the old range
`(ob, osz)`. -/
def nG1 (v ob osz : BitVec 64) : ND := ⟨pc0 lab + 15, oF, fun σ c => c = c0 ∧
  σ.regs.get64 .rbp = R.addr 0 ∧ σ.regs.get64 .rax = v - R.addr 0 ∧
  σ.regs.get64 .rdx = ob ∧ σ.regs.get64 .rcx = osz⟩

/-- The call to `scc_rt_grow`. -/
def nGrow : ND := ⟨lab "scc_rt_grow", oG, fun σ c => c = c0 ∧ σ.slot 8 = ra ∧ σ.slot 0 = fp ∧
  σ.regs.get64 .rbp = R.addr 0 ∧ σ.regs.get64 .rdi = R.addr 0 ∧ σ.regs.get64 .rsi = need ∧
  σ.slot (-8) = (pc0 lab + 15).toBitVec⟩

/-- The stack switch: `%rbp` at the new frame record. -/
def nSw (v ob osz : BitVec 64) : ND := ⟨pc0 lab + 18, oS, fun σ c => c = c0 ∧
  σ.regs.get64 .rbp = v ∧ σ.regs.get64 .rdx = ob ∧ σ.regs.get64 .rcx = osz⟩

/-- On the new stack, after the switch: `%rsp = w`, the saved `%rbp` `fr`
in the frame record. -/
def n2 (w fr ob osz : BitVec 64) : ND := ⟨pc0 lab + 21, oS, fun σ c =>
  c = c0 ∧ σ.regs.get64 .rsp = w ∧ σ.slot 8 = ra ∧ σ.slot 0 = fr ∧ σ.regs.get64 .rdx = ob ∧ σ.regs.get64 .rcx = osz⟩

/-- The return from `scc_rt_stack_release`. -/
def nR1 (fr : BitVec 64) : ND := ⟨pc0 lab + 32, oS, fun σ c => c = c0 ∧ σ.slot 8 = ra ∧ σ.slot 0 = fr⟩

/-- The call to `scc_rt_stack_release`. -/
def nRel (fr ob osz : BitVec 64) : ND := ⟨lab "scc_rt_stack_release", oR, fun σ c =>
  c = c0 ∧ σ.slot 8 = ra ∧ σ.slot 0 = fr ∧ σ.regs.get64 .rdi = ob ∧ σ.regs.get64 .rsi = osz ∧
  σ.slot (-8) = (nR1 lab c0 ra fr).pc.toBitVec⟩

/-- **The return**: pc at `ra`, `%rsp` at offset 16 of the new region,
`%rbp` the saved `fr`. -/
def nRet (fr : BitVec 64) : ND := ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => c = c0 ∧ σ.regs.get64 .rbp = fr⟩

/-- **The code**: every block, and the switch, at its node's pc. -/
structure Code (exe : _root_.Executable) (endPc : Int64) : Prop where
  e : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 (_root_.Executable.labels exe).label) b0
  g1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (pc0 (_root_.Executable.labels exe).label + 15) b1
  sw : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (pc0 (_root_.Executable.labels exe).label + 18) [(swDir .rbp, 3)]
  n2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (pc0 (_root_.Executable.labels exe).label + 21) b2
  r1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
    CodeAt s (pc0 (_root_.Executable.labels exe).label + 32) b3

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {ra need fp : BitVec 64}

/-- The frame record and the call to `scc_rt_grow`. -/
theorem seg_grow {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi)
    (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need fp))
      (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need fp)) := by
  refine (fn_seg (N := fun _ : Unit => nE _ R c0 ra need fp) (E := fun _ : Unit => nGrow _ R c0 ra need fp)
    (fun _ => seg_nd (by simp [b0]) b0_ok hF hR hlo hhi hcode.e fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post
    fun _ _ ⟨_, h⟩ => h
  rw [nE, b0_run]
  obtain ⟨hc, hsp, h8, hdi, hbp⟩ := hJ
  refine .inr ⟨(), rfl, rfl, ?_⟩
  simp_all [nGrow, upd_apply, Region.addr_sub8]

/-- `Moved` survives writes inside `R` when `F' v` does: the region `rN v`
is outside `R`. -/
theorem Moved.stable {F' : BitVec 64 → MachineData → Prop} {v : BitVec 64} (hF' : FStable R (F' v)) :
    FStable R (Moved R ra fp F' v) := by
  rintro m m' ⟨hok, hout, hcells, ⟨j0, hj0, hfr⟩, ⟨j8, hj8, hra⟩, hF⟩ hD
  have hd : ∀ k, (rN v).Off k → Mem.loadInt m'.dmem ((rN v).addr k) 8 = Mem.loadInt m.dmem ((rN v).addr k) 8 :=
    fun k hk => by
      have ha := Region.addr_toNat hok hk
      have hf := Region.addr_fit hok hk
      obtain ⟨-, hk0, hk16⟩ := hk
      have hb : (rN v).base = v := rfl
      rw [hb] at ha
      simp only [rN, swR] at hk0 hk16
      exact hD _ hf (by omega)
  have h0 : (rN v).Off 0 := ⟨rfl, by simp [rN, swR], by simp [rN, swR]⟩
  have h8 : (rN v).Off 8 := ⟨rfl, by simp [rN, swR], by simp [rN, swR]⟩
  exact ⟨hok, hout, fun k hk => (hd k hk).symm ▸ hcells k hk, ⟨j0, (hd 0 h0).trans hj0, hfr⟩,
    ⟨j8, (hd 8 h8).trans hj8, hra⟩, hF' _ _ hF hD⟩

/-- `%rbp` moved by the distance `scc_rt_grow` returned. -/
theorem seg_move {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64} (hF' : FStable R (F' v))
    (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi) (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R (Moved R ra fp F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz))
      (At exe endPc R (Moved R ra fp F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz)) := by
  refine (fn_seg (N := fun _ : Unit => nG1 _ R c0 v ob osz) (E := fun _ : Unit => nSw _ c0 v ob osz)
    (fun _ => seg_nd (by simp [b1]) b1_ok (Moved.stable hF') hR hlo hhi hcode.g1
      fun σ c hJ => ⟨c, .refl c, ?_⟩) ()).mono_post fun _ _ ⟨_, h⟩ => h
  rw [nG1, b1_run]
  obtain ⟨hc, hbp, hax, hdx, hcx⟩ := hJ
  refine .inr ⟨(), by simp [nSw, Int64.add_assoc], rfl, ?_⟩
  simp_all [nSw]

/-- The switch's step: `%rsp := %rbp`, `%rdx` and `%rcx` kept. -/
theorem sw_step (o : SO) (f : Int64) (σ : AS) :
    let σ' := AI.step o f (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rbp .W64))))) σ
    σ'.regs.get64 .rsp = σ.regs.get64 .rbp ∧ σ'.regs.get64 .rdx = σ.regs.get64 .rdx ∧
      σ'.regs.get64 .rcx = σ.regs.get64 .rcx := by
  simp [BlockSpec.AI.step_reg', regRes, Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Reg64s.set]

/-- The cells of the region after the switch, read from memory. -/
def movedSlot (m : MachineData) (v : BitVec 64) (k : Int) : BitVec 64 :=
  BitVec.ofInt 64 ((Mem.loadInt m.dmem ((rN v).addr k) 8).getD 0)

/-- **The stack switch** `movq %rbp, %rsp`: onto the moved frame record. -/
theorem seg_switch {F' : BitVec 64 → MachineData → Prop} {v ob osz : BitVec 64}
    (hF'' : FStable (rN v) (F' v)) (hcode : Code exe endPc) :
    Seg p lbl ms (At exe endPc R (Moved R ra fp F' v) (nSw (_root_.Executable.labels exe).label c0 v ob osz))
      (SwAt exe endPc (-8) 16 F' (n2 (_root_.Executable.labels exe).label c0 ra v (fp + (v - R.addr 0)) ob osz)) := by
  refine sw_nd rfl hcode.sw (by simp [nSw, n2, Int64.add_assoc]) rfl fun m σ c _ hG hJ => ?_
  obtain ⟨hok, -, hcells, ⟨j0, hj0, hfr⟩, ⟨j8, hj8, hra⟩, hF⟩ := hG
  obtain ⟨hc, hbp, hdx, hcx⟩ := hJ
  obtain ⟨hsp, hx1, hx2⟩ := sw_step oS ((nSw (_root_.Executable.labels exe).label c0 v ob osz).pc + Int64.ofNat 3) σ
  simp only [nSw] at hsp hx1 hx2 ⊢
  rw [hsp, hbp]
  have hs0 : movedSlot m v 0 = fp + (v - R.addr 0) := by unfold movedSlot; rw [hj0]; exact hfr
  have hs8 : movedSlot m v 8 = ra := by unfold movedSlot; rw [hj8]; exact hra
  refine ⟨hok, hF'' _ _ hF fun _ _ _ => rfl, movedSlot m v, fun k hk => ?_, c, .refl c, ?_⟩
  · obtain ⟨j, hj⟩ := hcells k hk
    exact ⟨j, hj, by simp [movedSlot, rN, hj]⟩
  · simp only [n2, hx1, hx2, hdx, hcx, hc, hs0, hs8, hsp, hbp, and_self]

/-- The nodes on the new stack. -/
inductive PB where
  | n2 | rel | r1

/-- The nodes on the new stack, by name. -/
def NB (lab : Label → Int64) (c0 : Ctl) (ra w fr ob osz : BitVec 64) : PB → ND
  | .n2 => n2 lab c0 ra w fr ob osz
  | .rel => nRel lab c0 ra fr ob osz
  | .r1 => nR1 lab c0 ra fr

/-- On the new stack: the call to `scc_rt_stack_release` and the return. -/
theorem seg_new {F' : BitVec 64 → MachineData → Prop} {v w fr ob osz : BitVec 64}
    (hF'' : FStable (rN v) (F' v)) (hok : (rN v).OK) (hcode : Code exe endPc)
    (hrel : Seg p lbl ms (At exe endPc (rN v) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra fr ob osz))
      (At exe endPc (rN v) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra fr))) :
    Seg p lbl ms (At exe endPc (rN v) (F' v) (n2 (_root_.Executable.labels exe).label c0 ra w fr ob osz))
      (At exe endPc (rN v) (F' v) (nRet c0 ra fr)) := by
  have hlo : (rN v).lo ≤ -8 := Int.le_refl _
  have hhi : 16 ≤ (rN v).hi := Int.le_refl _
  refine (fn_seg (N := NB _ c0 ra w fr ob osz) (E := fun _ : Unit => nRet c0 ra fr) (fun i => ?_) PB.n2).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case n2 =>
    refine seg_nd (by simp [b2]) b2_ok hF'' hok hlo hhi hcode.n2 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, n2] at hJ
    rw [NB, n2, b2_run]
    refine .inl ⟨PB.rel, rfl, rfl, ?_⟩
    simp_all [NB, nRel, nR1, upd_apply, BitVec.add_assoc]
  case rel => exact seg_given PB.r1 hrel
  case r1 =>
    refine seg_nd (by simp [b3]) b3_ok hF'' hok hlo hhi hcode.r1 fun σ c hJ => ⟨c, .refl c, ?_⟩
    simp only [NB, nR1] at hJ
    rw [NB, nR1, b3_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩ <;> simp_all [nRet]

/-- **`scc_rt_morestack` is one segment**, given its code and its calls to
`scc_rt_grow` and `scc_rt_stack_release`: from its entry on the old stack to
its return on the new one, at the moved frame record `v`, with `%rbp` the
caller's frame pointer moved by the same distance. -/
theorem seg_morestack {F : MachineData → Prop} {F' : BitVec 64 → MachineData → Prop}
    (hcode : Code exe endPc)
    (hF : FStable R F) (hF'R : ∀ v, FStable R (F' v)) (hF'' : ∀ v, FStable (rN v) (F' v))
    (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : 16 ≤ R.hi)
    (hgrow : Seg p lbl ms (At exe endPc R F (nGrow (_root_.Executable.labels exe).label R c0 ra need fp))
      (fun s c => ∃ v ob osz,
        At exe endPc R (Moved R ra fp F' v) (nG1 (_root_.Executable.labels exe).label R c0 v ob osz) s c))
    (hrel : ∀ v ob osz, Seg p lbl ms
      (At exe endPc (rN v) (F' v) (nRel (_root_.Executable.labels exe).label c0 ra (fp + (v - R.addr 0)) ob osz))
      (At exe endPc (rN v) (F' v) (nR1 (_root_.Executable.labels exe).label c0 ra (fp + (v - R.addr 0))))) :
    Seg p lbl ms (At exe endPc R F (nE (_root_.Executable.labels exe).label R c0 ra need fp))
      (fun s c => ∃ v, At exe endPc (rN v) (F' v) (nRet c0 ra (fp + (v - R.addr 0))) s c) := by
  refine ((seg_grow hF hR hlo hhi hcode).seq hgrow).seq ?_
  refine (Seg.exists_pre (P := fun g : BitVec 64 × BitVec 64 × BitVec 64 =>
      At exe endPc R (Moved R ra fp F' g.1) (nG1 _ R c0 g.1 g.2.1 g.2.2)) fun g => ?_).mono_pre
    fun _ _ ⟨v, ob, osz, h⟩ => ⟨(v, ob, osz), h⟩
  obtain ⟨v, ob, osz⟩ := g
  refine ((seg_move (hF'R v) hR hlo hhi hcode).seq (seg_switch (hF'' v) hcode)).seq
    (sw_seg fun v' hok => ?_)
  by_cases hv : v' = v
  · subst hv
    exact (seg_new (hF'' v') hok hcode (hrel v' ob osz)).mono_post fun _ _ h => ⟨v', h⟩
  · -- the switch's target is at `v`: no other region
    refine Seg.mono_pre (P := fun _ _ => False) ⟨fun _ _ => False, fun _ _ h => h, fun _ _ h => h.elim⟩ ?_
    rintro s c ⟨-, -, -, -, σ, hA, -, -, hsp, -⟩
    have := hA.so .rsp 0 (by simp [n2, oS, SO.get])
    exact hv (by rw [← hsp, this]; simp [swR, Region.addr])

end Proof

end Scc.Cert.Rt.X64.Morestack
