import Scc.Cert.Rt.A64Print
import Spike.Lib.A64Switch

/-!
# `scc_rt_morestack` in an emitted AArch64 program

The trampoline between a grow stub and the runtime's `scc_rt_grow`
(`Scc.Emit.A64.morestack`, the protocol in `Scc.IR.StackMap`):

    scc_rt_morestack(need = x0):
      frame record at sp - 16 (x29, x30), x29 := sp - 16
      (delta, ob, osz) := scc_rt_grow(x29, need)    -- copies the stack to a new range
      x29 := x29 + delta; sp := x29                 -- the stack switch
      scc_rt_stack_release(ob, osz)                 -- on the new stack
      reload x29, x30 from the moved frame record; sp += 16; ret

`seg_morestack` proves it one segment, in any valid layout of a program with
`morestackIn prog = true`, from its entry in the region `R` of the old stack
(`sp` at offset 0, cells `[-16, 0)` its frame record) to its return in the
region `swR v 0 16` based at the moved frame record `v`, with `sp` at offset
16, `x30` the return address and the frame condition `F' v`.

Given nodes (hypotheses):

- `hgrow`, the call to `scc_rt_grow`, from its entry (`x0` the frame record,
  `x1` the frame size `need`, `x30` the return address into the trampoline,
  the return address `ra` in the frame record) back to the trampoline, for
  some new frame record address `v` and old range `(ob, osz)`: `x29` kept,
  `x0` the distance `v - x29`, `(x1, x2) = (ob, osz)`, and the memory
  `Moved R ra F' v`: `v` 16-aligned with its 16 bytes outside `R` and not
  wrapping, the moved frame record's cells mapped with `ra` at `v + 8`, and
  `F' v`.
- `hrel`, the call to `scc_rt_stack_release`, on the new stack: from its
  entry (`(x0, x1) = (ob, osz)`) back, keeping the frame record's `ra`.

The stack switch `add sp, x29, #0` is `sw_nd`; the code before it is in `R`
and the code after it in `swR v 0 16` (`sw_seq`). The frame conditions are
`F` before the call to `scc_rt_grow` and `Moved R ra F' v` after it; `F'`
must survive writes inside both regions.

The theorems stated over the segment predicate (`Spike.Lib.Seg`, `MemSide`)
are in `Spike/Lib/Rt/Seg/A64Morestack.lean` (same namespace and names).
-/

namespace Scc.Cert.Rt.A64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Scc.Cert.Rt.A64.Print

/-! ## The blocks -/

def b0 : List Directive := parseAArch64("sub sp, sp, #16
str x29, [sp]
str x30, [sp, #8]
add x29, sp, #0
orr x1, xzr, x0
orr x0, xzr, x29
bl scc_rt_grow")
def b1 : List Directive := parseAArch64("add x29, x29, x0")
/-- The stack switch. -/
def bs : List Directive := parseAArch64("add sp, x29, #0")
def b2 : List Directive := parseAArch64("orr x0, xzr, x1
orr x1, xzr, x2
bl scc_rt_stack_release")
def b3 : List Directive := parseAArch64("ldr x29, [sp]
ldr x30, [sp, #8]
add sp, sp, #16
ret")

theorem bs_eq : bs = [swDir .X29] := by decide

/-- The offsets at entry. -/
abbrev oE : SO := ⟨0, []⟩
/-- The offsets in the frame on the old stack. -/
abbrev oF : SO := ⟨-16, [(.X29, -16)]⟩
/-- The offsets at the switch. -/
abbrev oS : SO := ⟨-16, []⟩

block_spec b0 (-16) 0 oE b0
block_spec b1 (-16) 0 oF b1
block_spec b2 0 16 SO.entry b2
block_spec b3 0 16 SO.entry b3

/-- **The code of `scc_rt_morestack` in `prog`**: its blocks and the switch
at their offsets from its label. -/
def morestackIn (prog : List Directive) : Bool :=
  blockAt prog "scc_rt_morestack" 0 b0 &&
  blockAt prog "scc_rt_morestack" 7 b1 &&
  blockAt prog "scc_rt_morestack" 8 bs &&
  blockAt prog "scc_rt_morestack" 9 b2 &&
  blockAt prog "scc_rt_morestack" 12 b3

/-! ## The specification -/

section Spec

variable (lab : Label → Int64) (R : Region) (c0 : Ctl) (ra need : BitVec 64)

/-- The trampoline's address. -/
abbrev pc0 : Int64 := lab "scc_rt_morestack"

/-- **The memory after `scc_rt_grow`** for the new frame record at `v`: `v`
16-aligned, its 16 bytes outside `R` and not wrapping, the moved frame
record mapped with the return address `ra` at `v + 8`, and `F' v`. -/
def Moved (F' : BitVec 64 → MachineData → Prop) (v : BitVec 64) (m : MachineData) : Prop :=
  v.toNat % 16 = 0 ∧ (swR v 0 16).OK ∧
  ((v.toNat : Int) + 16 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ v.toNat) ∧
  (∃ j, Mem.loadInt m.dmem v 8 = some j) ∧
  (∃ j, Mem.loadInt m.dmem (v + 8) 8 = some j ∧ BitVec.ofInt 64 j = ra) ∧
  F' v m

/-- The entry: `sp` at the region's base, `x30` the return address, `x0`
the frame size. -/
def nE : ND := ⟨pc0 lab, oE, fun σ c => c = c0 ∧ σ.regs.SP.toBitVec = R.base ∧
  σ.regs.X30.toBitVec = ra ∧ σ.regs.X0.toBitVec = need⟩

/-- The call to `scc_rt_grow`. -/
def nGrow : ND := ⟨lab "scc_rt_grow", oF, fun σ c => c = c0 ∧ σ.slot (-8) = ra ∧
  σ.regs.X29.toBitVec = R.addr (-16) ∧ σ.regs.X0.toBitVec = R.addr (-16) ∧ σ.regs.X1.toBitVec = need ∧
  σ.regs.X30.toBitVec = BitVec.ofInt 64 (((pc0 lab).toInt + 4 + 4 + 4 + 4 + 4 + 4 + 4).bmod 18446744073709551616)⟩

/-- The return from `scc_rt_grow`, the stack moved to `v`, the old range
`(ob, osz)`. -/
def nG1 (v ob osz : BitVec 64) : ND := ⟨pc0 lab + 4 + 4 + 4 + 4 + 4 + 4 + 4, oF, fun σ c => c = c0 ∧
  σ.regs.X29.toBitVec = R.addr (-16) ∧ σ.regs.X0.toBitVec = v - R.addr (-16) ∧
  σ.regs.X1.toBitVec = ob ∧ σ.regs.X2.toBitVec = osz⟩

/-- The stack switch: `x29` at the new frame record. -/
def nSw (v ob osz : BitVec 64) : ND := ⟨pc0 lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, oS, fun σ c => c = c0 ∧
  σ.regs.X29.toBitVec = v ∧ σ.regs.X1.toBitVec = ob ∧ σ.regs.X2.toBitVec = osz⟩

/-- On the new stack, after the switch. -/
def n2 (ob osz : BitVec 64) : ND := ⟨pc0 lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, SO.entry, fun σ c =>
  c = c0 ∧ σ.slot 8 = ra ∧ σ.regs.X1.toBitVec = ob ∧ σ.regs.X2.toBitVec = osz⟩

/-- The call to `scc_rt_stack_release`. -/
def nRel (ob osz : BitVec 64) : ND := ⟨lab "scc_rt_stack_release", SO.entry, fun σ c =>
  c = c0 ∧ σ.slot 8 = ra ∧ σ.regs.X0.toBitVec = ob ∧ σ.regs.X1.toBitVec = osz ∧
  σ.regs.X30.toBitVec = BitVec.ofInt 64
    (((pc0 lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4).toInt + 4 + 4 + 4).bmod 18446744073709551616)⟩

/-- The return from `scc_rt_stack_release`. -/
def nR1 : ND := ⟨pc0 lab + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4, SO.entry, fun σ c =>
  c = c0 ∧ σ.slot 8 = ra⟩

/-- **The return**: pc at `ra`, `sp` at offset 16 of the new region, `x30 =
ra`. -/
def nRet : ND := ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => c = c0 ∧ σ.regs.X30.toBitVec = ra⟩

end Spec

/-! ## The proof -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {c0 : Ctl} {ra need : BitVec 64}

theorem addr_m16 (R : Region) : R.addr (-16) = R.base - 16 := by
  simp only [Region.addr]; bv_omega

/-- `Moved` survives writes inside `R` when `F' v` does: the moved frame
record is outside `R`. -/
theorem Moved.stable {F' : BitVec 64 → MachineData → Prop} {v : BitVec 64} (hF' : FStable R (F' v)) :
    FStable R (Moved R ra F' v) := by
  rintro m m' ⟨h16, hok, hout, ⟨j0, hj0⟩, ⟨j8, hj8, hra⟩, hF⟩ hD
  have hv := hok.hi
  simp only [swR] at hv
  have h8 : (v + 8).toNat = v.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  refine ⟨h16, hok, hout, ⟨j0, (hD v (by omega) (by omega)).trans hj0⟩,
    ⟨j8, (hD (v + 8) (by omega) (by omega)).trans hj8, hra⟩, hF' _ _ hF hD⟩

/-- The switch's step: `sp := x29`, the other registers kept. -/
theorem sw_step (o : SO) (f : Int64) (σ : Flow.AS) :
    let σ' := AI.step o f (.reg .W64 (.ADD_e (.low .SP .W64) (.low (.reg .X29) .W64) (.imm ⟨.int64 0, .S0⟩))) σ
    σ'.regs.SP.toBitVec = σ.regs.X29.toBitVec ∧ σ'.regs.X1 = σ.regs.X1 ∧ σ'.regs.X2 = σ.regs.X2 := by
  simp [BlockSpec.AI.step_reg', Flow.regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp,
    Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, ExtOrImmReg.interp, ConstExpr.interp,
    RegOrSp.base]

/-- The cells of the moved frame record, read from memory. -/
def movedSlot (m : MachineData) (v : BitVec 64) (k : Int) : BitVec 64 :=
  BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR v 0 16).addr k) 8).getD 0)

/-- The nodes on the new stack. -/
inductive PB where
  | n2 | rel | r1

/-- The nodes on the new stack, by name. -/
def NB (lab : Label → Int64) (c0 : Ctl) (ra ob osz : BitVec 64) : PB → ND
  | .n2 => n2 lab c0 ra ob osz
  | .rel => nRel lab c0 ra ob osz
  | .r1 => nR1 lab c0 ra

end Proof

end Scc.Cert.Rt.A64.Morestack
