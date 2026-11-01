/-
**hello's `wc_main` entry invariants pinned** (AArch64, the level-1 chain): the
concrete `Jr` (`scc_rt_main`'s state back at `.sp0`, `wc_rodata`'s return) and `Jr1` (after `scc_rt_main`'s local
run to the box's `new`) that `MainGlueS.MainWcPS` and `HelloLand1.GsH1` leave as parameters.

At `wc_rodata`'s return the lowered code passes the slice in `x0`–`x3` (the buffer's address, `0`, `2`, `13`;
`HelloMainPreSrc.SlRep`), and the source pops `frH env` into the wrapper's continuation with `r` bound to the slice
(`HelloRdCf.JrH`). Past the continuation and `main`'s split and zero the source is at the box's `new` (`c0H`) on
the same slice and `me`'s word `mw`; the registers are unchanged (`scc_rt_main`'s `.sp0` block only moves them to
`wc_main`'s arguments, `Hello1.mWC`).

- `JrR lbl env`: `JrH env` with the slice's registers (`SlRep` at `x0`–`x3`).
- `Jr1H lbl mw`: the box's `new` (`c0H`) on the slice at some label and `me`'s word `mw`, the slice's registers.
- `jr1H_loc`: `MainWcPS.hloc` at these, from `JrT (JrR lbl env) t R` (`me` at `mw` in `env`).
- `jr1H_c0`: a `Jr1H` control is `c0H` on `slW`'s words.
- `SlRegs`, `slRegs_slRep`: the slice's registers, and their `SlRep`.

The thread pointer and `sp` at `wc_main`'s entry are `JrT`'s (`HelloM.JrT`); `x4` (the TCB) is `Hello1.mWC`'s
`σC.slot (-80)`, a fact on the caller's state `σC`, not on `Jr1`.
-/
import Spike.Lib.A64HelloMainPostT

namespace Spike.Lib.A64.Flow.HelloJr1

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl LocalRun LocalRunS)
open Spike.Lib.A64.Flow (AS)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainPreSrc (SlRep c0H c0H_run slTy)
open Spike.Lib.HelloRdCf (JrH slW setupCont_run)
open Spike.Lib.A64.Flow.HelloM (JrT)

/-- **The slice's registers** at the buffer's label `l`: `x0` the buffer's address `lbl l`, `x1 = 0`, `x2 = 2`,
`x3 = 13` (`slRegs_slRep`: `SlRep` of `slW l`). -/
def SlRegs (lbl : WeakMem.AllocLabel → Option Nat) (l : WeakMem.AllocLabel) (σ : AS) : Prop :=
  lbl l = some σ.regs.X0.toBitVec.toNat ∧ σ.regs.X1.toBitVec.toNat = 0 ∧ σ.regs.X2.toBitVec.toNat = 2 ∧
    σ.regs.X3.toBitVec.toNat = 13

/-- **`SlRegs` is `SlRep` of the slice's words** at the four registers. -/
theorem slRegs_slRep {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {σ : AS}
    (h : SlRegs lbl l σ) :
    SlRep lbl (slW l) σ.regs.X0.toBitVec.toNat σ.regs.X1.toBitVec.toNat σ.regs.X2.toBitVec.toNat
      σ.regs.X3.toBitVec.toNat :=
  ⟨l, rfl, h⟩

/-- **`scc_rt_main` back at `.sp0`**: the wrapper's continuation on `rodata`'s slice at some label `l` (`JrH`), the
slice in `x0`–`x3`. -/
def JrR (lbl : WeakMem.AllocLabel → Option Nat) (env : Env) (σ : AS) (c : Ctl) : Prop :=
  ∃ l, c = ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩ ∧ SlRegs lbl l σ

/-- **`scc_rt_main` at the box's `new`**: `c0H` on the slice at some label `l` and `me`'s word `mw`, the slice in
`x0`–`x3`. -/
def Jr1H (lbl : WeakMem.AllocLabel → Option Nat) (mw : Word) (σ : AS) (c : Ctl) : Prop :=
  ∃ l, c = c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw ∧ SlRegs lbl l σ

/-- `JrR` is `JrH` with the registers. -/
theorem jrR_jrH {lbl : WeakMem.AllocLabel → Option Nat} {env : Env} {σ : AS} {c : Ctl} (h : JrR lbl env σ c) :
    JrH env σ c := by
  obtain ⟨l, rfl, -⟩ := h
  exact ⟨l, rfl⟩

/-- **`MainWcPS.hloc` at the pinned invariants**: from `JrT (JrR lbl env) t R` the source's continuation, `main`'s
split and zero reach the box's `new` (`me` at `mw` in `env`), the registers unchanged. -/
theorem jr1H_loc {lbl : WeakMem.AllocLabel → Option Nat} {env : Env} {tm : Ty} {mw : Word} {t : UInt64}
    {R : Spike.Lib.Region} (hme : evalAt env (.var "me") = some (tm, [mw])) (σ : AS) (c : Ctl)
    (h : JrT (JrR lbl env) t R σ c) : ∃ c', LocalRun helloSrc c c' ∧ Jr1H lbl mw σ c' := by
  obtain ⟨⟨l, rfl, hsl⟩, -, -⟩ := h
  exact ⟨_, ((setupCont_run hme).trans (c0H_run _ _ _ _)).toLocalRun, l, rfl, hsl⟩

/-- **A `Jr1H` control is the box's `new`** on `slW`'s words. -/
theorem jr1H_c0 {lbl : WeakMem.AllocLabel → Option Nat} {mw : Word} {σ : AS} {c : Ctl} (h : Jr1H lbl mw σ c) :
    ∃ l, c = c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw := by
  obtain ⟨l, h, -⟩ := h
  exact ⟨l, h⟩

end Spike.Lib.A64.Flow.HelloJr1

/-- info: 'Spike.Lib.A64.Flow.HelloJr1.slRegs_slRep' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloJr1.slRegs_slRep

/-- info: 'Spike.Lib.A64.Flow.HelloJr1.jrR_jrH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloJr1.jrR_jrH

/-- info: 'Spike.Lib.A64.Flow.HelloJr1.jr1H_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloJr1.jr1H_loc

/-- info: 'Spike.Lib.A64.Flow.HelloJr1.jr1H_c0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloJr1.jr1H_c0
