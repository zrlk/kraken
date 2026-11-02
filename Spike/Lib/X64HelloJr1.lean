/-
**hello's `wc_main` entry invariants pinned** (x86-64; the twin of `Spike/Lib/A64HelloJr1.lean`): the concrete `Jr`
(`scc_rt_main`'s state back from `wc_rodata`) and `Jr1` (after `scc_rt_main`'s local run to the box's `new`) that
the root's level-1 chain leaves as parameters.

At `wc_rodata`'s return the lowered code passes the slice in `%rax`, `%rdx`, `%rcx`, `%rsi` (the buffer's address,
`0`, `2`, `13`; `X64HelloMainPreSrc.SlRep`), and the source pops `frH env` into the wrapper's continuation with `r`
bound to the slice (`JrH`). Past the continuation and `main`'s split and zero the source is at the box's `new`
(`c0H`) on the same slice and `me`'s word `mw`; `scc_rt_main` moves the registers to `wc_main`'s arguments
(`Hello1.mWC`: `%rdi ← %rax`, `%rsi ← %rdx`, `%rdx ← %rcx`, `%rcx ← %rsi`).

- `JrH env`: the wrapper's continuation on `rodata`'s slice at some label (the canonical return invariant).
- `JrR lbl env`: `JrH env` with the slice's registers (`SlRegs`).
- `Jr1H lbl mw`: the box's `new` (`c0H`) on the slice at some label and `me`'s word `mw`, the slice's registers.
- `jr1H_c0`: a `Jr1H` control is `c0H` on `slW`'s words.
- `SlRegs`, `slRegs_slRep`: the slice's registers at `wc_rodata`'s return, and their `SlRep`.

Unlike AArch64, the slice's registers are `wc_rodata`'s x86-64 return registers `%rax`, `%rdx`, `%rcx`, `%rsi`
(AArch64: `x0`–`x3`, unchanged into `wc_main`), `JrH` is stated here (AArch64: in `HelloRdCf`), and the local run
from `JrT (JrR lbl env)` to `Jr1H` (AArch64's `jr1H_loc`, over `HelloM.JrT`) is not stated: x86-64's `JrT` is not
yet available.
-/
import Spike.Lib.X64HelloRdCf

namespace Spike.Lib.X64.Flow.HelloJr1

open CoreLang CoreTerm TermRun
open Spike.Lib (Ctl)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64HelloMainPreSrc (SlRep c0H)
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64HelloRdCf (slW)

/-- **The slice's registers** at `wc_rodata`'s return, at the buffer's label `l`: `%rax` the buffer's address
`lbl l`, `%rdx = 0`, `%rcx = 2`, `%rsi = 13` (`slRegs_slRep`: `SlRep` of `slW l`). -/
def SlRegs (lbl : WeakMem.AllocLabel → Option Nat) (l : WeakMem.AllocLabel) (σ : AS) : Prop :=
  lbl l = some σ.regs.rax.toBitVec.toNat ∧ σ.regs.rdx.toBitVec.toNat = 0 ∧ σ.regs.rcx.toBitVec.toNat = 2 ∧
    σ.regs.rsi.toBitVec.toNat = 13

/-- **`SlRegs` is `SlRep` of the slice's words** at the four registers. -/
theorem slRegs_slRep {lbl : WeakMem.AllocLabel → Option Nat} {l : WeakMem.AllocLabel} {σ : AS}
    (h : SlRegs lbl l σ) :
    SlRep lbl (slW l) σ.regs.rax.toBitVec.toNat σ.regs.rdx.toBitVec.toNat σ.regs.rcx.toBitVec.toNat
      σ.regs.rsi.toBitVec.toNat :=
  ⟨l, rfl, h⟩

/-- **The canonical return invariant**: the wrapper's continuation on `rodata`'s slice at some label. -/
def JrH (env : Env) (_ : AS) (c : Ctl) : Prop :=
  ∃ l, c = ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩

/-- **`scc_rt_main` back from `wc_rodata`**: the wrapper's continuation on `rodata`'s slice at some label `l`
(`JrH`), the slice in `wc_rodata`'s return registers. -/
def JrR (lbl : WeakMem.AllocLabel → Option Nat) (env : Env) (σ : AS) (c : Ctl) : Prop :=
  ∃ l, c = ⟨SrcCalls.setupCont, ("r", slTy, slW l) :: env, none⟩ ∧ SlRegs lbl l σ

/-- **`scc_rt_main` at the box's `new`**: `c0H` on the slice at some label `l` and `me`'s word `mw`, the slice in
`wc_rodata`'s return registers. -/
def Jr1H (lbl : WeakMem.AllocLabel → Option Nat) (mw : Word) (σ : AS) (c : Ctl) : Prop :=
  ∃ l, c = c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw ∧ SlRegs lbl l σ

/-- `JrR` is `JrH` with the registers. -/
theorem jrR_jrH {lbl : WeakMem.AllocLabel → Option Nat} {env : Env} {σ : AS} {c : Ctl} (h : JrR lbl env σ c) :
    JrH env σ c := by
  obtain ⟨l, rfl, -⟩ := h
  exact ⟨l, rfl⟩

/-- **A `Jr1H` control is the box's `new`** on `slW`'s words. -/
theorem jr1H_c0 {lbl : WeakMem.AllocLabel → Option Nat} {mw : Word} {σ : AS} {c : Ctl} (h : Jr1H lbl mw σ c) :
    ∃ l, c = c0H (cst (.loc ⟨l, 0⟩ 0)) (cst (.num 2)) (cst (.num 13)) mw := by
  obtain ⟨l, h, -⟩ := h
  exact ⟨l, h⟩

/-- Inhabitation: `SlRegs` at a state holding the slice, the buffer's label placed at its address. -/
example (σ : AS) (hax : σ.regs.rax.toBitVec.toNat = 4096) (hdx : σ.regs.rdx.toBitVec.toNat = 0)
    (hcx : σ.regs.rcx.toBitVec.toNat = 2) (hsi : σ.regs.rsi.toBitVec.toNat = 13) :
    SlRegs (fun _ => some 4096) 0 σ :=
  ⟨by rw [hax], hdx, hcx, hsi⟩

end Spike.Lib.X64.Flow.HelloJr1

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.slRegs_slRep' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.slRegs_slRep

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.jrR_jrH' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.jrR_jrH

/-- info: 'Spike.Lib.X64.Flow.HelloJr1.jr1H_c0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloJr1.jr1H_c0
