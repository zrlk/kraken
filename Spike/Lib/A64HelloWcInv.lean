/-
**hello.w's state at main's `clone` decodes as a `clone` call** (AArch64): the machine-only
part of `Spike/Lib/A64WakeWcInv.lean` at hello's `ClonePostH`/`CloneInvH` (`A64HelloClonePreHOf`).

- `clonePcH L`: the clone's pc as a number (label based, no literal), `cloneAtH pfxM`.
- `clone_decode_of_postH`, `clone_decodeH`: at `ClonePostH` (`wcNSH`'s `x8 = 220`, `x0 = cloneFlags`, `x2 = 0`,
  `x4 = 0`) and so at `CloneInvH` the clone's call decodes (`Cl`'s third conjunct).

Deferred (B8, the instance; not twinned here): wake's `H0Stmt`/`H1Stmt`/`i2_cloneInv`/`land_I2` and the take
statements fix wake's one-allocation fragment `I2`. hello.w allocates rodata's buffer before main's box, so the shape
of hello's pre-spawn fragment is the instance's choice (R1O); its clone conjunct is `CloneInvH`.
-/
import Spike.Lib.A64HelloClonePreHOf

namespace Spike.Lib.HelloPreA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **The clone's pc** in `L`'s executable, as `pcOf` reads it. -/
def clonePcH (L : RuntimeLayout) : Nat := (cloneAtH pfxM L.exe).toBitVec.toNat

/-- **The clone's call decodes** at `ClonePostH`: `wcNSH`'s `x8 = 220`, `x0 = cloneFlags`, `x2 = 0`, `x4 = 0`
(`clone(flags, k, 0, t, 0)`), for `Cl`'s `decode` conjunct. -/
theorem clone_decode_of_postH {L : RuntimeLayout} {endPc : Int64} {t : UInt64} {s : State} {c : Ctl}
    (h : ClonePostH L endPc t s c) :
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl) := by
  obtain ⟨_, _, _, _, _, _, _, _, -, ⟨-, -, -, -, σ, hA, -, hJ⟩, -⟩ := h
  obtain ⟨-, h0, -, h2, -, h4, h8, -⟩ := hJ
  have hr := hA.regs
  refine ⟨σ.regs.X1.toNat, σ.regs.X3.toNat, ?_⟩
  simp only [Scc.Sem.Kernel.decode, Scc.Sem.A64.abi, Scc.Sem.A64.xRegs, hr]
  have e8 : σ.regs.X8.toNat = 220 := by rw [← UInt64.toNat_toBitVec, h8]; rfl
  have e0 : σ.regs.X0.toNat = 855808 := by rw [← UInt64.toNat_toBitVec, h0]; rfl
  have e2 : σ.regs.X2.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h2]; rfl
  have e4 : σ.regs.X4.toNat = 0 := by rw [← UInt64.toNat_toBitVec, h4]; rfl
  simp [e8, e0, e2, Scc.Sem.Kernel.Nrs.a64, Scc.Sem.Kernel.cloneFlags]
  exact ⟨e4, rfl⟩

/-- **The clone's call decodes** at `CloneInvH`. -/
theorem clone_decodeH {L : RuntimeLayout} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat} {s : State}
    {c : Ctl} {fs : List TermRun.Frame} (h : CloneInvH L endPc lbl s c fs) :
    ∃ st tl, Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
      some (.clone st tl) := by
  obtain ⟨-, _, _, _, hP, -⟩ := h
  exact clone_decode_of_postH hP

end Spike.Lib.HelloPreA

/-- info: 'Spike.Lib.HelloPreA.clone_decode_of_postH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.clone_decode_of_postH

/-- info: 'Spike.Lib.HelloPreA.clone_decodeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.clone_decodeH
