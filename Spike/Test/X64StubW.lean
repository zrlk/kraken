/-
**The overflow abort path's checks at `ret0.x`** (`Spike/Lib/X64StubW.lean`):
the phase check `abortPhOk` and the stub's `write` call (`hsysIn`) hold on
`ret0.x`'s cells at the phase record's `okPc`/`ph` (`Spike/Lib/X64PhRec.lean`),
and the exit call's site hypotheses (`hrel`, `htk`, `hk`) hold at `ret0.x`'s
marks; a phase table putting the exit call's next pc in another phase fails
the check. The twin of `Spike/Test/A64StubW.lean`.
-/
import Spike.Lib.X64StubW
import Spike.Test.X64PhRec

namespace Spike.Lib.X64.StubW.Test

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.PhRec
open Spike.Lib.X64.Rt.Ret0L (ret0L)
open Spike.Lib.X64.OwnLimRt (labIn label_labIn)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0_lays)
open SccCode (ret0Λ ret0Cells)

/-- `ret0.x`'s labels through `labIn` where the cells have them. -/
def labR (l : Label) : Int64 :=
  if (Scc.Cert.Rt.X64.labelIdx ret0Cells l).isSome then labIn ret0Λ.code.lo ret0Cells l
  else (_root_.Executable.labels ret0Exe).label l

theorem ret0_labR : (_root_.Executable.labels ret0Exe).label = labR := by
  funext l
  unfold labR
  split
  · next h => exact label_labIn ret0_lays rfl h
  · rfl

/-- **The abort path's phase check at `ret0.x`**, decided on the hand tables. -/
theorem ret0_abortPhOk_hand :
    abortPhOk Spike.Lib.X64.Flow.Ret0.Inst.okPc Spike.Lib.X64.Flow.Ret0.Inst.ph labR = true := by
  decide +kernel

/-- **The abort path's phase check at the record's `okPc`/`ph`.** -/
theorem ret0_abortPhOk : abortPhOk (okPc ret0L) (ph ret0L) ret0L.lab = true := by
  rw [Test.ret0_okPc, Test.ret0_ph]
  show abortPhOk _ _ (_root_.Executable.labels ret0Exe).label = true
  rw [ret0_labR]
  exact ret0_abortPhOk_hand

/-- **The stub's `write` call** in `ret0.x`'s cells. -/
theorem ret0_sysIn :
    Scc.Cert.Rt.X64.blockAtB ret0Cells Abort.overflow.entry 34
      [(Kraken.Promising.Lower.X64.op64 .syscall, 2)] = true := by
  decide +kernel

/-- The exit call's pc at `ret0.x`: the overflow's abort site. -/
theorem ret0_exit : (labR Abort.overflow.exit).toBitVec.toNat = 4198555 := by decide +kernel

/-- **The exit call's site hypotheses hold at `ret0.x`'s marks** (satisfiable). -/
example :
    (∀ a, Spike.Lib.X64.Flow.Ret0.Inst.μ0.site .release = some a → (labR Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ a, Spike.Lib.X64.Flow.Ret0.Inst.μ0.site .take = some a → (labR Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ k a, Spike.Lib.X64.Flow.Ret0.Inst.μ0.abortAt k = some a → (labR Abort.overflow.exit).toBitVec.toNat = a →
      k = .overflow) := by
  rw [ret0_exit]
  refine ⟨fun a h => ?_, fun a h => ?_, fun k a h e => ?_⟩
  · cases h; decide
  · cases h; decide
  · subst e; cases k <;> simp [Spike.Lib.X64.Flow.Ret0.Inst.μ0] at h ⊢

/-- A phase table with the exit call's next pc in another phase fails. -/
example : abortPhOk Spike.Lib.X64.Flow.Ret0.Inst.okPc
    (fun pc => if pc = 4198557 then 7 else Spike.Lib.X64.Flow.Ret0.Inst.ph pc) labR = false := by
  decide +kernel

/-- An `okPc` excluding the stub's `leaq` fails. -/
example : abortPhOk (fun pc => Spike.Lib.X64.Flow.Ret0.Inst.okPc pc && pc != (labR Abort.overflow.entry).toBitVec.toNat)
    Spike.Lib.X64.Flow.Ret0.Inst.ph labR = false := by
  decide +kernel

/-- The stubs' `write` node (`Abort.N .sys`) at `ret0.x`'s argument block:
`%rdi = 2`, `%rax = 1` after `x1Overflow` (`movl $1, %eax` zero-extends),
so its invariant is satisfiable. -/
example (lab : Label → Int64) (c0 : Ctl) (σ : Spike.Lib.X64.AS) :
    (Abort.N lab Abort.overflow c0 .sys).J
      (arun lab Abort.x1Overflow ⟨(Abort.N lab Abort.overflow c0 .n2).pc, Abort.oI, σ⟩).σ c0 :=
  ((by arg_hit Abort.x1Overflow_run : ∀ σ c, Abort.JI c0 σ c → Hit (Abort.N lab Abort.overflow c0 .sys)
      (arun lab Abort.x1Overflow ⟨(Abort.N lab Abort.overflow c0 .n2).pc, Abort.oI, σ⟩) c) σ c0 rfl).2.2

/-- `Abort.Local.at_lag`'s premise is satisfiable: a state at the `.ovf`
block held back at its own control (`C := (· = c)`), whose image is the
block at `LagJ`. -/
example {p : Prog} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {o : Spike.Lib.X64.SO} {pcA : Int64} {J : Spike.Lib.X64.AS → Ctl → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (Abort.Local.LN (_root_.Executable.labels exe).label o pcA J false) s c) :
    At exe endPc R F (Abort.Local.LN (_root_.Executable.labels exe).label o pcA
      (Spike.Lib.LagJ p (· = c) J) false) s c :=
  Abort.Local.at_lag ⟨c, h, .refl c, rfl⟩

end Spike.Lib.X64.StubW.Test
