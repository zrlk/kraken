/-
**The overflow abort path's checks at `ret0`** (`Spike/Lib/A64StubW.lean`):
the phase check `abortPhOk` and the stub's `write` call (now among `abortIn`'s blocks) hold on
`ret0`'s program at the phase record's `okPc`/`ph` (`Spike/Lib/A64PhRec.lean`),
and the exit call's site hypotheses (`hrel`, `htk`, `hk`) hold at `ret0`'s
marks; a phase table putting the exit call's next pc in another phase fails
the check.
-/
import Spike.Lib.A64StubW
import Spike.Test.A64PhRec

namespace Spike.Lib.A64.StubW.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.PhRec
open Spike.Lib.A64.Rt.Ret0L (ret0L)
open Spike.Lib.A64.OwnLimRt (labIn labOk label_labIn)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0_lays)
open SccCode (ret0Λ ret0Prog)

/-- `ret0`'s labels through `labIn` where the program has them. -/
def labR (l : Label) : Int64 :=
  if labOk ret0Prog l then labIn ret0Λ.code.lo ret0Prog l else (_root_.Executable.labels ret0Exe).label l

theorem ret0_labR : (_root_.Executable.labels ret0Exe).label = labR := by
  funext l
  unfold labR
  split
  · next h => exact label_labIn ret0_lays rfl h
  · rfl

/-- **The abort path's phase check at `ret0`**, decided on the hand tables. -/
theorem ret0_abortPhOk_hand :
    abortPhOk Spike.Lib.A64.Flow.Ret0.Inst.okPc Spike.Lib.A64.Flow.Ret0.Inst.ph labR = true := by
  decide +kernel

/-- **The abort path's phase check at the record's `okPc`/`ph`.** -/
theorem ret0_abortPhOk : abortPhOk (okPc ret0L) (ph ret0L) ret0L.lab = true := by
  rw [Test.ret0_okPc, Test.ret0_ph]
  show abortPhOk _ _ (_root_.Executable.labels ret0Exe).label = true
  rw [ret0_labR]
  exact ret0_abortPhOk_hand

/-- **The stub's `write` call** in `ret0`'s program. -/
theorem ret0_svcIn : Scc.Cert.Rt.A64.blockAt ret0Prog Abort.overflow.entry 7 [Spike.Lib.A64.Flow.svcDir] = true := by
  decide +kernel

/-- The exit call's pc at `ret0`: the overflow's abort site. -/
theorem ret0_exit : (labR Abort.overflow.exit).toBitVec.toNat = 4198512 := by decide +kernel

/-- **The exit call's site hypotheses hold at `ret0`'s marks** (satisfiable). -/
example :
    (∀ a, Spike.Lib.A64.Flow.Ret0.Inst.μ0.site .release = some a → (labR Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ a, Spike.Lib.A64.Flow.Ret0.Inst.μ0.site .take = some a → (labR Abort.overflow.exit).toBitVec.toNat ≠ a) ∧
    (∀ k a, Spike.Lib.A64.Flow.Ret0.Inst.μ0.abortAt k = some a → (labR Abort.overflow.exit).toBitVec.toNat = a →
      k = .overflow) := by
  rw [ret0_exit]
  refine ⟨fun a h => ?_, fun a h => ?_, fun k a h e => ?_⟩
  · cases h; decide
  · cases h; decide
  · subst e; cases k <;> simp [Spike.Lib.A64.Flow.Ret0.Inst.μ0] at h ⊢

/-- A phase table with the exit call's next pc in another phase fails. -/
example : abortPhOk Spike.Lib.A64.Flow.Ret0.Inst.okPc
    (fun pc => if pc = 4198516 then 7 else Spike.Lib.A64.Flow.Ret0.Inst.ph pc) labR = false := by
  decide +kernel

/-- An `okPc` excluding the stub's `adrp` fails. -/
example : abortPhOk (fun pc => Spike.Lib.A64.Flow.Ret0.Inst.okPc pc && pc != (labR Abort.overflow.entry).toBitVec.toNat)
    Spike.Lib.A64.Flow.Ret0.Inst.ph labR = false := by
  decide +kernel

end Spike.Lib.A64.StubW.Test
