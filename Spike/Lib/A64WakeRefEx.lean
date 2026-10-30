/-
**`RefEx`: the threads stub's exit call is an abort site of `ms1W`**
(AArch64, wake.w): the entry's marks are `PhRec.μ` (`marks_target`), whose
`.threads` abort is `codeOf` of the layout's abort label, `abortName
.threads`, at the stub's exit label's pc (decided on the certificate's code,
read through `hlab`).

- `refEx`: the piece.
-/
import Spike.Lib.A64WakeRefAbW
import Spike.Lib.A64WakeAbOffW

namespace Spike.Lib.WakeRefEx

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeRefStub (RefEx)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- The threads abort label is the stub's exit label, in the certificate's code. -/
theorem threads_exit_pc : Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) Spike.Lib.A64.Abort.threads.exit 0 =
    codeOf lo wakeProg (Scc.Cert.Link.abortName .threads) := by
  rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- **`RefEx`**: the exit call's pc is `PhRec.μ`'s `.threads` abort. -/
theorem refEx (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = lo)
    (E : Entry) (cT : Loc) (ls0 : Spike.Lib.A64Consumer.Lsize) (l : WeakMem.AllocLabel) (b n : Nat) :
    RefEx hp i E cT ls0 l b n := by
  intro s hs
  have hprog := Spike.Lib.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.WakeOAb.hlab_W hp i hpa hwp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceW.abortLbl_of_placeW (Spike.Lib.PlaceW.link i hp)
  cases hx : Scc.Cert.Rt.A64.pcAt (codeOf lo wakeProg) Spike.Lib.A64.Abort.threads.exit 0 with
  | none => rw [threads_exit_pc, ← Scc.Cert.Rt.A64.codeT_eq] at hx; exact absurd hx (by decide +kernel)
  | some x =>
    refine ⟨.threads, x, ?_, ?_⟩
    · rw [Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
      show codeOf (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .threads) = some x
      rw [hΛ, hlo, hprog, ← threads_exit_pc, hx]
    · unfold pcOf; rw [hs]; exact Spike.Lib.A64.Rt.PhOfTab.pcAt0_eq hlab hx

end Spike.Lib.WakeRefEx

/-- info: 'Spike.Lib.WakeRefEx.refEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRefEx.refEx
