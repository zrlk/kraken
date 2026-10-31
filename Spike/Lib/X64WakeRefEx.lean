/-
**`RefEx`: the threads stub's exit call is an abort site of `ms1W`**
(x86-64, wake.w; the twin of `Spike/Lib/A64WakeRefEx.lean`): the entry's
marks are `PhRec.μ` (`marks_target`), whose `.threads` abort is
`codeLabel` of the layout's abort label, `abortName .threads`, at the stub's
exit label's pc (decided on the certificate's code, read through `hlab`).

- `threads_exit_pc`, `refEx`: the piece.

**Unlike AArch64**: the labels are `wakeCells`' (`codeLabel`, A64's
`codeOf`); `RefEx` takes the assembly `asm`, whose cells are the output's
(`hpa`) and wake's (`hwp`), so `marks_target` reads them directly (A64's
`textProgram SccCertificate.asm`).
-/
import Spike.Lib.X64WakeRefAbW
import Spike.Lib.X64WakeAbOffW

namespace Spike.Lib.X64.WakeRefEx

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (lo)
open SccCode (wakeCells)
open Spike.Lib.X64.WakeRefStub (RefEx)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- The threads abort label is the stub's exit label, in the certificate's code. -/
theorem threads_exit_pc : Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) Spike.Lib.X64.Abort.threads.exit 0 =
    codeLabel lo wakeCells (Scc.Cert.Link.abortName .threads) := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- **`RefEx`**: the exit call's pc is `PhRec.μ`'s `.threads` abort. -/
theorem refEx (asm : Asm) (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = lo) (E : Entry) (cT : Loc) (ls0 : Spike.Lib.X64Consumer.Lsize) (l : WeakMem.AllocLabel)
    (b n : Nat) : RefEx asm hp i E cT ls0 l b n := by
  intro s hs
  have hprog := Spike.Lib.X64.WakeSrcCtl.prog_W hp i hpa hwp
  have hpL : cellsOf asm = some (Ly).prog := by rw [hprog]; exact hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hlab := Spike.Lib.X64WakeOAb.hlab_W hp i hpa hwp hlo0
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName := PlaceWX.abortLbl_of_placeWX (PlaceWX.link i hp)
  cases hx : Scc.Cert.Rt.X64.pcAt (codeLabel lo wakeCells) Spike.Lib.X64.Abort.threads.exit 0 with
  | none => rw [threads_exit_pc, ← Scc.Cert.Rt.X64.codeT_eq] at hx; exact absurd hx (by decide +kernel)
  | some x =>
    refine ⟨.threads, x, ?_, ?_⟩
    · rw [Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) hpL]
      show codeLabel (Ly).Λ.code.lo (Ly).prog ((Ly).Λ.abortLbl .threads) = some x
      rw [hΛ, hlo, hprog, ← threads_exit_pc, hx]
    · unfold pcOf; rw [hs]; exact Spike.Lib.X64.Rt.PhOfTab.pcAt0_eq hlab hx

end Spike.Lib.X64.WakeRefEx

/-- info: 'Spike.Lib.X64.WakeRefEx.threads_exit_pc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefEx.threads_exit_pc

/-- info: 'Spike.Lib.X64.WakeRefEx.refEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefEx.refEx
