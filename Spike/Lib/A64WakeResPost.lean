/-
**wake.w's reserve after the take** (AArch64): `ResPhP`
(`Spike/Lib/Rt/A64RtReservePost.lean`) at wake.w's extended phase `phW`
(`Spike/Lib/A64WakePh.lean`), for `wc_main`'s second reserve, called once
the main thread's range is taken.

- `resPhWP`: the phase facts, for any take's phase `TkW` of the phase that
  agrees on `0` and `16` (the add's phase and the one past it).
- `resPhWP_canon`: at the canonical take's phase (`A64PhRec.Tk`'s form,
  bit `3` clear), which does.
-/
import Spike.Lib.A64WakePh
import Spike.Lib.Rt.A64RtReservePost

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (okPcOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Reserve
open Spike.Lib.A64.Rt.Reserve (ResPh ResPhP ntA rmwTk_of_ph)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- **The reserve's phase facts after the take** at `phW`, returning to
`wc_main`'s `.sp3`, for a take's phase `TkW` of the phase agreeing on the
add's phase `0` and the next `16` (`hTk`). -/
theorem resPhWP (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {TkW : Nat → Prop}
    (hlab : ∀ l a, codeOf lo wakeProg l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA)
    (hTk : TkW 16 ↔ TkW 0) :
    ResPhP (okPcOf lo wakeProg Λ) phW (fun s => TkW (phW (pcOf s))) (ownW L (ntA lab)) lab
      (lab ".L21_wc_main.sp3") := by
  obtain ⟨-, lE, -⟩ := resLabs
  obtain ⟨-, -, -, p5, p6⟩ := resSteps
  rw [← phW_eq] at p5 p6
  have hrmw : (rmwPc lab).toBitVec.toNat = 2165168 := pc_eq hlab lE 5
  have hrmw4 : (rmwPc lab + Int64.ofNat 4).toBitVec.toNat = 2165172 := by
    unfold rmwPc; rw [hlab _ _ lE, Int64.add_assoc, ← Int64.ofNat_add, toNat_add]
  refine ResPhP.of_resPh (resPhW hΛ (Tk := fun _ => False) hlab hsep fun _ _ _ _ h => h)
    (rmwTk_of_ph (TkW := TkW) ?_)
  rw [hrmw, hrmw4, p5, p6]; exact hTk

/-- **`resPhWP` at the canonical take's phase** (bit `3` of the phase
clear). -/
theorem resPhWP_canon (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout}
    (hlab : ∀ l a, codeOf lo wakeProg l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA) :
    ResPhP (okPcOf lo wakeProg Λ) phW (fun s => phW (pcOf s) / 8 % 2 = 0) (ownW L (ntA lab)) lab
      (lab ".L21_wc_main.sp3") :=
  resPhWP (TkW := fun i => i / 8 % 2 = 0) hΛ hlab hsep (by decide)

/-- info: 'Spike.Lib.A64.WakePh.resPhWP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resPhWP

/-- info: 'Spike.Lib.A64.WakePh.resPhWP_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms resPhWP_canon

end Spike.Lib.A64.WakePh
