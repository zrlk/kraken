/-
**`h0InA_setup_assembled`'s code facts from `PlaceOK`** (AArch64; the twin
of `Spike/Lib/LowerX64/SetupCodeOf.lean`): for an `Accepted2` program with
a setup block whose output passes `placeOKAt`, at the runtime layout at any
immediates (`RuntimeLayout.ofPlaceOK h i`: its code, labels and phase
tables do not read the immediates), `main`'s prologue at `scc_rt_main`'s
user label `(setupMC sw).fn` with its check label off the write abort
(`hproF`, `hlF`) and the setup function's prologue, its check's head's
phase facts and its check label off the write abort (`hproS`, `hphS`,
`hlS`, `Spike/Lib/LowerA64/H0InAssembledA.lean`).

- `mainPro_ofPlaceOK`: `main`'s prologue at `wc_main`, from its compiled
  block's (`FnCode2.hpro`, `main_compiled2_ofAccepted2`), its check label
  a local label of a user function (`local_not_abLabs`);
- `setupCode_ofPlaceOK`: the setup function's facts (`setupPro_ofPlaceOK`
  at the `rodata` block, `rodata_compiled2_ofSetupOf`) at any immediates.
-/
import Spike.Lib.LowerA64.SetupProOf
import Spike.Lib.MainCompiled2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout setupMC)
open Spike.Lib.LowerNode (compiled2)
open Spike.Lib.A64.AllocG (abLabs)

/-- **`main`'s prologue from the placement check**: for an `Accepted2`
program whose output passes `placeOKAt`, `scc_rt_main`'s user label at any
`sw` has a prologue (`prologueIn`, `main`'s compiled block's) whose stack
check label is off the write abort. -/
theorem mainPro_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true) (sw : Nat) :
    ∃ (chk entry : Label) (Z lim : Int64) (Lg : Label) (ps : List (XReg × Int64)),
      Spike.Lib.A64.Flow.prologueIn (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog (setupMC sw).fn chk
        entry Z lim Lg ps = true ∧ chk ∉ abLabs := by
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨ws, rt, hws, -, hrt, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, -, -, -, hcx, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  have hfn : c.fn = (setupMC sw).fn := by rw [c.hfn, hn]; rfl
  refine ⟨c.cx.local "stack_check", c.entry, _, _, _, c.ps, hfn ▸ c.hpro, local_not_abLabs ?_ _⟩
  rw [hcx]
  show rt.length + j ≠ 9 ∧ rt.length + j ≠ 12 ∧ rt.length + j ≠ 16
  omega

/-- **The setup function's code facts from the placement check**, at the
runtime layout at any immediates `i`: for an `Accepted2` program with a
setup block (`hs`), `scc_rt_main`'s setup label at any `sw` has a prologue
with its stack check label `chk`, its check's head's phase facts, and `chk`
off the write abort (`setupPro_ofPlaceOK` at the `rodata` block). -/
theorem setupCode_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s) {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) (sw : Nat) :
    let Ly := RuntimeLayout.ofPlaceOK h i
    ∃ (chk entry : Label) (Zs lim : Int64) (Lg : Label) (ps : List (XReg × Int64)),
      Spike.Lib.A64.Flow.prologueIn Ly.prog (setupMC sw).setup chk entry Zs lim Lg ps = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (fun _ => false)
        Ly.lab (Ly.lab chk + Int64.ofNat (4 * 0)) 0 (Spike.Lib.A64.Flow.chkHead Zs) = true ∧
      chk ∉ abLabs := by
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf hp hs
  exact setupPro_ofPlaceOK hp h hd hn sw

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainPro_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainPro_ofPlaceOK

/-- info: 'Spike.Lib.LowerA64.setupCode_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.setupCode_ofPlaceOK
