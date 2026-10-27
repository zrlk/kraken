/-
**`h0In_setup_assembled`'s code facts from `PlaceOK`** (x86-64; the twin of
`Spike/Lib/LowerA64/SetupCodeOf.lean`): for an `Accepted2` program with a
setup block whose output passes `placeOKAt`, at the runtime layout at any
immediates (`RuntimeLayout.ofPlaceOK h i`: its code, labels and phase
tables do not read the immediates), `main`'s head at `scc_rt_main`'s user
label `(setupMC sw).fn` (`hfnB`) and the setup function's prologue, its
head's phase facts and its check label off the write abort (`hproS`,
`hphS`, `hlcS`, `Spike/Lib/LowerX64/H0InAssembled.lean`).

- `mainHead_ofPlaceOK`: `main`'s head `xHead` at `wc_main`, from its
  compiled block's prologue (`FnCode2.hpro`, `main_compiled2_ofAccepted2`);
- `setupCode_ofPlaceOK`: the setup function's facts (`setupPro_ofPlaceOK`
  at the `rodata` block, `rodata_compiled2_ofSetupOf`) at any immediates.
-/
import Spike.Lib.LowerX64.SetupProOf
import Spike.Lib.MainCompiled2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout setupMC)
open Spike.Lib.LowerNode (compiled2)
open Spike.Lib.X64.AllocG (abLabs)

/-- **`main`'s head from the placement check**: for an `Accepted2` program
whose output passes `placeOKAt`, `scc_rt_main`'s user label at any `sw`
starts with the prologue's head `xHead` (`main`'s compiled block's
prologue). -/
theorem mainHead_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) (sw : Nat) :
    Scc.Cert.Rt.X64.blockAtB (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (setupMC sw).fn 0 Spike.Lib.X64.Flow.xHead = true := by
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  obtain ⟨ws, rt, hws, -, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  have hfn : c.fn = (setupMC sw).fn := by rw [c.hfn, hn]; rfl
  have hpro := c.hpro
  rw [hfn] at hpro
  simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hpro
  exact hpro.1.1.1.1.1.2

/-- **The setup function's code facts from the placement check**, at the
runtime layout at any immediates `i`: for an `Accepted2` program with a
setup block (`hs`), `scc_rt_main`'s setup label at any `sw` has a prologue
with its stack check label `chk`, its head's phase facts there, and `chk`
off the write abort (`setupPro_ofPlaceOK` at the `rodata` block). -/
theorem setupCode_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {s : Ty}
    (hs : Scc.Lower.setupOf p = some s)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    (i : CoreTerm.Expr → String → Nat → Option Nat) (sw : Nat) :
    let Ly := RuntimeLayout.ofPlaceOK h i
    ∃ (chk entry : Label) (Zs lim : Int64) (Lg : Label) (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)),
      Spike.Lib.X64.Flow.prologueIn Ly.prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true ∧
      Spike.Lib.X64Consumer.blkPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) (fun _ => false)
        Ly.lab (Ly.lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true ∧
      chk ∉ abLabs := by
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.rodata_compiled2_ofSetupOf hp hs
  obtain ⟨chk, entry, Zs, lim, Lg, zl, zf, z1, z2, zs, ps, hpro, hph, -, hl⟩ := setupPro_ofPlaceOK hp h hd hn sw
  exact ⟨chk, entry, Zs, lim, Lg, zl, zf, z1, z2, zs, ps, hpro, hph, hl⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainHead_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainHead_ofPlaceOK

/-- info: 'Spike.Lib.LowerX64.setupCode_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupCode_ofPlaceOK
