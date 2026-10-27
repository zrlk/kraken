/-
**The setup function's prologue facts from `PlaceOK`** (x86-64; the twin of
`Spike/Lib/LowerA64/SetupProOf.lean`): for an `Accepted2` program whose
output passes `placeOKAt`, the setup function (`rodata`, a compiled block)
has at `scc_rt_main`'s setup label `(setupMC sw).setup` (`wc_rodata`) its
prologue, its head's phase facts and its labels off the write abort:
`h0_ofPlaceOK_setup`'s `hproS`, `hphS`, `hlS`, `hlcS`
(`Spike/Lib/LowerX64/Start2W2.lean`).

- `setupPro_ofPlaceOK`: from `fnCode2_ofPlaceOKR` at the block's index
  (`FnCode2.hpro`, `ProPh.hd`), the labels decided at `wc_rodata`.
-/
import Spike.Lib.LowerX64.FnCode2Build
import Spike.Lib.Rt.X64CodeInSetup

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout setupMC)
open Spike.Lib.LowerNode (compiled2)
open Spike.Lib.X64.AllocG (abLabs)

/-- **The setup function's prologue facts from the placement check**: for an
`Accepted2` program `p` whose output passes `placeOKAt` and a compiled block
`d` named `rodata` (the `j`th), at the runtime layout
`RuntimeLayout.ofPlaceOK h (imms2Of p)`, `scc_rt_main`'s setup label at any
`sw` has a prologue (`prologueIn`) with its stack check label `chk`, its
head's phase facts there, and both labels off the write abort. -/
theorem setupPro_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata") (sw : Nat) :
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    ∃ (chk entry : Label) (Zs lim : Int64) (Lg : Label) (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)),
      Spike.Lib.X64.Flow.prologueIn Ly.prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true ∧
      Spike.Lib.X64Consumer.blkPh (Spike.Lib.X64.PhRec.okPc Ly) (Spike.Lib.X64.PhRec.ph Ly) (fun _ => false)
        Ly.lab (Ly.lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true ∧
      (setupMC sw).setup ∉ abLabs ∧ chk ∉ abLabs := by
  intro Ly
  obtain ⟨ws, rt, hws, -, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, -, -, -, hfr, -, -, hph, -, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  have hfn : c.fn = (setupMC sw).setup := by rw [c.hfn, hn]; rfl
  have hfr' : c.fr.fn = (setupMC sw).setup := by rw [hfr, hn]; rfl
  refine ⟨_, c.entry, _, _, _, c.zl, c.zf, c.z1, c.z2, c.zs, c.ps, hfn ▸ c.hpro, hfn ▸ hph.hd,
    by simp only [setupMC]; decide, ?_⟩
  rw [hfr']
  simp only [setupMC]
  decide

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupPro_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.setupPro_ofPlaceOK
