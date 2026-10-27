/-
**The setup function's prologue facts from `PlaceOK`** (AArch64): for an
`Accepted2` program whose output passes `placeOKAt`, the setup function
(`rodata`, a compiled block) has at `scc_rt_main`'s setup label
`(setupMC sw).setup` (`wc_rodata`) its prologue, its head's phase facts and
its stack check label off the write abort: `h0_ofPlaceOK_setup`'s
`hproS`, `hphS`, `hlS` (`Spike/Lib/LowerA64/RtMainX.lean`).

- `setupPro_ofPlaceOK`: from `fnCode2_ofPlaceOKR` at the block's index
  (`FnCode2.hpro`, `ProPh.hd`, `local_not_abLabs` at the function index
  past the runtime's).
-/
import Spike.Lib.LowerA64.FnCode2Build
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.Rt.A64CodeInSetup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout setupMC)
open Spike.Lib.LowerNode (compiled2)
open Spike.Lib.A64.AllocG (abLabs)

/-- **The setup function's prologue facts from the placement check**: for an
`Accepted2` program `p` whose output passes `placeOKAt` and a compiled block
`d` named `rodata` (the `j`th), at the runtime layout
`RuntimeLayout.ofPlaceOK h (imms2Of p)`, `scc_rt_main`'s setup label at any
`sw` has a prologue (`prologueIn`) with its stack check label `chk`, its
head's phase facts there, and `chk` off the write abort. -/
theorem setupPro_ofPlaceOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata") (sw : Nat) :
    let Ly := RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
    ∃ (chk entry : Label) (Zs lim : Int64) (Lg : Label) (ps : List (XReg × Int64)),
      Spike.Lib.A64.Flow.prologueIn Ly.prog (setupMC sw).setup chk entry Zs lim Lg ps = true ∧
      Spike.Lib.A64Consumer.blkPh (Spike.Lib.A64.PhRec.okPc Ly) (Spike.Lib.A64.PhRec.ph Ly) (fun _ => false)
        Ly.lab (Ly.lab chk + Int64.ofNat (4 * 0)) 0 (Spike.Lib.A64.Flow.chkHead Zs) = true ∧
      chk ∉ abLabs := by
  intro Ly
  obtain ⟨ws, rt, hws, -, hrt, H⟩ := fnCode2_ofPlaceOKR hp h
  have hj : j < ws.length := hws.1 ▸ (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨c, -, -, -, hcx, -, -, hph, -⟩ := H j d ws[j] hd (List.getElem?_eq_getElem hj)
  have hfn : c.fn = (setupMC sw).setup := by rw [c.hfn, hn]; rfl
  refine ⟨c.cx.local "stack_check", c.entry, _, _, _, c.ps, hfn ▸ c.hpro, hph.hd, local_not_abLabs ?_ _⟩
  rw [hcx]
  show rt.length + j ≠ 9 ∧ rt.length + j ≠ 12 ∧ rt.length + j ≠ 16
  omega

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.setupPro_ofPlaceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.setupPro_ofPlaceOK
