/-
**A plain callee's prologue inside `W2` at a base context** (AArch64):
`ProCallG2` (`Spike/Lib/LowerA64/G1CallG2.lean`), the callee's prologue at
its entry invariant `calleeJSO`, in its region below the caller's frame, at
the call's frame pushed on the caller's frames.

- `proCallG2`: from the room and limit statements (`Room2OwnStmt`,
  `Room2CalleeStmt`, `Lim2CalleeStmt`): the callee's context
  (`CxG2M.callG2`), its prologue inside `W2` placed under its frame
  condition (`proW_w2F`), the abort phase (`proW_abStC`), the limit word
  mapped (`hmr_TP0`), the entry placed from `x0` and the caller's frames
  (`placedS_calleeEntry`).
-/
import Spike.Lib.LowerA64.G1CallG2
import Spike.Lib.LowerA64.G1ProW
import Spike.Lib.LowerA64.G1CalleePlace
import Spike.Lib.LowerA64.G1Hmr

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum)

section G1ProCall

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A plain callee's prologue inside `W2` at a base context**
(`ProCallG2`): the callee's context with the caller's record pushed
(`CxG2M.callG2`) gives its region, frame condition, thread pointer and
limit word; the prologue inside `W2` (`proW_w2F`) at the block's prologue
facts (`fnCode2OfPMe_spec`), its abort phase (`proW_abStC`, the overflow
target off the write abort, `posOff_proL_FC`), the limit word mapped
(`hmr_TP0`, the thread pointer the first TCB's), the entry's states placed
from `x0` on the call's frame and the caller's frames
(`placedS_calleeEntry`), the entry control `q.cE` free of `ZBad` at the
frames (the callee's ghosts). -/
theorem proCallG2 (hp : Scc.Lower.Accepted2 p = true) (hown : Room2OwnStmt h hp)
    (hrc : Room2CalleeStmt h hp) (hlc : Lim2CalleeStmt h hp) : ProCallG2 h hp := by
  intro Dt J j d hd R F fs fp ra tp G0 Ab hcx hra D hDe g q frm F' hF' hCF hex hav hbl hsite j' dg hd' hf
  have hc' := (CxG2M.callG2 h hp hown hrc hlc hd hcx hDe hF' hCF hex hsite hd' hf).1.1
  have hc := hcx.1
  have hrow := hown j d hd 256 R.lo (hc.room d hd)
  have hD0 : 0 ≤ D := by omega
  have hlo' : (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0).lo ≤ -((FC j' dg hd').cx.frame : Int) := by
    have := hown j' dg hd' 256 _ (hc'.room dg hd')
    omega
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))
  have hspec := (fnCode2OfPMe_spec hp h Λ j' dg hd').2.2
  have htp : ∀ σ c, calleeJSO (R.callee (-((FC j d hd).cx.frame : Int)) (-D) 0) F'
      (_root_.Executable.labels (Ly).exe).label g tp q σ c → σ.regs.TPIDR_EL0 = tp :=
    fun σ c hJ => hJ.1.2.2.2.2
  have hab := proW_abStC (FC j' dg hd')
    (ms := MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) (frm :: fs)) hI
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hspec.2.1 hspec.1 (posOff_proL_FC hp h Λ j' dg hd' _) hspec.2.2 htp hc'.hR hc'.hal hlo' hc'.hhi hc'.hun
  have hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) false ⟨limA tp, 8⟩ = true := by
    rw [hc'.htp]; exact hmr_TP0 h
  refine proW_w2F (FC j' dg hd') hI htp hspec.2.1 hc'.hR hc'.hal hlo' hc'.hhi hc'.hl hc'.hh hmr hc'.hun
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub (Ly) (Spike.Lib.A64.Rt.rS0_sub (Ly))) hc'.hFO
    (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hF' hab ?_ ?_
  · intro σ c hJ s hF ha
    exact placedS_calleeEntry h (FC j d hd).hf hCF (by omega) hc.hhi hD0 hc.hfp hav _ g tp _ σ c
      ⟨hJ.1, hJ.2.1⟩ s hF ha
  · rintro σ c ⟨⟨rfl, -⟩, -⟩
    exact ⟨fun h' => absurd h' (List.cons_ne_nil _ _), hc'.hG0F q.cE (.refl _)⟩

end G1ProCall

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.proCallG2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.proCallG2
