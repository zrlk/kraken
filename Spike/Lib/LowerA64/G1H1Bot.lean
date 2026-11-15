/-
**The landings' bottom frames' exits for any `Accepted2` program with a
setup block** (AArch64): `H1LandAW.hbot`'s shape at the bottom keys `BotH`
(`Spike/Test/A64Hello1CxOkH.lean`) at a landing's extended placement, from
`main`'s call at the reachable placements (`MainLUStmt`,
`Spike/Lib/LowerA64/G1H1Stmt.lean`) and the aborts' segment.

- `w2_ofBotHL`: a bottom key's exits inside `W2` at a reachable placement
  (`w2_ofSetupBotA` at the key's bounds, `main`'s call from `MainLUStmt`),
  the generic form of `hello1_hWBotA`;
- `exitStk_ofBotHL`: the bottom key's exits as a segment ending in `Q`
  (`exitStk_ofBotHRL`), given the aborts `Ab₀` ending in `Q`.
-/
import Spike.Lib.LowerA64.G1H1Stmt
import Spike.Test.A64Hello1HWBot

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 swFSL)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section Bot

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

/-- **A bottom key's exits inside `W2` at a reachable placement** (the
generic `hello1_hWBotA`): at a `BotH` key's exit at the setup result type,
`W2` at `L0`, `ls` by `w2_ofSetupBotA` at the key's bounds, `main`'s call
from `MainLUStmt`. -/
theorem w2_ofBotHL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (HM : MainLUStmt h ty) (J : InvS) {L0 : Lbl} {ls : Lsize} (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {k : StkKey} {fs : List TermRun.Frame} (hB : BotH h k fs) :
    ∀ c0 ty', k.G0 c0 → (∃ d, (compiled2 p)[k.j]? = some d ∧ d.retTy = ty') → ∀ s c,
      ExitC2SL p L0 (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty' (fun _ _ _ => False) s c fs →
        (W2T J L0 ls) s c fs := by
  intro c0 ty' _ hty' s c hE
  obtain ⟨⟨J0, L', D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, d', hd', hn⟩ := hB
  obtain ⟨d, hd, rfl⟩ := hty'
  cases Option.some.inj (hd.symm.trans hd')
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hp hty hd hn] at hE
  exact w2_ofSetupBotA h hp hty hR hBd (HM J L0 ls hR L' D1 D2 lS lM fS nS fM nM hBd) hSB
    (hE.resolve_right id).2

/-- **A bottom key's exits as a segment at a reachable placement**
(`exitStk_ofBotHRL` with `hW` by `w2_ofBotHL` and `main`'s call from
`MainLUStmt`), given the aborts `Ab₀` ending in `Q` (`hAb`). -/
theorem exitStk_ofBotHL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (HM : MainLUStmt h ty) (J : InvS) {L0 : Lbl} {ls : Lsize} (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {Q Ab₀ : FragS isaLSE2} (hAb : SegWS (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) Ab₀ Q)
    {k : StkKey} {fs : List TermRun.Frame} (hB : BotH h k fs) :
    SegWS (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) (ExitStk p (compiled2 p) L0 (Ly).exe (Ly).endPc k fs Ab₀) Q :=
  exitStk_ofBotHRL h hp hty (fun _ _ hd hn => Spike.Lib.LowerNode.rodata_retTy_compiled2 hp hty hd hn) hR hB
    (w2_ofBotHL h hp hty HM J hR hB) hAb fun L D1 D2 lS lM fS nS fM nM hBd => HM J L0 ls hR L D1 D2 lS lM fS nS fM nM hBd

end Bot

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.w2_ofBotHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.w2_ofBotHL

/-- info: 'Spike.Lib.LowerA64.exitStk_ofBotHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitStk_ofBotHL
