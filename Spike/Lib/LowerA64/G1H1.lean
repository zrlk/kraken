/-
**The setup block's landings for any program** (AArch64): `H1InAW` at the
landings `ElH` (the setup frame of `rodata`, `CxOkH`, at its bottom keys
`BotH`) at the write tail `fun _ => True`, for any `Accepted2` program with
a setup block, from `main`'s call at every reachable placement
(`MainLUStmt`).

Each landing's segment at the extended placement `upd L l b`,
`updN ls l n` is `landStk_segH`'s (one frame, no records) at the aborts'
fragment `AbG2L` there, with no walk restriction (`Tr := fun _ _ => True`):

- the element types by `newBufK_of_accepted2`;
- the region bound and the returned base's store by `hAW_H1OpenA`;
- the allocating frame's resumption by `resumeLU_ofCxOkH`;
- the bottom keys' exits by `exitStk_ofBotHL` at the extended placement
  (reachable: `Reach.step`);
- the aborts ending nowhere by `abG2L_seg`.

- `h1InAW_ofSetupL`: the landings' `H1InAW`;
- `h1SetupStmtL`: `H1SetupStmtL` (its `CallLUStmt` premise unused, the
  plain calls coming from `callLU_ofCxOkH` inside `resumeLU_ofCxOkH`).
-/
import Spike.Lib.LowerA64.G1H1Land
import Spike.Lib.LowerA64.G1H1Bot
import Spike.Lib.LowerA64.G1H1Res
import Spike.Test.A64Hello1HAW

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
open Spike.Lib.A64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section H1L

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

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

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

/-- **The setup block's landings' `H1InAW`** for any `Accepted2` program
with a setup block, from `main`'s call at every reachable placement
(`HM`): each landing's segment by `landStk_segH` at the aborts `AbG2L` at
the extended placement and no walk restriction. -/
theorem h1InAW_ofSetupL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (htg : tgOkB OP = true)
    (HM : MainLUStmt h ty) (E : Entry) :
    H1InAW h E (ElH h hp) (fun _ => True) := by
  refine ⟨fun J hJ L ls l b n hR hl hAL => ?_⟩
  have hz : ls l = 0 := Spike.Lib.LowerNode.Reach.lsize_none (fun _ _ => rfl) hR l hl
  have hR' := Reach.step hR hl hAL
  have hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true :=
    fun _ _ hd _ _ _ _ hT => (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  have hAbQ : SegWS (W2T J (LU) (LN)) (KT) p (LU) (MSR J (LU) (LN))
      (AbG2L h hp (fun _ => True) J (LU) (LN)) fun _ _ _ => False :=
    abG2L_seg h hp (room2Own h hp) J (LU) (LN) hR' (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ => trivial)
  exact (landStk_segH (hcode := fnCode2OfPMe hp h Λ) (CxOk := CxOkH h hp) (Bot := BotH h)
    (W := fun L ls => W2T J L ls) (K := KT) (ms := fun L ls => MSR J L ls)
    (Ab₀ := AbG2L h hp (fun _ => True) J (LU) (LN)) (Q := fun _ _ _ => False) (Tr := fun _ _ => True) hl hz
    (fun _ _ _ _ _ _ _ _ _ hC => by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩ := hC
      rfl)
    hTn (hAW_H1OpenA h hp hty hTn J hJ L ls hR) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ hd _ _ _ _ _ _ _ _ hC hB hra =>
      ⟨_, fun _ _ _ h' => h', resumeLU_ofCxOkH h hp hty hcfg hobj htg E hJ (fun _ _ => True) hR hl hAL hd hC hB hra⟩)
    (fun _ _ hB => exitStk_ofBotHL h hp hty HM J hR' hAbQ hB) hAbQ).mono_pre fun _ _ _ hE => LandStk.fam hE

/-- **`H1SetupStmtL`**: `h1InAW_ofSetupL` (the plain calls' premise
`CallLUStmt` is not needed: `resumeLU_ofCxOkH` takes them from
`callLU_ofCxOkH`). -/
theorem h1SetupStmtL : H1SetupStmtL :=
  fun _ _ _ _ hp _ hty _ hcfg hobj E _ h htg _ HM => h1InAW_ofSetupL h hp hty hcfg hobj htg HM E

end H1L

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.h1InAW_ofSetupL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.h1InAW_ofSetupL

/-- info: 'Spike.Lib.LowerA64.h1SetupStmtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.h1SetupStmtL
