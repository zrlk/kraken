/-
**The setup block's landings for any program** (x86-64; the twin of
`Spike/Lib/LowerA64/G1H1.lean`): `H1InW` at the landings `ElG` (the setup
frame of `rodata`, `CxOkH`, at its bottom keys `BotH`) at the write tail
`fun _ => True`, for any `Accepted2` program with a setup block, from
`main`'s call at every reachable placement (`MainLUStmt`).

Each landing's segment at the extended placement `upd L l b`,
`updN ls l n` is `landStk_segH`'s (one frame, no records) at the aborts'
fragment `AbG2L` there, with no walk restriction (`Tr := fun _ _ => True`):

- the element types by `newBufK_of_accepted2`;
- the region bound and the returned base's store by `hAW_H1RestXW`;
- the allocating frame's resumption by `resumeLU_ofCxOkH`;
- the bottom keys' exits by `exitStk_ofBotHL` at the extended placement
  (reachable: `Reach.step`);
- the aborts ending nowhere by `abG2L_seg`.

- `h1InW_ofSetupL`: the landings' `H1InW`;
- `h1SetupStmtL`: `H1SetupStmtL` (its `CallLUStmt` premise unused, the
  plain calls coming from `callLU_ofCxOkH` inside `resumeLU_ofCxOkH`);
- `h1SetupStmt_of`: `H1SetupStmt` (`Spike/Lib/LowerX64/G1Closed2.lean`)
  from `MainLUStmt` at every instance with a setup block.
-/
import Spike.Lib.LowerX64.G1H1Land
import Spike.Lib.LowerX64.G1H1Bot
import Spike.Lib.LowerX64.G1H1Res
import Spike.Lib.LowerX64.G1Closed2
import Spike.Test.X64Hello1HAW

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (rS0)
open Spike.Lib.LowerNode (compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)

section H1L

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
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

/-- **The setup block's landings' `H1InW`** for any `Accepted2` program
with a setup block, from `main`'s call at every reachable placement
(`HM`): each landing's segment by `landStk_segH` at the aborts `AbG2L` at
the extended placement and no walk restriction. -/
theorem h1InW_ofSetupL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOk pcfg = true) (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (htg : tgOkB OP = true)
    (HM : MainLUStmt h ty) (E : Entry) :
    H1InW h E (ElG h hp) (fun _ => True) := by
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
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfs, _⟩ := hC
      rw [hfs]; rfl)
    hTn (hAW_H1RestXW h hp hty hTn (Bot := BotH h) J hJ L ls hR) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ hd _ _ _ _ _ _ _ _ hC hB hra =>
      ⟨_, fun _ _ _ h' => h', resumeLU_ofCxOkH h hp hty hcfg hobj htg E hJ (fun _ _ => True) hR hl hAL hd hC hB hra⟩)
    (fun _ _ hB => exitStk_ofBotHL h hp hty HM J hR' hAbQ hB) hAbQ).mono_pre fun _ _ _ hE => LandStk.fam hE

end H1L

/-- **`H1SetupStmtL`**: `h1InW_ofSetupL` (the plain calls' premise
`CallLUStmt` is not needed: `resumeLU_ofCxOkH` takes them from
`callLU_ofCxOkH`). -/
theorem h1SetupStmtL : H1SetupStmtL :=
  fun _ _ _ _ _ _ hp _ hty _ hcfg hobj E _ h htg _ HM => h1InW_ofSetupL h hp hty hcfg hobj htg HM E

/-- **`H1SetupStmt` from `main`'s call** at every instance with a setup
block: `h1InW_ofSetupL` at `MainLUStmt` (`HM`). -/
theorem h1SetupStmt_of
    (HM : ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
      (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
      ∀ ty : Ty, Scc.Lower.setupOf p = some ty →
      ∀ h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true,
      MainLUStmt h ty) :
    H1SetupStmt :=
  fun cfg pcfg p sizes labelOffs Λ hp ty hty _ hcfg hobj E _ h htg =>
    h1InW_ofSetupL h hp hty hcfg hobj htg (HM cfg pcfg p sizes labelOffs Λ hp ty hty h) E

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h1InW_ofSetupL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h1InW_ofSetupL

/-- info: 'Spike.Lib.LowerX64.h1SetupStmtL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h1SetupStmtL

/-- info: 'Spike.Lib.LowerX64.h1SetupStmt_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h1SetupStmt_of
