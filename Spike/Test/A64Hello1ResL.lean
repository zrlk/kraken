/-
**The landing contexts' blocks at any placement** (AArch64; the
placement-independent part of a landing context's resumption `ResumeCx2T`,
`Spike/Lib/LowerA64/ResumeCx2T.lean`):
at a context `CxOkH` (`Spike/Test/A64Hello1CxOkH.lean`, the setup frame of
the block `rodata`) and any placement `L'`, `ls'` (in particular a landing's
extended placement `upd L l b`, `updN ls l n`), the body's and pending
blocks inside `W2` (`ResumeCx2T`'s body and pending blocks) and the abort
node empty (`ResumeCx2T`'s abort node, `rodata` addition-free). The
context's `CxLB` at the extended placement is not here: it is asked only on
the walk-restricted resumption (plan b1).

- `cxBlk2_ofCxOkHA`: `CxBlk2` inside `W2R J Dt L' ls'` at a `CxOkH` context
  (`cxBlk2_ofFn`: the region from the setup call's premises, the frames
  placed at no label and so at any (`FramesPlacedInI.mono_lbl`), the return
  point `scc_rt_main`'s marshalling block, the targets by `tgOkB`);
- `habN_ofCxOkHA`: no state at a `CxOkH` context's abort node at any
  placement (`abortN2_none_addFree`);
- plan b1's `Tr` (the walk points after a buffer's allocation): `TrNb T`,
  closed under the walk (`TrNb.tail`, `tailOf_trans`), inside a closed walk
  (`TrNb.of_closed`, `TrNb.tailAt2`); at `hello1o`'s `rodata` neither an
  allocation (`hello1_rodata_nbOnce` decided, `noNb_of_nbOnceL`,
  `hello1_rodata_trNoNb`) nor a call (`hello1_rodata_trNoCall`) there.
-/
import Spike.Test.A64Hello1BotRes
import Spike.Test.A64Hello1SetupAb
import Spike.Lib.LowerA64.UserTgt
import Spike.Lib.LowerA64.FramesPlacedSetup
import Spike.Test.A64Hello1NoCall

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me addFreeT)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`A64Hello1BotRes`'s). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (Spike.Lib.AllocReach.IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th block's code facts (`ElH`'s). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

/-- **A landing context's blocks inside `W2` at any placement**
(`cxBlk2_ofFn` at `CxOkH`'s data): at a context `CxOkH` of the `j`th
compiled block (`hd`) and any placement `L'`, `ls'`, the body's and pending
blocks inside `W2R J Dt L' ls'` (`ResumeCx2T`'s body and pending blocks, whose frames `[fr]`
discharge `CxBlk2`'s `main`-return premise by `nofun`). The region facts
from the setup call's premises and bounds (as `setupCxLB_ofPre`), the
frames placed at no label (`framesPlaced_setup`) and so at `L'`
(`FramesPlacedInI.mono_lbl`), the ghosts `FrOk2` from the setup call, the
return point `scc_rt_main`'s marshalling block off the write abort, the
jump targets by the output's check `tgOkB` (`hTg_of_tgOkB`). -/
theorem cxBlk2_ofCxOkHA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTg : tgOkB OP = true) {Dt : State → Prop} (J : InvS) (L' : Lbl) (ls' : Lsize) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hc : CxOkH h hp j R F fs fp ra tp G0 Ab) :
    CxBlk2 (W2R J Dt L' ls') (KT) p L' ls' (FC) R F fs fp ra G0 := by
  obtain ⟨d', hd', L, D1, fS, nS, v, g, fr, J0, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, hra, -, hct, -⟩, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  cases (Option.some.inj (hd.symm.trans hd'))
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hlo0 : ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0).lo ≤
      -((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) := by
    show -D1 ≤ _; rw [hframe]; omega
  have hFO0 : ∀ m, F m → StackOff (rS0 (Ly)) ((swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0)
      m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`, one instruction past
  -- `e0`) is off the write abort
  have hraP : PosOff OP (Ly).lab ((Ly).lab (setupMC (setupWords2 p)).e0 + 4) := by
    have hin := Spike.Lib.A64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2A h hp hs')
    simp only [Spike.Lib.A64.Rt.mainSIn, Bool.and_eq_true] at hin
    have h0 := posOff_of_blockAt (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide) (i := 0)
      (by simp [Spike.Lib.A64.Rt.marshal]; omega)
    have hg : (Ly).lab (setupMC (setupWords2 p)).sp0 = (Ly).lab (setupMC (setupWords2 p)).e0 + 4 :=
      Scc.Cert.Rt.A64.label_labelGap (Ly).lays hin.1.1.1.2
    rw [Nat.add_zero, ofNat4_zero, hg] at h0
    exact h0
  exact cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN (fnCode2OfPMe hp h Λ j d hd) hF' hR0 hal hlo0
    (show (0 : Int) ≤ 0 from Int.le_refl _) (by show (-D1) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl)
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO0
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (fun _ _ h0 => by cases h0) hB)
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2A hty _)))
    (fun _ _ h => h) (by rw [hra, Int64.ofBitVec_toBitVec]; exact hraP)
    (hTg_of_tgOkB hTg (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h1
      (fnCode2OfPMe hp h Λ j d hd).h16 (fun _ _ h => h) (Ly).lab)

/-- **No state at a landing context's abort node at any placement**
(`ResumeCx2T`'s abort node): a `CxOkH` context's block is `rodata`, addition-free
(`hno`), so its overflow abort node has no state (`abortN2_none_addFree`). -/
theorem habN_ofCxOkHA (hp : Scc.Lower.Accepted2 p = true)
    (hno : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (L' : Lbl) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (hc : CxOkH h hp j R F fs fp ra tp G0 Ab) :
    ∀ c0, G0 c0 → ∀ s c', At (Ly).exe (Ly).endPc R F
      (abortN2 (imms2Me Λ p) (TailAt2 p j) p L' (FC).cx (_root_.Executable.labels (Ly).exe).label fp ra c0) s c' →
      Ab s c' fs := by
  obtain ⟨d', hd', -, -, -, -, -, -, -, -, hn, -⟩ := hc
  cases (Option.some.inj (hd.symm.trans hd'))
  exact fun _ _ s c' hA => (abortN2_none_addFree (hno j d hd hn) hd s c' hA).elim

end Assembled

section Tr

open Spike.Lib.LowerNode (TailOf)

/-- **`TailOf` is transitive**: a point of a point of `e` is a point of `e`. -/
theorem tailOf_trans {t u e : Expr} (h1 : TailOf t u) (h2 : TailOf u e) : TailOf t e := by
  induction h2 with
  | refl => exact h1
  | let_ x op _ ih => exact .let_ x op ih
  | split a x y _ ih => exact .split a x y ih
  | unpack a i x _ ih => exact .unpack a i x ih
  | unpackT a α x _ ih => exact .unpackT a α x ih
  | yes a b no _ ih => exact .yes a b no ih
  | no a b yes _ ih => exact .no a b yes ih

/-- **The walk's points after a buffer's allocation** (plan b1's `Tr`):
the points of the continuation `e` of some `let x = newBuf cn τ; e` at a
walk point (`T`), i.e. the strict tails of an allocation's `let`. -/
def TrNb (T : Expr → Prop) (t : Expr) : Prop :=
  ∃ x cn τ e, T (.let_ x (.newBuf cn τ) e) ∧ TailOf t e

/-- **A point of an allocation's continuation is in `TrNb`** (`landStk_segT`'s `hTr`). -/
theorem TrNb.intro {T : Expr → Prop} {x : String} {cn : At} {τ : Ty} {e t : Expr}
    (hT : T (.let_ x (.newBuf cn τ) e)) (ht : TailOf t e) : TrNb T t := ⟨x, cn, τ, e, hT, ht⟩

/-- **`TrNb` is closed under the walk** (`TailOf`). -/
theorem TrNb.tail {T : Expr → Prop} {t t' : Expr} (h : TrNb T t) (ht : TailOf t' t) : TrNb T t' := by
  obtain ⟨x, cn, τ, e, hT, he⟩ := h
  exact ⟨x, cn, τ, e, hT, tailOf_trans ht he⟩

/-- **`TrNb` stays inside a walk predicate closed under `TailOf`.** -/
theorem TrNb.of_closed {T : Expr → Prop} (hT : ∀ t u, T u → TailOf t u → T t) {t : Expr} (h : TrNb T t) :
    T t := by
  obtain ⟨x, cn, τ, e, hL, he⟩ := h
  exact hT t _ hL (tailOf_trans he (.let_ x _ (.refl e)))

/-- **`TailAt2` is closed under `TailOf`.** -/
theorem tailAt2_tail {p : Prog} {j : Nat} {t u : Expr} (hu : TailAt2 p j u) (ht : TailOf t u) :
    TailAt2 p j t := fun d hd => tailOf_trans ht (hu d hd)

/-- **`TrNb` at the `j`th compiled block's walk is in the walk.** -/
theorem TrNb.tailAt2 {p : Prog} {j : Nat} {t : Expr} (h : TrNb (TailAt2 p j) t) : TailAt2 p j t :=
  h.of_closed fun _ _ hu ht => tailAt2_tail hu ht

/-- A buffer allocation's `let`. -/
def isNewBufLet : Expr → Bool
  | .let_ _ (.newBuf _ _) _ => true
  | _ => false

/-- **The listed check of a single allocation**: at every allocation's
`let` among the points of `e`, no point of its continuation is an
allocation's `let`. -/
def nbOnceL (e : Expr) : Bool :=
  (tailsL e).all fun t => match t with
    | .let_ _ (.newBuf _ _) b => (tailsL b).all fun u => !isNewBufLet u
    | _ => true

/-- **No allocation after an allocation** from `nbOnceL`. -/
theorem noNb_of_nbOnceL {e : Expr} (h : nbOnceL e = true) :
    ∀ x cn τ b, ¬ TrNb (fun t => TailOf t e) (.let_ x (.newBuf cn τ) b) := by
  rintro x cn τ b ⟨y, cn', τ', e', hL, ht⟩
  have h1 := List.all_eq_true.mp h _ (tailOf_mem_tailsL hL)
  have h2 := List.all_eq_true.mp h1 _ (tailOf_mem_tailsL ht)
  simp [isNewBufLet] at h2

end Tr

section Hello1

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- **`rodata`'s body allocates once** in `hello1o` (decided). -/
theorem hello1_rodata_nbOnce : ∀ (j : Nat) (d : Decl), (compiled2 P1A)[j]? = some d → d.name = "rodata" →
    nbOnceL d.body = true := by
  have hc : ∀ d ∈ compiled2 P1A, d.name = "rodata" → nbOnceL d.body = true := by decide
  exact fun j d hd hn => hc d (List.mem_of_getElem? hd) hn

/-- **No allocation in `rodata`'s `Tr`** (plan b1): no point after its
buffer's allocation is an allocation's `let`. -/
theorem hello1_rodata_trNoNb {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x cn τ b, ¬ TrNb (TailAt2 P1A j) (.let_ x (.newBuf cn τ) b) := by
  rintro x cn τ b ⟨y, cn', τ', e', hL, ht⟩
  exact noNb_of_nbOnceL (hello1_rodata_nbOnce j d hd hn) x cn τ b ⟨y, cn', τ', e', hL d hd, ht⟩

/-- **No call in `rodata`'s `Tr`** (plan b1; `rodata` is call-free). -/
theorem hello1_rodata_trNoCall {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x g is a ts e, ¬ TrNb (TailAt2 P1A j) (.let_ x (.call g is a ts) e) := fun x g is a ts e h =>
  hello1_rodata_noCallT hd hn x g is a ts e h.tailAt2

/-- **No allocation at `rodata`'s walk restricted to `Tr`** (`T ∧ Tr`). -/
theorem hello1_rodata_trNoNbT {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d) (hn : d.name = "rodata") :
    ∀ x cn τ e, ¬ (TailAt2 P1A j (.let_ x (.newBuf cn τ) e) ∧ TrNb (TailAt2 P1A j) (.let_ x (.newBuf cn τ) e)) :=
  fun x cn τ e h => hello1_rodata_trNoNb hd hn x cn τ e h.2

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.cxBlk2_ofCxOkHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxBlk2_ofCxOkHA

/-- info: 'Spike.Lib.LowerA64.habN_ofCxOkHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.habN_ofCxOkHA

/-- info: 'Spike.Lib.LowerA64.tailOf_trans' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tailOf_trans

/-- info: 'Spike.Lib.LowerA64.TrNb.tail' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.TrNb.tail

/-- info: 'Spike.Lib.LowerA64.TrNb.of_closed' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.TrNb.of_closed

/-- info: 'Spike.Lib.LowerA64.tailAt2_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tailAt2_tail

/-- info: 'Spike.Lib.LowerA64.TrNb.tailAt2' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.TrNb.tailAt2

/-- info: 'Spike.Lib.LowerA64.noNb_of_nbOnceL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.noNb_of_nbOnceL

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_nbOnce' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_nbOnce

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_trNoNb' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_trNoNb

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_trNoCall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_trNoCall

/-- info: 'Spike.Lib.LowerA64.TrNb.intro' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.TrNb.intro

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_trNoNbT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_rodata_trNoNbT
