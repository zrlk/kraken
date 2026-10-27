/-
**A lane store's premise inside `W2`** (AArch64): `LaneC`
(`Spike/Lib/LowerA64/Body2.lean`) from `laneC_of`
(`Spike/Lib/LowerA64/LaneC2.lean`) with its `LaneW` from `laneW_w2`
(`Spike/Lib/LowerA64/LaneW2.lean`), at the code predicate `CdC` and the
nodes' states in `W2`; the twin of `Spike/Lib/LowerX64/LaneCW2.lean`.

`laneC_of` gives `laneW_w2` the site's facts (`LaneH`): the site control at
the `let`, placed in the slot file (with `d`'s slot updated) from the walk's
facts at the `let`, the base's value not moved by `d`'s slot and the
element's word a word of a placed label. The word is a heap word (`HeapW`)
by `hHW` (`heapW_of`, `Spike/Lib/LowerA64/HeapW.lean`, at a placement).

- `laneC_w2`: `LaneC` at `CdC` with the exchange's nodes inside `W2`.
- `laneC_w2'`: `LaneC` at `CdCL` (`Spike/Lib/LowerA64/UserAbC.lean`), the
  code predicate's pcs off the write abort's from its labels
  (`posOff_of_subCdL`, `notAbPc_of_posOff`) but the pc right after a lane
  store's `strOff` (`hend`); the lane's controls' facts (`main`'s `ret`
  excluded, `FrOk2`) from the walk's `FrOk2` at the ghost (`hG0F`) along the
  node's local run.
- `laneC_w2G`: the same at a code predicate inside `CdCL` with `hend`;
  `laneC_w2E`: at `CdCLE` (`Spike/Lib/LowerA64/CdCLE.lean`), `hend` from
  the code predicate.
-/
import Spike.Lib.LowerA64.LaneW2
import Spike.Lib.LowerA64.CdCLE
import Spike.Lib.LowerA64.LaneC2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (FStable)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab abPcs)
open Spike.Lib.LowerNode (FrOk2 ZBad LocBaseRegAt ImmIn LblRoom IsNum LblRange ofEnv2)
open Spike.Lib.Form (lookupS)
open Scc.Emit.A64 (FnCtx strOff xs directives)
open Scc.Lower.InvA64 (FrameOk)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize}

/-- **A lane store's premise inside `W2`** (`LaneC` at the code predicate
`CdC`, the immediates `Λ.imms`): `laneC_of` with `LaneW` by `laneW_w2`. The
exchange's nodes' states in `W2` lie in `W` (`hW₀`); the code predicate's
pcs off the write abort's (`hnab`); a placed label's words heap words
(`hHW`); at the lane's node the controls exclude `main`'s `ret` and `ZBad`
(`hJn`); at the lane's `let` no `ZBad` (`hnz`; the walk's facts there, free
variables placed, register bases, immediates, are `LaneC`'s). -/
theorem laneC_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hnab : ∀ pc' blk, CdC prog okPc ph lab ra0 pc' blk → ∀ k ≤ blk.length,
      pc' + Int64.ofNat (4 * k) ∉ abPcs lab)
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2} (lcx : Scc.Lower.Ctx) {fp ra : BitVec 64} (tp : UInt64)
    {Bl : Int64 → Label → Nat → Prop} {W : FragS isaLSE2}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w') (hroom : LblRoom lbl) (hrg : LblRange Λ lbl lsize)
    (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem)
    (hHW : ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
      HeapW Λ own ar lbl lsize F A)
    {G0 : Ctl → Prop} {T : Expr → Prop} {Ab' : FragS isaLSE2}
    (hJn : ∀ c0 pc t env lits cs bufs σ c, G0 c0 → T t →
      laneJ p lbl lsize Λ.imms cx fp ra tp c0 pc t env lits cs bufs σ c →
      (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs)
    (hnz : ∀ (c0 : Ctl) (t : Expr), G0 c0 → T t → NoS ZBad t) :
    LaneC p lbl lsize lcx cx (CdC prog okPc ph lab ra0) Bl exe endPc R F W K ms fp ra tp fs G0 Λ.imms T Ab' := by
  have hCd : ∀ pc blk, CdC prog okPc ph lab ra0 pc blk → CdOf exe endPc pc blk := by
    rw [← hI.labOk]; exact cdOf_cdC hI.lays hI.endOk
  exact laneC_of hf h1 h16 hFS hR hal hlo hhi hCd hW₀ hrd hroom hrg hwn lcx tp
    fun c0 pc t env lits cs bufs _ _ _ hG0 hT htot hlb himm hH =>
      laneW_w2 hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hFS hp hnab hrs hfp (ms fs)
        (fun _ _ h => slotRepAt_bodyN2 _ _ h.1) (hJn c0 pc t env lits cs bufs · · hG0 hT)
        (fun σ c c1 hJ hP => by
          obtain ⟨hterm, hnr, hsr, -⟩ := hH σ c c1 hJ hP
          obtain ⟨hs1, hs2⟩ := hsr htot hlb himm
          exact ⟨hs1, hs2, fun _ => hnr, ⟨by rw [hterm]; exact hnz c0 t hG0 hT,
            (hJn c0 pc t env lits cs bufs σ c hG0 hT hJ).2.2⟩⟩)
        (fun σ c c1 hJ hP => by
          obtain ⟨-, -, -, hbase, hword⟩ := hH σ c c1 hJ hP
          refine ⟨hbase, fun vb hvb => ?_⟩
          obtain ⟨l, b, k, hlb, hk, hA⟩ := hword vb hvb
          exact hHW l b k _ hlb hk hA)

/--
info: 'Spike.Lib.LowerA64.laneC_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneC_w2

/-- **A lane store's premise inside `W2` at a code predicate inside `CdCL`**
(`LaneC` at `Cd`, the immediates `Λ.imms`): `laneC_of` with `LaneW` by
`laneW_w2E`. The code predicate's pcs are off the write abort's by their
labels (`hcl`, `hpr`, `hab`), the pc right after a lane store's chunk by
`hend`; the lane's controls exclude `main`'s `ret` (their local run reaches
the `let`) and `ZBad` (`FrOk2` at the ghost, `hG0F`, kept by the local run).
The exchange's nodes' states in `W2` lie in `W` (`hW₀`); a placed label's
words heap words (`hHW`); at the lane's `let` the walk's facts (free
variables placed, register bases, immediates, from `LaneC`). -/
theorem laneC_w2G {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} (hcl : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hend : ∀ pc' blk (disp : Int),
      Cd pc' (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)) →
      PosOff prog lab (pc' + Int64.ofNat (4 * (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)).length)))
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2} (lcx : Scc.Lower.Ctx) {fp ra : BitVec 64} (tp : UInt64)
    {Bl : Int64 → Label → Nat → Prop} {W : FragS isaLSE2}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w') (hroom : LblRoom lbl) (hrg : LblRange Λ lbl lsize)
    (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem)
    (hHW : ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
      HeapW Λ own ar lbl lsize F A)
    {G0 : Ctl → Prop} {T : Expr → Prop} {Ab' : FragS isaLSE2}
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) :
    LaneC p lbl lsize lcx cx Cd Bl exe endPc R F W K ms fp ra tp fs G0 Λ.imms T Ab' := by
  have hna : ∀ t, PosOff prog lab t → t ∉ abPcs lab := fun t h => by
    have := notAbPc_of_posOff hI.lays hpr hab (t := t) (by rw [hI.labOk]; exact h)
    rwa [hI.labOk] at this
  have hCd : ∀ pc blk, CdC prog okPc ph lab ra0 pc blk → CdOf exe endPc pc blk := by
    rw [← hI.labOk]; exact cdOf_cdC hI.lays hI.endOk
  refine laneC_of hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => hCd _ _ (hcl _ _ h).toCdC) hW₀ hrd hroom hrg hwn
    lcx tp
    fun c0 pc t env lits cs bufs _ _ _ hG0 hT htot hlb himm hH => ?_
  have hF : ∀ c, LocalRun p c0 c → FrOk2 c fs := fun c h =>
    Spike.Lib.LowerNode.FrOk2.run hp (Spike.Lib.FrameRun.ofLocal h fs) (hG0F c0 hG0)
  refine laneW_w2E hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hFS hp (fun _ _ h => (hcl _ _ h).toCdC)
    (fun _ _ h _ hk => hna _ (posOff_of_subCdL (SubCd.whole (hcl _ _ h)) hk))
    (fun _ _ _ h => hna _ (hend _ _ _ h)) hrs hfp (ms fs)
    (fun _ _ h => slotRepAt_bodyN2 _ _ h.1) (fun σ c hJ => ?_) (fun σ c c1 hJ hP => ?_)
    (fun σ c c1 hJ hP => ?_)
  · obtain ⟨L, sm, B, c1, hr, hj, hn, hb, hm, hS⟩ := hJ.1.1
    have hP : laneP p lbl lsize cx t env lits cs bufs σ c c1 := ⟨hr, L, sm, B, hj, hn, hb, hm, hS⟩
    exact ⟨fun _ => noRet_of_run hr (hH σ c c1 hJ hP).2.1, hF c hJ.1.2.2.1⟩
  · obtain ⟨-, hnr, hsr, -⟩ := hH σ c c1 hJ hP
    obtain ⟨hs1, hs2⟩ := hsr htot hlb himm
    exact ⟨hs1, hs2, fun _ => hnr, hF c1 (hJ.1.2.2.1.trans hP.1)⟩
  · obtain ⟨-, -, -, hbase, hword⟩ := hH σ c c1 hJ hP
    refine ⟨hbase, fun vb hvb => ?_⟩
    obtain ⟨l, b, k, hlb, hk, hA⟩ := hword vb hvb
    exact hHW l b k _ hlb hk hA


/-- **A lane store's premise inside `W2` off the write abort's labels**
(`LaneC` at `CdCL`, the immediates `Λ.imms`): `laneC_of` with `LaneW` by
`laneW_w2E`. The code predicate's pcs are off the write abort's by their
labels (`hpr`, `hab`), the pc right after a lane store's chunk by `hend`;
the lane's controls exclude `main`'s `ret` (their local run reaches the
`let`) and `ZBad` (`FrOk2` at the ghost, `hG0F`, kept by the local run). The
exchange's nodes' states in `W2` lie in `W` (`hW₀`); a placed label's words
heap words (`hHW`); at the lane's `let` the walk's facts (free variables
placed, register bases, immediates, from `LaneC`). -/
theorem laneC_w2' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hend : ∀ pc' blk (disp : Int),
      CdCL prog okPc ph lab ra0 pc' (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)) →
      PosOff prog lab (pc' + Int64.ofNat (4 * (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)).length)))
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2} (lcx : Scc.Lower.Ctx) {fp ra : BitVec 64} (tp : UInt64)
    {Bl : Int64 → Label → Nat → Prop} {W : FragS isaLSE2}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w') (hroom : LblRoom lbl) (hrg : LblRange Λ lbl lsize)
    (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem)
    (hHW : ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
      HeapW Λ own ar lbl lsize F A)
    {G0 : Ctl → Prop} {T : Expr → Prop} {Ab' : FragS isaLSE2}
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) :
    LaneC p lbl lsize lcx cx (CdCL prog okPc ph lab ra0) Bl exe endPc R F W K ms fp ra tp fs G0 Λ.imms T Ab' :=
  laneC_w2G hI hpr hab hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hFS hp (fun _ _ h => h) hend hrs hfp lcx tp
    hW₀ hrd hroom hrg hwn hHW hG0F

/-- **A lane store's premise inside `W2` at `CdCLE`** (`LaneC` at `CdCLE`,
`Spike/Lib/LowerA64/CdCLE.lean`, the immediates `Λ.imms`): `laneC_w2G`, the
pc right after a lane store's chunk off the write abort by `CdCLE`
(`posOff_end_lane`); the lane's controls exclude `main`'s `ret` (their local
run reaches the `let`) and `ZBad` (`FrOk2` at the ghost, `hG0F`, kept by the
local run). The exchange's nodes' states in `W2` lie in `W` (`hW₀`); a
placed label's words heap words (`hHW`); at the lane's `let` the walk's
facts (free variables placed, register bases, immediates, from `LaneC`). -/
theorem laneC_w2E {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra0 : Int64}
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    {fs : List TermRun.Frame} (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    {ms : List TermRun.Frame → MemSide isaLSE2} (lcx : Scc.Lower.Ctx) {fp ra : BitVec 64} (tp : UInt64)
    {Bl : Int64 → Label → Nat → Prop} {W : FragS isaLSE2}
    (hW₀ : ∀ s c, W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w') (hroom : LblRoom lbl) (hrg : LblRange Λ lbl lsize)
    (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem)
    (hHW : ∀ l b k (A : BitVec 64), lbl l = some b → k < lsize l → A.toNat = b + 8 * k →
      HeapW Λ own ar lbl lsize F A)
    {G0 : Ctl → Prop} {T : Expr → Prop} {Ab' : FragS isaLSE2}
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) :
    LaneC p lbl lsize lcx cx (CdCLE prog okPc ph lab ra0) Bl exe endPc R F W K ms fp ra tp fs G0 Λ.imms T Ab' :=
  laneC_w2G hI hpr hab hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hFS hp (fun _ _ h => h.toCdCL)
    (fun _ _ _ h => posOff_end_lane h) hrs hfp lcx tp hW₀ hrd hroom hrg hwn hHW hG0F

/--
info: 'Spike.Lib.LowerA64.laneC_w2'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneC_w2'

/--
info: 'Spike.Lib.LowerA64.laneC_w2E' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneC_w2E

end Spike.Lib.LowerA64
