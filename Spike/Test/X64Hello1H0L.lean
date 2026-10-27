/-
**The setup bottom keys' `h0` at any current placement** (x86-64):
`scc_rt_main`'s segment from the marshalling block, after the setup frame
returned, inside `W2AtL` / `MSAtL` at a current placement `L0`, `ls` some
allocations past the start's (`exitStk_ofBotH`'s `h0`,
`Spike/Test/X64Hello1BotH.lean`), from `mainS0_segL`
(`Spike/Lib/LowerX64/MainS0L.lean`) at the setup call's post `SPostC` at the
setup result's type: the record's code and phase facts from the placement
check (as `h0In_of_setupFNPVBF`), the start control's facts at `L0`
(`Spike/Lib/LowerX64/Start2C0.lean`), the marshalling block's placement
(`hPlS_ofSPostC` at `L0`), `main`'s call from `mainCallWSF_ofVacHMVL`
(`Spike/Test/X64Hello1HUL.lean`) moved to the frame condition with
`WordsNone`, the exit (`uPostRF_exit`), the bounds from `Bounds2`.

The keys' block is pinned to the setup function (`BotH` carries it,
`BotHR` names it): `main`'s call is only at the setup result's type.

- `BotHR`: `BotH` at a key whose block is the setup function `rodata`;
- `exitStk_ofBotHR`: `exitStk_ofBotH` at a `BotHR` key, `h0` only at the
  setup function;
- `h0L_ofPreUL`: the segment at every top, from `MainPreUL` at the bounds'
  `main` frame and the placement's reach.
-/
import Spike.Test.X64Hello1HUL
import Spike.Test.X64Hello1BotH
import Spike.Lib.LowerX64.MainS0L
import Spike.Lib.LowerX64.H0InAssembledCVBF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64Consumer (K0)
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.AllocReach (IN Reach)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs MainCallWSF rS0 arOf swFSL mainS0)

section Generic

variable {L0 : Lbl} {ls : Lsize} {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance at the current placement `L0`, `ls`. -/
local notation "W2S" J:max => W2AtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0) L0 ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`) at `L0`, `ls`. -/
local notation "MSS" J:max => MSAtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0) L0 ls

set_option hygiene false in
/-- The stack take at the first stack's range. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v` (`BotH`'s). -/
local notation "FW" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

/-- **A setup frame's bottom key at the setup function**: `BotH` at a key
whose block is the compiled `rodata` (`CxOkH`'s block, the one the
landings' contexts at the key carry). `BotH` carries the block itself;
`BotHR` names it at the setup function. -/
abbrev BotHR (k : StkKey) (fs : List TermRun.Frame) : Prop :=
  BotH h k fs

/-- **`exitStk_ofBotH` at a `BotHR` key** (`H1OpenXW.hbot`'s per-key shape at
`Bot := BotHR h`): `scc_rt_main`'s segment `h0` only at the setup function's
block. -/
theorem exitStk_ofBotHR {W : FragS isa} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isa} {Q : FragS isa} {Ab₀ : FragS isa}
    {k : StkKey} {fs : List TermRun.Frame}
    (hZ8 : (SC).Z.toInt % 8 = 0) (hZ : 8 ≤ (SC).Z.toInt)
    (hB : BotHR h k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 p)[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ (J0 : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
      Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
      SetupBot p (Ly).lab ((MSAt h (imms2Me Λ p) p IsNum J0 (ab2 p (Ly).lab) (fun _ => 0)) []) (RS v) (FW v)
        (SC) D1 (Int64.ofInt fS) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs →
      ∀ d, (compiled2 p)[k.j]? = some d → d.name = "rodata" → SegWS W K p lbl ms
        ((At (Ly).exe (Ly).endPc (RS v) (FW v) (mainS0 (Ly).lab (SC)
          (SPostC p lbl d.retTy C0) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)).at []) Q) :
    SegWS W K p lbl ms (ExitStk p (compiled2 p) lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨-, d0, hd0, hn0⟩ := id hB
  refine exitStk_ofBotH h hZ8 hZ hB hW hAb ?_
  intro J0 L D1 fS v D2 lS lM nS fM nM hBd hSB d hd
  obtain rfl : d = d0 := Option.some.inj (hd.symm.trans hd0)
  exact h0 J0 L D1 fS v D2 lS lM nS fM nM hBd hSB d hd hn0

/-- **The setup bottom keys' `h0` at a current placement `L0`, `ls`**
(`mainS0_segL` at the setup call's post `SPostC` at the setup result's type
`ty`, the start control `C0`): at every top `v`, from `main`'s callee entry
`MainPreUL` at the bounds' `main` frame (`hpre`), `main`'s call's construct
facts as `mainCallWSF_ofVacHMVL` takes them, and the placement's reach
(`hR`). -/
theorem h0L_ofPreUL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hfd : p.find? (·.name == "main") = some d)
    (hint : d.retTy = .int) (hm : Scc.Lower.mainRetOk p = true)
    (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1))
    (hnoC : ∀ x g is a ts e, TailAt2 p j (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee (FC).lcx g →
      False)
    (hnoX : ∀ x b i v e, ¬ TailAt2 p j (.let_ x (.xchgAt b i v) e))
    (hnoB : ∀ x cn τ e, ¬ TailAt2 p j (.let_ x (.newBuf cn τ) e))
    {Dt : State → Prop} (J : InvS) (hR : Reach (arOf (lay2 Λ p)) (fun _ => none) (fun _ => 0) L0 ls)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM)
    (hpre : MainPreUL (L0 := L0) (ls := ls) h hp hd Dt J L D2 (TOP)) {Q : FragS isa} (v : BitVec 64) :
    SegWS (W2S J) (KT) p L0 (MSS J)
      ((At (Ly).exe (Ly).endPc (RS v) (FW v)
        (mainS0 (Ly).lab (SC) (SPostC p L0 ty C0) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)).at []) Q := by
  obtain ⟨-, -, -, -, -, -, hnM, -, hnD, -, -, hrowM, hL, hLm, hL8, -, -, hD20, hD28, -, -, hL2, -, -, hZU,
    hOff⟩ := id hB
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2 h hp hs
  have htl := tail_setup_of_accepted2 h hp hs
  obtain ⟨hsw, hrt⟩ := setupIn_sw_eq h htl hc
  have hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (SC) :=
    mainPhS_of_tab (Ly) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h _) hrt fun _ hf => hf
  obtain ⟨chk, entry, Zs, lim, Lg, zl, zf, z1, z2, zs, ps, hproS, -, -⟩ :=
    setupCode_ofPlaceOK hp hty h (imms2Me Λ p) (setupWords2 p)
  have hlS : (SC).setup ∉ Spike.Lib.X64.AllocG.abLabs := by simp only [setupMC]; decide
  have hlF : (SC).fn ∉ Spike.Lib.X64.AllocG.abLabs := by simp only [setupMC]; decide
  have hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (SC).grow) :=
    ⟨".Lscc_rt_main.stk", 0, hstk_of_placeOKAt h hp hs, by decide, by simp [setupMC]⟩
  have hhd : Scc.Cert.Rt.X64.blockAtB (Ly).prog (SC).setup 0 Spike.Lib.X64.Flow.xHead = true := by
    simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hproS
    exact hproS.1.1.1.1.1.2
  have hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (SC).setup) := by
    have h' := posOff_of_blockAtB (lab := (Ly).lab) hhd hlS (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h'
  have hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (SC).fn) := by
    have h' := posOff_of_blockAtB (cells := (Ly).prog) (lab := (Ly).lab) (mainHead_ofPlaceOK hp h _) hlF
      (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h'
  have hPlS := hPlS_ofSPostC (Λ := lay2 Λ p) (lbl := L0) (p := p) (ty := ty)
    (exe := (Ly).exe) (endPc := (Ly).endPc) (F := FS (TOP)) (Ly).lab
    (sc := SC) (g := ⟨TOP - 8#64, TP0, C0⟩) (x0 := (TP0).toBitVec)
    (by simp only [setupMC]; omega) (Spike.Lib.LowerNode.simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkS h hp hty hc) hOff (hme_start2 h hty L0)
  have hU0 := mainCallWSF_ofVacHMVL (L0 := L0) (ls := ls) h hp hty hd hfd hint hm hdT hnl hargW hnoC hnoX hnoB
    hrowM J (by omega) hL hLm hL8 hD20 hD28 hL2 (TOP) hpre
  have hpS := postS_setupTerm (p := p) (lbl := L0) (ty := ty) (c0 := C0) (th02_term_setup hty _)
  have hpl : ∀ s c, Placed (Ly).Λ L0 s c → ((MSS J) []).pl s c := fun s c hP => by
    show (msOfAX _ _ _ _ _ _ _ _ (ab2 p (Ly).lab) _ _ []).pl s c
    cases ab2 p (Ly).lab <;> exact ⟨rfl, hP⟩
  exact mainS0_segL h (imms2Me Λ p) (rd := IsNum) (J := J) (Dt := Dt) (ls0 := fun _ => 0)
    (ab := ab2 p (Ly).lab) (lbl0 := L0) (c0 := C0) (progNoS_zbad_of_accepted2 hp) hL hLm hL8 hsw hc hph
    hgrow hset hfn hD20 hD28 hL2 hR hZU (hC0_start2 h hty L0) (hov_start2 hty _) (fun c rs h' => (hpS c rs h').1)
    ⟨hf0_start2 hty _, hov_start2 hty _, hpl0_start2 h hty L0⟩ (fun c rs h' => (hpS c rs h').2)
    (fun _ _ _ h' => h'.2) hPlS
    (fun F' a b hFF g hra htp =>
      (hU0 F' a b (fun m hm => ⟨⟨(hFF m hm).1.1.2, (hFF m hm).1.2⟩, (hFF m hm).2⟩) g hra htp).mono_pre
        fun _ _ _ ⟨⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩, hfs⟩ =>
          ⟨⟨he, hn, hdc, hpc, σ, hA, hF, hJ.1,
            ⟨hJ.2.rt, hJ.2.mp, fun m hm => by rw [htp]; exact hm.1.1.2, hJ.2.room⟩⟩, hfs⟩)
    (fun s c fs w hP hA => uPostRF_exit hpl _ _ s c fs w hP.1 hA) v

end Generic

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.exitStk_ofBotHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.exitStk_ofBotHR

/-- info: 'Spike.Lib.LowerX64.h0L_ofPreUL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h0L_ofPreUL
