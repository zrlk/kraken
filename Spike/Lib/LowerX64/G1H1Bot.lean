/-
**The landings' bottom frames' exits for any `Accepted2` program with a
setup block** (x86-64; the twin of `Spike/Lib/LowerA64/G1H1Bot.lean`):
`H1LandAW.hbot`'s shape at the bottom keys `BotH`
(`Spike/Test/X64Hello1CxOkH.lean`) at a reachable placement, from `main`'s
call at the reachable placements (`MainLUStmt`,
`Spike/Lib/LowerX64/G1H1Stmt.lean`) and the aborts' segment.

- `h0L_ofMainLU`: `scc_rt_main`'s segment after the setup frame returned
  (`mainS0_segL` at the setup call's post `SPostC`, as `h0L_ofPreUL`'s),
  `main`'s call from `MainLUStmt`;
- `w2_ofBotHL`: a bottom key's exits inside `W2` at a reachable placement:
  the pop to `mainS0` (`setupBot_popM`, `hPS_framed`), `W2` there by
  `h0L_ofMainLU`'s segment, back by `w2_ofPopped` (the popped control by
  `postS_setupTerm`, the exit's `ret` placed by `RetJS.placed`, the setup
  frame by `framesPlaced_setup`); the generic form of `hello1_hWBot`;
- `exitStk_ofBotHL`: the bottom key's exits as a segment ending in `Q`
  (`exitStk_ofBotHR`), given the aborts `Ab₀` ending in `Q`.
-/
import Spike.Lib.LowerX64.G1H1Stmt
import Spike.Test.X64Hello1HWBot
import Spike.Test.X64Hello1HS
import Spike.Lib.LowerX64.PlacedRetJS

namespace Spike.Lib.LowerX64

set_option autoImplicit false

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

section Bot

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

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

/-- **`scc_rt_main`'s segment after the setup frame returned, at a
reachable placement `L0`, `ls`** (`h0L_ofPreUL` with `main`'s call from
`MainLUStmt`): `mainS0_segL` at the setup call's post `SPostC` at the setup
result's type `ty`, at every top `v`, at the bounds `Bounds2`. -/
theorem h0L_ofMainLU (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (HM : MainLUStmt h ty) (J : InvS) {L0 : Lbl} {ls : Lsize}
    (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM) {Q : FragS isa} (v : BitVec 64) :
    SegWS (W2T J L0 ls) (KT) p L0 (MSR J L0 ls)
      ((At (Ly).exe (Ly).endPc (RS v) (FW v)
        (mainS0 (Ly).lab (SC) (SPostC p L0 ty C0) ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec)).at []) Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL, hLm, hL8, -, -, hD20, hD28, -, -, hL2, -, -, hZU,
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
  have hpS := postS_setupTerm (p := p) (lbl := L0) (ty := ty) (c0 := C0) (th02_term_setup hty _)
  have hpl : ∀ s c, Placed (Ly).Λ L0 s c → ((MSR J L0 ls) []).pl s c := fun s c hP => by
    show (msOfAX _ _ _ _ _ _ _ _ (ab2 p (Ly).lab) _ _ []).pl s c
    cases ab2 p (Ly).lab <;> exact ⟨rfl, hP⟩
  exact mainS0_segL h (imms2Me Λ p) (rd := IsNum) (J := J) (Dt := fun _ => True) (ls0 := fun _ => 0)
    (ab := ab2 p (Ly).lab) (lbl0 := L0) (c0 := C0) (progNoS_zbad_of_accepted2 hp) hL hLm hL8 hsw hc hph
    hgrow hset hfn hD20 hD28 hL2 hR hZU (hC0_start2 h hty L0) (hov_start2 hty _) (fun c rs h' => (hpS c rs h').1)
    ⟨hf0_start2 hty _, hov_start2 hty _, hpl0_start2 h hty L0⟩ (fun c rs h' => (hpS c rs h').2)
    (fun _ _ _ h' => h'.2) hPlS (HM J L0 ls hR L D1 D2 lS lM fS nS fM nM hB)
    (fun s c fs w hP hA => uPostRF_exit hpl _ _ s c fs w hP.1 hA) v

/-- **A bottom key's exits inside `W2` at a reachable placement** (the
generic `hello1_hWBot`): at a `BotH` key's return exit at its block's
result type, the key's frames are the setup call's one frame and the
source pops it to `mainS0` (`setupBot_popM`); `W2` there by
`h0L_ofMainLU`'s invariant at its pre; back by `w2_ofPopped`, the `ret`
placed by `RetJS.placed` above the placed setup frame. -/
theorem w2_ofBotHL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (HM : MainLUStmt h ty) (J : InvS) {L0 : Lbl} {ls : Lsize} (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {k : StkKey} {fs : List TermRun.Frame} (hB : BotH h k fs) :
    ∀ c0 ty', k.G0 c0 → (∃ d, (compiled2 p)[k.j]? = some d ∧ d.retTy = ty') → ∀ s c,
      ExitC2SL p L0 (Ly).exe (Ly).endPc (rbR k.R) k.F k.fp k.ra k.tp c0 fs ty' (fun _ _ _ => False) s c fs →
        (W2T J L0 ls) s c fs := by
  intro c0 ty' _ hd s c hE
  rcases hE with ⟨-, c0', hr, hA⟩ | hE
  case inr => exact hE.elim
  obtain ⟨⟨J0, L', D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, d', hd', hn⟩ := hB
  obtain ⟨d, hd, rfl⟩ := hd
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hp hty hd hn] at hA
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) (rtCodeOkS_setupWords2 h hp hs)).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hD10, -, -, -, -, hL1, -⟩ := id hBd
  -- the pop to `mainS0` at the setup call's continuation
  obtain ⟨cE, fr, c'', rfl, hCT, -, hAt⟩ := setupBot_popM (PostS := SPostC p L0 ty C0) hD10
    (by rw [hZ]; omega) (by simp only [Region.callee]; omega) (by simp only [Region.callee]; omega) hSB
    (hPS_framed (ty := ty)) ⟨c0', hr, hA⟩
  -- `W2` at the popped pair: `h0`'s invariant at its pre
  obtain ⟨inv, hpre, hinvW, -⟩ := h0L_ofMainLU h hp hty HM J hR hBd (Q := fun _ _ _ => False) v
  have hW2 := hinvW s c'' [] (hpre s c'' [] ⟨hAt, rfl⟩)
  -- the continuation's facts
  obtain ⟨-, -, -, -, σ', -, -, ⟨hPost, -⟩, -⟩ := hAt
  have hc0 := th02_term_setup hty (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))
  obtain ⟨hCF, hMC⟩ := postS_setupTerm hc0 c'' _ hPost
  have hNN := postS_setupTerm_noNew hc0 c'' _ hPost
  obtain ⟨cE', fr', cr, a', t', ws, hct', -, -, -, rfl⟩ := hPost
  obtain rfl := (CallTo.unique hCT hct').2
  -- the `ret`'s exit by placements: the `ret` itself, the setup frame below
  obtain ⟨-, -, -, -, σ, hAbs, -, ⟨⟨hJ, -⟩, -⟩, -⟩ := hA
  obtain ⟨a, -, -, -, -, -, ht, -⟩ := id hJ
  obtain ⟨B, hFP⟩ := framesPlaced_setup h hp hty hCT s
  exact w2_ofPopped (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hW2 hCF.noAlloc
    hNN hMC.2
    (List.cons_ne_nil _ _) (frOk2_retFr ht hMC.1.1)
    (PlacedSE.of_placedS (PlacedS.ofFrames (RetJS.placed hJ _ hAbs.regs)
      (FramesPlaced.mono_lbl (fun _ _ h0 => by cases h0) hFP.toFramesPlaced)))

/-- **A bottom key's exits as a segment at a reachable placement**
(`exitStk_ofBotHR` with `hW` by `w2_ofBotHL` and `h0` by `h0L_ofMainLU`),
given the aborts `Ab₀` ending in `Q` (`hAb`). -/
theorem exitStk_ofBotHL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (HM : MainLUStmt h ty) (J : InvS) {L0 : Lbl} {ls : Lsize} (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {Q Ab₀ : FragS isa} (hAb : SegWS (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) Ab₀ Q)
    {k : StkKey} {fs : List TermRun.Frame} (hB : BotH h k fs) :
    SegWS (W2T J L0 ls) (KT) p L0 (MSR J L0 ls) (ExitStk p (compiled2 p) L0 (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) (rtCodeOkS_setupWords2 h hp hs)).1
  have hZ := setupMC_Z _ hsw
  refine exitStk_ofBotHR h (by rw [hZ]; omega) (by rw [hZ]; omega) hB (w2_ofBotHL h hp hty HM J hR hB) hAb ?_
  intro J0 L D1 fS v D2 lS lM nS fM nM hBd _ d hd hn
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hp hty hd hn]
  exact h0L_ofMainLU h hp hty HM J hR hBd v

end Bot

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h0L_ofMainLU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h0L_ofMainLU

/-- info: 'Spike.Lib.LowerX64.w2_ofBotHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.w2_ofBotHL

/-- info: 'Spike.Lib.LowerX64.exitStk_ofBotHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.exitStk_ofBotHL
