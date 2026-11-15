/-
**`main`'s call from `main`'s segment at every reachable placement**
(x86-64; the twin of `Spike/Lib/LowerA64/G1MainCallL.lean`): `MainLUStmt`
(`Spike/Lib/LowerX64/G1H1Stmt.lean`, the premise of the landings
`h1InW_ofSetupL`) from `MainSeg2L` (`Spike/Lib/LowerX64/G1MainStmtL.lean`),
as `mainCallWSF_ofMainSeg2F` (`Spike/Lib/LowerX64/G1MainCall.lean`) at a
reachable placement `L0`, `ls`: the context facts `MainCx2L` from
`mainCx2_setup` (`MainCx2.toLAt`), the prologue's edge at the setup call's
entry invariant `uNM` at the memory side `MSAtL … L0 ls`.

- `mainCallWSF_ofMainSeg2FL`: `main`'s call `MainCallWSF` at `W2AtL`,
  `MSAtL` at `L0`, `ls`, from `MainSeg2L`;
- `mainLU_ofMainSeg2L`: `MainLUStmt` from `MainSeg2L` at every invariant;
- `MainSeg2LStmt`, `mainSeg2Stmt_ofL`: G1.4's statement at every
  reachable placement, and `MainSeg2Stmt` from it;
- `h1SetupStmt_ofMainSeg2L`: the landings `H1SetupStmt` from
  `MainSeg2LStmt` (`h1InW_ofSetupL` at `mainLU_ofMainSeg2L`, the instance's
  `mainRetOk` and need check in hand).
-/
import Spike.Lib.LowerX64.G1MainStmtL
import Spike.Lib.LowerX64.G1Closed2H

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
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.AllocReach (Reach)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs MainCallWSF rS0 swFSL arOf)

section Generic

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
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
/-- `W2AtL` at `Closed2At`'s instance, placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`), placement
`L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The stack take at the first stack's range. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`HUBVF`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`main`'s call at `WordsNone ∧ swFSL` from `main`'s segment at a
reachable placement** `L0`, `ls` (`mainCallWSF_ofMainSeg2F` at `L0`, `ls`):
off the first stack's top no state is in the frame condition; at it,
`main`'s code facts as there, the context facts `MainCx2L` by
`mainCx2_setup` at `L0`, `ls` (`MainCx2.toLAt`), and from `MainSeg2L` at
`L0`, `ls` the constructs' segments and `CalleePre2R` at the setup call's
entry invariant `uNM` at the memory side `MSAtL … L0 ls`, its prologue edge
by `proEdge2_ofUNM`. -/
theorem mainCallWSF_ofMainSeg2FL {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOk pcfg = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS) (HM : MainSeg2L h hp Dt J)
    {L0 : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L0 ls) (v : BitVec 64) :
    MainCallWSF (W2L J L0 ls) (KT) p L0 (MSL J L0 ls) (Ly).exe (Ly).endPc (RS v) (FS v)
      (SC).fn (SC).Z D2 (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p L0 ty C0) (SC).sw (TP0).toBitVec)
      (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
      ((Ly).lab (SC).sp1).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.2.1.1
  subst hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hrowM, -⟩ := id hB
  obtain ⟨d, hfd⟩ : ∃ d, p.find? (·.name == "main") = some d := by
    simp only [Scc.Lower.setupOf] at hty
    split at hty
    · exact ⟨_, ‹_›⟩
    · cases hty
  have hdT : d.argTy = .prod ty (.ptr .pub .void) := by
    simp only [Scc.Lower.setupOf, hfd] at hty
    split at hty
    · next s hs => cases hty; exact hs
    · cases hty
  obtain ⟨j, hd, hdn⟩ := Spike.Lib.LowerNode.main_compiled2 hfd
  have hok : Scc.Lower.heldRetOk d.body = true := by simpa [Scc.Lower.mainRetOk, hfd] using hm
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2 h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) hc).1
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hw := valWords_of_rtCodeOkS h hp hty hc
  have hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1) := by
    rw [hdT]; exact valWords_setupArg hw
  obtain ⟨w, hLw, hna, hmem, hfr⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).fr.size = fM := by
    rw [hfr]; exact hrowM _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])
  refine mainCallWSF_ofPlaceOKHMVCR (Λv := lay2 Λ p) (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 (mainRetInt_of_accepted2 hp hfd)
    hok (hlitP_of_mainRetOk hm hfd) hc
    (by rw [(FC).hfn, hdn]; rfl) (posOff_proL_main h hp hd) (simpleTy_of_accepted2 hp ty hty) hw
    (Nat.le_of_lt_succ hsw) (hme_start2 h hty L0)
    (hE_setupTerm (th02_term_setup hty _)) ?_ ?_ (fun m hm => hm.1.2.1.2) hsub
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub) (progNoS_zbad_of_accepted2 hp) ?_
  · rintro c regs ⟨_, ⟨cE, fr, cr, a, t, ws, hct, -, -, -, hc'⟩, -⟩
    obtain ⟨x, f, a', e, d', t', ws', ht, -, -, -, rfl⟩ := hct
    have ht' : (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term =
        .let_ x (.call f [] a' []) e := ht
    rw [th02_term_setup hty, setupTerm_eq] at ht'
    cases ht'
    subst hc'
    exact ⟨⟨fun h => h, trivial⟩, fun _ h => nomatch h⟩
  · rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hok' hst hFF g hra htp _ cP hcP
    have hC := (mainCx2_setup h hp hty hcfg hB hok' hst hFF hra htp).toLAt h L0 ls
    obtain ⟨Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩ := HM L0 ls hre j d hd hdn _ F' g cP hC hcP
    -- the prologue's edge at the setup call's entry invariant `uNM`
    have he := proEdge2_ofUNM (lsize := ls) (lbl := L0)
      (J := (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (Ly).exe).label ((MSL J L0 ls) []) (FS (TOP)) (SC).fn
        (Int64.ofInt (fM : Int))
        (fun c rs => SetupArgs (SPostC p L0 ty C0) (SC).sw (TP0).toBitVec c rs ∧ c = cP) g).J)
      (FC) hdT hfd
      (hna.trans (Option.some.inj (hLw.1.symm.trans hargW))) hsw (hloc_of_accepted2 hp ty hty) (c0 := C0)
      (th02_term_setup hty _)
      (by rw [th02_setup hty]; rfl) (Spike.Lib.LowerNode.isNum_meNum (UInt64.toNat_lt_size _))
      (x0 := (TP0).toBitVec) (by rw [tp0_start2 h]; exact valRep_meW2_of_placeOKAt h _)
      (g := g) (lab := (_root_.Executable.labels (Ly).exe).label) (ms0 := (MSL J L0 ls) [])
      (ms1 := (MSL J L0 ls) [])
      (F := FS (TOP)) (F' := F') (fn := (SC).fn) (ZU := Int64.ofInt (fM : Int)) (by rw [hframe])
      (fun _ _ h => h) (fun m hm => (hFF m hm).1) (cP := cP) (fun _ _ h => h)
    have hpre := hab _ he
    rw [htp] at hpre hC2 hL hN hP hCH hPH
    exact ⟨GM cP, Ab, cP, hpre, hC2, hL, hN, hP, hCH, hPH, hA⟩

/-- **`MainLUStmt` from `main`'s segment at every reachable placement**
(`mainCallWSF_ofMainSeg2FL` at every invariant, placement and choice of
the bounds, the first stack's top, the write tail `fun _ => True`). -/
theorem mainLU_ofMainSeg2L (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOk pcfg = true)
    (HM : ∀ J, MainSeg2L h hp (fun _ => True) J) : MainLUStmt h ty :=
  fun J _ _ hre _ _ _ _ _ _ _ _ _ hB => mainCallWSF_ofMainSeg2FL h hp hty hm hcfg hB J (HM J) hre _

end Generic

/-- **`main`'s segment at every reachable placement for every `Accepted2`
program** (`MainSeg2Stmt` at `MainSeg2L`): at every output passing the
placement check (its need table's rows checked) whose user code's direct
branches pass `tgOkB`, at every invariant `J`, `MainSeg2L` with the
trivial write tail. -/
def MainSeg2LStmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout) (hp : Scc.Lower.Accepted2 p = true),
    CfgNeedOk pcfg = true →
    ∀ (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true),
    tgOkB (Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true →
    ∀ J : InvS, MainSeg2L h hp (fun _ => True) J

/-- **`MainSeg2Stmt` from `MainSeg2LStmt`** (`mainSeg2_ofL` at each
instance). -/
theorem mainSeg2Stmt_ofL (HM : MainSeg2LStmt) : MainSeg2Stmt :=
  fun cfg pcfg p sizes labelOffs Λ hp hcfg h htg J =>
    mainSeg2_ofL h (HM cfg pcfg p sizes labelOffs Λ hp hcfg h htg J)

/-- **The landings with a setup block from `main`'s segment at every
reachable placement** (`h1InW_ofSetupL` at `mainLU_ofMainSeg2L`, the
instance's `mainRetOk`, need check and branch-target check in hand). -/
theorem h1SetupStmt_ofMainSeg2L (HM : MainSeg2LStmt) : H1SetupStmt :=
  fun cfg pcfg p sizes labelOffs Λ hp _ hty hm hcfg hobj E _ h htg =>
    h1InW_ofSetupL h hp hty hcfg hobj htg
      (mainLU_ofMainSeg2L h hp hty hm hcfg (HM cfg pcfg p sizes labelOffs Λ hp hcfg h htg)) E

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.mainCallWSF_ofMainSeg2FL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.mainCallWSF_ofMainSeg2FL

/-- info: 'Spike.Lib.LowerX64.mainLU_ofMainSeg2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainLU_ofMainSeg2L

/-- info: 'Spike.Lib.LowerX64.mainSeg2Stmt_ofL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainSeg2Stmt_ofL

/-- info: 'Spike.Lib.LowerX64.h1SetupStmt_ofMainSeg2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.h1SetupStmt_ofMainSeg2L
