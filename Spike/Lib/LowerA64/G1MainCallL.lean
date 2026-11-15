/-
**`main`'s call at every reachable placement from `main`'s segment there,
for any `Accepted2` program with a setup block** (AArch64): `MainLUStmt`
(`Spike/Lib/LowerA64/G1H1Stmt.lean`, the landings' `main` call) from
`MainSeg2L` (`Spike/Lib/LowerA64/G1MainStmtL.lean`), as
`mainCallWSF_ofMainSeg2F` (`Spike/Lib/LowerA64/G1MainCall.lean`) at a
reachable placement `L0`, `ls`: `mainCallWSF_ofPlaceOKHMVCR` is generic in
the placement, the start's `me` word valued at any placement
(`hme_start2A`), and the callee frame's context facts `MainCx2` are
`MainCx2L` at any placement (the limit word's row read the same in the
memory sides at every placement).

- `MainCx2.toLAt`: `MainCx2` gives `MainCx2L` at any placement;
- `mainCallWSF_ofMainSeg2FL`: `main`'s call `MainCallWSF` at the switch
  region's frame condition with `WordsNone`, inside `W2AtL`, `MSAtL` at a
  reachable placement, from `MainSeg2L`;
- `mainLU_ofMainSeg2L`: `MainLUStmt` from `MainSeg2L` at every invariant.
-/
import Spike.Lib.LowerA64.G1MainStmtL
import Spike.Lib.LowerA64.G1MainCall
import Spike.Lib.LowerA64.G1H1Stmt

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.AllocReach (IN Reach)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs MainCallWSF rS0 arOf swFSL rtF)

section GenericL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance, placement `L0`, `ls`. -/
local notation "W2L" J:max L0:max ls:max =>
  W2AtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0) L0 ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`), placement `L0`, `ls`. -/
local notation "MSL" J:max L0:max ls:max =>
  MSAtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0) L0 ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`. -/
local notation "FWS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ (FS v) m

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`MainCx2` is `MainCx2L` at any placement**: the limit row's word is
read the same in the memory sides at every placement (`MSAt`, `MSAtL`
agree on the static memory `G`). -/
theorem MainCx2.toLAt {L0 : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat} {R : Region}
    {F : MachineData → Prop} {ra : BitVec 64} {tp : UInt64} (H : MainCx2 h R F ra tp) :
    MainCx2L h L0 ls R F ra tp :=
  { H with
    lim := fun m hm J => by
      have hl := H.lim m hm J
      revert hl
      dsimp only [MSAt, MSAtL]; generalize ab2 p _ = ab; cases ab <;> exact id }

/-- **`main`'s call at `WordsNone ∧ swFSL` from `main`'s segment at a
reachable placement** (`mainCallWSF_ofMainSeg2F` at `L0`, `ls`): off the
first stack's top no state is in the frame condition; at it, `main`'s code
facts as there, the start's `me` word at `L0` (`hme_start2A`), the callee
frame's context facts by `mainCx2_setup` and `MainCx2.toLAt`, and
`CalleePre2R` and the constructs' segments from `MainSeg2L` at `L0`, `ls`
(`hR`). -/
theorem mainCallWSF_ofMainSeg2FL {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS) (HM : MainSeg2L h hp Dt J)
    {L0 : Lbl} {ls : Lsize} (hR : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L0 ls) (v : BitVec 64) :
    MainCallWSF (W2L J L0 ls) (KT) p L0 (MSL J L0 ls) (Ly).exe (Ly).endPc (swR v (-L) 0) (FWS v)
      (SC).fn (SC).Z D2 (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p L0 ty C0) (SC).sw (X0))
      (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
      ((Ly).lab (SC).sp1).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.2.1.1
  subst hv
  obtain ⟨-, -, -, -, -, -, -, -, -, hrowM, -⟩ := id hB
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
  have hc := rtCodeOkS_setupWords2A h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) hc).1
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hw := valWords_of_rtCodeOkSA h hp hty hc
  have hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1) := by
    rw [hdT]; exact valWords_setupArg hw
  obtain ⟨w, fi, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hZU : Int64.ofInt (fM : Int) = Int64.ofInt (FC).cx.frame := by
    rw [hcx, hrowM _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])]
  have hmeW : (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))).val =
      .num (Scc.Cert.Rt.A64.rtA (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
        (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs "scc_rt_pinned" + 8#64).toNat := rfl
  refine mainCallWSF_ofPlaceOKHMVCR (Λv := lay2 Λ p) (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 (mainRetInt_of_accepted2 hp hfd)
    hok (hlitP_of_mainRetOk hm hfd) hc
    (by rw [(FC).hfn, hdn]; rfl) (posOff_proL_mainA h hp hd) hdT hfd
    (hna.trans (Option.some.inj (hLw.1.symm.trans hargW))) (hloc_of_accepted2 hp ty hty) hZU
    (simpleTy_of_accepted2 hp ty hty) hw (Nat.le_of_lt_succ hsw) (th02_term_setup hty _)
    (by rw [th02_setupA hty]; rfl) ⟨_, hmeW, BitVec.isLt _⟩
    (by rw [x0_start2A h]; exact valRep_meW2_of_placeOKAtA h _) (hme_start2A h hty L0) ?_ ?_
    (fun m hm => hm.2.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (progNoS_zbad_of_accepted2 hp) ?_
  · rintro c regs ⟨_, ⟨cE, fr, cr, a, t, ws, hct, -, -, -, hc'⟩, -⟩
    obtain ⟨x, f, a', e, d', t', ws', ht, -, -, -, rfl⟩ := hct
    have ht' : (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term =
        .let_ x (.call f [] a' []) e := ht
    rw [th02_term_setup hty, setupTerm_eq] at ht'
    cases ht'
    subst hc'
    exact ⟨⟨fun h => h, trivial⟩, fun _ h => nomatch h⟩
  · rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hok' h16 hst hF g hra htp cP hcP
    have hC := mainCx2_setup h hp hty hcfg hB hok' h16 hst hF hra htp
    obtain ⟨Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩ := HM L0 ls hR j d hd hdn _ F' g cP (hC.toLAt h) hcP
    rw [htp] at hab hC2 hL hN hP hCH hPH
    exact ⟨GM cP, Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩

/-- **`MainLUStmt` from `main`'s segment at every reachable placement**
(`mainCallWSF_ofMainSeg2FL` at the write tail `fun _ => True`, every
choice of the bounds, invariant and reachable placement, at the first
stack's top), for any `Accepted2` program with a setup block and `main`'s
held returns (`mainRetOk`). -/
theorem mainLU_ofMainSeg2L (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true)
    (HM : ∀ J, MainSeg2L h hp (fun _ => True) J) : MainLUStmt h ty :=
  fun J _ _ hR _ _ _ _ _ _ _ _ _ hB => mainCallWSF_ofMainSeg2FL h hp hty hm hcfg hB J (HM J) hR _

end GenericL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.MainCx2.toLAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.MainCx2.toLAt

/--
info: 'Spike.Lib.LowerA64.mainCallWSF_ofMainSeg2FL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainCallWSF_ofMainSeg2FL

/-- info: 'Spike.Lib.LowerA64.mainLU_ofMainSeg2L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainLU_ofMainSeg2L
