/-
**`main`'s call from `main`'s segment, for any `Accepted2` program with a
setup block** (AArch64): `HUBVFA` (`Spike/Test/A64Hello1HUF.lean`) from
`MainSeg2` (`Spike/Lib/LowerA64/G1MainStmt.lean`), as `hello1o`'s
`mainCallWSF_ofVacHMVAF` with the callee frame's construct premise
`MainSeg2`'s at the context facts `MainCx2` built here.

- `valWords_setupArg`, `mainRetInt_of_accepted2`: `main`'s argument's
  words (the setup result's and the thread word) and its result `Int`;
- `limS_main`: `main`'s limit room at `main`'s callee region below the
  first stack's top (`calleeRowA`, as `limS_setup`);
- `mainCx2_setup`: `MainCx2` at `main`'s callee region from the call's
  premises and the bounds `Bounds2A`;
- `mainCallWSF_ofMainSeg2F`: `main`'s call `MainCallWSF` at the switch
  region's frame condition with `WordsNone`, from `MainSeg2`;
- `hUBVFA_of_mainSeg2`: `HUBVFA` from `MainSeg2` at every invariant.
-/
import Spike.Lib.LowerA64.G1MainStmt
import Spike.Lib.LowerA64.G1SetupCx
import Spike.Test.A64Hello1HUF

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

/-- **`main`'s argument's words with a setup block**: the setup result's
`sw` words and the thread word. -/
theorem valWords_setupArg {ty : Ty} {sw : Nat} (hw : Scc.Obj.valWords ty = some sw) :
    Scc.Obj.valWords (.prod ty (.ptr .pub .void)) = some (sw + 1) := by
  unfold Scc.Obj.valWords at hw ⊢
  obtain ⟨la, hla, rfl⟩ := Option.map_eq_some_iff.1 hw
  simp [Scc.Obj.slots, hla]

/-- **An `Accepted2` program's `main` returns `Int`** (`main2`). -/
theorem mainRetInt_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {d : Decl}
    (hfd : p.find? (·.name == "main") = some d) : d.retTy = .int := by
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hn : d.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds d (List.mem_of_find?_eq_some hfd)
  have hpe : Scc.Lower.isPrintExt d = false := by simp [Scc.Lower.isPrintExt, hn]
  have hnl : (Scc.Lower.hasPrint p && "main" == "printL") = false := by
    rw [show ("main" == "printL") = false by decide, Bool.and_false]
  simp only [Scc.Lower.decl2, hpe, hn, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  rw [hnl] at hE'
  simp only [Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.main2 at hE'
  simp only [Bool.and_eq_true, beq_iff_eq] at hE'
  exact hE'.1.1.2

section Generic

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the lowering's immediates (`fnCode2OfP`'s). -/
local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The record's static memory. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

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
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`Closed2AtWA`'s start frame carried to `scc_rt_main`). -/
local notation "FWS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ (FS v) m

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- `main`'s callee region below the first stack's top, at the room `D`. -/
local notation "RCT" D:max => (swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`main`'s limit room at `main`'s callee region** (`MainCx2.lim`), the
switch region's top the first stack's: `main` is a stack-checked callee of
`scc_rt_main` whose need `n` fits `Z + n ≤ 12288` (`calleeRowA` at
`CfgNeedOkA`), so above the limit `stacksA + 4096` or the limit word's
initial `0` the need fits below the callee region's base `TOP - Z`
(`limS_setup`'s argument at `main`). -/
theorem limS_main (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    (hcfg : CfgNeedOkA pcfg = true) {L D2 : Int} (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hD20 : 0 ≤ D2)
    (hL2 : (SC).Z.toInt + D2 ≤ L) (J : InvS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "main") :
    LimRoomA (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.need (Scc.Lower.Names.user d.name)
      (((MSS J) []).G ⟨limA (TP0), 8⟩) (RCT D2).base.toNat := by
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) (rtCodeOkS_setupWords2A h hp hs)).1
  have hZ8 := setupMC_Z _ hsw
  obtain ⟨f, fi, hf, hck, hfn⟩ := userFn2A h hp hd
  have hcall := (user_mem_calleesA (setupWords2 p) (Spike.Lib.LowerNode.setupMask2 p)).2
  rw [← hn, ← hfn] at hcall
  obtain ⟨l, n, hr, -, hn⟩ := calleeRowA h hp hs hcfg hf hck hcall
  rw [hfn] at hr
  refine ⟨l, _, n, hr, fun w hw => ?_⟩
  -- the callee region's base: `TOP - Z`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
  have hb := Region.callee_base (kc := -(SC).Z.toInt) (lo' := -D2) (hi' := 0) hok
    (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have htop : ((swR (TOP) (-L) 0).base.toNat : Int) = (Ly).stacksA.toNat + 16384 := by
    show ((TOP).toNat : Int) = _
    rw [show stacksA (Ly).lab = (Ly).stacksA from (Ly).lab_stacks, Spike.Lib.A64.Rt.top0_toNat]; rfl
  have hw' : Spike.Lib.A64.PhRec.GOf Ly M0 ⟨(Ly).pinA + 16#64, 8⟩ w := by
    revert hw
    rw [(Ly).lab_pin, Spike.Lib.A64.Rt.limA_tcb0]
    dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun h' => h'
  have := (Ly).pool_fit
  obtain ⟨h1, h2⟩ := (Ly).stacks_sub
  simp only at h1 h2
  rcases Spike.Lib.A64.PhRec.gOf_lim hw' with rfl | rfl
  · have hv : ((Spike.Lib.A64.PhRec.limV (Ly)).setWidth 64).toNat = (Ly).stacksA.toNat + 4096 := by
      simp only [Spike.Lib.A64.PhRec.limV, BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128),
        BitVec.setWidth_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [hv]
    omega
  · have hv : (((M0).initVal ⟨(Ly).pinA + 16#64, 8⟩).setWidth 64).toNat = 0 := by
      rw [Spike.Lib.A64.PhRec.limInit_ofPlaceOK h (imms2Me Λ p)]
      rfl
    rw [hv]
    omega

/-- **`main`'s context facts at its callee region** (`MainCx2` at the
setup call's `main` call, below the first stack's top): the region's facts
from the call's premises (`stackOff_callee` as in `calleePre2R_mainA`),
`WordsNone` and the limit word's freedom from the frame condition, the
return point `sp1` off the write abort (`posOff_mainRetS`), the room from
`Bounds2A`'s `nM + 48 + 208 ≤ D2` and the limit room by `limS_main`. -/
theorem mainCx2_setup (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hcfg : CfgNeedOkA pcfg = true) {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM) {F' : MachineData → Prop} {g : WcG}
    (hok' : (RCT D2).OK) (h16 : (RCT D2).base.toNat % 16 = 0) (hst : FStable (RCT D2) F')
    (hFF : ∀ m, F' m → (FWS (TOP)) m ∧ CallerCells (swR (TOP) (-L) 0) (-(SC).Z.toInt) (-D2) 0 m)
    (hra : g.ra = ((Ly).lab (SC).sp1).toBitVec) (htp : g.tp = TP0) :
    MainCx2 h (RCT D2) F' g.ra g.tp := by
  obtain ⟨-, -, -, -, hrM, -, -, hnM, -, -, hL0, hLm, hL8, -, -, hD20, hD28, -, hL2, -⟩ := id hB
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2A h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) hc).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨j, d, hd, hn⟩ := Spike.Lib.LowerNode.main_compiled2_ofAccepted2 hp
  refine
    { hR := hok'
      hal := h16
      hl := by show (-D2) % 8 = 0; omega
      hh := by show (0 : Int) % 8 = 0; rfl
      hhi := Int.le_refl _
      hFS := hst
      hFO := fun m hm => ?_
      hwn := fun m hm => (hFF m hm).1.1
      hraP := by rw [hra]; exact posOff_mainRetS (Spike.Lib.A64.Rt.mainSIn_of_okS hc)
      hraK := by rw [hra]; exact RaMain.raOk_main h (Scc.Lower.imms2Of p) hc
      htp := htp
      hun := fun m hm => by rw [htp]; exact (hFF m hm).1.2.1.2
      room := ⟨lM, fM, nM, hrM, by show -D2 ≤ _; omega⟩
      lim := fun m hm J => ?_ }
  · obtain ⟨⟨-, -, hoff⟩, hcc⟩ := hFF m hm
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  · have := limS_main h hp hs hcfg hL0 hLm hD20 hL2 J hd hn
    rw [hn] at this
    rw [htp]
    exact this

/-- **`main`'s call at `WordsNone ∧ swFSL` from `main`'s segment**
(`mainCallWSF_ofVacHMVAF` with the construct premise `MainSeg2`'s): off
the first stack's top no state is in the frame condition; at it, `main`'s
code facts from the placement check and `Accepted2` (`main`'s result `Int`,
argument the setup result's and the thread word, held returns from
`mainRetOk`), the callee frame's context facts `MainCx2` by
`mainCx2_setup`, and `CalleePre2R` and the constructs' segments from
`MainSeg2` at the ghosts `GM cP`. -/
theorem mainCallWSF_ofMainSeg2F {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS) (HM : MainSeg2 h hp Dt J)
    (v : BitVec 64) :
    MainCallWSF (W2S J) (KT) p (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FWS v)
      (SC).fn (SC).Z D2 (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p (fun _ => none) ty C0) (SC).sw (X0))
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
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
    (by rw [x0_start2A h]; exact valRep_meW2_of_placeOKAtA h _) (hme_start2A h hty (fun _ => none)) ?_ ?_
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
    obtain ⟨Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩ := HM j d hd hdn _ F' g cP hC hcP
    rw [htp] at hab hC2 hL hN hP hCH hPH
    exact ⟨GM cP, Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩

/-- **`HUBVFA` from `main`'s segment** (`mainCallWSF_ofMainSeg2F` at every
choice of the bounds and invariant), for any `Accepted2` program with a
setup block and `main`'s held returns (`mainRetOk`). -/
theorem hUBVFA_of_mainSeg2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOkA pcfg = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2) {Dt : State → Prop}
    (HM : ∀ J, MainSeg2 h hp Dt J) : HUBVFA h ty E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J _ v
  exact mainCallWSF_ofMainSeg2F h hp hty hm hcfg hB J (HM J) v

end Generic

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.valWords_setupArg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.valWords_setupArg

/-- info: 'Spike.Lib.LowerA64.mainRetInt_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainRetInt_of_accepted2

/-- info: 'Spike.Lib.LowerA64.limS_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limS_main

/-- info: 'Spike.Lib.LowerA64.mainCx2_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCx2_setup

/--
info: 'Spike.Lib.LowerA64.mainCallWSF_ofMainSeg2F' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.mainCallWSF_ofMainSeg2F

/-- info: 'Spike.Lib.LowerA64.hUBVFA_of_mainSeg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hUBVFA_of_mainSeg2
