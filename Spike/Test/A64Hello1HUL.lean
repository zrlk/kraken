/-
**`hello1`'s `main` call `hU` at any current placement** (AArch64; the twin
of `Spike/Test/X64Hello1HUL.lean`): `Spike/Test/A64Hello1HU.lean`'s generic
part at the current placement `L0`, `ls` (`W2AtL`, `MSAtL`,
`Spike/Lib/LowerA64/RtMainXRL.lean`) and the labels `L0`: a landing's
segment resumes `scc_rt_main` at a placement some allocations past the
start's (a setup bottom key's `h0`). The library's bridge
`mainCallWSF_ofPlaceOKHMVC` is generic in the labels and placement; `me`'s
words (`hme_start2`) and the prologue's edge (`proEdge2_ofUNM`) too.

- `MainPreUAL`, `calleePre2R_mainAL`, `mainCallWSF_ofVacHMVAL`,
  `cxBlk2_mainAL`: `MainPreUA`, `calleePre2R_mainA`, `mainCallWSF_ofVacHMVA`,
  `cxBlk2_mainA` at `L0`, `ls`.
-/
import Spike.Test.A64Hello1HU
import Spike.Lib.LowerA64.RtMainXRL

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
open Spike.Lib.AllocReach (IN)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs MainCallWSF rS0 arOf swFSL)
open Spike.Lib.A64.AllocG (abLabs)

section Generic

variable {L0 : Lbl} {ls : Lsize} {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
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
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance at the current placement `L0`, `ls`. -/
local notation "W2S" J:max => W2AtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0) L0
  ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`) at `L0`, `ls`. -/
local notation "MSS" J:max => MSAtL h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)
  L0 ls

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
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- `main`'s callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(SC).Z.toInt) (-D) 0

set_option hygiene false in
/-- `main`'s code predicate at the return address `ra`. -/
local notation "CD" ra:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`mainCallWSF_ofPlaceOKHMV`'s construct premise `hpre` left open**, at
the top `v` (the first stack's top at `hello1o`): at every callee frame of
`main`'s call and entry control `cP` free of `ZBad` (`FrOk2`), at the ghosts `GM cP` the frame runs
reach from `cP`, some aborts' fragment `Ab` holding the abort node's states
(`CalleePre2R`'s `hab`), `main`'s blocks inside `W2` (`CxBlk2`), `print`'s
call segments `PrintCallC`, `PrintCallCH` and the aborts' segment. The rest
of `CalleePre2R` is `calleePre2R_mainAL`'s. -/
def MainPreUAL (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (Dt : State → Prop) (J : InvS) (L D : Int) (v : BitVec 64) : Prop :=
  ∀ F' : MachineData → Prop, (RC).OK → (RC).base.toNat % 16 = 0 → FStable (RC) F' →
    (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(SC).Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ((Ly).lab (SC).sp1).toBitVec → g.tp = TP0 → ∀ cP : Ctl, FrOk2 cP [] →
    ∃ Ab : FragS isaLSE2,
      (∀ c0, (GM cP) c0 → ∀ s c', Spike.Lib.A64.Flow.At (LY).exe (LY).endPc (RC) F'
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p L0 (FC).cx
          (_root_.Executable.labels (LY).exe).label g.fp g.ra c0) s c' → Ab s c' []) ∧
      CxBlk2 (W2S J) (KT) p L0 ls (FC) (RC) F' [] g.fp g.ra (GM cP) ∧
      PrintCallC p L0 ls (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY).exe (LY).endPc
        (RC) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      PrintCallCH p L0 ls (FC).lcx (FC).cx (CD g.ra) ((FC).Bl g.ra) (LY).exe (LY).endPc
        (RC) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      SegWS (W2S J) (KT) p L0 (MSS J) Ab (fun _ _ _ => False)

/-- **`main`'s callee entry `CalleePre2R` from its callee frame** at the
first stack's top (`v := TOP`), the trivial base context and the ghosts
`GM cP`: the region facts from the bounds (`stackOff_callee` as in
`hS_ofOpenA`), `main`'s frame `fM` from the bounds' `main` row (`hrowM`,
`fnCode2OfP_spec2`), the blocks and aborts given. -/
theorem calleePre2R_mainAL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hdn : d.name = "main") {fM : Nat}
    (hrowM : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM)
    {Dt : State → Prop} (J : InvS) {L D : Int} (hfD : (fM : Int) ≤ D) (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD8 : D % 8 = 0) (hL2 : (SC).Z.toInt + D ≤ L)
    {F' : MachineData → Prop} (hok' : ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0).OK)
    (h16 : ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0).base.toNat % 16 = 0)
    (hst : FStable ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0) F')
    (hFF : ∀ m, F' m → (FS (TOP)) m ∧ CallerCells (swR (TOP) (-L) 0) (-(SC).Z.toInt) (-D) 0 m)
    {g : WcG} (cP : Ctl) {Ab : FragS isaLSE2}
    (hab : ∀ c0, (GM cP) c0 → ∀ s c', Spike.Lib.A64.Flow.At (LY).exe (LY).endPc
      ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0) F'
      (abortN2 (imms2Me Λ p) (TailAt2 p j) p L0 (FC).cx
        (_root_.Executable.labels (LY).exe).label g.fp g.ra c0) s c' → Ab s c' [])
    (hblk : CxBlk2 (W2S J) (KT) p L0 ls (FC)
      ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0) F' [] g.fp g.ra (GM cP)) :
    CalleePre2R (W2S J) (KT) p L0 ls (MSS J) (fun _ _ _ _ _ _ _ _ => True) (FC)
      (rS0 (Ly)) ((swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0) F' [] g.fp g.ra TP0 (GM cP) Ab cP := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) (rtCodeOkS_setupWords2A h hp hs)).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).cx.frame = fM := by
    rw [hcx]; exact hrowM _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])
  refine ⟨trivial, hst, hok', h16, ?_, ?_, fun _ _ h1 h2 => h1.trans h2, hblk.1, hblk.2, hab, .refl _, ?_, ?_,
    ?_⟩
  · show -D ≤ -((FC).cx.frame : Int)
    rw [hframe]; omega
  · show (0 : Int) ≤ 0; exact Int.le_refl _
  · show (-D) % 8 = 0; omega
  · show (0 : Int) % 8 = 0; rfl
  · intro m hm
    obtain ⟨⟨-, hoff⟩, hcc⟩ := hFF m hm
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc

/-- **`main`'s call from the placement check, the vacuous constructs and
the callee's entry closed** (`mainCallWSF_ofPlaceOKHMV` at `h0`'s
instance): the setup words, `main`'s label, overflow stub, parameter count
and frame, the start control's facts, the TCB's limit cell and the stack
pool from the library; `main`'s held returns and literal tails from
`mainRetOk` (`hlitP_of_mainRetOk`); `CallC2`, `CallC2H`, `LaneC`, `NewBufC`
from a body with no plain call, lane store or buffer allocation (`VacC2`);
the callee's entry `CalleePre2R` at the first stack's top
(`calleePre2R_mainAL`), off it no state in the switch region's frame
condition. -/
theorem mainCallWSF_ofVacHMVAL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hfd : p.find? (·.name == "main") = some d)
    (hint : d.retTy = .int) (hm : Scc.Lower.mainRetOk p = true)
    (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1))
    (hnoC : ∀ x g is a ts e, TailAt2 p j (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee (FC).lcx g →
      False)
    (hnoX : ∀ x b i v e, ¬ TailAt2 p j (.let_ x (.xchgAt b i v) e))
    (hnoB : ∀ x cn τ e, ¬ TailAt2 p j (.let_ x (.newBuf cn τ) e))
    {fM : Nat}
    (hrowM : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fM)
    {Dt : State → Prop} (J : InvS) {L D : Int} (hfD : (fM : Int) ≤ D) (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD8 : D % 8 = 0) (hL2 : (SC).Z.toInt + D ≤ L)
    (v : BitVec 64) (hpre : MainPreUAL (L0 := L0) (ls := ls) h hp hd Dt J L D (TOP)) :
    MainCallWSF (W2S J) (KT) p L0 (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (SC).fn (SC).Z D (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p L0 ty C0) (SC).sw (X0))
      (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
      ((Ly).lab (SC).sp1).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.1
  subst hv
  have hdn : d.name = "main" := by simpa using List.find?_some hfd
  have hok : Scc.Lower.heldRetOk d.body = true := by simpa [Scc.Lower.mainRetOk, hfd] using hm
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2A h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) hc).1
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  obtain ⟨w, fi, hLw, hna, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hZU : Int64.ofInt (fM : Int) = Int64.ofInt (FC).cx.frame := by
    rw [hcx, hrowM _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])]
  have hmeW : (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))).val =
      .num (Scc.Cert.Rt.A64.rtA (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
        (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs "scc_rt_pinned" + 8#64).toNat := rfl
  refine mainCallWSF_ofPlaceOKHMVC (Λv := lay2 Λ p) (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 hint hok
    (hlitP_of_mainRetOk hm hfd) hc
    (by rw [(FC).hfn, hdn]; rfl) (posOff_proL_mainA h hp hd) hdT hfd
    (hna.trans (Option.some.inj (hLw.1.symm.trans hargW))) hnl hZU (simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkSA h hp hty hc) (Nat.le_of_lt_succ hsw) (th02_term_setup hty _)
    (by rw [th02_setupA hty]; rfl) ⟨_, hmeW, BitVec.isLt _⟩
    (by rw [x0_start2A h]; exact valRep_meW2_of_placeOKAtA h _) (hme_start2A h hty L0) ?_ ?_
    (fun m hm => hm.1.2) hsub (Spike.Lib.A64.Rt.fitS_of_sub _ hsub) (progNoS_zbad_of_accepted2 hp) ?_
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
    obtain ⟨Ab, hab, hblk, hP, hPH, hA⟩ := hpre F' hok' h16 hst hF g hra htp cP hcP
    exact ⟨GM cP, Ab, calleePre2R_mainAL h hp hty hd hdn hrowM J hfD hL0 hLm hL8 hD8 hL2 hok' h16 hst hF cP hab
        hblk,
      callC2_of_noCallee hnoC, laneC_of_noXchg hnoX, newBufC_of_noNewBuf hnoB, hP,
      callC2H_of_noCallee hnoC, hPH, hA⟩

/-- **`main`'s blocks inside `W2` at no frames** (`cxBlk2_ofFn` at `main`'s
code `fnCode2OfPMe`, the theorem's instance at `(Ly).Λ`, generic in the
program so its immediates stay folded): in a region and frame condition
with `cxBlk2_ofFn`'s facts, at ghosts whose controls are `FrOk2`, the
return point off the write abort (`hraP`) and the targets' check (`hTg`). -/
theorem cxBlk2_mainAL (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Dt : State → Prop} (J : InvS) {R : Region} {F : MachineData → Prop} (hFS : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -((FC).cx.frame : Int)) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m) {G0 : Ctl → Prop}
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 []) {fp ra : BitVec 64} (hraP : PosOff OP (LY).lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra)) pc blk → Kind2 (FC).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff OP (LY).lab ((LY).lab L)) :
    CxBlk2 (W2S J) (KT) p L0 ls (FC) R F [] fp ra G0 :=
  cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (progNoS_zbad_of_accepted2 hp) (FC) hFS hR hal hlo hhi
    hl hh (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO
    (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F (fun _ _ h => h) hraP hTg

end Generic

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.calleePre2R_mainAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.calleePre2R_mainAL

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofVacHMVAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofVacHMVAL

/-- info: 'Spike.Lib.LowerA64.cxBlk2_mainAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxBlk2_mainAL
