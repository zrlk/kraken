/-
**`hello1`'s `main` call `hU` at any current placement and the start's
frame condition `WordsNone`** (AArch64): `Spike/Test/A64Hello1HUL.lean`'s
`mainCallWSF_ofVacHMVAL` at the frame `WordsNone ∧ swFSL`, as
`Spike/Test/A64Hello1HUF.lean` does at the start's placement: a setup
bottom key's `h0` resumes `scc_rt_main` at the frame with `WordsNone`
(`BotH`'s) and a placement some allocations past the start's.

- `mainCallWSF_ofVacHMVAFL`: `mainCallWSF_ofVacHMVAL` at `WordsNone ∧ swFSL`
  (`mainCallWSF_ofVacHMVAF` at `L0`, `ls`);
- `hello1_hUAFL`: its instance at `hello1o` at every choice of the bounds and
  every placement reachable from the start's, closed (the write tail
  `fun _ => True`; the placed labels inside the heap by `lblRange_reach`).
-/
import Spike.Test.A64Hello1HUF
import Spike.Test.A64Hello1MainL
import Spike.Lib.LblRangeReach

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

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`
(`Closed2AtWA`'s start frame carried to `scc_rt_main`). -/
local notation "FWS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ (FS v) m

/-- **`main`'s call at `WordsNone ∧ swFSL`** (`mainCallWSF_ofVacHMVAL` at the
frame with `WordsNone`): the limit cell's freedom from `swFSL`'s, the
callee frame's `MainPreUAL` at `swFSL` by weakening. -/
theorem mainCallWSF_ofVacHMVAFL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
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
    MainCallWSF (W2S J) (KT) p L0 (MSS J) (Ly).exe (Ly).endPc (swR v (-L) 0) (FWS v)
      (SC).fn (SC).Z D (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p L0 ty C0) (SC).sw (X0))
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
    replace hF : ∀ m, F' m → (FS (TOP)) m ∧ _ := fun m hm => ⟨(hF m hm).1.2, (hF m hm).2⟩
    obtain ⟨Ab, hab, hblk, hP, hPH, hA⟩ := hpre F' hok' h16 hst hF g hra htp cP hcP
    exact ⟨GM cP, Ab, calleePre2R_mainAL h hp hty hd hdn hrowM J hfD hL0 hLm hL8 hD8 hL2 hok' h16 hst hF cP hab
        hblk,
      callC2_of_noCallee hnoC, laneC_of_noXchg hnoX, newBufC_of_noNewBuf hnoB, hP,
      callC2H_of_noCallee hnoC, hPH, hA⟩

end Generic

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- `hello1o`'s `main`. -/
local notation "MD" => Spike.Test.Hello1MainSrc.mainD

open Spike.Test.Hello1MainSrc (hello1_main_compiled2 hello1_main_find hello1_main_noCallee
  hello1_main_noXchg hello1_main_noNewBuf)

/-- **`main`'s call at `hello1o` at any reachable placement**, at the frame
`WordsNone ∧ swFSL` (`h0`'s `hU`), closed at the write tail `fun _ => True`
(`mainCallWSF_ofVacHMVAFL` at `main`, compiled block `1`, its `MainPreUAL` by
`hello1_mainPreUATL` at `hello1_mainTgA`, the placed labels inside the heap
from the reachability by `lblRange_reach`). -/
theorem hello1_hUAFL (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
      (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A SccCertificate.config P1A (RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)) L D1 D2 lS lM fS nS fM nM)
    (J : InvS) {L0 : Lbl} {ls : Lsize} (hR : Reach (arOf (lay2 LeA P1A)) (fun _ => none) (fun _ => 0) L0 ls)
    (v : BitVec 64) :
    let Ly := RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)
    let TP0 := UInt64.ofBitVec (pinA Ly.lab + 0#64 + 8#64)
    MainCallWSF (W2AtL h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum (rS0 Ly) J (fun _ => True) (fun _ => 0) L0 ls)
      (TakeK (Ly.lab StackTake.siteL) (rS0 Ly)) P1A L0
      (MSAtL h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum J (ab2 P1A Ly.lab) (fun _ => 0) L0 ls)
      Ly.exe Ly.endPc (swR v (-L) 0)
      (fun m => Spike.Lib.DmemPriv.WordsNone Ly.Λ (MachineData.dmem m) ∧
        swFSL L (rS0 Ly) (stacksA Ly.lab + 0#64 + 16384#64) (limA TP0) v m)
      (setupMC (setupWords2 P1A)).fn (setupMC (setupWords2 P1A)).Z D2 (Int64.ofInt (fM : Int))
      (SetupArgs (SPostC P1A L0 hello1_htyA.choose
        (⟨(th02 P1A (meW2 (lay2 LeA P1A) (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)))).term,
          (th02 P1A (meW2 (lay2 LeA P1A) (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)))).env,
          none⟩ : Ctl)) (setupMC (setupWords2 P1A)).sw (pinA Ly.lab + 0#64 + 8#64))
      (fun c fs v => UPostRF P1A L0 c fs v ∧ MainCtlV (lay2 LeA P1A) L0 c fs v)
      (Ly.lab (setupMC (setupWords2 P1A)).sp1).toBitVec TP0 := by
  intro Ly TP0
  obtain ⟨-, -, -, -, -, hfn, hnD, -, -, hrowM, hL0, hLm, hL8, -, -, -, hD8, -, hL2, -⟩ := id hB
  have hcx : (fnCode2OfPMe hello1o_accepted2 h LeA 1 MD hello1_main_compiled2).lcx.externs =
      Scc.Frontend.externs P1A := by
    rw [(fnCode2OfPMe_spec hello1o_accepted2 h LeA 1 MD hello1_main_compiled2).1]
  have hrg : LblRange (RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)).Λ L0 ls :=
    lblRange_reach (Spike.Lib.A64.Rt.arOf_sub h) (fun _ => rfl) hR
  exact mainCallWSF_ofVacHMVAFL h hello1o_accepted2 hello1_htyA.choose_spec hello1_main_compiled2
    hello1_main_find rfl (by decide) (by rw [hello1_htyA_eq]; rfl) (by rw [hello1_htyA_eq]; decide)
    (by decide) (hello1_main_noCallee hcx) hello1_main_noXchg hello1_main_noNewBuf hrowM J (by omega) hL0 hLm hL8
    hD8 hL2 v (hello1_mainPreUATL h hB J hrg (fun _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)
      (hello1_mainTgA h))

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainCallWSF_ofVacHMVAFL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mainCallWSF_ofVacHMVAFL

/-- info: 'Spike.Lib.LowerA64.hello1_hUAFL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hUAFL
