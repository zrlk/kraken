/-
**`hello1`'s `main` call `hU`, the vacuous constructs closed** (x86-64):
`HUBV` (`Spike/Test/X64Hello1ClosedBVB.lean`) from
`mainCallWSF_ofPlaceOKHMV` (`Spike/Lib/LowerX64/HeldPostXV.lean`) at
`Λv := lay2 Λ p`, `lbl := fun _ => none`, the start control `C0` and the
first TCB.

The generic part (`mainCallWSF_ofVacHMV`, any `Accepted2` program with a
setup block, `main` at a compiled index `j`) closes from the placement check
and the start control: A11's code at the setup words (`rtCodeOkS_setupWords2`),
the words' count and type (`setupIn_sw_eq`, `valWords_of_rtCodeOkS`,
`simpleTy_of_accepted2`), `main`'s label and overflow stub
(`posOff_proL_main`), the start environment (`hme_start2`), `setupTerm`'s call (`hE_setupTerm`, the frame's rest free
of `ZBad`), the first TCB's limit cell (mapped, and free in the switch
frame), the stack pool and `ZBad`. Main's body with no plain call, lane
store or buffer allocation (`hnoC`, `hnoX`, `hnoB`) closes `CallC2`,
`CallC2H`, `LaneC` and `NewBufC` (`Spike/Lib/LowerX64/VacC2.lean`).

`main`'s held returns and literal tails come from `mainRetOk`
(`hlitP_of_mainRetOk`). The callee's entry `CalleePre2R` (`calleePre2R_main`)
is closed at the first stack's top, the trivial base context and the ghosts
the frame runs reach from the entry control: the region facts from the
bounds, `main`'s frame from the bounds' `main` row, the prologue's edge from
`proEdge2_ofUNM`. Off the first stack's top no state is in the switch
region's frame condition.

At `hello1o` (`hello1_hUBV`): `main` is compiled block `1`, returns `Int`,
passes `mainRetOk`, takes the setup result `iex sliceTy` and the thread
word, and its only call is to the extern `print`.

Left open at `hello1o` (`MainOpenU`, `MainPreU` at every choice of the
bounds, at the first stack's top), each with its producer: `main`'s blocks
inside `W2` (`CxBlk2`, the `W2` block instances), some aborts' fragment
holding the abort node's states with its segment `SegWS … False`
(`MainAbX`'s `mainAb_seg'`), and `print`'s call segments `PrintCallC`
(`printCallC_of`, `Spike/Lib/LowerX64/PrintCallC2.lean`) and `PrintCallCH`
(`printCallCH_of`, `Spike/Lib/LowerX64/PrintCallC2H.lean`).

- `posOff_proL_main`: a compiled block's overflow stub off the write abort
  (`fnCode2OfP_spec2`, `posOff_proL_of_fnOk1`);
- `MainPreU`, `calleePre2R_main`, `mainCallWSF_ofVacHMV`: the generic bridge;
- `cxBlk2_main`: `main`'s blocks inside `W2` (`cxBlk2_ofFn` at `fnCode2OfPMe`);
- `hello1o`'s `main` facts from `Spike/Test/Hello1MainFacts.lean`;
- `MainOpenU`, `hello1_hUBV`: the open premises and `HUBV` from them.
-/
import Spike.Lib.LowerX64.HeldPostXV
import Spike.Lib.LowerX64.VacC2
import Spike.Lib.LowerX64.SetupTailOf
import Spike.Lib.LowerX64.Start2C0
import Spike.Lib.LowerX64.StkOf
import Spike.Lib.LowerX64.UserLabs
import Spike.Lib.LowerX64.MainCode1
import Spike.Test.X64Hello1ClosedBVB
import Spike.Lib.Src.HeldLit2
import Spike.Test.Hello1MainFacts
import Spike.Test.X64Hello1HS

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
open Spike.Lib.AllocReach (IN)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rtCodeOkS SetupArgs MainCallWSF rS0 arOf swFSL)

section Generic

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the lowering's immediates (`fnCode2OfP`'s). -/
local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The stack take at the first stack's range. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 p)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- `main`'s callee region. -/
local notation "RC" => (RS v).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8

set_option hygiene false in
/-- `main`'s code predicate at the return address of `g`. -/
local notation "CD" g:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec (WcG.ra g))

/-- **A compiled block's overflow stub is off the write abort** (`fnCode2OfP_spec2`'s frame at the lowered IR's
function, A12's `fnOk1` there, `posOff_proL_of_fnOk1`). -/
theorem posOff_proL_main (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) :
    PosOff OP (LY).lab ((LY).lab (proL (FC).fr)) := by
  obtain ⟨w, -, -, hmem, hfr⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  obtain ⟨n, hn⟩ := mem_starts _ 0 hmem
  have h12 := Scc.Cert.PlaceOK.X64.fnCode1_of_placeOKAt h (Scc.Cert.PlaceOK.X64.place_ir_ofEmitted _ _ _)
  rw [hfr]
  exact posOff_proL_of_fnOk1 (Scc.Cert.Code1X64.fnOk1_of_fnCode1Ok h12 hn rfl) (labelOf_user_not_abLabs _ _) _

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`mainCallWSF_ofPlaceOKHMV`'s construct premise `hpre` left open**, at
the top `v` (the first stack's top at `hello1o`): at every callee frame of
`main`'s call and entry control `cP` free of `ZBad` (`FrOk2`), at the ghosts `GM cP` the frame runs
reach from `cP`, some aborts' fragment `Ab` holding the abort node's states
(`CalleePre2R`'s `hab`), `main`'s blocks inside `W2` (`CxBlk2`), `print`'s
call segments `PrintCallC`, `PrintCallCH` and the aborts' segment. The rest
of `CalleePre2R` is `calleePre2R_main`'s. -/
def MainPreU (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (Dt : State → Prop) (J : InvS) (L D : Int) (v : BitVec 64) : Prop :=
  ∀ F' : MachineData → Prop, (RC).OK → FStable (RC) F' →
    (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (SC).Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ((Ly).lab (SC).sp1).toBitVec → g.tp = TP0 → (RC).base = g.sp →
    ∀ cP : Ctl, FrOk2 cP [] →
    ∃ Ab : FragS isa,
      (∀ c0, (GM cP) c0 → ∀ s c', Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RC)) F'
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p (fun _ => none) (FC).fr
          (_root_.Executable.labels (LY).exe).label g.fp g.ra c0) s c' → Ab s c' []) ∧
      CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (FC) (rbR (RC)) F' [] g.fp g.ra (GM cP) ∧
      PrintCallC p (fun _ => none) (fun _ => 0) (FC).lcx (FC).fr (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
        (rbR (RC)) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      PrintCallCH p (fun _ => none) (fun _ => 0) (FC).lcx (FC).fr (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
        (rbR (RC)) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] (GM cP) (imms2Me Λ p) (TailAt2 p j) Ab ∧
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J) Ab (fun _ _ _ => False)

/-- **`main`'s callee entry `CalleePre2R` from its callee frame** at the
first stack's top (`v := TOP`), the trivial base context and the ghosts
`GM cP`: the region facts from the bounds (`Region.callee_ok`,
`Region.callee_base`, `stackOff_callee` twice as in `hS_ofOpen`), `main`'s
frame `fM` from the bounds' `main` row (`hrowM`, `fnCode2OfP_spec2`), the
prologue's edge from `proEdge2_ofUNM` (the start control at `setupTerm`,
`me` the first TCB's number), the blocks and aborts given. -/
theorem calleePre2R_main (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hfd : p.find? (·.name == "main") = some d)
    (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1)) {fM : Nat}
    (hrowM : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM)
    {Dt : State → Prop} (J : InvS) {L D : Int} (hfD : (fM : Int) + 48 ≤ D) (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hL2 : 8 + 8 + (SC).Z.toInt + 8 + D ≤ L)
    {F' : MachineData → Prop} (hok' : ((RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8).OK)
    (hst : FStable ((RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8) F')
    (hFF : ∀ m, F' m → (FS (TOP)) m ∧ CallerCells (RS (TOP)) (-8 - (SC).Z.toInt - 8 - 0) (-D) 8 m)
    {g : WcG} (htp : g.tp = TP0) (cP : Ctl) {Ab : FragS isa}
    (hab : ∀ c0, (GM cP) c0 → ∀ s c', Spike.Lib.X64.At (LY).exe (LY).endPc
      (rbR ((RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8)) F'
      (abortN2 (imms2Me Λ p) (TailAt2 p j) p (fun _ => none) (FC).fr
        (_root_.Executable.labels (LY).exe).label g.fp g.ra c0) s c' → Ab s c' [])
    (hblk : CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (FC)
      (rbR ((RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8)) F' [] g.fp g.ra (GM cP)) :
    CalleePre2R (W2S J) (KT) p (fun _ => none) (fun _ => 0) (MSS J) (fun _ _ _ _ _ _ _ _ => True) (FC)
      (rS0 (Ly)) ((RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8) F' [] g.fp g.ra TP0 (GM cP) Ab
      (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS (TOP)) (SC).fn
        (Int64.ofInt (fM : Int))
        (fun c rs => SetupArgs (SPostC p (fun _ => none) ty C0) (SC).sw (TP0).toBitVec c rs ∧ c = cP) g).J
      cP := by
  have hdn : d.name = "main" := by simpa using List.find?_some hfd
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) (rtCodeOkS_setupWords2 h hp hs)).1
  have hZ := setupMC_Z _ hsw
  obtain ⟨w, hLw, hna, hmem, hfr⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).fr.size = fM := by
    rw [hfr]; exact hrowM _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])
  -- the regions: the switch region, its callee `RS TOP`, `main`'s `RC`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (SC).Z.toInt - 8 - 0)
    (lo' := -D) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have he := proEdge2_ofUNM (lsize := fun _ => 0) (lbl := fun _ => none)
    (J := (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels (Ly).exe).label ((MSS J) []) (FS (TOP)) (SC).fn
      (Int64.ofInt (fM : Int))
      (fun c rs => SetupArgs (SPostC p (fun _ => none) ty C0) (SC).sw (TP0).toBitVec c rs ∧ c = cP) g).J)
    (FC) hdT hfd
    (hna.trans (Option.some.inj (hLw.1.symm.trans hargW))) hsw hnl (c0 := C0) (th02_term_setup hty _)
    (by rw [th02_setup hty]; rfl) (Spike.Lib.LowerNode.isNum_meNum (UInt64.toNat_lt_size _))
    (x0 := (TP0).toBitVec) (by rw [tp0_start2 h]; exact valRep_meW2_of_placeOKAt h _)
    (g := g) (lab := (_root_.Executable.labels (Ly).exe).label) (ms0 := (MSS J) []) (ms1 := (MSS J) [])
    (F := FS (TOP)) (F' := F') (fn := (SC).fn) (ZU := Int64.ofInt (fM : Int)) (by rw [hframe])
    (fun _ _ h => h) (fun m hm => (hFF m hm).1) (cP := cP) (fun _ _ h => h)
  rw [htp] at he
  exact {
    hcx := trivial
    hF := hst
    hR := hok'
    hlo := by
      show -D ≤ -8 - ((FC).fr.size : Int)
      rw [hframe]; omega
    hhi := by show (8 : Int) ≤ 8; exact Int.le_refl _
    hG0 := fun _ _ h1 h2 => h1.trans h2
    hW := hblk.1
    hWp := hblk.2
    hab := hab
    hg0 := .refl _
    hedge := he
    hR8 := by omega
    hl := by show (-D) % 8 = 0; omega
    hh := by show (8 : Int) % 8 = 0; rfl
    hFO := fun m hm =>
      Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
        (hFF m hm).2 }

/-- **`main`'s call from the placement check, the vacuous constructs and
the callee's entry closed** (`mainCallWSF_ofPlaceOKHMV` at `h0`'s
instance): the setup words, `main`'s label, the start control's facts, the
TCB's limit cell and the stack pool from the library; `main`'s held returns
and literal tails from `mainRetOk` (`hlitP_of_mainRetOk`); `CallC2`,
`CallC2H`, `LaneC`, `NewBufC` from a body with no plain call, lane store or
buffer allocation (`VacC2`); the callee's entry `CalleePre2R` at the first
stack's top (`calleePre2R_main`), off it no state in the switch region's
frame condition. -/
theorem mainCallWSF_ofVacHMV (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hfd : p.find? (·.name == "main") = some d)
    (hint : d.retTy = .int) (hm : Scc.Lower.mainRetOk p = true)
    (hdT : d.argTy = .prod ty (.ptr .pub .void)) (hnl : Scc.Lower.shapeOf ty ≠ .loc)
    (hargW : Scc.Obj.valWords d.argTy = some (setupWords2 p + 1))
    (hnoC : ∀ x g is a ts e, TailAt2 p j (.let_ x (.call g is a ts) e) → Spike.Lib.LowerCall.Callee (FC).lcx g →
      False)
    (hnoX : ∀ x b i v e, ¬ TailAt2 p j (.let_ x (.xchgAt b i v) e))
    (hnoB : ∀ x cn τ e, ¬ TailAt2 p j (.let_ x (.newBuf cn τ) e))
    {fM : Nat}
    (hrowM : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "main" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fM)
    {Dt : State → Prop} (J : InvS) {L D : Int} (hfD : (fM : Int) + 48 ≤ D) (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) (hL2 : 8 + 8 + (SC).Z.toInt + 8 + D ≤ L)
    (v : BitVec 64) (hpre : MainPreU h hp hd Dt J L D (TOP)) :
    MainCallWSF (W2S J) (KT) p (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (SC).fn (SC).Z D (Int64.ofInt (fM : Int)) (SetupArgs (SPostC p (fun _ => none) ty C0) (SC).sw (TP0).toBitVec)
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab (SC).sp1).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.1.1
  subst hv
  have hdn : d.name = "main" := by simpa using List.find?_some hfd
  have hok : Scc.Lower.heldRetOk d.body = true := by simpa [Scc.Lower.mainRetOk, hfd] using hm
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2 h hp hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs) hc).1
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  refine mainCallWSF_ofPlaceOKHMVC (Λv := lay2 Λ p) (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 hint hok
    (hlitP_of_mainRetOk hm hfd) hc
    (by rw [(FC).hfn, hdn]; rfl) (posOff_proL_main h hp hd) (simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkS h hp hty hc)
    (Nat.le_of_lt_succ hsw) (hme_start2 h hty (fun _ => none))
    (hE_setupTerm (th02_term_setup hty _)) ?_ ?_ (fun m hm => hm.1.1.2) hsub
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
  · intro F' hok' hst hF g hra htp hb cP hcP
    obtain ⟨Ab, hab, hblk, hP, hPH, hA⟩ := hpre F' hok' hst hF g hra htp hb cP hcP
    exact ⟨GM cP, Ab, cP, calleePre2R_main h hp hty hd hfd hdT hnl hargW hrowM J hfD hL0 hLm hL8 hD0 hD8 hL2
        hok' hst hF htp cP hab hblk,
      callC2_of_noCallee hnoC, laneC_of_noXchg hnoX, newBufC_of_noNewBuf hnoB, hP,
      callC2H_of_noCallee hnoC, hPH, hA⟩

/-- **`main`'s blocks inside `W2` at no frames** (`cxBlk2_ofFn` at `main`'s
code `fnCode2OfPMe`, the theorem's instance at `(Ly).Λ`, generic in the
program so its immediates stay folded): in a region and frame condition
with `cxBlk2_ofFn`'s facts, at ghosts whose controls are `FrOk2`, the
return point off the write abort (`hraP`) and the targets' check (`hTg`). -/
theorem cxBlk2_main (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {Dt : State → Prop} (J : InvS) {R : Region} {F : MachineData → Prop} (hFS : FStable R F) (hR : R.OK)
    (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -((FC).fr.size : Int)) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hFO : ∀ m, F m → StackOff (rS0 (Ly)) R m) {G0 : Ctl → Prop}
    (hG0F : ∀ c0, G0 c0 → FrOk2 c0 []) {fp ra : BitVec 64} (hraP : PosOff OP (LY).lab (Int64.ofBitVec ra))
    (hTg : ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
        (Int64.ofBitVec ra)) pc blk → Kind2 (FC).fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff OP (LY).lab ((LY).lab L)) :
    CxBlk2 (W2S J) (KT) p (fun _ => none) (fun _ => 0) (FC) R F [] fp ra G0 :=
  cxBlk2_ofFn (Λ := (Ly).Λ) (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (progNoS_zbad_of_accepted2 hp) (FC) hFS hR hR8 hlo hhi
    hl hh (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hFO
    (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F (fun _ _ h => h) hraP hTg

end Generic

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

open Spike.Test.Hello1MainSrc (hello1_main_compiled2 hello1_main_find hello1_main_noCallee hello1_main_noXchg
  hello1_main_noNewBuf)

/-- `hello1o`'s `main`. -/
local notation "MD" => Spike.Test.Hello1MainSrc.mainD

section Hello1

open Spike.Lib.AllocReach (Reach)
open Spike.Lib.X64.Rt (rtF)

variable (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
  (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes
    SccCertificate.labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Le P1)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (arOf (lay2 Le P1)) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 P1 (Ly).lab) L ls s c fs → J L ls s c fs

/-- **`hello1o`'s setup result is `iex sliceTy`.** -/
theorem hello1_hty_eq : hello1_hty.choose = .iex Spike.Lib.Hello1Src.sliceTy :=
  Option.some.inj (hello1_hty.choose_spec.symm.trans rfl)

/-- **`hU`'s open premises at `hello1o`**: at every choice of the bounds
and invariant, `MainPreU` at the first stack's top (the aborts' fragment,
`main`'s blocks, `print`'s call segments `printCallC_of`/`printCallCH_of`,
the aborts' segment). -/
def MainOpenU (E : Entry) (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) :
    Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J →
      MainPreU h hello1o_accepted2 hello1_main_compiled2 Dt J L D2 (stacksA (Ly).lab + 0#64 + 16384#64)

/-- **`hello1`'s `hU` (`HUBV`) from its open premises** (`mainCallWSF_ofVacHMV`
at `main`, compiled block `1`; `main`'s frame and the region's bounds from
`Bounds2`). -/
theorem hello1_hUBV {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (H : MainOpenU h E El Dt) : HUBV h hello1_hty.choose E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ v
  obtain ⟨-, -, -, -, -, -, -, -, -, hfD, -, hrowM, hL0, hLm, hL8, -, -, hD0, hD8, -, -, hL2, -⟩ := id hB
  have hcx : (fnCode2OfPMe hello1o_accepted2 h Le 1 MD hello1_main_compiled2).lcx.externs =
      Scc.Frontend.externs P1 := by
    rw [(fnCode2OfPMe_spec hello1o_accepted2 h Le 1 MD hello1_main_compiled2).1]
  exact mainCallWSF_ofVacHMV h hello1o_accepted2 hello1_hty.choose_spec hello1_main_compiled2 hello1_main_find
    rfl (by decide) (by rw [hello1_hty_eq]; rfl) (by rw [hello1_hty_eq]; decide) (by decide)
    (hello1_main_noCallee hcx) hello1_main_noXchg hello1_main_noNewBuf hrowM J hfD hL0 hLm hL8 hD0 hD8 hL2 v
    (H L D1 D2 lS lM fS nS fM nM hB J hJ)

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.calleePre2R_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.calleePre2R_main

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_ofVacHMV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_ofVacHMV

/-- info: 'Spike.Lib.LowerX64.cxBlk2_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxBlk2_main

/-- info: 'Spike.Lib.LowerX64.hello1_hUBV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hUBV
