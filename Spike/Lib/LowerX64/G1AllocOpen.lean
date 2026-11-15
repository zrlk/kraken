/-
**The allocator's `W2` instance at the setup frame, for any `Accepted2`
program** (x86-64; the twin of `Spike/Lib/LowerA64/G1AllocOpen.lean`): the
per-allocation premises of the setup frame's allocator instance (`OpenAPt`,
`Spike/Test/X64Hello1HAWNone.lean`) without the count's literal leaf, at any
`Accepted2` program whose object layout's count field ends below bit `22`.

- `allocCtx_msOfAX`: `AllocCtx` at `msOfAX` free of the frame invariant;
- `OpenAPtV`: `OpenAPt` with `AllocPtV` (no count's leaf) at each
  allocation;
- `cxLB_hAW_noneV`: `OpenAWF` from `OpenAPtV` (`cxLB_hAW_none` at
  `allocW2At_ofV`, the elements one word by `newBufK_of_accepted2`);
- `openAWF_of_accepted2`: `OpenAWF` at any `Accepted2` program
  (`cxLB_hAW_noneV` at `openAPtV_of_accepted2`);
- `ElG`: the landings' states at the setup frame's context;
- `openAPtV_of_accepted2`: `OpenAPtV` at the landings `ElG` and the write tail
  `fun _ => True`: the walk fields by `allocPt_of_accepted2` at the arena
  `arOf`, `hms` by `hms_of_elem2`, `hstub` by `hello1_rodata_hstub` (generic
  in the program), and `hxa`, `hxaF` by `landStk_hxa` at the setup frame's
  context `CxOkH` with no records, as for `hello1o`.
-/
import Spike.Test.X64Hello1HAWNone
import Spike.Test.X64Hello1AllocHS
import Spike.Test.X64Hello1CxOkH
import Spike.Lib.LowerX64.LandStk2
import Spike.Lib.LowerX64.LandHu
import Spike.Lib.LowerX64.CalleeRgn2
import Spike.Lib.LowerX64.G1AllocPt
import Spike.Lib.LowerX64.G1AllocMs

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRun FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (swFSL rS0 rtF setupMC arOf)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

/-- **`AllocCtx` at the rows' memory side does not depend on the frame
invariant** (`msOfAX` at either abort phase). -/
theorem allocCtx_msOfAX {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Spike.Lib.Arena} {I I' : InvS} {ab : Option (State → Prop)}
    {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame} {L : Label → Int64} {R : Region} {fr : Int}
    {Jc : Spike.Lib.X64.AS → Ctl → Prop} {q : Spike.Lib.X64.Alloc.Call} {m : MachineData}
    (h : Spike.Lib.X64.Flow.NewBuf.AllocCtx (msOfAX Λ μ p rd G own ar I ab lbl lsize fs) L R fr Jc q m) :
    Spike.Lib.X64.Flow.NewBuf.AllocCtx (msOfAX Λ μ p rd G own ar I' ab lbl lsize fs) L R fr Jc q m := by
  cases ab <;> exact h

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **The start's frame condition** (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX` at `WNF`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (WNF) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v`. -/
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
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises at `FS` with `WordsNone` (`PREF`). -/
local notation "PREF" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
/-- The stack records' bottom keys at the setup frame (`SetupBot` at `FS`
with `WordsNone`). -/
local notation "SB" J:max v:max D1:max fS:max => fun k fs =>
  SetupBot p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 (Int64.ofInt fS)
    ⟨TOP - 8#64, TP0, C0⟩ (TP0).toBitVec k fs

set_option hygiene false in
/-- The `j`th block's code (`fnCode2OfPMe`). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The setup frame's code at its return address `ra` (`OpenAWF`'s). -/
local notation "CdR" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)

set_option hygiene false in
/-- The setup frame's calls at its return address `ra` (`fnCode2OfPMe_spec`'s `Bl`). -/
local notation "BlR" ra:max => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (FC).fr (Int64.ofBitVec ra)

set_option linter.unusedVariables false in
/-- **`allocW2At_ofV`'s per-allocation premise at `OpenAWF`'s instance, at
every choice of the bounds**: `OpenAPt` with `AllocPtV` (no count's leaf)
at each allocation of the setup frame's walk. -/
def OpenAPtV (hp : Scc.Lower.Accepted2 p = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) (Dt : State → Prop) : Prop :=
  ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat),
    Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM →
    ∀ J : InvS, StJ J → ∀ j d (hd : (compiled2 p)[j]? = some d), d.name = "rodata" →
      ∀ (v : BitVec 64), v = TOP →
      ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREF F' g fr →
        (SB J v D1 fS) ⟨j, RC, F', g.fp, g.ra, TP0, GR g fr⟩ [fr] →
        ∀ (c0 : Ctl) (pc : Int64) (kk : Nat) (x : String) (cn : At) (τ : Ty) (e : Expr)
          (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat))
          (tk : Ty) (kv : UInt64) (en em hh : Nat), (GR g fr) c0 → TailAt2 p j (.let_ x (.newBuf cn τ) e) →
          Spike.Lib.LowerNode.Fresh env n → Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]) →
          Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em) →
          Scc.Obj.header0 (FC).lcx.obj .array en em = some hh →
          PtC2 (FC).lcx (FC).fr (CdR g.ra) (BlR g.ra) (_root_.Executable.labels (Ly).exe).label
            (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e) →
          AllocPtV (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
            (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
            (fun _ => none) (fun _ => 0) (S0X h E (WNF)) El J (ab2 p (Ly).lab) Dt (LY0).lab
            ((Ly).lab StackTake.siteL) (fun _ => none) (fun _ => 0) [fr] (Ly).exe (Ly).endPc (rbR (RC)) F'
            (FC).fr (CdR g.ra) (BlR g.ra) g.fp g.ra (TP0) c0 pc x cn τ e env lits cs bufs hh kv
            (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)

/-- **`OpenAWF` from `OpenAPtV`** (`cxLB_hAW_none` at `allocW2At_ofV`): the
same record, frame, region, arena and ghost facts, the elements one word at
every allocation of every compiled block (`newBufK_of_accepted2`). -/
theorem cxLB_hAW_noneV (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {Dt : State → Prop}
    (H : OpenAPtV h hp E El Dt) : OpenAWF h hp E El Dt := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB
  have HP := H L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB
  have hTn : ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true :=
    fun _ _ _ _ hT => (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  obtain ⟨hR0, hF', hFF, -, -, hct, -⟩ := hP
  have hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (lay2 Λ p) m.dmem := fun m hm => (hFF m hm).1.1.1
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hok : (swR v (-L) 0).OK := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : v.toNat % 8 = 0 := by
    rw [hv, Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS v).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS v).base.toNat : Int) = v.toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : (RC).lo ≤ -8 := by show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RC).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo0 : (rbR (RC)).lo ≤ -((FC).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR (RC)).hi := by show (0 : Int) ≤ 8 + 8; decide
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (rbR (RC)) m := by
    intro m hm
    refine stackOff_rbR hR0 hlo1 hhi1 ?_
    have H := hFF m hm
    have hb8 : (RS v).base.toNat % 8 = 0 := by omega
    exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) H.1.1.2.2 H.1.2)
      H.2
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  haveI : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, -, -, -, hH, hCt, hU, hO, hCl, -⟩ := msOfAX_fields (Λ := (Ly).Λ) (μ := Spike.Lib.X64.PhRec.μ (Ly))
    (p := p) (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (own := fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (ar := Ar) (I := IN (Ar) (fun _ => none) (fun _ => 0) J) (lbl := fun _ => none) (lsize := fun _ => 0)
    (fs := [fr]) (ab2 p (Ly).lab)
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
  exact allocW2At_ofV (ownOf := Spike.Lib.X64.PhRec.ownOf (Ly))
    (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))) (allocIn_of_placeOKAt h)
    (Spike.Lib.X64.PhRec.allocPhOk_ofPlaceOK h (Scc.Lower.imms2Of p))
    (Spike.Lib.X64.PhRec.allocAbOk_ofPlaceOK h (Scc.Lower.imms2Of p)) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) (fun _ => rfl) (FC).hf (FC).h1 (FC).h16 (rbR_ok hR0 hlo1 hhi1) (by omega)
    (by show (-D1 + 8) % 8 = 0; omega) (by show ((8 : Int) + 8) % 8 = 0; decide)
    (by show -D1 + 8 ≤ -((FC).fr.size : Int) - 8 + -160 - 32; rw [hframe]; omega)
    (by show (16 : Int) ≤ 8 + 8; decide) (rbR_fstable hR0 hlo1 hhi1 hF')
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hFO hpN hJ
    Reach.base (fun s _ => framesPlaced_setup h hp hty hct s)
    (fun _ _ hr => regionOff_of_rsOf (FC).hf hlo0 hhi hr)
    (fun q hq a ha => hmem_arOf h hc hwn hH hCl hCt hU hO q hq a (by rw [hCt, hU, hCl]; exact ha))
    (hno_arOf h (imms2Me Λ p) hH hO) (hlt_arOf h hc) (h64_arOf h hc)
    (fun _ _ _ _ _ hl => nomatch hl) hTn
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))) HP

/-- **The landings' states at the setup frame's context** (`ElX` at the
blocks' code `fnCode2OfPMe`, the context `CxOkH` and the bottom key
`BotH`; `hello1o`'s `ElH` at any `Accepted2` program). -/
noncomputable def ElG (hp : Scc.Lower.Accepted2 p = true) :
    Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  ElX h (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h)

/-- **`OpenAPtV` at any `Accepted2` program** (the landings `ElG`, the write
tail `fun _ => True`), when the object layout's count field ends below bit
`22` (`hobj`): at the setup frame's allocations, the walk fields by
`allocPt_of_accepted2` at the arena `arOf` (`AllocPtWk.ofAr`), `hms` by
`hms_of_elem2`, `hstub` by `hello1_rodata_hstub`, and `hxa`, `hxaF` by
`landStk_hxa` at the setup frame's context `CxOkH` with no records, the
setup call's return address of the phase anchor's phase (`raOk_setup`), the
resumption point `BodyPtW` from `PtC2` and `Fresh`, the arena's units
(`arOf_units_fit`); for `hxaF` at the family `J'`, the call's premises
rebuilt there (`callOK_msOfAX`). -/
theorem openAPtV_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) :
    OpenAPtV h hp E (ElG h hp) (fun _ => True) := by
  intro L D1 D2 lS lM fS nS fM nM hB J hJ j d hd hn v hv F' g fr hP hSB c0 pc kk x cn τ e env n lits cs
    bufs tk kv en em hh hc0 hT hfr hat hco hhd hpt
  -- the setup frame's context with its (no) records: `CxOkH`'s witnesses as in `setupOpenF_ofPreH`
  have hcx : CxOkS (p := p) (lbl := fun _ => none) (lsize := fun _ => 0)
      (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h) j (RC) F' [fr] g.fp g.ra (TP0)
      (fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr]))
      (AbU2 p (MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0))
        (fun _ => none) (FC) (rbR (RC)) F' [fr] g.fp g.ra
        (fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr]))) := by
    obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
    have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
    have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
    have hZ := setupMC_Z _ hsw
    subst hv
    have hok : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
    have htop8 : (TOP).toNat % 8 = 0 := by
      rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
    have hR1 : ((swR (TOP) (-L) 0).callee (-8 - 0) (8 - L) 8).OK :=
      Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
        (by show _ ≤ (0 : Int); omega)
    have hb1 : (((swR (TOP) (-L) 0).callee (-8 - 0) (8 - L) 8).base.toNat : Int) = (TOP).toNat - 8 :=
      Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
    have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
      (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
    refine CxOkS.bot ⟨d, hd, L, D1, fS, nS, _, g, fr, J, hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
      ⟨hP.1, ?_, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2⟩,
      fun m hm => (hP.2.2.1 m hm).1.1.1, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨⟨J, L, D1, fS, _, D2, lS, lM, nS, fM, nM, hB, hSB⟩, d, hd, hn⟩
    omega
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  -- the setup call's return address has the phase anchor's phase
  have hra : Spike.Lib.X64.PhRec.ph (LY0) (Int64.ofBitVec g.ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph (LY0) ((LY0).lab raL).toBitVec.toNat := by
    rw [hP.2.2.2.1]
    exact raOk_setup _ _
  -- the allocation a resumption point of the block's code
  have hpt' : BodyPtW (FC) g.ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs := by
    obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := hpt
    unfold BodyPtW
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
    exact ⟨l, k, r, kk, h1, hfr, h2, h3, h4, h5, h6, h7⟩
  have hnb : NbArgs (FC).lcx env cn τ hh kv
      (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) :=
    ⟨tk, en, em, hat, hco, hhd, rfl⟩
  have hel := (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  have hst := hello1_rodata_hstub h hp hty (E := E) (El := ElG h hp) hB J hd hn hv hP (c0 := c0) (kv := kv) (en := en)
    (em := em) (hh := hh) hel hpt
  have hbl := (fnCode2OfPMe_spec hp h Λ j d hd).2.1
  have hobj' : Scc.Obj.nShift (FC).lcx.obj < 22 := by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]; exact hobj
  have W := allocPt_of_accepted2 Λ (Ly).Λ p hp j d hd (FC).lcx (FC).fr (CdR g.ra) (BlR g.ra)
    (_root_.Executable.labels (Ly).exe).label (RetLk d.retTy) kk pc env n lits cs bufs x cn τ e tk kv en em [fr]
    hat hco hpt (List.cons_ne_nil _ _)
  refine ⟨AllocPtWk.ofAr W, hms_of_elem2 h (imms2Me Λ p) hobj' hel hco hhd, ?hxa, ?hxaF, hst⟩
  case hxa =>
    intro lw zs zc k hla hzs hcla hk'
    exact landStk_hxa (Spike.Lib.X64.Rt.arOf_ok h hc) (startsN_of_startsS hJ) Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _)
  case hxaF =>
    intro lw zs zc k hla hzs hcla hk' q hq J' hJ' l b w s c hl hAt htp
    exact landStk_hxa (J := J') (Spike.Lib.X64.Rt.arOf_ok h hc) hJ' Spike.Lib.AllocReach.Reach.base hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _) ⟨q, callOK_msOfAX hq⟩ _
      (fun m hm => hm.1) (fun m hm => allocCtx_msOfAX hm.2.2) l b w s c hl hAt htp

/-- **The allocator's `W2` instance at the setup frame of any `Accepted2`
program** (`OpenAWF` at the landings `ElG` and the write tail `fun _ => True`):
`cxLB_hAW_noneV` at `openAPtV_of_accepted2`. -/
theorem openAWF_of_accepted2 (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) :
    OpenAWF h hp E (ElG h hp) (fun _ => True) :=
  cxLB_hAW_noneV h hp hty (openAPtV_of_accepted2 h hp hty hobj E)

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.allocCtx_msOfAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocCtx_msOfAX

/-- info: 'Spike.Lib.LowerX64.cxLB_hAW_noneV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxLB_hAW_noneV

/--
info: 'Spike.Lib.LowerX64.openAPtV_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.openAPtV_of_accepted2

/--
info: 'Spike.Lib.LowerX64.openAWF_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.LowerX64.openAWF_of_accepted2
