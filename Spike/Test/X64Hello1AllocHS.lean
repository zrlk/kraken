/-
**`AllocPtW.hstub` at the setup frame's allocation of `OpenAWF`'s
instance** (x86-64): the heap abort path's obligations without code inside
`W2` at the record, at the allocator's `W2` instance at the setup frame
(`OpenAWF`, `Spike/Test/X64Hello1HolesW.lean`) for every choice of the
bounds (`Bounds2`), at an allocation of the `rodata` block placed by its
resumption facts (`PtC2`): `hstub_ofNbJc`
(`Spike/Test/X64Hello1AllocStub.lean`) in the rebased setup callee region
`rbR RC`, the call node `NbJcOf` by `nbJcOf_nbJ1` at the walk's facts
(`PtC2.newBufW`).

The region's facts are `PREF`'s and the bounds' (as `setupOpenF_ofPre` and
`hAW_CxOkHX`): the region below the allocator's frame and the dispatcher's
`32` bytes past the frame row (`fS + 8 ≤ nS`, `nS + 48 + 208 ≤ D1`), the
stack off it by `stackOff_callee` twice and `stackOff_rbR`, the frame `[fr]`
placed (`framesPlaced_setup`); the write tail `fun _ => True`.

- `hello1_rodata_hstub`: `AllocPtW.hstub` at `OpenAWF`'s instance.
-/
import Spike.Test.X64Hello1HolesW
import Spike.Test.X64Hello1AllocStub

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable CKept Abs)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbJc)
open Spike.Lib.X64.Rt (swFSL rS0 rtF setupMC arOf)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

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
/-- **The start's frame condition** (`Closed2AtW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

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
/-- The `rodata` block's frame (`fnCode2OfPMe`'s). -/
local notation "FR" => (fnCode2OfPMe hp h Λ j d hd).fr

set_option hygiene false in
/-- **`AllocPtW`'s memory side at `OpenAWF`'s instance** over `IN … J`
(`MSAt`'s at the nodes' abort `ab2`, the frame `[fr]`). -/
local notation "MSX" J:max => msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
  (Spike.Lib.X64.PhRec.GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (arOf (Ly).Λ)
  (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) (fun _ => none) (fun _ => 0) [fr]

set_option hygiene false in
/-- **The allocation's call node** at the `callq` at `pcB` of size `zc`
(`AllocPtW`'s `NJ` at `OpenAWF`'s instance). -/
local notation "NJX" pcB:max zc:max => nbJc (_root_.Executable.labels (Ly).exe).label
  [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] pcB (oB FR)
  (nbJ1 p (fun _ => none) (fun _ => 0) FR (rbR (RC)) g.fp g.ra (TP0) c0 (.let_ x (.newBuf cn τ) e) env lits cs
    bufs (Scc.Lower.imm hh) (.imm kv) (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-- **`AllocPtW.hstub` at `OpenAWF`'s instance**: at every choice of the
bounds (`hB`), family `J`, the `rodata` block (`hd`, `hn`) at the first
stack's top (`hv`), a setup call's premises `PREF` (`hP`) and an allocation
`let x = newBuf cn τ in e` of an `elem2` element type (`hel`) placed by its
resumption facts (`hpt`), the allocator's heap abort path's obligations
without code inside `W2` at the record (`hstub_ofNbJc` in the rebased
setup callee region `rbR RC`, the frame `fr` placed, the write tail
`fun _ => True`), the field's shape at the start's states `S0X h E WNF`,
the landings' `El`, the code `CdCLE … g.ra` and calls `BlC2L … g.ra`. -/
theorem hello1_rodata_hstub (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 cfg p sizes labelOffs (Ly) L D1 D2 lS lM fS nS fM nM) (J : InvS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {v : BitVec 64} (hv : v = TOP) {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame}
    (hP : PREF F' g fr)
    {c0 : Ctl} {pc : Int64} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {kv : UInt64} {en em hh : Nat}
    (hel : Scc.Lower.elem2 τ = true)
    {lcx : Scc.Lower.Ctx} {Cd' : Int64 → List (Directive × Nat) → Prop} {Bl' : Int64 → Nat → Label → Nat → Prop}
    {lab' : Label → Int64} {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} {kk n : Nat}
    (hpt : PtC2 lcx FR Cd' Bl' lab' (imms2Me Λ p) T Lk kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    ∀ (lw : List Scc.Emit.X64.Item) (zs : List Nat) (zc k : Nat),
      getOps FR ([Scc.Lower.imm hh, .imm kv,
          Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv].zip Scc.Emit.X64.argRegs) =
        .ok lw → zs.length = (dirs lw).length →
      CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra) pc
        ((dirs lw).zip zs) →
      BlC2L OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab FR (Int64.ofBitVec g.ra)
        (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (MSX J) (_root_.Executable.labels (Ly).exe).label →
        ∀ J' : InvS, (∀ L ls, Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls → ∀ s c fs,
          StartsN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) (S0X h E (WNF)) El L ls s c fs → J' L ls s c fs) →
        ∀ m0 σC c0', (HeldAb (_root_.Executable.labels (Ly).exe).label (MSX J') q (fun _ => none) (rbR (RC))
          (FR).size (fun σC => (NJX (pc + Int64.ofNat zs.sum) zc) σC q.c0)).J σC c0' →
        StubHN (fun s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
            (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
            (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J')
            (fun _ => True) (Ab (Ly).lab) (fun _ => none) (fun _ => 0) s c [fr])
          (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) (MSX J') (Ly).exe (Ly).endPc
          ((rbR (RC)).callee (-((FR).size : Int) - 8 + -160 - 8) (-24) 16)
          (fun m => F' m ∧ CKept (rbR (RC)) (-((FR).size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
            Abs (rbR (RC)) ⟨-((FR).size : Int) - 8 + -160, []⟩ m0 σC) c0' := by
  intro lw zs zc k _ _ _ _ q hq J' _
  subst hv
  obtain ⟨-, hfS, -, hnS, -, -, -, -, -, -, hrow, -, hL0, hLm, hL8, -, hD18, -, -, -, hL1, -⟩ := id hB
  obtain ⟨hR0, hF', hFF, -, -, hct, -⟩ := hP
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  -- the regions: the switch region, its callee `RS TOP`, the setup call's `RC`
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
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo1 : ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤ -8 := by
    show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
    show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hJc := nbJcOf_nbJ1 (fnCode2OfPMe hp h Λ j d hd).hf (p := p) (lbl := fun _ => none) (lsize := fun _ => 0)
    (R := rbR ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)) (fp := g.fp)
    (ra := g.ra) (tp := TP0) (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs) (a0 := Scc.Lower.imm hh)
    (a1 := .imm kv) (a2 := Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
    (_root_.Executable.labels (Ly).exe).label (pc + Int64.ofNat zs.sum) zc hel
    (PtC2.newBufW hpt).1 (PtC2.newBufW hpt).2.1 (PtC2.newBufW hpt).2.2.1
  exact hstub_ofNbJc h (imms2Me Λ p) (fnCode2OfPMe hp h Λ j d hd).hf (rbR_ok hR0 hlo1 hhi1) (by omega)
    (by
      simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]
      show -D1 + 8 ≤ _; rw [hframe]; omega)
    (by show (0 : Int) ≤ 8 + 8; decide) (by show (-D1 + 8) % 8 = 0; omega)
    (by show ((8 : Int) + 8) % 8 = 0; decide) (rbR_fstable hR0 hlo1 hhi1 hF')
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
    (fun m hm => stackOff_rbR hR0 hlo1 hhi1
      (Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
        (hFF m hm).2))
    (fun s _ => framesPlaced_setup h hp hty hct s) (fun _ _ _ _ _ _ => trivial) hJc q (callOK_msOfAX hq)

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_rodata_hstub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_rodata_hstub
