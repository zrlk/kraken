/-
**The allocator's `W2` instance at a reachable placement** (x86-64; the
twin of `Spike/Lib/LowerA64/G1AllocL.lean`): `AllocW2At` at a landings'
context (`CxOkS` over `CxOkH`, with its records at the placement) at any
placement `L`, `ls` reachable from no label, in the rebased setup callee
region `rbR R`, for any `Accepted2` program with a setup block whose object
layout puts a one-word element's header below the allocator's trace-count
field (`hobj`): `allocW2At_ofV` at `L`, `ls`, as `cxLB_hAW_noneV` and
`openAPtV_of_accepted2` (`Spike/Lib/LowerX64/G1AllocOpen.lean`) at no label.
In an `Accepted2` program only the setup block allocates, so these landing
contexts are the only ones whose `AllocW2At` is not vacuous.

The facts reading the placement:

- `rt_ctr_reach`: no reachable label meets the counter (a reachable label
  lands in the arena, `Reach.placed`, which the counter, in `.data`, is
  off);
- `callMsOK_arOfL`: `CallMsOK` at the placement (`callMsOK_arOfA`'s fields
  but the runtime reads: the counter by `rt_ctr_reach`, a header above the
  counter's floor `LoOf` by `rt_of_loOf`);
- `hsz_arOfL`: `allocW2At_ofV`'s `hsz`, vacuous above the floor;
- `cxOkH_rgn`: the setup callee region's facts at a context `CxOkH`;
- `hstubL`: `hello1_rodata_hstub` at the placement and a context `CxOkH`;
- the landings' `hxa`, `hxaF` by `landStk_hxa` at the reachable placement
  with the context's records there.

- `allocPtV_ofCxOkSL`: `AllocPtV` at every allocation at the placement;
- `allocW2AtL_ofCxOkS`: `AllocW2At` at the placement at the block's tails;
- `AllocW2At.monoT` (with `PtC2.monoT`): at any smaller walk predicate;
- `allocW2AtL_ofCxOkH`: at a context with no records (`CxOkS.bot`).
-/
import Spike.Lib.LowerX64.G1AllocOpen
import Spike.Lib.LowerX64.LevelMono2
import Spike.Lib.AllocLo

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
open Spike.Lib.X64.Rt (swFSL rS0 rtF setupMC arOf CtrZ)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.X64.Alloc (Call mOf)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

/-! ## The walk predicate -/

section Walk

/-- **The resumption facts at a larger walk predicate**: `PtC2` reads the
walk `T` only at the lowering walk's terms. -/
theorem PtC2.monoT {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {lab : Label → Int64} {i : Expr → String → Nat → Option Nat}
    {T T' : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} {kk : Nat} {pc : Int64}
    {env : Scc.Lower.Env} {n : Nat} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {t : Expr} (hT : ∀ t, T t → T' t) (h : PtC2 lcx fr Cd Bl lab i T Lk kk pc env n lits cs bufs t) :
    PtC2 lcx fr Cd Bl lab i T' Lk kk pc env n lits cs bufs t := by
  obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨l, k, r, h1, h2, h3, fun q hq => ?_, h5, h6, h7⟩
  obtain ⟨a, b, c, d, e⟩ := h4 q hq
  exact ⟨a, hT _ b, c, d, e⟩

/-- **`AllocW2At` at a smaller walk predicate**: it reads the walk only in
its premises (the term's, `PtC2`'s, `PtC2.monoT`). -/
theorem AllocW2At.monoT {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Spike.Lib.Frag isa}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T T' : Expr → Prop}
    {Lk : Expr × List (String × Scc.Lower.LitV) → Prop} (hT : ∀ t, T' t → T t)
    (H : AllocW2At p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk) :
    AllocW2At p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T' Lk :=
  fun c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT' hfr hat hco hhd hpc =>
    H c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 (hT _ hT') hfr hat hco hhd (hpc.monoT hT)

end Walk

/-! ## The arena's memory side at a reachable placement -/

section Place

variable {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
  {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS} {I : InvS}
  {fs : List TermRun.Frame}

/-- **No label reachable from none meets the counter**: a reachable label
lands in the arena (`Reach.placed`), inside the heap, which `.data`, where
the counter is, is disjoint from. -/
theorem rt_ctr_reach (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) {L : Lbl} {ls : Lsize}
    (hR : Reach (arOf Λ) (fun _ => none) (fun _ => 0) L ls) :
    ¬ ∃ l b, L l = some b ∧ (lrange ls l b).contains (heapUseOf Λ) := by
  rintro ⟨l, b, hl, hcb⟩
  rcases hR.placed hl with ⟨h0, -⟩ | ⟨h1, h2, -⟩
  · cases h0
  · have hd := Spike.Lib.X64.Rt.ctr_data_of_placeOKAt h hc
    have hdh := (wf_of_placeOKAt h).disjoint.2.2.2.1
    have hsz := heapSize_of_placeOKAt h
    have e1 : (arOf Λ).heap = Λ.heap.lo := rfl
    have e2 : (arOf Λ).cells = allocCells := rfl
    simp only [e1, e2] at h1 h2
    simp only [lrange, Range.contains, Range.Disjoint] at hcb hd hdh
    omega

/-- **`CallMsOK` at the rows' memory side over the arena `arOf Λ` at a
placement reachable from none**, at either write abort phase `ab`:
`callMsOK_arOfA`'s fields but the runtime reads, which the placement's
labels may meet: the counter by `rt_ctr_reach`, a fitting header above the
counter's floor (`MemSide.lo`, `LoOf`) by `rt_of_loOf` (the header at the
cursor, in the free range). -/
theorem callMsOK_arOfL (h : placeOKAt cfg Λ o = true) (hc : CtrZ o) (E : Entry) (ab : Option (State → Prop))
    (hGc : ∀ v, G ⟨BitVec.ofNat 64 (arOf Λ).ctr, 8⟩ v)
    (hGh : ∀ a : BitVec 64, (∀ i < 8, Λ.heap.contains (a.toNat + i)) → ∀ v, G ⟨a, 8⟩ v)
    {L : Lbl} {ls : Lsize} (hR : Reach (arOf Λ) (fun _ => none) (fun _ => 0) L ls)
    {q : Call} (hacc : ∃ us, TermRun.accs (TermRun.close [] q.τ) = some us) (hm : (mOf q.h).toNat = 0) :
    CallMsOK (msOfAX Λ μ p rd G own (arOf Λ) I ab L ls fs)
      (_root_.Executable.labels
        (Scc.Sem.X64.threadAt E Λ.code.lo o.prog (Scc.Sem.loadSyms Λ o.secs.rodata)).exe).label q := by
  have H := callMsOK_arOfA (μ := μ) (rd := rd) (own := own) (I := I) (ls := ls) (fs := fs) h hc E hGc hGh hacc hm
  obtain ⟨ec, -⟩ := ctr_bytes_arOf h hc
  have hu1 : 1 ≤ (arOf Λ).units q.n q.τ := arOf_units_pos hacc
  have hnm : q.n * (mOf q.h).toNat = 0 := by rw [hm, Nat.mul_zero]
  have hrtc : ¬ ∃ l b, L l = some b ∧ (lrange ls l b).contains (BitVec.ofNat 64 (arOf Λ).ctr).toNat := by
    rw [ec]; exact rt_ctr_reach h hc hR
  have hhdr : ∀ o', Spike.Lib.AllocLo.LoOf (arOf Λ).heap (arOf Λ).cells L ls o' →
      o' + (arOf Λ).units q.n q.τ ≤ (arOf Λ).cells →
      ¬ ∃ l b, L l = some b ∧
        (lrange ls l b).contains ((arOf Λ).heap + 16 * o' + 8 * (q.n * (mOf q.h).toNat)) := by
    intro o' hlo ho
    refine Spike.Lib.AllocLo.rt_of_loOf hlo ?_
    rw [hnm]
    simp only [Spike.Lib.AllocRow.freeR, Range.contains]
    omega
  have hlo0 : ∀ o', Spike.Lib.AllocLo.LoOf (arOf Λ).heap (arOf Λ).cells (fun _ => none) ls o' :=
    fun _ _ _ h0 => by cases h0
  cases ab
  · exact ⟨H.ctr, H.heap, H.room, H.cells, H.units, H.off, hrtc, H.mp, H.grow,
      fun o' hlo ho => ⟨hhdr o' hlo ho, (H.hdr o' (hlo0 o') ho).2⟩⟩
  · exact ⟨H.ctr, H.heap, H.room, H.cells, H.units, H.off, hrtc, H.mp, H.grow,
      fun o' hlo ho => ⟨hhdr o' hlo ho, (H.hdr o' (hlo0 o') ho).2⟩⟩

/-- **`allocW2At_ofV`'s `hsz` at the rows' memory side over `arOf Λ`**, at
any placement: vacuous above the counter's floor (`LoOf`), an object
returned at the cursor `old` being past its first word (`arOf_off_eq`) and
inside the arena (`arOf_units_pos`). -/
theorem hsz_arOfL {ab : Option (State → Prop)} {L : Lbl} {ls : Lsize} {lab : Label → Int64} :
    ∀ q : Call, q.OK (msOfAX Λ μ p rd G own (arOf Λ) I ab L ls fs) lab → ∀ l b old, L l = some b →
      (msOfAX Λ μ p rd G own (arOf Λ) I ab L ls fs).lo old →
      b = (arOf Λ).heap + 16 * old + (arOf Λ).off q.n q.τ → old + (arOf Λ).units q.n q.τ ≤ (arOf Λ).cells →
      q.n ≤ ls l := by
  intro q hq l b old hl hlo hb hold
  have hlo' : Spike.Lib.AllocLo.LoOf (arOf Λ).heap (arOf Λ).cells L ls old := by cases ab <;> exact hlo
  have hu1 := arOf_units_pos (Λ := Λ) (n := q.n) hq.accs
  rw [arOf_off_eq hq.accs] at hb
  exact absurd ⟨by omega, by omega⟩ (hlo' l b hl).2

end Place

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)
set_option hygiene false in
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)
set_option hygiene false in
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)
set_option hygiene false in
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)
set_option hygiene false in
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs
set_option hygiene false in
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m
set_option hygiene false in
/-- The frame invariant `J` holds at the starts of the landings `ElG`
(`OpenAWF`'s at the write tail `fun _ => True`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (WNF) (ElG h hp) (fun _ => True) (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs
set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64
set_option hygiene false in
/-- The `j`th block's code. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd
set_option hygiene false in
/-- The `j`th block's frame. -/
local notation "FR" => (fnCode2OfPMe hp h Λ j d hd).fr
set_option hygiene false in
/-- A context's code at its return address `ra`. -/
local notation "CdR" ra:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (Int64.ofBitVec ra)
set_option hygiene false in
/-- A context's calls at its return address `ra`. -/
local notation "BlR" ra:max => BlC2L OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab
  (FC).fr (Int64.ofBitVec ra)
set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))
set_option hygiene false in
/-- **The rows' memory side at the placement `L`, `ls`** over `IN … J`. -/
local notation "MSL" J:max L:max ls:max => msOfAX (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
  (Spike.Lib.X64.PhRec.GOf Ly M0) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (arOf (Ly).Λ)
  (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls fs
set_option hygiene false in
/-- **The allocation's call node** at the `callq` at `pcB` of size `zc`, at
the placement `L`, `ls`, in the rebased region `rbR R`. -/
local notation "NJL" pcB:max zc:max L:max ls:max => nbJc (_root_.Executable.labels (Ly).exe).label
  [(Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel Scc.Lower.Names.alloc)), zc)] pcB (oB FR)
  (nbJ1 p L ls FR (rbR R) fp ra tp c0 (.let_ x (.newBuf cn τ) e) env lits cs bufs
    (Scc.Lower.imm hh) (.imm kv) (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))

/-- **The setup callee region's facts at a landings' context** `CxOkH` (as
`hello1_rodata_hstub` and `cxLB_hAW_noneV` from the bounds and `PREF`): the
region holds the frame of the `rodata` block with the allocator's frame and
the dispatcher's bytes below it (`fS + 8 ≤ nS`, `nS + 48 + 208 ≤ D1`), the
rebased region 8-aligned, the stack off the rebased region (the switch
region's top the first stack's, `stackOff_callee` twice, `stackOff_rbR`). -/
theorem cxOkH_rgn (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') :
    R.OK ∧ R.lo ≤ -8 ∧ R.hi = 8 ∧ R.lo % 8 = 0 ∧ R.lo + 8 ≤ -((FC).fr.size : Int) - 200 ∧
      (rbR R).base.toNat % 8 = 0 ∧ FStable R F ∧ (∀ m, F m → StackOff (rS0 (Ly)) (rbR R) m) := by
  obtain ⟨d', hd', L1, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF, hFF, -, -, -, -⟩, -, -, hRe, -, -, -, -, -, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  subst hRe
  have hlo1 : (((swR v (-L1) 0).callee (-8 - 0) (8 - L1) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤ -8 := by
    show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (((swR v (-L1) 0).callee (-8 - 0) (8 - L1) 8).callee
      (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
    show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  refine ⟨hR0, hlo1, rfl, by show (-D1) % 8 = 0; omega, by show -D1 + 8 ≤ _; rw [hframe]; omega,
    by omega, hF, fun m hm => ?_⟩
  refine stackOff_rbR hR0 hlo1 hhi1 ?_
  obtain ⟨⟨⟨-, ⟨hvt, -⟩, hso⟩, hcc1⟩, hcc2⟩ := hFF m hm
  subst hvt
  have hok : (swR (TOP) (-L1) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : ((swR (TOP) (-L1) 0).callee (-8 - 0) (8 - L1) 8).OK :=
    Region.callee_ok hok (by show -L1 ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : (((swR (TOP) (-L1) 0).callee (-8 - 0) (8 - L1) 8).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L1 ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : ((swR (TOP) (-L1) 0).callee (-8 - 0) (8 - L1) 8).base.toNat % 8 = 0 := by omega
  exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L1) % 8 = 0; omega)
    (by show (8 : Int) % 8 = 0; decide) (by show 8 - L1 ≤ _; omega) (by omega)
    (by show _ < (8 : Int); omega) (by omega)
    (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L1) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) (by show -L1 ≤ _; omega) (by omega)
      (by show _ < (0 : Int); omega) (by decide) hso hcc1)
    hcc2

/-- **`AllocPtV.hstub` at a reachable placement and a landings' context**
(`hello1_rodata_hstub` at `L`, `ls` and `CxOkH`): the allocator's heap abort
path's obligations without code inside `W2` at the record at the placement
(`hstub_ofNbJc` in the rebased region `rbR R`, `cxOkH_rgn`, at the call node
`nbJcOf_nbJ1`, the frame `[fr]` placed at no label and so at `L`,
`FramesPlacedInI.mono_lbl`; the write tail `fun _ => True`). -/
theorem hstubL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa} {L : Lbl} {ls : Lsize}
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab') {J : InvS}
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
      (CdR ra) pc ((dirs lw).zip zs) → (BlR ra) (pc + Int64.ofNat zs.sum) zc Scc.Lower.Names.alloc k →
      ∀ q : Call, q.OK (MSL J L ls) (_root_.Executable.labels (Ly).exe).label →
        ∀ J' : InvS, (∀ L ls, Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls → ∀ s c fs,
          StartsN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) (S0X h E (WNF)) El L ls s c fs → J' L ls s c fs) →
        ∀ m0 σC c0', (HeldAb (_root_.Executable.labels (Ly).exe).label (MSL J' L ls) q L (rbR R)
          (FR).size (fun σC => (NJL (pc + Int64.ofNat zs.sum) zc L ls) σC q.c0)).J σC c0' →
        StubHN (fun s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
            (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly))
            (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J')
            (fun _ => True) (Ab (Ly).lab) L ls s c fs)
          (KT) (MSL J' L ls) (Ly).exe (Ly).endPc
          ((rbR R).callee (-((FR).size : Int) - 8 + -160 - 8) (-24) 16)
          (fun m => F m ∧ CKept (rbR R) (-((FR).size : Int) - 8 + -160 - 8) (-24) 16 m0 m ∧
            Abs (rbR R) ⟨-((FR).size : Int) - 8 + -160, []⟩ m0 σC) c0' := by
  intro lw zs zc k _ _ _ _ q hq J' _
  obtain ⟨hR0, hlo1, hhi8, hl8, hlo, hb8, hF', hFO⟩ := cxOkH_rgn h hp hty hd hc
  obtain ⟨-, -, -, -, -, -, -, g, fr, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, hct, -⟩, -, -, -,
    rfl, -, -, -, -, -⟩ := hc
  have hJc := nbJcOf_nbJ1 (fnCode2OfPMe hp h Λ j d hd).hf (p := p) (lbl := L) (lsize := ls)
    (R := rbR R) (fp := fp) (ra := ra) (tp := tp) (c0 := c0) (lits := lits) (cs := cs) (bufs := bufs)
    (a0 := Scc.Lower.imm hh) (a1 := .imm kv)
    (a2 := Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)
    (_root_.Executable.labels (Ly).exe).label (pc + Int64.ofNat zs.sum) zc hel
    (PtC2.newBufW hpt).1 (PtC2.newBufW hpt).2.1 (PtC2.newBufW hpt).2.2.1
  exact hstub_ofNbJc h (imms2Me Λ p) (fnCode2OfPMe hp h Λ j d hd).hf (rbR_ok hR0 hlo1 (by omega)) hb8
    (by
      simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]
      show R.lo + 8 ≤ _; omega)
    (by show (0 : Int) ≤ R.hi + 8; omega) (by show (R.lo + 8) % 8 = 0; omega)
    (by show (R.hi + 8) % 8 = 0; omega) (rbR_fstable hR0 hlo1 (by omega) hF')
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hFO
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (fun _ _ h0 => by cases h0) hB)
    (fun _ _ _ _ _ _ => trivial) hJc q (callOK_msOfAX hq)

/-- **`AllocPtV` at every allocation at a reachable placement**
(`openAPtV_of_accepted2` at `L`, `ls`): at a landings' context `CxOkS` at
the placement (the context `CxOkH` with its records), for any family `J`
containing the starts, in the rebased region `rbR R`: the walk fields by
`allocPt_of_accepted2`, `hms` by `callMsOK_arOfL`, `hxa`, `hxaF` by
`landStk_hxa` at the reachable placement and `hstub` by `hstubL`. -/
theorem allocPtV_ofCxOkSL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) {J : InvS} (hJ : StJ J) {L : Lbl} {ls : Lsize}
    (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa}
    (hcx : CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h) j R F fs fp ra tp
      G0 Ab')
    {c0 : Ctl} {pc : Int64} {kk : Nat} {x : String} {cn : At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {tk : Ty} {kv : UInt64}
    {en em hh : Nat} (hc0 : G0 c0) (hT : TailAt2 p j (.let_ x (.newBuf cn τ) e))
    (hfr : Spike.Lib.LowerNode.Fresh env n) (hat : Scc.Lower.Inv.atomV env cn = some (tk, [.imm kv]))
    (hco : Spike.Lib.LowerShape.countsO (FC).lcx.obj τ = some (en, em))
    (hhd : Scc.Obj.header0 (FC).lcx.obj .array en em = some hh)
    (hpt : PtC2 (FC).lcx (FC).fr (CdR ra) (BlR ra) (_root_.Executable.labels (Ly).exe).label
      (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) kk pc env n lits cs bufs (.let_ x (.newBuf cn τ) e)) :
    AllocPtV (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
      (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
      (fun _ => none) (fun _ => 0) (S0X h E (WNF)) (ElG h hp) J (ab2 p (Ly).lab) (fun _ => True) (LY0).lab
      ((Ly).lab StackTake.siteL) L ls fs (Ly).exe (Ly).endPc (rbR R) F
      (FC).fr (CdR ra) (BlR ra) fp ra tp c0 pc x cn τ e env lits cs bufs hh kv
      (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) := by
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  have hC := hcx.1
  -- the setup call's return address has the phase anchor's phase
  have hra : Spike.Lib.X64.PhRec.ph (LY0) (Int64.ofBitVec ra).toBitVec.toNat =
      Spike.Lib.X64.PhRec.ph (LY0) ((LY0).lab raL).toBitVec.toNat := by
    obtain ⟨-, -, -, -, -, -, -, g, fr, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, hgra, -⟩, -, -, -, -, -,
      hra, -⟩ := id hC
    rw [hra, hgra]
    exact raOk_setup _ _
  have hfs : fs ≠ [] := by
    obtain ⟨-, -, -, -, -, -, -, -, fr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfs, -⟩ := id hC
    rw [hfs]; exact List.cons_ne_nil _ _
  -- the allocation a resumption point of the block's code
  have hpt' : BodyPtW (FC) ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs := by
    obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := hpt
    unfold BodyPtW
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
    exact ⟨l, k, r, kk, h1, hfr, h2, h3, h4, h5, h6, h7⟩
  have hnb : NbArgs (FC).lcx env cn τ hh kv
      (Spike.Lib.LowerShape.unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) :=
    ⟨tk, en, em, hat, hco, hhd, rfl⟩
  have hel := (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1
  have hbl := (fnCode2OfPMe_spec hp h Λ j d hd).2.1
  have hobj' : Scc.Obj.nShift (FC).lcx.obj < 22 := by
    rw [(fnCode2OfPMe_spec hp h Λ j d hd).1]; exact hobj
  have W := allocPt_of_accepted2 Λ (Ly).Λ p hp j d hd (FC).lcx (FC).fr (CdR ra) (BlR ra)
    (_root_.Executable.labels (Ly).exe).label (RetLk d.retTy) kk pc env n lits cs bufs x cn τ e tk kv en em fs
    hat hco hpt hfs
  refine ⟨AllocPtWk.ofAr W, ?hms, ?hxa, ?hxaF, hstubL h hp hty hd hC hel hpt⟩
  case hms =>
    intro q _ hτ hqh
    obtain ⟨-, us, hus, -⟩ := elem2_words_accs hel
    exact callMsOK_arOfL (Λ := (Ly).Λ) h hc Scc.Sem.Entry.linux _
      (gOf_ctr_arOf h (imms2Me Λ p) _) (gOf_heap_arOf h (imms2Me Λ p) _) hR
      (by rw [hτ]; exact ⟨us, hus⟩) (by rw [hqh]; exact mOf_header_elem2 hobj' hel hco hhd)
  case hxa =>
    intro lw zs zc k hla hzs hcla hk'
    exact landStk_hxa (Spike.Lib.X64.Rt.arOf_ok h hc) (startsN_of_startsS hJ) hR hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _)
  case hxaF =>
    intro lw zs zc k hla hzs hcla hk' q hq J' hJ' l b w s c hl hAt htp
    exact landStk_hxa (J := J') (Spike.Lib.X64.Rt.arOf_ok h hc) hJ' hR hd
      hcx hra hc0 hpt' hnb hla hzs hcla (by rw [hbl]; exact hk') (arOf_units_fit _) ⟨q, callOK_msOfAX hq⟩ _
      (fun m hm => hm.1) (fun m hm => allocCtx_msOfAX hm.2.2) l b w s c hl hAt htp

/-- **The allocator's `W2` instance at a landings' context at a reachable
placement** (`allocW2At_ofV` at `L`, `ls`, as `cxLB_hAW_noneV` at no label):
for any family `J` containing the starts of the landings `ElG`, at a
placement `L`, `ls` reachable from none and a context `CxOkS` there, in the
rebased region `rbR R`: the region's facts by `cxOkH_rgn`, the frame placed
at no label and so at `L` (`FramesPlacedInI.mono_lbl`), the arena's words
from `ArCallMs` at `CxOkH`'s `WordsNone`, the labels' sizes vacuous above
the floor (`hsz_arOfL`), each allocation by `allocPtV_ofCxOkSL`. -/
theorem allocW2AtL_ofCxOkS (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) {J : InvS} (hJ : StJ J) {L : Lbl} {ls : Lsize}
    (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa}
    (hcx : CxOkS (p := p) (lbl := L) (lsize := ls) (fnCode2OfPMe hp h Λ) (CxOkH h hp) (BotH h) j R F fs fp ra tp
      G0 Ab') :
    AllocW2At p L ls (FC).lcx (FC).fr (CdR ra) ((FC).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Ab (Ly).lab) lbl lsize
        s c fs)
      (KT) (Ly).exe (Ly).endPc (rbR R) F (MSL J L ls) fp ra tp G0 (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy) := by
  have hC := hcx.1
  obtain ⟨hR0, hlo1, hhi8, hl8, hlo, hb8, hF', hFO⟩ := cxOkH_rgn h hp hty hd hC
  obtain ⟨-, -, -, -, -, -, -, g, fr, -, -, -, -, -, -, -, -, -, -, ⟨-, -, -, -, -, -, hct, -⟩, hwn, -, -,
    rfl, -, -, -, rfl, -⟩ := hC
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo0 : (rbR R).lo ≤ -((FC).fr.size : Int) := by show R.lo + 8 ≤ _; omega
  have hhi : (0 : Int) ≤ (rbR R).hi := by show (0 : Int) ≤ R.hi + 8; omega
  have hc := Spike.Lib.X64.Rt.ctrZ_ofPlaceOK h
  haveI : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨-, -, -, -, hH, hCt, hU, hO, hCl, -⟩ := msOfAX_fields (Λ := (Ly).Λ) (μ := Spike.Lib.X64.PhRec.μ (Ly))
    (p := p) (rd := Spike.Lib.LowerNode.IsNum) (G := Spike.Lib.X64.PhRec.GOf Ly M0)
    (own := fun s _ => Spike.Lib.X64.PhRec.own (Ly) s)
    (ar := arOf (Ly).Λ) (I := IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (lbl := L) (lsize := ls)
    (fs := [fr]) (ab2 p (Ly).lab)
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1]
  exact allocW2At_ofV (ownOf := Spike.Lib.X64.PhRec.ownOf (Ly))
    (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Λ p) (rS := rS0 (Ly))) (allocIn_of_placeOKAt h)
    (Spike.Lib.X64.PhRec.allocPhOk_ofPlaceOK h (Scc.Lower.imms2Of p))
    (Spike.Lib.X64.PhRec.allocAbOk_ofPlaceOK h (Scc.Lower.imms2Of p)) (printIn_of_placeOKAt h)
    (abortIn_of_placeOKAt h) (fun _ => rfl) (FC).hf (FC).h1 (FC).h16 (rbR_ok hR0 hlo1 (by omega)) hb8
    (by show (R.lo + 8) % 8 = 0; omega) (by show (R.hi + 8) % 8 = 0; omega)
    (by show R.lo + 8 ≤ -((FC).fr.size : Int) - 8 + -160 - 32; omega)
    (by show (16 : Int) ≤ R.hi + 8; omega) (rbR_fstable hR0 hlo1 (by omega) hF')
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) hFO hpN hJ
    hR (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (fun _ _ h0 => by cases h0) hB)
    (fun _ _ hr => regionOff_of_rsOf (FC).hf hlo0 hhi hr)
    (fun q hq a ha => hmem_arOf h hc (fun m hm => hwn m hm) hH hCl hCt hU hO q hq a
      (by rw [hCt, hU, hCl]; exact ha))
    (hno_arOf h (imms2Me Λ p) hH hO) (hlt_arOf h hc) (h64_arOf h hc)
    hsz_arOfL
    (fun x cn τ e hT => (Spike.Lib.LowerNode.newBufK_of_accepted2 hp hd hT).1)
    (fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2 hty _)))
    (fun c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT hfr hat hco hhd hpt =>
      allocPtV_ofCxOkSL h hp hty hobj E hJ hR hd hcx hc0 hT hfr hat hco hhd hpt)

/-- **At a landings' context with no records** (`allocW2AtL_ofCxOkS` at
`CxOkS.bot`), at any walk predicate `T` within the block's tails. -/
theorem allocW2AtL_ofCxOkH (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hobj : Scc.Obj.nShift cfg.layout.obj < 22) (E : Entry) {J : InvS} (hJ : StJ J) {L : Lbl} {ls : Lsize}
    (hR : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab' : FragS isa} (hC : CxOkH h hp j R F fs fp ra tp G0 Ab')
    (hB : BotH h ⟨j, R, F, fp, ra, tp, G0⟩ fs) {T : Expr → Prop} (hT : ∀ t, T t → TailAt2 p j t) :
    AllocW2At p L ls (FC).lcx (FC).fr (CdR ra) ((FC).Bl ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Ab (Ly).lab) lbl lsize
        s c fs)
      (KT) (Ly).exe (Ly).endPc (rbR R) F (MSL J L ls) fp ra tp G0 (imms2Me Λ p) T (RetLk d.retTy) :=
  AllocW2At.monoT hT (allocW2AtL_ofCxOkS h hp hty hobj E hJ hR hd (CxOkS.bot hC hB))

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.PtC2.monoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PtC2.monoT

/-- info: 'Spike.Lib.LowerX64.AllocW2At.monoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.AllocW2At.monoT

/-- info: 'Spike.Lib.LowerX64.rt_ctr_reach' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.rt_ctr_reach

/-- info: 'Spike.Lib.LowerX64.callMsOK_arOfL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.callMsOK_arOfL

/-- info: 'Spike.Lib.LowerX64.hsz_arOfL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hsz_arOfL

/-- info: 'Spike.Lib.LowerX64.cxOkH_rgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxOkH_rgn

/-- info: 'Spike.Lib.LowerX64.hstubL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hstubL

/-- info: 'Spike.Lib.LowerX64.allocPtV_ofCxOkSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocPtV_ofCxOkSL

/-- info: 'Spike.Lib.LowerX64.allocW2AtL_ofCxOkS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2AtL_ofCxOkS

/-- info: 'Spike.Lib.LowerX64.allocW2AtL_ofCxOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2AtL_ofCxOkH
