/-
**Every base context's aborts never end** (x86-64; the twin of
`Spike/Lib/LowerA64/G1AbG2.lean`): `AbG2`
(`Spike/Lib/LowerX64/G1FnSpec.lean`, the aborts of every context with
`CxCore2`) as a segment to the empty fragment inside the assembled
theorem's `W2`, so that a base context's aborts' fragment can be `AbG2`
itself (the setup frame's). Its three kinds, at any frames `fs` of the
context:

- the overflow label (`abortN2`, the jump of a checked `+` to the
  function's `.ovf` block): `ovfAb_segF`, `ovfAb_seg`
  (`Spike/Lib/LowerX64/MainAbX.lean`) at any suspended frames, by
  `ovfSeg2A` (`ovfSeg2` by `Local.seg_localW_adv`: no condition on the
  outside moves); the block's code from the placement check when the walk
  reaches a `+` (`ovfFacts_me`, by `lowerC2_add_blocks`);
- a buffer allocation's heap abort exit (`nbX … .abort`): `heapAb_seg`;
- an abort of the output call (`printNAS`): `printAb_segP`.

The room below each context's frame is the stack need table's row with the
slack `256` (`CxCore2.room`), at least the frame, the saved `%rbp` and the
slack (`Room2OwnStmt`, a premise); the write tails at the abort stubs'
`write` calls are premises (`hDtO`, `hDtW`, `hDtH`).

- `ovfSeg2A`, `ovfAb_segF`: the overflow label at frames `fs`;
- `ovfFacts_me`: the overflow block's code and phase at a compiled block
  whose walk reaches a `+`;
- `noS_of_tailOf`: a tail of a `ZBad`-free body is `ZBad`-free;
- `at_F`: a node's states have memories in its frame condition;
- `abCx_seg`: one context's aborts never end;
- `abG2_seg`: every context's.
-/
import Spike.Lib.LowerX64.G1FnSpec
import Spike.Lib.LowerX64.MainAbX
import Spike.Lib.LowerX64.PrintAbP
import Spike.Lib.LowerX64.HeapAbX
import Spike.Lib.LowerX64.AbortSeg2
import Spike.Lib.LowerX64.FnCode2Of
import Spike.Lib.LowerX64.FnCode2Me
import Spike.Lib.LowerAddChk2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64

/-! ## The overflow label at any frames -/

section Seg

open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl}

/-- **The overflow abort label is a segment with frames, with no condition
on the outside moves** (`ovfSeg2` by `Local.seg_localW_adv` at the block's
own invariant): from `abortN2` at frames `fs`, inside `W` at `fs`, given
the block's code (`hblk`), its states inside `W` (`hW`), the abort code and
the overflow abort path's obligations without code (`StubON`). -/
theorem ovfSeg2A {W : FragS isa} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa}
    {fs : List TermRun.Frame} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64}
    (hblk : blockAtB cells (ovfL fr) 0 ovfBlk = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 40) (hhi : -(fr.size : Int) ≤ R.hi)
    (h8 : (fr.size : Int) % 8 = 0) (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hW : BlkW (fun s c => W s c fs) K exe endPc R F
      (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0) Abort.Local.lb)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -24 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) → R' = R.callee (-(fr.size : Int) - 8 - 8) (-24) 16 →
      ∀ c1, (∃ σ0, (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J σ0 c1) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨-(fr.size : Int) - 8, []⟩ mC σC ∧
        (∀ k, k ≠ -(fr.size : Int) - 8 → σC.slot k = σ0.slot k) ∧
        (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J σ0 c1 ∧
        ∀ k, R.Off k → ¬ R'.Off (k - (-(fr.size : Int) - 8 - 8)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubON (fun s c => W s c fs) K (ms fs) exe endPc R' F' c1)
    (Q : FragS isa) :
    SegWS W K p lbl ms
      ((At exe endPc R F (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0)).at fs) Q := by
  have h0 := Abort.Local.seg_localW_adv (p := p) (lbl := lbl) (ms := ms fs) (Q := fun _ _ => False)
    (o := oB fr) (pcA := (_root_.Executable.labels exe).label (ovfL fr))
    (JA := (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J)
    (JB := (abortN2 i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J)
    hF hR hlo hhi (by simp only [oB]; omega) hK (ovfCode_codeAt hp hend hblk) hW (fun _ c hJ => ⟨c, .refl c, hJ⟩)
    (fun R' F' hR' hlo' hhi' hF' hFF' hRe c1 hJ hm =>
      (hstub R' F' hR' hlo' hhi' hF' hFF' hRe c1 hJ hm).stubW hp hend hprog hK hF')
  exact (SegWS.liftS fs h0 fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim

end Seg

section Place

open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun OvfReady EnvSmall)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At okBlk FStable KStable)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff TakeK takeMem)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Spike.Lib.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.PhRec (μ K)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

variable {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}
  {c0 : Ctl} {rS : Range} {Λw : Scc.Sem.Layout}

/-- **The overflow abort label of a user function's body never ends, at
any suspended frames `fs`** (`ovfAb_seg` at `fs`, by `ovfSeg2A`: no
condition on the take): the frames placed under `F` (`hfp`), `c0` and the
frames free of `ZBad` (`hc0`) and the frames' environments small (`hes`);
the rest as `ovfAb_seg`'s. -/
theorem ovfAb_segF {ia : Expr → String → Nat → Option Nat} {T : Expr → Prop} {fr : Scc.Emit.X64.Frame}
    {fp ra : BitVec 64} {f : String}
    (hf : FrameOk fr) (hfn : fr.fn = Scc.Lower.Names.user f)
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog (ovfL fr) 0 ovfBlk = true ∧
      blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
        (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
        ((RuntimeLayout.ofPlaceOK h i).lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 40) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λw.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λw lbl s fs B)
    (hJp : ∀ σ c, (abortN2 ia T p lbl fr (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      SlotRepAt Λw.imms lbl (rsOf fr) σ.slot c)
    (hc0 : FrOk2 c0 fs) (hes : ∀ f ∈ fs, EnvSmall f.env)
    {ms : List TermRun.Frame → MemSide isa}
    (hma : ∀ s : State, (∃ k a, (μ (RuntimeLayout.ofPlaceOK h i)).abortAt k = some a ∧ pcOf s = a) →
      (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (RuntimeLayout.ofPlaceOK h i).exe
      (RuntimeLayout.ofPlaceOK h i).endPc R' F' (Abort.N (RuntimeLayout.ofPlaceOK h i).lab Abort.overflow c .sys)
        s c' → Dt s)
    (Q : FragS isa) :
    SegWS (fun s c fs => W2 Λw (μ (RuntimeLayout.ofPlaceOK h i)) p rd G
        (Spike.Lib.X64.PhRec.own (RuntimeLayout.ofPlaceOK h i)) rS
        (Spike.Lib.X64.PhRec.Tk (RuntimeLayout.ofPlaceOK h i)) ar J Dt
        (Spike.Lib.X64.WriteAb.Ab (RuntimeLayout.ofPlaceOK h i).lab) lbl lsize s c fs)
      (K (RuntimeLayout.ofPlaceOK h i) rS) p lbl ms
      ((At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc R F
        (abortN2 ia T p lbl fr (_root_.Executable.labels (RuntimeLayout.ofPlaceOK h i).exe).label fp ra c0)).at fs)
      Q := by
  haveI := (RuntimeLayout.ofPlaceOK h i).valid
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs ⟨⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hTc⟩, -⟩, -⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  rw [Spike.Lib.X64.Flow.ofNat_zero'] at hphA
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK (rS := rS) h i
  have h8 : (fr.size : Int) % 8 = 0 := by have := frame_mod8 hf; omega
  have hJc : ∀ σ c, (abortN2 ia T p lbl fr (RuntimeLayout.ofPlaceOK h i).lab fp ra c0).J σ c →
      CtlW2 c fs := by
    rintro σ c ⟨⟨⟨sv, lits, hAb, -, -, -⟩, -⟩, hr⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    refine ⟨fun _ a' h' => ?_, FrOk2.run hp (FrameRun.ofLocal hr fs) hc0, hes⟩
    rw [he] at h'; cases h'
  have hrs : ∀ r k, rsOf fr r = some k → R.Off k := fun r k hr => by
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    exact ⟨h2, by omega, by omega⟩
  have hW := ovf_hW_w2 (rd := rd) (G := G) (ar := ar) (J := J) (Dt := Dt) (lsize := lsize) hI
    (printIn_of_placeOKAt h) (hprog_ofPlaceOK h i) hblk (by rw [ovfL, hfn]; exact labelOf_user_not_abLabs f "ovf")
    hR hR8 (by omega) (by omega) hl hh h8 hsub hfit hFO hF hp hphA hJp hrs hfp
    fun σ c hj => ⟨(hJc σ c hj).1, (hJc σ c hj).2.1⟩
  refine ovfSeg2A hI.lays hI.endOk (hprog_ofPlaceOK h i) hblk hF hR hlo (by omega) h8 hK hW ?_ Q
  intro R' F' hR' hlo' hhi' hF' hFF' hR'e c1 ⟨σ0, hJ0⟩ hmem
  subst hR'e
  have hkc8 : (-(fr.size : Int) - 8 - 8) % 8 = 0 := by omega
  refine stubON_w2_ofPlaceOKw h i hp hR' (addr_toNat_mod8 R hR8 hkc8) hlo' hhi'
    (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide) hF' hsub hfit ?_
    hJ0.1.1.choose_spec.choose_spec.1.1 hJ0.1.1.choose_spec.choose_spec.2.1 ?_ hma hK (hwr _ _ c1)
    (fun s hs => (hfp s (hFF' _ hs)).choose_spec.toFramesPlaced) (hJc σ0 c1 hJ0)
  · intro m hm
    refine Spike.Lib.X64.Rt.stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) hkc8
      (hFO m (hFF' m hm)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m hm
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s hs
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 hs
    refine placed_of_slotRep (pf := fun k => .slot (R.addr k).toNat) (hJp σ1 c1 hJ1) fun r k hr => ?_
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    have hk : R.Off k := hrs r k hr
    have hn : ¬ (R.callee (-(fr.size : Int) - 8 - 8) (-24) 16).Off (k - (-(fr.size : Int) - 8 - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    show ((s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
    rw [he k hk hn, hj, Option.map_some, hjs, hsl k (by omega)]; rfl

end Place

/-! ## The overflow block's code at a compiled block -/

section Ovf

open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 Scc.Lower.InvX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Code1X64 (hasAddChk fnOk1_of_fnCode1Ok fnOk1_facts)
open Scc.Cert.Ph1X64 (fnPh1Ok_parts fnPhF_of_fnPhAll1 fnPhF_facts)
open Spike.Lib.X64Consumer (blkPh)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.LowerNode (compiled2 TailAt2)

variable {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
  {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

/-- **The overflow block's code and phase at a compiled block whose walk
reaches a `+`** (`ovfAb_segF`'s `hab` at `fnCode2OfPMe`'s frame): the
function has a checked `+` (`lowerC2_add_blocks` at `LowC2`'s closed form),
so the function's checks (`fnOk1_facts`, `fnPhF_facts`) place its local
overflow block, as in `fnPh2_ofPlaceOK`. -/
theorem ovfFacts_me (Λm : Scc.Sem.Layout) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (∃ x a b e, TailAt2 p j (.let_ x (.add a b) e)) →
      Scc.Cert.Rt.X64.blockAtB (RuntimeLayout.ofPlaceOK h i).prog (ovfL (fnCode2OfPMe hp h Λm j d hd).fr) 0
          ovfBlk = true ∧
        blkPh (Spike.Lib.X64.PhRec.okPc (RuntimeLayout.ofPlaceOK h i))
          (Spike.Lib.X64.PhRec.ph (RuntimeLayout.ofPlaceOK h i)) (fun _ => false) (RuntimeLayout.ofPlaceOK h i).lab
          ((RuntimeLayout.ofPlaceOK h i).lab (ovfL (fnCode2OfPMe hp h Λm j d hd).fr) + Int64.ofNat 0) 0
          Abort.Local.lb = true := by
  rintro ⟨x, a, b, e, ht⟩
  obtain ⟨w, hLw, -, hmem, hfr⟩ := fnCode2OfPMe_spec2 hp h Λm j d hd
  have hadd : hasAddChk (Spike.Lib.LowerShape.func2 (Scc.Lower.Names.user d.name)
      (Spike.Lib.LowerShape.paramsR d w.na) w.sc w.hp w.r) = true :=
    Spike.Lib.LowerAddChk.lowerC2_add_blocks hLw.2.2 (ht d hd)
  have hlab : ∀ l a, Scc.Sem.X64.codeLabel Λ.code.lo
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog l = some a →
      (RuntimeLayout.ofPlaceOK h i).lab l = Int64.ofNat a :=
    Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h i
  have hirP := lowerAll_place_ir cfg p sizes labelOffs
  have hc := fnCode1_of_placeOKAt h hirP
  obtain ⟨-, hall⟩ := fnPh1Ok_parts (fnPh1_of_placeOKAt h hirP)
  obtain ⟨n, hn⟩ := mem_starts _ 0 hmem
  have hc1 := fnOk1_of_fnCode1Ok hc hn rfl
  obtain ⟨zl, zf, z1, z2, zs, zps, ps, hz, hps⟩ := fnOk1_sizes hc1
  obtain ⟨-, -, -, -, -, hovf, -⟩ := fnOk1_facts hc1 rfl hz hps
  have hF := fnPhF_of_fnPhAll1 hall hn rfl
  obtain ⟨-, -, -, -, -, hovp⟩ := fnPhF_facts hF hz hps
  obtain ⟨rab, rlb, hb⟩ := hovp hadd
  rw [labC_eq hlab rab, blkPh_labC hlab rlb, ovfBlk_eq_lb] at hb
  rw [hfr]
  exact ⟨(hovf hadd).2, hb⟩

end Ovf

/-- **A tail of a body free of `bad` is free of `bad`.** -/
theorem noS_of_tailOf {bad : Op → Prop} {t e : Expr} (ht : Spike.Lib.LowerNode.TailOf t e) (he : NoS bad e) :
    NoS bad t := by
  induction ht with
  | refl => exact he
  | let_ _ _ _ ih => exact ih he.2
  | split _ _ _ _ ih => exact ih he
  | unpack _ _ _ _ ih => exact ih he
  | unpackT _ _ _ _ ih => exact ih he
  | yes _ _ _ _ ih => exact ih he.1
  | no _ _ _ _ ih => exact ih he.2

/-- **A node's states have memories in its frame condition.** -/
theorem at_F {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : Spike.Lib.X64.ND} {s : State} {c : Ctl} (h : Spike.Lib.X64.At exe endPc R F n s c) :
    F s.st.1 :=
  let ⟨_, _, _, _, _, _, hF, _⟩ := h
  hF

/-! ## Every base context's aborts -/

section G2

open Kraken.Promising.Lower.X64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRunM Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (At AS)
open Spike.Lib.X64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.X64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.X64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum printFrame)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.AllocReach (IN)

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.X64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **One base context's aborts never end** (`AbG2`'s body at a context
with `CxCore2`): the overflow label by `ovfAb_segF`, the heap abort exits
by `heapAb_seg`, the output call's aborts by `printAb_segP`, each in the
context's region, whose room below the frame (`CxCore2.room` and
`Room2OwnStmt`) holds the frame, the saved `%rbp` and the slack `256`; the
frames' environments small at a memory of `F` (`CxCore2.hes`: no state of
`F`, no abort state). -/
theorem abCx_seg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hRo : Room2OwnStmt h hp) (J : InvS)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.overflow c .sys) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.write c .sys) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    (hC : CxCore2 h hp Dt J j R F fs fp ra tp G0) :
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
      (fun s c fs' =>
        (fs' = fs ∧ ∃ c0, G0 c0 ∧ At (Ly).exe (Ly).endPc R F
            (abortN2 (imms2Me Λ p) (TailAt2 p j) p (fun _ => none) (FC j d hd).fr
              (_root_.Executable.labels (Ly).exe).label fp ra c0) s c) ∨
         (fs' = fs ∧ ∃ (Jc : AS → Ctl → Prop) (pcR : Int64),
            NbJcOf (imms2Me Λ p) (fun _ => none) (FC j d hd).fr Jc ∧
            (∀ σ c', Jc σ c' → TailAt2 p j c'.term) ∧
            At (Ly).exe (Ly).endPc R F (nbX ((MSS J) fs) (_root_.Executable.labels (Ly).exe).label
              (fun _ => none) R (FC j d hd).fr.size pcR Jc .abort) s c) ∨
         (∃ c0 x is a e c1, G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e) ∧
            fs' = printFrame x e c1 :: fs ∧
            At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label (FC j d hd).fr
              (fun _ => none) (imms2Me Λ p) x e c1) s c))
      (fun _ _ _ => False) := by
  by_cases hm : ∃ m, F m
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs' (⟨_, _, _, hA⟩ | ⟨_, _, _, _, _, hA⟩ | ⟨_, _, _, _, _, _, _, _, _, hA⟩)
    all_goals exact hm ⟨_, at_F hA⟩
  obtain ⟨m, hm⟩ := hm
  have hes := hC.hes m hm
  have hlo := hRo j d hd 256 (R.lo - 8) (hC.room d hd)
  have hhi0 : (0 : Int) ≤ R.hi := by have := hC.hhi; omega
  have hpz := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.X64.Rt.fitS_of_sub _ hsub
  obtain ⟨w, -, -, -, hfr⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hfn : (FC j d hd).fr.fn = Scc.Lower.Names.user d.name := by rw [hfr]; rfl
  have hma : ∀ fs1, ∀ s : State, (∃ k a, (Spike.Lib.X64.PhRec.μ (Ly)).abortAt k = some a ∧ pcOf s = a) →
      ((MSS J) fs1).abortAt s := by
    intro fs1
    dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  refine SegWS.or_pre ?_ (SegWS.or_pre ?_ ?_)
  · -- the overflow label
    refine (SegWS.exists_pre (P := fun c0 s c fs' => G0 c0 ∧ (At (Ly).exe (Ly).endPc R F
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p (fun _ => none) (FC j d hd).fr
          (_root_.Executable.labels (Ly).exe).label fp ra c0)).at fs s c fs') fun c0 => ?_).mono_pre
      fun s c fs' ⟨hfs, c0, hg, hA⟩ => ⟨c0, hg, hA, hfs⟩
    by_cases hg : G0 c0
    case neg => exact SegWS.empty fun _ _ _ h' => hg h'.1
    refine (ovfAb_segF h (imms2Me Λ p) (FC j d hd).hf hfn (ovfFacts_me hp h Λ hd (imms2Me Λ p)) hC.hR hC.hR8
      (by omega) hhi0 hC.hl hC.hh hC.hFS hsub hfit hC.hFO hpz hC.hfp
      (abortN2_slotRepAt h (imms2Me Λ p) rfl) (hC.hG0F c0 hg) hes (hma fs) msOfAX_K_abi hDtO _).mono_pre
      fun _ _ _ h' => h'.2
  · -- the heap abort exits
    refine (SegWS.exists_pre (P := fun (q : (AS → Ctl → Prop) × Int64) s c fs' => fs' = fs ∧
        NbJcOf (imms2Me Λ p) (fun _ => none) (FC j d hd).fr q.1 ∧
        At (Ly).exe (Ly).endPc R F (nbX ((MSS J) fs) (_root_.Executable.labels (Ly).exe).label
          (fun _ => none) R (FC j d hd).fr.size q.2 q.1 .abort) s c) fun ⟨Jc, pcR⟩ => ?_).mono_pre
      fun s c fs' ⟨hfs, Jc, pcR, hJ, _, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
    by_cases hJc : NbJcOf (imms2Me Λ p) (fun _ => none) (FC j d hd).fr Jc
    case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
    refine (heapAb_seg h (imms2Me Λ p) (Λw := (Ly).Λ) (fs := fs) (pcR := pcR)
      (FC j d hd).hf hJc hC.hR hC.hR8
      (by simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]; omega)
      hhi0 hC.hl hC.hh hC.hFS hsub hfit hC.hFO hC.hfp ?_ ?_ ?_ (hma fs) msOfAX_K_abi hDtH _).mono_pre ?_
    · intro n τ us hus
      try dsimp only [MSAt]
      generalize ab2 p _ = ab
      cases ab <;>
        (show (arOf (Ly).Λ).units n τ ≤ _
         unfold arOf; exact arena_ofWords_units_le hus)
    · try dsimp only [MSAt]
      generalize ab2 p _ = ab; cases ab <;> rfl
    · try dsimp only [MSAt]
      generalize ab2 p _ = ab; cases ab <;> rfl
    · rintro s c fs' ⟨rfl, -, hA⟩
      exact ⟨hA, rfl⟩
  · -- the output call's aborts
    refine (SegWS.exists_pre (P := fun (q : Ctl × String × List String × CoreTerm.At × Expr × Ctl) s c fs' =>
        G0 q.1 ∧ TailAt2 p j (.let_ q.2.1 (.call "print" q.2.2.1 q.2.2.2.1 []) q.2.2.2.2.1) ∧
        (At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label (FC j d hd).fr
          (fun _ => none) (imms2Me Λ p) q.2.1 q.2.2.2.2.1 q.2.2.2.2.2)).at
          (printFrame q.2.1 q.2.2.2.2.1 q.2.2.2.2.2 :: fs) s c fs') fun ⟨c0, x, is, a, e, c1⟩ => ?_).mono_pre
      fun s c fs' ⟨c0, x, is, a, e, c1, hg, hT, hfs, hA⟩ => ⟨⟨c0, x, is, a, e, c1⟩, hg, hT, hA, hfs⟩
    by_cases hgT : G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e)
    case neg => exact SegWS.empty fun _ _ _ h' => hgT ⟨h'.1, h'.2.1⟩
    obtain ⟨hg, hT⟩ := hgT
    have he : NoS ZBad e :=
      (noS_of_tailOf (hT d hd) (hpz d (List.mem_filter.1 (List.mem_of_getElem? hd)).1)).2
    refine (printAb_segP h (imms2Me Λ p) (it := imms2Me Λ p) (e := e) (FC j d hd).hf
      hC.hR hC.hR8 (by omega) hhi0 hC.hl hC.hh hC.hFS hsub hfit hC.hFO hpz rfl he
      (hC.hG0F c0 hg).2 hC.hfp (hma _) msOfAX_K_abi hDtW _).mono_pre
      fun _ _ _ h' => h'.2.2

/-- **Every base context's aborts never end** (`AbG2` as a segment to the
empty fragment inside the assembled theorem's `W2`): at each context
(`abCx_seg`), no state at a tuple failing `CxCore2`. -/
theorem abG2_seg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hRo : Room2OwnStmt h hp) (J : InvS)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.overflow c .sys) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.write c .sys) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s) :
    SegWS (W2S J) (KT) p (fun _ => none) (MSS J) (AbG2 h hp Dt J) (fun _ _ _ => False) := by
  unfold AbG2
  refine SegWS.exists_pre fun j => SegWS.exists_pre fun d => SegWS.exists_pre fun hd =>
    SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun fs =>
    SegWS.exists_pre fun fp => SegWS.exists_pre fun ra => SegWS.exists_pre fun tp =>
    SegWS.exists_pre fun G0 => ?_
  by_cases hC : CxCore2 h hp Dt J j R F fs fp ra tp G0
  case neg => exact SegWS.empty fun _ _ _ h' => hC h'.1
  exact (abCx_seg h hp hRo J hDtO hDtW hDtH hd hC).mono_pre fun _ _ _ h' => h'.2

end G2

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.ovfSeg2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ovfSeg2A

/-- info: 'Spike.Lib.LowerX64.ovfAb_segF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ovfAb_segF

/-- info: 'Spike.Lib.LowerX64.ovfFacts_me' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.ovfFacts_me

/-- info: 'Spike.Lib.LowerX64.noS_of_tailOf' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.noS_of_tailOf

/-- info: 'Spike.Lib.LowerX64.abCx_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.abCx_seg

/-- info: 'Spike.Lib.LowerX64.abG2_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.abG2_seg
