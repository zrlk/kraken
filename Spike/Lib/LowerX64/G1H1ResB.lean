/-
**A landing context's resumption at the extended placement from its abort
node and constructs** (x86-64): the parts of the allocating frame's
`ResumeCx2T` (`Spike/Lib/LowerX64/ResumeCx2T.lean`) that a landing context
`CxOkH` gives at any walk restriction `Tr` and any program with a setup
block, at the extended placement `upd L l b`, `updN ls l n` of a
placement reachable from none: the code's program (`fnCode2OfPMe_spec`),
the entry region's facts from the setup call's premises, the ghosts'
closure from the context's `CxLB` there (`cxLBT_ofCxOkH` at the empty
walk), the calls in the code (`cdOf_blC`) and the body's and pending
blocks (`cxBlk2_ofFn`, as `resumeCx2T_ofCxOkH`'s; the return point
`scc_rt_main`'s marshalling block off the write abort, the jump targets by
`tgOkB`). The abort node and the four constructs at `TailAt2 p j ∧ Tr`
are premises.

- `resumeLU_ofParts`: the resumption from the abort node and the
  constructs.
-/
import Spike.Test.X64Hello1ResI
import Spike.Lib.LowerX64.ResumeCx2T

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At BlkW ND okBlk)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Rt (setupMC rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

section ResB

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
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True)
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- A context's code at the saved return address (`fnCode2OfPMe`'s). -/
local notation "CD" ra:max =>
  CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra)

set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

/-- **A landing context's `ResumeCx2T` at the extended placement from its
abort node and constructs** at the walk `TailAt2 p j ∧ Tr` (`habN`,
`hcon`) at any aborts' fragment `Ab'`: the rest as `resumeCx2T_ofCxOkH`'s
(the ghosts' closure from `cxLBT_ofCxOkH` at the empty walk, the blocks by
`cxBlk2_ofFn`, the entry region's facts from `CxOkH`'s setup call). -/
theorem resumeLU_ofParts (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTg : tgOkB OP = true) (J : InvS) (Tr : Expr → Prop) {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel}
    {b n : Nat} (hL : Reach (Ar) (fun _ => none) (fun _ => 0) L ls) (hl : L l = none)
    (hAL : Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame}
    {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop} {Ab : FragS isa}
    (hc : CxOkH h hp j R F fs fp ra tp G0 Ab) {Ab' : FragS isa}
    (habN : ∀ c0, G0 c0 → ∀ s c',
      At (LY0).exe (LY0).endPc (rbR R) F
        (abortN2 (imms2Me Λ p) (fun t => TailAt2 p j t ∧ Tr t) p (LU) (FC).fr
          (_root_.Executable.labels (LY0).exe).label fp ra c0) s c' → Ab' s c' fs)
    (hcon : CallC2 p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (fun t => TailAt2 p j t ∧ Tr t)
        Ab' (RetLk d.retTy) ∧
      LaneC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (fun t => TailAt2 p j t ∧ Tr t)
        Ab' ∧
      NewBufC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (fun t => TailAt2 p j t ∧ Tr t)
        Ab' (RetLk d.retTy) ∧
      PrintCallC p (LU) (LN) (FC).lcx (FC).fr (CD ra) ((FC).Bl ra) (LY0).exe (LY0).endPc (rbR R) F
        (W2T J (LU) (LN)) (KT) (MSR J (LU) (LN)) fp ra tp fs G0 (imms2Me Λ p) (fun t => TailAt2 p j t ∧ Tr t)
        Ab') :
    ResumeCx2T (W2T J (LU) (LN)) (KT) p (LU) (LN) (MSR J (LU) (LN)) (FC) R F fs fp ra tp G0 Ab' Tr := by
  have H := cxLBT_ofCxOkH h hp hty J (Dt := fun _ => True) (T := fun _ => False) hL hl hAL hd
    (fun _ _ _ _ _ hF => hF) hc
  obtain ⟨d', hd', L1, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF, hFF, hraE, htp, hct, hbase⟩, hwn, hSB, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  have e : d = d' := Option.some.inj (hd.symm.trans hd')
  subst e
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  -- the setup call's return point (`scc_rt_main`'s marshalling block at `sp0`) is off the write abort
  have hraP : PosOff OP (Ly).lab (Int64.ofBitVec g.ra) := by
    have hin := Spike.Lib.X64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2 h hp hs')
    simp only [Spike.Lib.X64.Rt.mainSIn, Bool.and_eq_true] at hin
    have h0 := posOff_of_blockAtB (lab := (Ly).lab) hin.1.1.2 (by simp only [setupMC]; decide)
      (by simp [Spike.Lib.X64.Rt.marshal] <;> omega)
    rw [Spike.Lib.X64.Flow.ofNat_zero'] at h0
    rwa [hraE, Int64.ofBitVec_toBitVec]
  haveI := (LY0).valid
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  have hblk := cxBlk2_ofFn (Λ := (Ly).Λ) hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) hpN
    (fnCode2OfPMe hp h Λ j d hd) H.hFS H.hR H.hR8 H.hloF (by have := H.hhi; omega) H.hl H.hh
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _)) H.hFO H.hfp
    H.hG0F (fun _ _ h => h) hraP (hTg_of_tgOkB hTg (fun _ _ h => h) (Ly).lab)
    (rd := Spike.Lib.LowerNode.IsNum) (G := G2 h p) (μ := Mk) (own := Spike.Lib.X64.PhRec.own (Ly))
    (Tk := Spike.Lib.X64.PhRec.Tk (Ly)) (ar := Ar) (J := IN (Ar) (fun _ => none) (fun _ => 0) J)
    (Dt := fun _ => True) (fp := g.fp) (lsize := Spike.Lib.AllocReach.updN ls l n)
  refine ⟨by rw [(fnCode2OfPMe_spec hp h Λ j d hd).1], hF, hR0, by show -D1 ≤ _; rw [hframe]; omega,
    by show (8 : Int) ≤ 8; exact Int.le_refl _, H.hG0, ?_, fun s c => (W2T J (LU) (LN)) s c [fr],
    fun _ _ h' => h',
    fun c0 hc0 pc t s lits cs bufs blk hsub hk => hblk.1 c0 hc0 pc t s lits cs bufs blk hsub hk nofun,
    fun c0 hc0 pc t s lits cs bufs k blk hsub hk h1 => hblk.2 c0 hc0 pc t s lits cs bufs k blk hsub hk h1 nofun,
    habN, hcon⟩
  intro pc zc g k hb
  rw [(fnCode2OfPMe_spec hp h Λ j d hd).2.1] at hb
  exact cdOf_blC hI.lays hI.endOk pc zc g k (by rw [hI.labOk]; exact hb.1.1)

end ResB

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.resumeLU_ofParts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.resumeLU_ofParts
