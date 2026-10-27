/-
**The runtime's start blocks inside `RtX` from `PlaceOK`** (x86-64; the
twin of `Spike/Lib/LowerA64/RtStartXOf.lean`): `RtX`'s producers
(`Spike/Lib/LowerX64/RtStartX.lean`) at the runtime's blocks before
`scc_rt_alloc_tcb`, at the record of an output passing `placeOK`. The
blocks are the code's (`rtCode0_of_placeOKAt`), the phase table's rows
(`startFact_ofPlaceOK`); the targets' positions off the write abort are the
next block's or node's (`posOff_of_blockAtB`).

- `labs_nil`: a block without branch labels;
- `posOff_of_blockAtB`, `notAbPc_of_blockAtB`: a block's first cell is a
  position off the write abort, so off its pcs;
- `startW_rtX`: the entry's four nodes (`XStartW`);
- `startCall_rtX`: the call block of `scc_rt_alloc_tcb` (`St0W.blk`);
- `labs_one`, `noAbt`, `posOff_next`, `notAb_of_blockAtB`: a block's labels
  and fall-through;
- `tcbW_rtX`: `scc_rt_alloc_tcb`'s nodes (`TcbW`), for any program with its
  code;
- `takeW_rtX`: `scc_rt_stack_take`'s nodes (`TakeW`), likewise;
- `tiWAt_rtX`, `tiW_rtX`: `scc_rt_thread_init`'s nodes (`TiWAt` at any
  return point, `TiW` at `.x7`), the call's through `takeW_rtX`;
- `swEW_rtX`: the switch, `xorl %ebp, %ebp` and the call of
  `scc_rt_main` (`SwEW`);
- `startE1W_rtX`, `startEW_rtX`: `scc_rt_start`'s nodes from its entry
  (`StartE1W`), and with `_start`'s (`StartEW`), at a placed output.
-/
import Spike.Lib.LowerX64.RtStartX
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.Rt.X64RtTcb
import Spike.Lib.Rt.X64RtTi
import Spike.Lib.Rt.X64StartE

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND classify)
open Spike.Lib.X64.Flow (XStartW xStart0 xStartArgs xStartN1 xStartN2 xStartN3 startE siSig ofNat_zero'
  ofNat_add' xStart0_ok xStartArgs_ok)
open Spike.Lib.X64.Flow.Ret0 (startN0 startN1R startCall startCall_ok)
open Spike.Lib.X64.Rt (RuntimeLayout InstOk startPhTab startFact_ofPlaceOK lab_ofPlaceOK)
open Spike.Lib.X64.Rt.StartU (xStart0_noRet xStartArgs_noRet startCall_noRet startE41)
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- A block without branch labels meets any condition on them. -/
theorem labs_nil {b : List (Directive × Nat)} {P : Label → Prop} (h : blkLabs b = []) :
    ∀ L ∈ blkLabs b, P L := by
  rw [h]; simp

/-- **A block's first cell is a position off the write abort** when its
label is none of the write abort's. -/
theorem posOff_of_blockAtB {cells : List (Directive × Nat)} {lab : Label → Int64} {l : Label} {off : Nat}
    {b : List (Directive × Nat)} (hb : blockAtB cells l off b = true) (hl : l ∉ Spike.Lib.X64.AllocG.abLabs)
    (h0 : 0 < b.length) : PosOff cells lab (lab l + Int64.ofNat off) :=
  ⟨l, off, by simpa using inRunB_of_blockAtB hb h0, hl, rfl⟩

/-- **A block's first cell is off the write abort's pcs**, in a layout of
cells with the runtime's code. -/
theorem notAbPc_of_blockAtB {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Scc.Cert.Rt.X64.Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {l : Label} {off : Nat} {b : List (Directive × Nat)} (hb : blockAtB cells l off b = true)
    (hl : l ∉ Spike.Lib.X64.AllocG.abLabs) (h0 : 0 < b.length) :
    (_root_.Executable.labels exe).label l + Int64.ofNat off ∉
      Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label :=
  notAbPc_of_posOff hp hpr hab (posOff_of_blockAtB hb hl h0)

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

open Spike.Lib.X64.Rt.PhOfTab in
/-- **The entry's four nodes inside `RtX`** (`XStartW`), at the record of an
output passing `placeOK`, in a region holding the entry's frame, at the
source start's control `c0` placed at no frame (`hpl0`). -/
theorem startW_rtX {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    XStartW (RtX Λ' (Spike.Lib.X64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False) (Ly).exe (Ly).endPc R F
      (startN0 (Ly).lab c0).J := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hpr := printIn_of_placeOKAt h
  have hab := abortIn_of_placeOKAt h
  have hrc := Spike.Lib.X64.Rt.rtCode0_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hst := hrc.start
  simp only [Spike.Lib.X64.Flow.startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨g0, cb0⟩, cbSi⟩, cbArgs⟩, cbSys⟩ := hst
  have hcl := hrc.call
  simp only [Spike.Lib.X64.Flow.Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have hnx : ∀ {l : Label} {off : Nat} {b : List (Directive × Nat)}, blockAtB o.prog l off b = true →
      l ∉ Spike.Lib.X64.AllocG.abLabs → 0 < b.length →
      (Ly).lab l + Int64.ofNat off ∉ Spike.Lib.X64.WriteAb.abPcs (Ly).lab := fun hb hl' h0 => by
    have := notAbPc_of_blockAtB hI.lays hpr hab hb hl' h0
    rwa [hI.labOk] at this
  have hlg := Scc.Cert.Rt.X64.label_labelGapB hI.lays g0
  rw [hI.labOk] at hlg
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The frame's setup.
    have hph := blkPh_of_factOk hl hr hn
      (hf (.blk "scc_rt_start" 0 xStart0 none none) (by simp [startPhTab]))
    rw [ofNat_zero'] at hph
    refine blkW_rtX hI hpr hab cb0 (ofNat_zero' _) xStart0_ok hR (by omega) (by omega) hph xStart0_noRet
      (by decide) (fun _ => ?_) (labs_nil (by decide)) (fun _ _ hJ => hJ) hpl0
    have := posOff_of_blockAtB (lab := (Ly).lab) cbSi (by decide) (by decide)
    rw [show 0 + Spike.Lib.X64.cellOff xStart0 xStart0.length = 8 by decide]
    rwa [ofNat_zero', hlg] at this
  · -- The handler's `lea`.
    have hs := step_of_factOk hl (hf (.step startE 0 7) (by simp [startPhTab]))
    exact nodeW_rtX_si (si := siSig) (p := (Ly).lab startE + Int64.ofNat 0) hI cbSi rfl (ofNat_zero' _).symm hs.1
      (by rw [← ofNat_add']; exact hnx cbArgs (by decide) (by decide)) (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0
  · -- The arguments.
    have hph := blkPh_of_factOk hl hr hn (hf (.blk startE 7 xStartArgs none none) (by simp [startPhTab]))
    refine blkW_rtX hI hpr hab cbArgs rfl xStartArgs_ok hR (by omega) (by omega) hph xStartArgs_noRet
      (by decide) (fun _ => ?_) (labs_nil (by decide)) (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0
    exact posOff_of_blockAtB (lab := (Ly).lab) cbSys (by decide) (by decide)
  · -- `rt_sigaction`'s `syscall`.
    have hs := step_of_factOk hl (hf (.step startE 41 2) (by simp [startPhTab]))
    exact nodeW_rtX_sys (p := (Ly).lab startE + Int64.ofNat 41) hI cbSys rfl (startE41 (Ly).lab) hs.1
      (by rw [← ofNat_add']; exact hnx cc (by decide) (by decide)) (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0

open Spike.Lib.X64.Rt.PhOfTab in
/-- **The call block of `scc_rt_alloc_tcb` inside `RtX`** (`St0W.blk`), as
`startW_rtX`: its call target `scc_rt_alloc_tcb`'s first block. -/
theorem startCall_rtX {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    BlkW (RtX Λ' (Spike.Lib.X64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False) (Ly).exe (Ly).endPc R F
      (startN1R (Ly).lab c0) startCall := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := Spike.Lib.X64.Rt.rtCode0_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hcl := hrc.call
  simp only [Spike.Lib.X64.Flow.Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have bE : blockAtB o.prog Spike.Lib.X64.Flow.Ret0.AllocTcb.fnL 0 Spike.Lib.X64.Flow.Ret0.AllocTcb.atPro = true := by
    have ht := hrc.tcb
    unfold Spike.Lib.X64.Flow.Ret0.AllocTcb.allocTcbIn at ht
    repeat (first | exact (cast (Bool.and_eq_true _ _) ht).2 | replace ht := (cast (Bool.and_eq_true _ _) ht).1)
  exact blkW_rtX hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) cc rfl startCall_ok hR
    (by omega) (by omega)
    (blkPh_of_factOk hl hr hn (hf (.blk startE 43 Spike.Lib.X64.Rt.Code.Start.startCall none none)
      (by simp [startPhTab])))
    startCall_noRet (by decide) (fun h => absurd h (by decide))
    (fun L hL => by
      have hb : blkLabs startCall = [Spike.Lib.X64.Flow.Ret0.AllocTcb.fnL] := by decide
      have : L = Spike.Lib.X64.Flow.Ret0.AllocTcb.fnL := by simpa [hb] using hL
      subst this
      have := posOff_of_blockAtB (lab := (Ly).lab) bE (by decide) (by decide)
      rwa [ofNat_zero'] at this)
    (fun _ _ hJ => hJ.1) hpl0

end Start

/-! ## `scc_rt_alloc_tcb` -/

/-- A block with one branch label meets a condition on it. -/
theorem labs_one {b : List (Directive × Nat)} {L0 : Label} {P : Label → Prop} (h : blkLabs b = [L0])
    (hp : P L0) : ∀ L ∈ blkLabs b, P L := by
  rw [h]; simpa using hp

/-- A block without the abort's entry among its labels never branches to it. -/
theorem noAbt {b : List (Directive × Nat)} (h : "scc_rt_abort" ∉ blkLabs b) :
    ∀ k (hk : k < b.length) a, classify b[k].1 = some a → aiLab a ≠ some "scc_rt_abort" :=
  fun k hk a ha hL => h (List.mem_filterMap.mpr ⟨b[k], List.getElem_mem hk, by simp only [ha, Option.bind_some, hL]⟩)

/-- **The position after a block is a position off the write abort** when a
block of the same label starts there (`hb`, `he`). -/
theorem posOff_next {cells : List (Directive × Nat)} {lab : Label → Int64} {l : Label} {off off' : Nat}
    {blk b : List (Directive × Nat)} (hb : blockAtB cells l off' b = true) (hl : l ∉ Spike.Lib.X64.AllocG.abLabs)
    (h0 : 0 < b.length) (he : off + Spike.Lib.X64.cellOff blk blk.length = off') :
    PosOff cells lab (lab l + Int64.ofNat (off + Spike.Lib.X64.cellOff blk blk.length)) := by
  rw [he]; exact posOff_of_blockAtB hb hl h0

section Tcb

open Spike.Lib.X64.Rt.Tcb Spike.Lib.X64.Flow.Ret0.AllocTcb
open Spike.Lib.X64.Flow.Ret0 (TN TcbG TcbW tcbN pnA pinA hdrBlk_eq rmwBlk_eq)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- A block's first position off the write abort's pcs, at a label off the
write abort's. -/
theorem notAb_of_blockAtB (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {l : Label} {off : Nat} {b : List (Directive × Nat)} (hb : blockAtB cells l off b = true)
    (hl : l ∉ Spike.Lib.X64.AllocG.abLabs) (h0 : 0 < b.length) :
    lab l + Int64.ofNat off ∉ Spike.Lib.X64.WriteAb.abPcs lab := by
  have := notAbPc_of_blockAtB hI.lays hpr hab hb hl h0
  rwa [hI.labOk] at this

set_option hygiene false in
/-- A plain block of `scc_rt_alloc_tcb` falling through to a node at the
same label (`next`). -/
local macro "tblk " b:term:max ok:term:max f:term:max nr:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab $b (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega)
      (by first | exact $f | (have hf := $f; rw [ofNat_zero'] at hf; exact hf)) $nr (by decide)
      (fun _ => posOff_next $nx (by decide) (by decide) (by decide)) (labs_nil (by decide)) (hc0 _) hpl0))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc_tcb` at `l + off` of size `z`
without an event, the next node at `next`. -/
local macro "tstep " lem:ident b:term:max l:term:max off:term:max z:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TcbW]; rw [hI.labOk]
    exact $lem (p := lab $l + Int64.ofNat $off) hI $b rfl (by first | rfl | exact (ofNat_zero' _).symm)
      (hstep (lab $l + Int64.ofNat $off, $z) (by simp [stepPcs])).1
      (by rw [← ofNat_add']; exact hnx $nx (by decide) (by decide)) (hc0 _) hpl0))

/-- **`scc_rt_alloc_tcb`'s states inside `RtX`**, for any program with the
function's code (`hin`) and the runtime's (`hpr`, `hab`), in any region
holding its frame, at the source control `c0` placed at no frame (`hq`,
`hpl0`), returning to `ra okL` (`hra`) off the write abort's pcs (`hraOff`),
its phase facts (`hph`), the counter's old value with room for a TCB
(`hn0`), its two words unmapped in private memory under the frame condition
(`hunP`, `hunH`) and off the arena's counter and heap (`hoffP`, `hoffH`). -/
theorem tcbW_rtX (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hin : allocTcbIn cells = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {F : MachineData → Prop}
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi) (q : TcbG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hraOff : ra okL ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hph : TcbPh okPc ph Tk ownOf lab ra q.n0) (hn0 : q.n0.toNat + 80 ≤ 131072)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (pinA lab + q.n0) 8 = none)
    (hoffP : (⟨pnA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (pnA lab).toNat ∧ (pnA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffH : (⟨pinA lab + q.n0, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (pinA lab + q.n0).toNat ∧ (pinA lab + q.n0).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TcbW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F q i := by
  have h := hin
  simp only [allocTcbIn, fiAt, siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at h
  obtain ⟨h, bRet⟩ := h; obtain ⟨h, bHdr⟩ := h; obtain ⟨h, bO5⟩ := h; obtain ⟨h, fOr1⟩ := h
  obtain ⟨h, bO4⟩ := h; obtain ⟨h, fShl3⟩ := h; obtain ⟨h, bO3⟩ := h; obtain ⟨h, fShl2⟩ := h
  obtain ⟨h, bO2⟩ := h; obtain ⟨h, fImul2⟩ := h; obtain ⟨h, bO1⟩ := h; obtain ⟨h, sOk⟩ := h
  obtain ⟨h, bJ2⟩ := h; obtain ⟨h, bBnd⟩ := h; obtain ⟨h, bRmw⟩ := h; obtain ⟨h, bArg⟩ := h
  obtain ⟨h, sLea1⟩ := h; obtain ⟨h, bL6⟩ := h; obtain ⟨h, fShl1⟩ := h; obtain ⟨h, bL5⟩ := h
  obtain ⟨h, fImul1⟩ := h; obtain ⟨h, bL4⟩ := h; obtain ⟨h, fAnd2⟩ := h; obtain ⟨h, bL3⟩ := h
  obtain ⟨h, fShr2⟩ := h; obtain ⟨h, bL2⟩ := h; obtain ⟨h, fAnd1⟩ := h; obtain ⟨h, bL1⟩ := h
  obtain ⟨h, fShr1⟩ := h; obtain ⟨h, bLen⟩ := h; obtain ⟨h, bJ1⟩ := h; obtain ⟨h, bEn⟩ := h
  obtain ⟨gE, bE⟩ := h
  have hc0 : ∀ (i : TN), ∀ σ c, (tcbN lab q i).J σ c → c = c0 := fun i σ c hJ => by
    cases i <;> exact hJ.1.trans hq
  have hstep : ∀ pz ∈ stepPcs lab, okPc pz.1.toBitVec.toNat = true ∧
      ph (pz.1 + Int64.ofNat pz.2).toBitVec.toNat = ph pz.1.toBitVec.toNat := hph.step
  have hnx := fun {l off b} (hb : blockAtB cells l off b = true) hl h0 => notAb_of_blockAtB hI hpr hab hb hl h0
  intro i
  cases i
  case e =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat_zero' _) atPro_ok hR (by omega) (by omega)
      (by have := hph.e; rw [ofNat_zero'] at this; exact this) atPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (hc0 .e) hpl0
    have := posOff_of_blockAtB (lab := lab) bEn (by decide) (by decide)
    have hg := Scc.Cert.Rt.X64.label_labelGapB hI.lays gE
    rw [hI.labOk] at hg
    rw [show 0 + Spike.Lib.X64.cellOff atPro atPro.length = 19 by decide]
    rwa [ofNat_zero', hg] at this
  case entry =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bEn (ofNat_zero' _) atChk_ok hR (by omega) (by omega)
      (by have := hph.entry; rw [ofNat_zero'] at this; exact this) (by decide)
      (fun _ _ _ k hk hr => (noRet_false atChk_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_next bJ1 (by decide) (by decide) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .entry) hpl0
    dsimp only [tcbN] at hJ ⊢
    rw [(atChk_walk lab _ hJ.2).1]
    exact posOff_of_blockAtB (lab := lab) bJ1 (by decide) (by decide)
  case j1 =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bJ1 rfl atJ1_ok hR (by omega) (by omega) hph.j1 atJ1_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := lenL) (by decide) ?_) (hc0 .j1) hpl0
    have := posOff_of_blockAtB (lab := lab) bLen (by decide) (by decide)
    rwa [ofNat_zero'] at this
  case len => tblk bLen atL0_ok hph.len atL0_noRet fShr1
  case shr1 => tstep nodeW_rtX_fi fShr1 lenL 11 3 bL1
  case l1 => tblk bL1 atL1_ok hph.l1 atL1_noRet fAnd1
  case and1 => tstep nodeW_rtX_fi fAnd1 lenL 29 3 bL2
  case l2 => tblk bL2 atL2_ok hph.l2 atL2_noRet fShr2
  case shr2 => tstep nodeW_rtX_fi fShr2 lenL 47 3 bL3
  case l3 => tblk bL3 atL3_ok hph.l3 atL3_noRet fAnd2
  case and2 => tstep nodeW_rtX_fi fAnd2 lenL 65 3 bL4
  case l4 => tblk bL4 atL4_ok hph.l4 atL4_noRet fImul1
  case imul1 => tstep nodeW_rtX_fi fImul1 lenL 95 4 bL5
  case l5 => tblk bL5 atL5_ok hph.l5 atL5_noRet fShl1
  case shl1 => tstep nodeW_rtX_fi fShl1 lenL 132 3 bL6
  case l6 => tblk bL6 atL6_ok hph.l6 atL6_noRet sLea1
  case lea1 => tstep nodeW_rtX_si sLea1 lenL 139 7 bArg
  case arg => tblk bArg atArg_ok hph.arg atArg_noRet bRmw
  case rmw =>
    dsimp only [TcbW]; rw [hI.labOk]
    have hA : ∀ σ c, (tcbN lab q .rmw).J σ c → Spike.Lib.X64.bAddr σ.regs .rcx 0 = pnA lab := by
      intro σ c hJ
      obtain ⟨-, -, -, hc⟩ := hJ
      rw [← hc]
      simp [Spike.Lib.X64.bAddr, Reg64s.get64]
    refine nodeW_rtX_xadd (p := rmwPc lab) hI bRmw rfl rfl hph.rmwOk
      (by show lab lenL + Int64.ofNat 158 + Int64.ofNat 5 ∉ _
          rw [← ofNat_add']; exact hnx bBnd (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_) (hc0 .rmw) hpl0
    · rw [hA σ c hJ]; exact hunP m hF
    · rw [hA σ c hJ]; exact hoffP
  case bnd =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bBnd rfl atBnd_ok hR (by omega) (by omega) hph.bnd (by decide)
      (fun _ _ _ k hk hr => (noRet_false atBnd_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_next bJ2 (by decide) (by decide) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .bnd) hpl0
    dsimp only [tcbN] at hJ ⊢
    rw [(atBnd_walk lab _ hJ.2.1 hJ.2.2 hn0).1, ← ofNat_add']
    exact posOff_of_blockAtB (lab := lab) bJ2 (by decide) (by decide)
  case j2 =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bJ2 rfl atJ2_ok hR (by omega) (by omega) hph.j2 atJ2_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := okL) (by decide) ?_) (hc0 .j2) hpl0
    have := posOff_of_blockAtB (lab := lab) sOk (by decide) (by decide)
    rwa [ofNat_zero'] at this
  case ok => tstep nodeW_rtX_si sOk okL 0 7 bO1
  case o1 => tblk bO1 atO1_ok hph.o1 atO1_noRet fImul2
  case imul2 => tstep nodeW_rtX_fi fImul2 okL 34 4 bO2
  case o2 => tblk bO2 atO2_ok hph.o2 atO2_noRet fShl2
  case shl2 => tstep nodeW_rtX_fi fShl2 okL 53 3 bO3
  case o3 => tblk bO3 atO3_ok hph.o3 atO3_noRet fShl3
  case shl3 => tstep nodeW_rtX_fi fShl3 okL 74 3 bO4
  case o4 => tblk bO4 atO4_ok hph.o4 atO4_noRet fOr1
  case or1 => tstep nodeW_rtX_fi fOr1 okL 95 3 bO5
  case o5 => tblk bO5 atO5_ok hph.o5 atO5_noRet bHdr
  case hdr =>
    dsimp only [TcbW]; rw [hI.labOk]
    have hA : ∀ σ c, (tcbN lab q .hdr).J σ c → Spike.Lib.X64.bAddr σ.regs .rcx 0 = pinA lab + q.n0 := by
      intro σ c hJ
      obtain ⟨-, -, -, hc⟩ := hJ
      have he : σ.regs.rcx.toBitVec = pinA lab + q.n0 := hc
      simp [Spike.Lib.X64.bAddr, Reg64s.get64, he]
    refine nodeW_rtX_st (p := lab okL + Int64.ofNat 140) hI bHdr rfl rfl
      (hstep (lab okL + Int64.ofNat 140, 3) (by simp [stepPcs])).1
      (by rw [← ofNat_add']; exact hnx bRet (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_) (hc0 .hdr) hpl0
    · rw [hA σ c hJ]; exact hunH m hF
    · rw [hA σ c hJ]; exact hoffH
  case ret =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl atRet_ok hR (by omega) (by omega) hph.ret (by decide)
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (hc0 .ret) hpl0

end Tcb

/-! ## `scc_rt_stack_take` -/

section Take

open Spike.Lib.X64.Rt.Take Spike.Lib.X64.Flow.Ret0.StackTake
open Spike.Lib.X64.Flow.Ret0 (TK TakeG TakeW takeNG lockA freeNA nextA swpBlk_eq ldnBlk_eq unlBlk_eq
  nxtBlk_eq)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

set_option hygiene false in
/-- A plain block of `scc_rt_stack_take` falling through to a node at the
same label (`next`). -/
local macro "kblk " b:term:max ok:term:max f:term:max nr:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab $b (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega)
      (by first | exact $f | (have hf := $f; rw [ofNat_zero'] at hf; exact hf)) $nr (by decide)
      (fun _ => posOff_next $nx (by decide) (by decide) (by decide)) (labs_nil (by decide)) (hc0 _) hpl0))

set_option hygiene false in
/-- A plain block of `scc_rt_stack_take` ending in a jump to label `L`'s
first node (`next`). -/
local macro "kjmp " b:term:max ok:term:max f:term:max nr:term:max L:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab $b (by first | rfl | exact ofNat_zero' _) $ok hR (by omega) (by omega)
      (by first | exact $f | (have hf := $f; rw [ofNat_zero'] at hf; exact hf)) $nr (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := $L) (by decide) (hpos $nx (by decide) (by decide)))
      (hc0 _) hpl0))

set_option hygiene false in
/-- A `leaq L(%rip), %rax` of `scc_rt_stack_take` at `l + off`, the next
node at `next`. -/
local macro "ksi " b:term:max l:term:max off:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TakeW]; rw [hI.labOk]
    exact nodeW_rtX_si (p := lab $l + Int64.ofNat $off) hI $b rfl (by first | rfl | exact (ofNat_zero' _).symm)
      (hsi (lab $l + Int64.ofNat $off) (by simp [siPcs])).1
      (by rw [← ofNat_add']; exact hnx $nx (by decide) (by decide)) (hc0 _) hpl0))

set_option maxHeartbeats 800000 in
/-- **`scc_rt_stack_take`'s states inside `RtX`**, for any program with the
function's code (`hin`) and the runtime's (`hpr`, `hab`), in any region
holding its frame, at the source control `c0` placed at no frame (`hq`,
`hpl0`), returning to `ra siteL` (`hra`) off the write abort's pcs
(`hraOff`), its phase facts (`hph`), room for the stack below `2^29` (`hk`),
its three words unmapped in private memory under the frame condition
(`hunL`, `hunN`, `hunX`) and its two written words off the arena's counter
and heap (`hoffL`, `hoffX`). -/
theorem takeW_rtX (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hin : stackTakeIn cells = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {F M : MachineData → Prop}
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -200) (hhi : 8 ≤ R.hi) (q : TakeG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra siteL).toBitVec) (hraOff : ra siteL ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hph : TakePh okPc ph Tk ownOf μ lab ra) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hoffL : (⟨lockA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (lockA lab).toNat ∧ (lockA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffX : (⟨nextA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (nextA lab).toNat ∧ (nextA lab).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TakeW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F M q i := by
  have h := hin
  simp only [stackTakeIn, Spike.Lib.X64.Flow.Ret0.AllocTcb.siAt, swpBlk_eq, ldnBlk_eq, unlBlk_eq, nxtBlk_eq,
    nopBlk_eq, Bool.and_eq_true] at h
  obtain ⟨h, bRet⟩ := h; obtain ⟨h, bSite⟩ := h; obtain ⟨h, gT⟩ := h; obtain ⟨h, bTk⟩ := h
  obtain ⟨h, bOk7⟩ := h; obtain ⟨h, sOk0⟩ := h; obtain ⟨h, bB108⟩ := h; obtain ⟨h, bB61⟩ := h
  obtain ⟨h, bNxt⟩ := h; obtain ⟨h, bB38⟩ := h; obtain ⟨h, sB31⟩ := h; obtain ⟨h, bUnl⟩ := h
  obtain ⟨h, bB7⟩ := h; obtain ⟨h, sB0⟩ := h; obtain ⟨h, bLk7⟩ := h; obtain ⟨h, bLdn⟩ := h
  obtain ⟨h, bLk0⟩ := h; obtain ⟨h, bSp14⟩ := h; obtain ⟨h, bSwp⟩ := h; obtain ⟨h, bSp0⟩ := h
  obtain ⟨h, bD59⟩ := h; obtain ⟨h, sD52⟩ := h; obtain ⟨h, bD33⟩ := h; obtain ⟨h, sD26⟩ := h
  obtain ⟨h, bD7⟩ := h; obtain ⟨h, sD0⟩ := h; obtain ⟨h, bJ1⟩ := h; obtain ⟨h, bCls⟩ := h
  obtain ⟨h, bEn⟩ := h
  obtain ⟨gE, bE⟩ := h
  have hc0 : ∀ (i : TK), ∀ σ c, (takeNG lab q true i).J σ c → c = c0 := fun i σ c hJ => by
    cases i <;> first | exact hJ.1.trans hq | exact hJ.2.1.trans hq
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 7).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnx := fun {l off b} (hb : blockAtB cells l off b = true) hl h0 => notAb_of_blockAtB hI hpr hab hb hl h0
  have hpos : ∀ {l : Label} {b : List (Directive × Nat)}, blockAtB cells l 0 b = true →
      l ∉ Spike.Lib.X64.AllocG.abLabs → 0 < b.length → PosOff cells lab (lab l) := fun hb hl h0 => by
    have := posOff_of_blockAtB (lab := lab) hb hl h0
    rwa [ofNat_zero'] at this
  intro i
  cases i
  case e =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat_zero' _) stPro_ok hR (by omega) (by omega)
      (by have := hph.e; rw [ofNat_zero'] at this; exact this) stPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (hc0 .e) hpl0
    have := hpos bEn (by decide) (by decide)
    have hg := Scc.Cert.Rt.X64.label_labelGapB hI.lays gE
    rw [hI.labOk] at hg
    rw [show 0 + Spike.Lib.X64.cellOff stPro stPro.length = 15 by decide]
    rwa [hg] at this
  case entry => kjmp bEn stInit_ok hph.entry stInit_noRet clsL bCls
  case cls =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bCls (ofNat_zero' _) stCls_ok hR (by omega) (by omega)
      (by have := hph.cls; rw [ofNat_zero'] at this; exact this) (by decide)
      (fun _ _ _ k hk hr => (noRet_false stCls_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_next bJ1 (by decide) (by decide) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .cls) hpl0
    dsimp only [takeNG] at hJ ⊢
    rw [(stCls_walk lab _ hJ.2).1]
    exact posOff_of_blockAtB (lab := lab) bJ1 (by decide) (by decide)
  case j1 => kjmp bJ1 stJ1_ok hph.j1 stJ1_noRet doneL sD0
  case d0 => ksi sD0 doneL 0 bD7
  case d7 => kblk bD7 stFreeN_ok hph.d7 stFreeN_noRet sD26
  case d26 => ksi sD26 doneL 26 bD33
  case d33 => kblk bD33 stFree_ok hph.d33 stFree_noRet sD52
  case d52 => ksi sD52 doneL 52 bD59
  case d59 => kjmp bD59 stLock_ok hph.d59 stLock_noRet spinL bSp0
  case sp0 => kblk bSp0 stSwp_ok hph.sp0 stSwp_noRet bSwp
  case swp =>
    dsimp only [TakeW]; rw [hI.labOk]
    have hA : ∀ σ c, (takeNG lab q true .swp).J σ c → Spike.Lib.X64.bAddr σ.regs .rcx 0 = lockA lab :=
      fun σ c hJ => by simp [Spike.Lib.X64.bAddr, Reg64s.get64, hJ.2.2.1]
    refine nodeW_rtX_xchg (p := swpPc lab) hI bSwp rfl rfl hph.swpOk
      (by show lab spinL + Int64.ofNat 11 + Int64.ofNat 3 ∉ _
          rw [← ofNat_add']; exact hnx bSp14 (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_) (hc0 .swp) hpl0
    · rw [hA σ c hJ]; exact hunL m hF
    · rw [hA σ c hJ]; exact hoffL
  case sp14 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bSp14 rfl stSpin_ok hR (by omega) (by omega) hph.sp14 (by decide)
      (fun _ _ _ k hk hr => (noRet_false stSpin_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inr fun σ c hJ => ?_) (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .sp14) hpl0
    all_goals
      dsimp only [takeNG] at hJ ⊢
      rw [(stSpin_walk lab _ hJ.2.1 hJ.2.2).1]
      exact hpos bLk0 (by decide) (by decide)
  case lk0 => kblk bLk0 stLdN_ok hph.lk0 stLdN_noRet bLdn
  case ldn =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_rtX_ld (p := freeNPc lab) hI bLdn rfl rfl hph.ldnOk
      (by show lab lockedL + Int64.ofNat 4 + Int64.ofNat 3 ∉ _
          rw [← ofNat_add']; exact hnx bLk7 (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (hc0 .ldn) hpl0
    have hA : Spike.Lib.X64.bAddr σ.regs .rcx 0 = freeNA lab := by
      simp [Spike.Lib.X64.bAddr, Reg64s.get64, hJ.2.2]
    rw [hA]; exact hunN m hF
  case lk7 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bLk7 rfl stEmpty_ok hR (by omega) (by omega) hph.lk7 (by decide)
      (fun _ _ _ k hk hr => (noRet_false stEmpty_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inr fun σ c hJ => ?_) (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .lk7) hpl0
    all_goals
      dsimp only [takeNG] at hJ ⊢
      rw [(stEmpty_walk lab _ hJ.2.1 hJ.2.2).1]
      exact hpos sB0 (by decide) (by decide)
  case b0 => ksi sB0 bumpL 0 bB7
  case b7 => kblk bB7 stUnl_ok hph.b7 stUnl_noRet bUnl
  case unl =>
    dsimp only [TakeW]; rw [hI.labOk]
    have hA : ∀ σ c, (takeNG lab q true .unl).J σ c → Spike.Lib.X64.bAddr σ.regs .rcx 0 = lockA lab :=
      fun σ c hJ => by simp [Spike.Lib.X64.bAddr, Reg64s.get64, hJ.2.2.1]
    refine nodeW_rtX_st (p := unlPc lab) hI bUnl rfl rfl hph.unlOk
      (by show lab bumpL + Int64.ofNat 28 + Int64.ofNat 3 ∉ _
          rw [← ofNat_add']; exact hnx sB31 (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_) (hc0 .unl) hpl0
    · rw [hA σ c hJ]; exact hunL m hF
    · rw [hA σ c hJ]; exact hoffL
  case b31 => ksi sB31 bumpL 31 bB38
  case b38 => kblk bB38 stAdd_ok hph.b38 stAdd_noRet bNxt
  case nxt =>
    dsimp only [TakeW]; rw [hI.labOk]
    have hA : ∀ σ c, (takeNG lab q true .nxt).J σ c → Spike.Lib.X64.bAddr σ.regs .rcx 0 = nextA lab :=
      fun σ c hJ => by simp [Spike.Lib.X64.bAddr, Reg64s.get64, hJ.2.2.1]
    refine nodeW_rtX_xadd (p := nextPc lab) hI bNxt rfl rfl hph.nxtOk
      (by show lab bumpL + Int64.ofNat 56 + Int64.ofNat 5 ∉ _
          rw [← ofNat_add']; exact hnx bB61 (by decide) (by decide))
      (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_) (hc0 .nxt) hpl0
    · rw [hA σ c hJ]; exact hunX m hF
    · rw [hA σ c hJ]; exact hoffX
  case b61 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bB61 rfl stBnd_ok hR (by omega) (by omega) hph.b61 (by decide)
      (fun _ _ _ k hk hr => (noRet_false stBnd_noRet k hk hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_next bB108 (by decide) (by decide) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .b61) hpl0
    dsimp only [takeNG] at hJ ⊢
    rw [(stBnd_walk lab _ hJ.2.1 hJ.2.2 hk).1, ← ofNat_add']
    exact posOff_of_blockAtB (lab := lab) bB108 (by decide) (by decide)
  case b108 => kjmp bB108 stJ2_ok hph.b108 stJ2_noRet okL sOk0
  case ok0 => ksi sOk0 okL 0 bOk7
  case ok7 => kjmp bOk7 stOk_ok hph.ok7 stOk_noRet takenL bTk
  case tk =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bTk (ofNat_zero' _) stSite_ok hR (by omega) (by omega)
      (by have := hph.tk; rw [ofNat_zero'] at this; exact this) stSite_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (hc0 .tk) hpl0
    have := hpos bSite (by decide) (by decide)
    have hg := Scc.Cert.Rt.X64.label_labelGapB hI.lays gT
    rw [hI.labOk] at hg
    rw [show 0 + Spike.Lib.X64.cellOff stSite stSite.length = 11 by decide]
    rwa [hg] at this
  case site =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact site_rtX hI bSite (ofNat_zero' _) rfl (hnx bRet (by decide) (by decide)) (hc0 .site) hpl0
  case ret =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl stRet_ok hR (by omega) (by omega) hph.ret (by decide)
      (hret_of_run stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(stRet_walk lab _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (hc0 .ret) hpl0

end Take

/-! ## `scc_rt_thread_init` -/

section Ti

open Spike.Lib.X64.Rt.Ti Spike.Lib.X64.Flow.Ret0.ThreadInit
open Spike.Lib.X64.Rt (TiWAt tiNAt tiX7At tiWAt_x7)
open Spike.Lib.X64.Flow.Ret0 (TI TiG TiW tiTake tiCall tiCall_ok lockA freeNA nextA storeBlks_eq bAddr_rcx)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

set_option hygiene false in
/-- A block of `scc_rt_thread_init` after the call at the return point `x`
+ `off`, falling through to the store at `next`. -/
local macro "iblk " b:term:max ok:term:max f:term:max nr:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab $b rfl $ok hR (by omega) (by omega) $f $nr hx
      (fun _ => posOff_next $nx hx (by decide) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0))

set_option hygiene false in
/-- The store of TCB field `j` (`z` bytes at the return point `x` + `off`,
displacement `k`) of `scc_rt_thread_init`, the next block at `next`. -/
local macro "ist " b:term:max j:term:max off:term:max z:term:max nx:term:max : tactic =>
  `(tactic| (
    dsimp only [TiWAt]; rw [hI.labOk]
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ tiAddrs q.tcb := by simp [tiAddrs]
    refine nodeW_rtX_st (p := lab x + Int64.ofNat $off) hI $b rfl rfl
      (hph.st (lab x + Int64.ofNat $off, $z) (by simp [stPcsAt])).1
      (by rw [← ofNat_add']; exact hnx $nx hx (by decide)) (fun σ c m hJ hF => ?_) (fun σ c hJ => ?_)
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    · rw [bAddr_rcx hJ.2.2.2, show BitVec.ofInt 64 (Int64.toInt _) = BitVec.ofNat 64 (8 * $j) by decide]
      exact hunF _ ha m hF.1
    · rw [bAddr_rcx hJ.2.2.2, show BitVec.ofInt 64 (Int64.toInt _) = BitVec.ofNat 64 (8 * $j) by decide]
      exact hoffF _ ha))

set_option maxHeartbeats 800000 in
set_option linter.unusedSectionVars false in
/-- **`scc_rt_thread_init`'s states inside `RtX`, its return point at any
label `x`** off the write abort's (`hx`), for any program with the
function's code there (`hin`) and the runtime's (`hpr`, `hab`), in any
region holding its frame and the take's below, at the source control `c0`
placed at no frame (`hq`, `hpl0`), returning to `ra x` (`hra`) off the write
abort's pcs (`hraOff`), its phase facts at `x` (`hph`), the TCB's six words
unmapped in private memory under the frame condition (`hunF`) and off the
arena's counter and heap (`hoffF`), and at its call `scc_rt_stack_take`'s
premises of `takeW_rtX` (`hin'` to `hoffX`), returning to `x`. -/
theorem tiWAt_rtX {x : Label} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hx : x ∉ Spike.Lib.X64.AllocG.abLabs) (hin : threadInitInAt cells x = true) {Λ' : Scc.Sem.Layout}
    {lbl : Lbl} {ar : Arena} {c0 : Ctl} {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64}
    {F M : MachineData → Prop} {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra x).toBitVec) (hraOff : ra x ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hph : TiPhAt okPc ph Tk lab ra x)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hoffF : ∀ a ∈ tiAddrs q.tcb, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hin' : Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn cells = true)
    (hphT : Spike.Lib.X64.Rt.Take.TakePh okPc ph Tk ownOf μ lab fun _ => lab x)
    (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hoffL : (⟨lockA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (lockA lab).toNat ∧ (lockA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffX : (⟨nextA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (nextA lab).toNat ∧ (nextA lab).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TiWAt (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F M q x i := by
  have h := hin
  simp only [threadInitInAt, storeOff, storeBlks_eq, List.zip_cons_cons, List.zip_nil_right, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h, s0, s1, s2, s3, s4, s5⟩ := h
  obtain ⟨h, bRet⟩ := h; obtain ⟨h, bF5⟩ := h; obtain ⟨h, bF4⟩ := h; obtain ⟨h, bF3⟩ := h
  obtain ⟨h, bF2⟩ := h; obtain ⟨h, bF1⟩ := h; obtain ⟨h, bX⟩ := h; obtain ⟨h, gX⟩ := h
  obtain ⟨h, bC7⟩ := h; obtain ⟨h, bEn⟩ := h; obtain ⟨gE, bE⟩ := h
  have bT : blockAtB cells Spike.Lib.X64.Flow.Ret0.StackTake.fnL 0 Spike.Lib.X64.Flow.Ret0.StackTake.stPro =
      true := by
    have ht := hin'
    unfold Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn at ht
    repeat (first | exact (cast (Bool.and_eq_true _ _) ht).2 | replace ht := (cast (Bool.and_eq_true _ _) ht).1)
  have hnx := fun {l off b} (hb : blockAtB cells l off b = true) hl h0 => notAb_of_blockAtB hI hpr hab hb hl h0
  have hpos : ∀ {l : Label} {b : List (Directive × Nat)}, blockAtB cells l 0 b = true →
      l ∉ Spike.Lib.X64.AllocG.abLabs → 0 < b.length → PosOff cells lab (lab l) := fun hb hl h0 => by
    have := posOff_of_blockAtB (lab := lab) hb hl h0
    rwa [ofNat_zero'] at this
  intro i
  cases i
  case e =>
    dsimp only [TiWAt]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat_zero' _) tiPro_ok hR (by omega) (by omega)
      (by have := hph.e; rw [ofNat_zero'] at this; exact this) tiPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1.trans hq) hpl0
    have := hpos bEn (by decide) (by decide)
    have hg := Scc.Cert.Rt.X64.label_labelGapB hI.lays gE
    rw [hI.labOk] at hg
    rw [show 0 + Spike.Lib.X64.cellOff tiPro tiPro.length = 12 by decide]
    rwa [hg] at this
  case entry =>
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bEn (ofNat_zero' _) tiArg_ok hR (by omega) (by omega)
      (by have := hph.entry; rw [ofNat_zero'] at this; exact this) tiArg_noRet (by decide)
      (fun _ => posOff_next bC7 (by decide) (by decide) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case c7 =>
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab (show blockAtB cells entryL 7 tiCall = true from bC7) rfl tiCall_ok hR
      (by omega) (by omega) hph.c7 tiCall_noRet (by decide) (fun h => absurd h (by decide))
      (labs_one (L0 := Spike.Lib.X64.Flow.Ret0.StackTake.fnL) (by decide) (hpos bT (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case call =>
    intro g hg j
    rw [hI.labOk] at hg
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -200) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    have hxo : lab x ∉ Spike.Lib.X64.WriteAb.abPcs lab := by
      have := hnx bX hx (by decide)
      rwa [ofNat_zero'] at this
    exact takeW_rtX hI hpr hab hin' hR' (by show (-200 : Int) ≤ -200; omega) (by show (8 : Int) ≤ 8; omega)
      (tiTake q g) hq hg hxo hphT hk hunL hunN hunX hoffL hoffX hpl0 j
  case x7 =>
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bX (ofNat_zero' _) tiSp_ok hR (by omega) (by omega)
      (by have := hph.x7; rw [ofNat_zero'] at this; exact this) tiSp_noRet hx
      (fun _ => posOff_next s0 hx (by decide) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st0 => ist s0 0 48 3 bF1
  case f1 => iblk bF1 tiF1_ok hph.f1 tiF1_noRet s1
  case st1 => ist s1 1 59 4 bF2
  case f2 => iblk bF2 tiZ_ok hph.f2 tiZ_noRet s2
  case st2 => ist s2 2 74 4 bF3
  case f3 => iblk bF3 tiZ_ok hph.f3 tiZ_noRet s3
  case st3 => ist s3 3 89 4 bF4
  case f4 => iblk bF4 tiF4_ok hph.f4 tiF4_noRet s4
  case st4 => ist s4 4 101 4 bF5
  case f5 => iblk bF5 tiF5_ok hph.f5 tiF5_noRet s5
  case st5 => ist s5 5 113 4 bRet
  case ret =>
    dsimp only [TiWAt]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl tiRet_ok hR (by omega) (by omega) hph.ret hx
      (hret_of_run tiRet_ok fun _ _ hJ => by
        dsimp only [tiNAt] at hJ ⊢
        rw [(tiRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (fun _ _ hJ => hJ.1.trans hq) hpl0

/-- **`scc_rt_thread_init`'s states inside `RtX`** (`tiWAt_rtX` at `.x7`). -/
theorem tiW_rtX (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hin : threadInitIn cells = true) {Λ' : Scc.Sem.Layout}
    {lbl : Lbl} {ar : Arena} {c0 : Ctl} {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64}
    {F M : MachineData → Prop} {R : Region} (hR : R.OK) (hlo : R.lo ≤ -248) (hhi : 8 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra x7L).toBitVec) (hraOff : ra x7L ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hph : TiPh okPc ph Tk lab ra)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hoffF : ∀ a ∈ tiAddrs q.tcb, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hin' : Spike.Lib.X64.Flow.Ret0.StackTake.stackTakeIn cells = true)
    (hphT : Spike.Lib.X64.Rt.Take.TakePh okPc ph Tk ownOf μ lab fun _ => lab x7L)
    (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hoffL : (⟨lockA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (lockA lab).toNat ∧ (lockA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffX : (⟨nextA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (nextA lab).toNat ∧ (nextA lab).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TiW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F M q i := fun i =>
  tiWAt_x7 (W := RtX Λ' μ ar lbl lab c0) i ▸
    tiWAt_rtX hI hpr hab (by decide) hin hR hlo hhi q hq hra hraOff hph.toAt hunF hoffF hin' hphT hk hunL hunN
      hunX hoffL hoffX hpl0 i

end Ti

/-! ## From the switch to `call scc_rt_main` -/

section Sw

open Spike.Lib.X64.Flow.Ret0 (startN6 startN7 startN8 startMain startTailIn x1L)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **The switch, `xorl %ebp, %ebp` and the call block after them inside
`RtX`** (`SwEW`), for any program with the start's tail (`hin`) and the
runtime's code (`hpr`, `hab`): their phase facts (`hsw`) and `scc_rt_main`
positioned off the write abort (`hmain`), in the new region of depth `L`
at the top `top` (`hL`, `hok`; vacuous off it), at the source control `c0`
placed at no frame (`hpl0`). -/
theorem swEW_rtX (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hin : startTailIn cells = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {R : Region} {F : MachineData → Prop} {rS : Range} {tcb top : BitVec 64} {L : Int}
    (hsw : Spike.Lib.X64.Rt.MainU.SwPh okPc ph lab) (hmain : PosOff cells lab (lab "scc_rt_main"))
    (hL : 8 ≤ L) (hok : (Spike.Lib.X64.swR top (-L) 0).OK) (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    Spike.Lib.X64.Rt.SwEW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F rS tcb top c0 L := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, bSw⟩, bXor⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_, fun v => ?_⟩
  · rw [hI.labOk]
    exact nodeW_rtX_reg (p := lab x1L + Int64.ofNat 28) hI (by rfl) bSw rfl rfl hsw.sw.1
      (by rw [← ofNat_add']; exact notAb_of_blockAtB hI hpr hab bXor (by decide) (by decide))
      (fun _ _ hJ => hJ.1) hpl0
  · rw [hI.labOk]
    exact nodeW_rtX_fi (p := lab x1L + Int64.ofNat 31) hI bXor rfl rfl hsw.xor.1
      (by rw [← ofNat_add']; exact notAb_of_blockAtB hI hpr hab bMain (by decide) (by decide))
      (fun _ _ hJ => hJ.1) hpl0
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact blkW_rtX hI hpr hab bMain rfl (Spike.Lib.X64.Rt.startMain_okL hL) hok (Int.le_refl _)
        (Int.le_refl _) hsw.main (by rfl) (by decide) (fun h => absurd h (by decide))
        (labs_one (L0 := "scc_rt_main") (by decide) hmain) (fun _ _ hJ => hJ.1) hpl0
    · exact Spike.Lib.X64.Rt.blkW_ofFalse fun _ h => hv h.1.1

end Sw

/-! ## `scc_rt_start` from `_start` to `call scc_rt_main` -/

section Start2

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option maxHeartbeats 1600000 in
open Spike.Lib.X64.Rt.PhOfTab Spike.Lib.X64.Rt.PhRecOf Spike.Lib.X64.Rt.StartU in
open Spike.Lib.X64.Flow.Ret0 (pnA pinA lockA freeNA nextA stacksA StackM x0L x1L startTailIn startCall2In
  startCall2 startCall2_ok startFs startFs_ok startSw startSw_ok) in
/-- **`scc_rt_start`'s states inside `RtX` from its entry to `call
scc_rt_main`** (`StartE1W`), at the record of an output passing `placeOK`,
in a region holding its frame and its callees' below (`hR`, `hlo`, `hhi`),
at the source control `c0` placed at no frame (`hpl0`), the frame condition
giving the runtime's words unloaded (`hFr`), room for the first stack
(`hk`), the runtime's words off the arena's counter and heap (`hoff`);
`scc_rt_main` positioned off the write abort (`hmain`), the new stack's
region (`hL`, `hok`). -/
theorem startE1W_rtX
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {k0 : BitVec 64} {L : Int}
    (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) (hk : k0.toNat + 16384 ≤ 536870912)
    (hoff : ∀ a ∈ (Ly).rtWords, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hmain : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main")) (hL : 8 ≤ L)
    (hok : (Spike.Lib.X64.swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    Spike.Lib.X64.Rt.StartE1W (RtX Λ' (Spike.Lib.X64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False)
      (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 L (Spike.Lib.X64.Rt.tiOf o.place.tail) := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hpr := printIn_of_placeOKAt h
  have hab := abortIn_of_placeOKAt h
  have hrc := Spike.Lib.X64.Rt.rtCodeTi_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hnx := fun {l off b} (hb : blockAtB o.prog l off b = true) hl h0 => notAb_of_blockAtB hI hpr hab hb hl h0
  have hpn : pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  have hlk : lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hfr : freeNA (Ly).lab = (Ly).freeNA := (Ly).lab_freeN
  have hnxa : nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  have h0 : ∃ j < 7, (Ly).pinA + 0#64 = (Ly).pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hcl2 := hrc.call2
  simp only [startCall2In, Bool.and_eq_true] at hcl2
  obtain ⟨cc2, -⟩ := hcl2
  have htl := hrc.tail
  simp only [startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨tFs, tSys⟩, tSw⟩, tSwp⟩, -⟩, -⟩ := htl
  have hti := Spike.Lib.X64.Rt.threadInitInAt_of_placeOKAt h
  have bT : blockAtB o.prog Spike.Lib.X64.Flow.Ret0.ThreadInit.fnL 0 Spike.Lib.X64.Flow.Ret0.ThreadInit.tiPro =
      true := by
    have ht := hti
    unfold Spike.Lib.X64.Flow.Ret0.ThreadInit.threadInitInAt at ht
    repeat (first | exact (cast (Bool.and_eq_true _ _) ht).2 | replace ht := (cast (Bool.and_eq_true _ _) ht).1)
  refine ⟨⟨startW_rtX h i (rS := rS) hR (by omega) (by omega) hpl0,
    startCall_rtX h i (rS := rS) hR (by omega) (by omega) hpl0, fun g hg j => ?_⟩,
    ⟨?_, fun g hg j => ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- `scc_rt_alloc_tcb`.
    rw [hI.labOk] at hg
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -184) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    have hx0 : (Ly).lab x0L ∉ Spike.Lib.X64.WriteAb.abPcs (Ly).lab := by
      have := hnx cc2 (by decide) (by decide); rwa [ofNat_zero'] at this
    exact tcbW_rtX hI hpr hab hrc.tcb hR' (by show (-184 : Int) ≤ -184; omega) (by show (8 : Int) ≤ 8; omega)
      ⟨g, 0#64, c0⟩ rfl hg hx0 (tcbPh_ofPlaceOK h i)
      (by show (0#64 : BitVec 64).toNat + 80 ≤ 131072; decide)
      (fun m hm => by rw [hpn]; exact Spike.Lib.X64.PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) h0)
      (by rw [hpn]; exact hoff _ (Ly).pn_mem)
      (by rw [hpin]; exact hoff _ (Spike.Lib.X64.PhRec.tcb_mem h0)) hpl0 j
  · -- `.x0`'s block.
    rw [hI.labOk]
    refine blkW_rtX hI hpr hab cc2 (ofNat_zero' _) startCall2_ok hR (by omega) (by omega)
      (by have := blkPh_of_factOk hl hr hn
            (hf (.blk Spike.Lib.X64.Rt.Code.Start.x0L 0 Spike.Lib.X64.Rt.Code.Start.startCall2 none none)
              (by simp [startPhTab]))
          rw [ofNat_zero'] at this; exact this)
      startCall2_noRet (by decide) (fun h => absurd h (by decide))
      (labs_one (L0 := Spike.Lib.X64.Flow.Ret0.ThreadInit.fnL) (by decide) ?_) (fun _ _ hJ => hJ.1.1.1) hpl0
    have := posOff_of_blockAtB (lab := (Ly).lab) bT (by decide) (by decide)
    rwa [ofNat_zero'] at this
  · -- `scc_rt_thread_init`.
    rw [hI.labOk] at hg
    have hR' := Region.callee_ok (kc := -48 - 0) (lo' := -248) (hi' := 8) hR (by omega) (by decide) (by omega)
      (by omega)
    have hx1 : (Ly).lab x1L ∉ Spike.Lib.X64.WriteAb.abPcs (Ly).lab := by
      have := hnx tFs (by decide) (by decide); rwa [ofNat_zero'] at this
    rw [hI.labOk]
    exact tiWAt_rtX hI hpr hab (by cases o.place.tail <;> decide) hti hR' (by show (-248 : Int) ≤ -248; omega)
      (by show (8 : Int) ≤ 8; omega) ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ rfl hg hx1 (tiPhAt_ofPlaceOK h i)
      (fun _ ha m hm => Spike.Lib.X64.PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => hoff _ (Spike.Lib.X64.PhRec.tcb_mem (tcb_fld ha)))
      hrc.take (takePhAt_ofPlaceOK h i) hk
      (fun m hm => by rw [hlk]; exact Spike.Lib.X64.PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact Spike.Lib.X64.PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnxa]; exact Spike.Lib.X64.PhRec.rtF_next (hFr m hm))
      (by rw [hlk]; exact hoff _ (Ly).lock_mem) (by rw [hnxa]; exact hoff _ (Ly).next_mem) hpl0 j
  · -- `.x1`'s block.
    rw [hI.labOk]
    exact blkW_rtX hI hpr hab tFs (ofNat_zero' _) startFs_ok hR (by omega) (by omega)
      (by have := blkPh_of_factOk hl hr hn
            (hf (.blk Spike.Lib.X64.Rt.Code.Start.x1L 0 Spike.Lib.X64.Rt.Code.Start.startFs none none)
              (by simp [startPhTab]))
          rw [ofNat_zero'] at this; exact this)
      startFs_noRet (by decide) (fun _ => posOff_next tSys (by decide) (by decide) (by decide))
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1.1) hpl0
  · -- `arch_prctl`'s `syscall`.
    rw [hI.labOk]
    have hs := step_of_factOk hl (hf (.step Spike.Lib.X64.Rt.Code.Start.x1L 18 2) (by simp [startPhTab]))
    exact nodeW_rtX_sys (p := (Ly).lab x1L + Int64.ofNat 18) hI tSys rfl rfl hs.1
      (by rw [← ofNat_add']; exact hnx tSw (by decide) (by decide)) (fun _ _ hJ => hJ.1) hpl0
  · -- The block before the switch.
    rw [hI.labOk]
    exact blkW_rtX hI hpr hab tSw rfl startSw_ok hR (by omega) (by omega)
      (blkPh_of_factOk hl hr hn
        (hf (.blk Spike.Lib.X64.Rt.Code.Start.x1L 20 Spike.Lib.X64.Rt.Code.Start.startSw none none)
          (by simp [startPhTab])))
      startSw_noRet (by decide) (fun _ => posOff_next tSwp (by decide) (by decide) (by decide))
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1) hpl0
  · -- The switch and the block after it.
    rw [hI.labOk]
    exact swEW_rtX hI hpr hab hrc.tail (swPh_ofPlaceOK h i) hmain hL hok hpl0

set_option maxHeartbeats 1600000 in
open Spike.Lib.X64.Rt.PhOfTab in
open Spike.Lib.X64.Rt (entryN0 entryN1 entryN2) in
open Spike.Lib.X64.Flow.Ret0 (stacksA) in
/-- **The start's states inside `RtX` up to `call scc_rt_main`**
(`StartEW`): `_start`'s three nodes, and `scc_rt_start`'s
(`startE1W_rtX`) in its callee region, at the record of an output passing
`placeOK`, in a region holding `_start`'s frame and its callees' below,
the premises otherwise `startE1W_rtX`'s. -/
theorem startEW_rtX
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {k0 : BitVec 64} {L : Int}
    (hR : R.OK) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.X64.Rt.rtF (Ly) m) (hk : k0.toNat + 16384 ≤ 536870912)
    (hoff : ∀ a ∈ (Ly).rtWords, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hmain : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main")) (hL : 8 ≤ L)
    (hok : (Spike.Lib.X64.swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    Spike.Lib.X64.Rt.StartEW (RtX Λ' (Spike.Lib.X64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False)
      (Ly).exe (Ly).endPc R F rS 0#64 k0 c0 L (Spike.Lib.X64.Rt.tiOf o.place.tail) := by
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hpr := printIn_of_placeOKAt h
  have hab := abortIn_of_placeOKAt h
  have hrc := Spike.Lib.X64.Rt.rtCode0_of_placeOKAt h
  have hl := lab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => startFact_ofPlaceOK h i (f := f) hf
  have hn : ∀ t, Scc.Cert.Rt.X64.deadN (Scc.Sem.X64.codeLabel (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.X64.deadN] at h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = (Ly).lab r + Int64.ofNat o' :=
    fun _ _ h => nomatch h
  have hnx := fun {l off b} (hb : blockAtB o.prog l off b = true) hl h0 => notAb_of_blockAtB hI hpr hab hb hl h0
  have he := hrc.start0
  simp only [Spike.Lib.X64.Rt.Code.Start.entryIn, Bool.and_eq_true] at he
  obtain ⟨⟨eX, eA⟩, eC⟩ := he
  have hst := hrc.start
  simp only [Spike.Lib.X64.Flow.startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨-, cb0⟩, -⟩, -⟩, -⟩ := hst
  refine ⟨⟨?_, ?_, ?_⟩, fun F' _ _ hF' => startE1W_rtX h i
    (Region.callee_ok (kc := -8) (lo' := -296) (hi' := 8) hR (by omega) (by decide) (by omega) (by omega))
    (by show (-296 : Int) ≤ -296; omega) (by show (8 : Int) ≤ 8; omega) (fun m hm => hFr m (hF' m hm)) hk hoff
    hmain hL hok hpl0⟩
  · -- `xorl %ebp, %ebp`.
    rw [hI.labOk]
    have hs := step_of_factOk hl (hf (.step "_start" 0 2) (by simp [startPhTab]))
    exact nodeW_rtX_fi (p := (Ly).lab "_start" + Int64.ofNat 0) hI eX rfl (ofNat_zero' _).symm hs.1
      (by rw [← ofNat_add']; exact hnx eA (by decide) (by decide)) (fun _ _ hJ => hJ) hpl0
  · -- `andq $-16, %rsp`.
    rw [hI.labOk]
    have hs := step_of_factOk hl (hf (.step "_start" 2 4) (by simp [startPhTab]))
    exact nodeW_rtX_and (p := (Ly).lab "_start" + Int64.ofNat 2) hI eA rfl rfl hs.1
      (by rw [← ofNat_add']; exact hnx eC (by decide) (by decide)) (fun _ _ hJ => hJ) hpl0
  · -- The call of `scc_rt_start`.
    rw [hI.labOk]
    have hph := blkPh_of_factOk hl hr hn
      (hf (.blk "_start" 6 Spike.Lib.X64.Rt.Code.Start.entryCall none none) (by simp [startPhTab]))
    refine blkW_rtX hI hpr hab eC (ofNat_add' _ 2 4) Spike.Lib.X64.Rt.entryCallB_ok hR (by omega) (by omega)
      (by show blkPh _ _ _ _ ((Ly).lab "_start" + Int64.ofNat 2 + Int64.ofNat 4) _ _ = true
          rw [← ofNat_add']; exact hph)
      (by rfl) (by decide) (fun h => absurd h (by decide))
      (labs_one (L0 := "scc_rt_start") (by decide) ?_) (fun _ _ hJ => hJ) hpl0
    have := posOff_of_blockAtB (lab := (Ly).lab) cb0 (by decide) (by decide)
    rwa [ofNat_zero'] at this

end Start2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.startW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startW_rtX

/-- info: 'Spike.Lib.LowerX64.startCall_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startCall_rtX

/-- info: 'Spike.Lib.LowerX64.tcbW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcbW_rtX

/-- info: 'Spike.Lib.LowerX64.takeW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms takeW_rtX

/-- info: 'Spike.Lib.LowerX64.tiWAt_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tiWAt_rtX

/-- info: 'Spike.Lib.LowerX64.tiW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tiW_rtX

/-- info: 'Spike.Lib.LowerX64.swEW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swEW_rtX

/-- info: 'Spike.Lib.LowerX64.startE1W_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startE1W_rtX

/-- info: 'Spike.Lib.LowerX64.startEW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_rtX

end Spike.Lib.LowerX64
