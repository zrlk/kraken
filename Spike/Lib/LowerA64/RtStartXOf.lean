/-
**`scc_rt_start`'s states inside `RtX`, for any placed output**: the
runtime's start nodes, at the record `RuntimeLayout.ofPlaceOK h i` of an
output passing `placeOK` whose program passes the decided phase table, keep
the write abort's phase, write nothing to the arena and hold the source
start's control placed at no frame (`RtX`, `Spike/Lib/LowerA64/RtStartX.lean`).

The facts are `startAllUW_gen`'s (`Spike/Lib/Rt/A64RtStartU.lean`): the code
(`rtCode0_of_placeOKAt`), the phase table's rows; the targets' positions off
the write abort are the next block's or node's (`posOff_of_blockAt`).

- `startW_rtX`: the entry's five nodes (`StartW`);
- `startCall_rtX`: the call block of `scc_rt_alloc_tcb` (`Sp0W.blk`);
- `tcbW_rtX`: `scc_rt_alloc_tcb`'s nodes (`TcbW`), for any program with its
  code; its stores' words off the arena's counter and heap given;
- `pairW_rtX`, `takeW_rtX`: a label address pair; `scc_rt_stack_take`'s
  nodes (`TakeW`), for any program with its code; its two written words off
  the arena's counter and heap given;
- `tiW_rtX`: `scc_rt_thread_init`'s nodes (`TiW`), its call's by `takeW_rtX`;
  the TCB's words off the arena's counter and heap given;
- `swEW_rtX`: the switch and the block after it (`SwEW`), the switch's
  phase, the block's and `scc_rt_main`'s position given;
- `startEW_rtX`: `_start` to `bl scc_rt_main` (`StartEW`) at a placed
  output, the runtime's words (`rtWords`) off the arena's counter and heap
  given (`hoff`, the one place of that fact), the switch's phase rows from
  `swPh_ofPlaceOK`, `scc_rt_main`'s position given.
-/
import Spike.Lib.LowerA64.RtStartX
import Spike.Lib.Rt.A64RtStartU
import Spike.Lib.Rt.A64StartE

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (ofNat4_succ' startN0 startN1)
open Spike.Lib.A64.Rt
open Spike.Lib.A64.Rt.StartU (b0_noRet startArgs_noRet startCall_noRet startE2 startE8)
open Scc.Cert.Rt.A64 (blockAt label_labelGap)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

/-- A block without branch labels meets any condition on them. -/
theorem labs_nil {b : List Directive} {P : Label → Prop} (h : blkLabs b = []) : ∀ L ∈ blkLabs b, P L := by
  rw [h]; simp

/-- A block with one branch label meets a condition on it. -/
theorem labs_one {b : List Directive} {L0 : Label} {P : Label → Prop} (h : blkLabs b = [L0]) (hp : P L0) :
    ∀ L ∈ blkLabs b, P L := by
  rw [h]; simpa using hp

/-- A block without the abort's entry among its labels never branches to it. -/
theorem noAbt {b : List Directive} (h : "scc_rt_abort" ∉ blkLabs b) :
    ∀ k (hk : k < b.length) a, classify b[k] = some a → aiLab a ≠ some "scc_rt_abort" :=
  fun k hk a ha hL => h (List.mem_filterMap.mpr ⟨b[k], List.getElem_mem hk, by simp only [ha, Option.bind_some, hL]⟩)

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

open PhRecOf PhOfTab in
/-- **The entry's five nodes inside `RtX`** (`StartW`), at the record of an
output passing `placeOK` whose program passes the table (`hrt`), in a region
holding the entry's frame, at the source start's control `c0` placed at no
frame (`hpl0`). -/
theorem startW_rtX
    (hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (rtPhTab none) = true)
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    StartW (RtX Λ' (Spike.Lib.A64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False) (Ly).exe (Ly).endPc R F
      (startN0 (Ly).lab c0).J := by
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hpr := printIn_of_placeOKAt h
  have hab := abortIn_of_placeOKAt h
  have hrc := rtCode0_of_placeOKAt h
  have hl := hlab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => Scc.Cert.Rt.A64.factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (Scc.Cert.Link.A64.codeOf (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (Ly).lab r := fun _ h => nomatch h
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨⟨g0, cb0⟩, cb1⟩, cb2⟩, cb3⟩, cb4⟩ := hst
  have hcl := hrc.call
  simp only [Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have hnx : ∀ {l : Label} {k : Nat} {b : List Directive}, blockAt o.prog l k b = true →
      l ∉ Spike.Lib.A64.AllocG.abLabs →
      0 < b.length → (Ly).lab l + Int64.ofNat (4 * k) ∉ Spike.Lib.A64.WriteAb.abPcs (Ly).lab :=
    fun hb hl' h0 => by
      have := notAbPc_of_posOff hI.lays hpr hab (posOff_of_blockAt (lab := (Ly).lab) hb hl' h0)
      rwa [Nat.add_zero] at this
  have hlg := label_labelGap hI.lays g0
  rw [hI.labOk] at hlg
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The frame's setup.
    have hph := blkPh_of_factOk hl hr hn
      (hf (.blk "scc_rt_start" 0 Spike.Lib.A64.Abort.b0 none none) (by simp [startPhTab]))
    rw [ofNat4_zero] at hph
    refine blkW_rtX hI hpr hab cb0 (ofNat4_zero _) Spike.Lib.A64.Abort.b0_ok hR hal (by omega) (by omega) hph b0_noRet
      (by decide) (fun _ => ?_) (labs_nil (by decide)) (fun _ _ hJ => hJ) hpl0
    have := posOff_of_blockAt (lab := (Ly).lab) cb1 (by decide) (i := 0) (by decide)
    rwa [Nat.add_zero, ofNat4_zero, hlg] at this
  · -- The `adrp`.
    have hs := step_of_factOk hl (hf (.step startE 0) (by simp [startPhTab]))
    exact nodeW_rtX_si (si := SI.adrp .X9 sigign) (p := (Ly).lab startE + Int64.ofNat (4 * 0)) hI cb1 rfl
      (ofNat4_zero _).symm hs.1 (by rw [ofNat4_succ']; exact hnx cb2 (by decide) (by decide))
      (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0
  · -- The `add`.
    have hs := step_of_factOk hl (hf (.step startE 1) (by simp [startPhTab]))
    exact nodeW_rtX_si (si := SI.addLo12 .X9 .X9 sigign) (p := (Ly).lab startE + Int64.ofNat (4 * 1)) hI cb2 rfl
      rfl hs.1 (by rw [ofNat4_succ']; exact hnx cb3 (by decide) (by decide))
      (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0
  · -- The arguments.
    have hph := blkPh_of_factOk hl hr hn (hf (.blk startE 2 startArgs none none) (by simp [startPhTab]))
    rw [← startE2] at hph
    refine blkW_rtX hI hpr hab cb3 (startE2 (Ly).lab).symm startArgs_ok hR hal (by omega) (by omega) hph
      startArgs_noRet (by decide) (fun _ => ?_) (labs_nil (by decide)) (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0
    exact posOff_of_blockAt (lab := (Ly).lab) cb4 (by decide) (i := 0) (by decide)
  · -- The system call.
    have hs := step_of_factOk hl (hf (.step startE 8) (by simp [startPhTab]))
    exact nodeW_rtX_svc (p := (Ly).lab startE + Int64.ofNat (4 * 8)) hI cb4 rfl (startE8 (Ly).lab) hs.1
      (by rw [ofNat4_succ']; exact hnx cc (by decide) (by decide)) (fun _ _ ⟨_, hJ, _⟩ => hJ) hpl0

open PhRecOf PhOfTab in
/-- **The call block of `scc_rt_alloc_tcb` inside `RtX`** (`Sp0W.blk`), as
`startW_rtX`: its call target `scc_rt_alloc_tcb`'s first block. -/
theorem startCall_rtX
    (hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (rtPhTab none) = true)
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    BlkW (RtX Λ' (Spike.Lib.A64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False) (Ly).exe (Ly).endPc R F
      (startN1 (Ly).lab c0) Ret0.startCall := by
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hrc := rtCode0_of_placeOKAt h
  have hl := hlab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => Scc.Cert.Rt.A64.factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (Scc.Cert.Link.A64.codeOf (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (Ly).lab r := fun _ h => nomatch h
  have hcl := hrc.call
  simp only [Ret0.startCallIn, Bool.and_eq_true] at hcl
  obtain ⟨cc, -⟩ := hcl
  have ht := hrc.tcb
  simp only [Ret0.AllocTcb.allocTcbIn, Bool.and_eq_true] at ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := ht
  exact blkW_rtX hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) cc rfl Ret0.startCall_ok hR hal
    (by omega) (by omega)
    (blkPh_of_factOk hl hr hn (hf (.blk startE 9 Code.Start.startCall none none) (by simp [startPhTab])))
    startCall_noRet (by decide) (fun h => absurd h (by decide))
    (fun L hL => by
      have hb : blkLabs Ret0.startCall = [Ret0.AllocTcb.fnL] := by decide
      have : L = Ret0.AllocTcb.fnL := by simpa [hb] using hL
      subst this
      have := posOff_of_blockAt (lab := (Ly).lab) bE (by decide) (i := 0) (by decide)
      rwa [Nat.add_zero, ofNat4_zero] at this)
    (fun _ _ hJ => hJ) hpl0

end Start

/-! ## `scc_rt_alloc_tcb` -/

section Tcb

open Spike.Lib.A64.Rt.Tcb Spike.Lib.A64.Flow.Ret0.AllocTcb
open Spike.Lib.A64.Flow.Ret0 (TN TcbG TcbW tcbN pnA pinA)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- A block's first position off the write abort's pcs, at a label off the
write abort's. -/
theorem notAb_of_blockAt (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {l : Label} {k : Nat} {b : List Directive} (hb : blockAt prog l k b = true)
    (hl : l ∉ Spike.Lib.A64.AllocG.abLabs) (h0 : 0 < b.length) :
    lab l + Int64.ofNat (4 * k) ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
  have := notAbPc_of_posOff hI.lays hpr hab (posOff_of_blockAt (lab := (_root_.Executable.labels exe).label) hb hl h0)
  rwa [Nat.add_zero, hI.labOk] at this

/-- **`scc_rt_alloc_tcb`'s states inside `RtX`**, for any program with the
function's code (`hin`) and the runtime's (`hpr`, `hab`), in any region
holding its frame, at the source control `c0` placed at no frame (`hq`,
`hpl0`), returning to `ra okL` (`hra`) off the write abort's pcs (`hraOff`),
its phase facts (`hph`), the counter's old value with room for a TCB
(`hn0`), its two words unmapped in private memory under the frame condition
(`hunP`, `hunH`) and off the arena's counter and heap (`hoffP`, `hoffH`). -/
theorem tcbW_rtX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hin : allocTcbIn prog = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {F : MachineData → Prop}
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (q : TcbG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hraOff : ra okL ∉ Spike.Lib.A64.WriteAb.abPcs lab)
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
  simp only [allocTcbIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gE, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := h
  have hc0 : ∀ (i : TN), ∀ σ c, (tcbN lab q i).J σ c → c = c0 := fun i σ c hJ => by
    cases i <;> exact hJ.1.trans hq
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnx := fun {l k b} (hb : blockAt prog l k b = true) hl h0 => notAb_of_blockAt hI hpr hab hb hl h0
  intro i
  cases i
  case e =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat4_zero _) atPro_ok hR hal (by omega) (by omega)
      (by have := hph.e; rw [ofNat4_zero] at this; exact this) atPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide))
      (hc0 .e) hpl0
    have := posOff_of_blockAt (lab := lab) bEn (by decide) (i := 0) (by decide)
    have hg := label_labelGap hI.lays gE
    rw [hI.labOk] at hg
    rwa [Nat.add_zero, ofNat4_zero, hg] at this
  case entry =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bEn (ofNat4_zero _) atChk_ok hR hal (by omega) (by omega)
      (by have := hph.entry; rw [ofNat4_zero] at this; exact this) (by decide)
      (fun _ _ _ k hk r hr => (noRet_false atChk_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_of_blockAt (lab := lab) bJ1 (by decide) (i := 0) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .entry) hpl0
    dsimp only [tcbN] at hJ ⊢
    rw [(atChk_walk lab _ hJ.2).1]
    exact posOff_of_blockAt (lab := lab) bJ1 (by decide) (i := 0) (by decide)
  case j1 =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bJ1 rfl atJ1_ok hR hal (by omega) (by omega) hph.j1 atJ1_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := lenL) (by decide) ?_) (hc0 .j1) hpl0
    have := posOff_of_blockAt (lab := lab) bLen (by decide) (i := 0) (by decide)
    rwa [Nat.add_zero, ofNat4_zero] at this
  case len =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bLen (ofNat4_zero _) atLen_ok hR hal (by omega) (by omega)
      (by have := hph.len; rw [ofNat4_zero] at this; exact this) atLen_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bA (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (hc0 .len) hpl0
  case adrp =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact nodeW_rtX_si hI bA rfl rfl (hsi _ (by simp [siPcs])).1
      (by rw [ofNat4_succ']; exact hnx bA1 (by decide) (by decide)) (hc0 .adrp) hpl0
  case add =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact nodeW_rtX_si hI bA1 rfl rfl (hsi _ (by simp [siPcs])).1
      (by rw [ofNat4_succ']; exact hnx bArg (by decide) (by decide)) (hc0 .add) hpl0
  case arg =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bArg rfl atArg_ok hR hal (by omega) (by omega) hph.arg atArg_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bRmw (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (hc0 .arg) hpl0
  case rmw =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine nodeW_rtX_ldop (p := lab lenL + Int64.ofNat (4 * 37)) hI bRmw rfl rfl hph.rmwOk
      (by rw [ofNat4_succ']; exact hnx bBnd (by decide) (by decide)) (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_)
      (hc0 .rmw) hpl0
    · have h10 : (σ.regs.getXReg .X10).toBitVec = pnA lab := hJ.2.2.2
      rw [h10]; exact hunP m hF
    · have h10 : (σ.regs.getXReg .X10).toBitVec = pnA lab := hJ.2.2.2
      rw [h10]; exact hoffP
  case bnd =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bBnd rfl atBnd_ok hR hal (by omega) (by omega) hph.bnd (by decide)
      (fun _ _ _ k hk r hr => (noRet_false atBnd_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_of_blockAt (lab := lab) bJ2 (by decide) (i := 0) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (hc0 .bnd) hpl0
    dsimp only [tcbN] at hJ ⊢
    rw [(atBnd_walk lab _ hJ.2.1 hJ.2.2 hn0).1, ← ofNat4_add]
    exact posOff_of_blockAt (lab := lab) bJ2 (by decide) (i := 0) (by decide)
  case j2 =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bJ2 rfl atJ2_ok hR hal (by omega) (by omega) hph.j2 atJ2_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := okL) (by decide) ?_) (hc0 .j2) hpl0
    have := posOff_of_blockAt (lab := lab) bO (by decide) (i := 0) (by decide)
    rwa [Nat.add_zero, ofNat4_zero] at this
  case ok =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact nodeW_rtX_si (p := lab okL + Int64.ofNat (4 * 0)) hI bO rfl (ofNat4_zero _).symm
      (hsi _ (by simp [siPcs])).1 (by rw [ofNat4_succ']; exact hnx bO1 (by decide) (by decide)) (hc0 .ok) hpl0
  case ok1 =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact nodeW_rtX_si hI bO1 rfl rfl (hsi _ (by simp [siPcs])).1
      (by rw [ofNat4_succ']; exact hnx bO2 (by decide) (by decide)) (hc0 .ok1) hpl0
  case ok2 =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bO2 rfl atOk_ok hR hal (by omega) (by omega) hph.ok2 atOk_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bH (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (hc0 .ok2) hpl0
  case hdr =>
    dsimp only [TcbW]; rw [hI.labOk]
    refine nodeW_rtX_st (p := lab okL + Int64.ofNat (4 * 29)) hI bH rfl rfl (hsi _ (by simp [siPcs])).1
      (by rw [ofNat4_succ']; exact hnx bRet (by decide) (by decide)) (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_)
      (hc0 .hdr) hpl0
    · have h10 : (σ.regs.getXReg .X10).toBitVec = pinA lab + q.n0 := hJ.2.2.2
      rw [rAddr_zero, h10]; exact hunH m hF
    · have h10 : (σ.regs.getXReg .X10).toBitVec = pinA lab + q.n0 := hJ.2.2.2
      rw [rAddr_zero, h10]; exact hoffH
  case ret =>
    dsimp only [TcbW]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl atRet_ok hR hal (by omega) (by omega) hph.ret (by decide)
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbN] at hJ ⊢
        rw [(atRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (hc0 .ret) hpl0

end Tcb

/-! ## `scc_rt_stack_take` -/

section Take

open Spike.Lib.A64.Rt.Take Spike.Lib.A64.Flow.Ret0.StackTake
open Spike.Lib.A64.Flow.Ret0 (TK TakeG TakeW takeNG labMid lockA freeNA nextA)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **A label address pair** `adrp x9, L; add x9, x9, :lo12:L` at `l`, `k`
inside `RtX`: both nodes off the sites, the position after the pair off the
write abort's pcs (`hnx2`). -/
theorem pairW_rtX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl} {R : Region} {F : MachineData → Prop}
    {L l : Label} {k : Nat} {sp : Int} {n : ND}
    (hb1 : blockAt prog l k [(SI.adrp .X9 L).toDir] = true)
    (hb2 : blockAt prog l (k + 1) [(SI.addLo12 .X9 .X9 L).toDir] = true) (hl : l ∉ Spike.Lib.A64.AllocG.abLabs)
    (hnx2 : lab l + Int64.ofNat (4 * (k + 2)) ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hp : n.pc = lab l + Int64.ofNat (4 * k)) (hok1 : okPc (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (hok2 : okPc (lab l + Int64.ofNat (4 * (k + 1))).toBitVec.toNat = true)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    NodeW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n ∧
      NodeW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F (labMid lab l L k sp n.J) :=
  ⟨nodeW_rtX_si hI hb1 rfl hp hok1 (by rw [ofNat4_succ']; exact notAb_of_blockAt hI hpr hab hb2 hl (Nat.succ_pos 0))
      hc0 hpl0,
    nodeW_rtX_si hI hb2 rfl (ofNat4_succ' _ _) hok2 (by rw [ofNat4_succ']; exact hnx2)
      (fun _ c ⟨_, hJ, _⟩ => hc0 _ c hJ) hpl0⟩

set_option maxHeartbeats 800000 in
/-- **`scc_rt_stack_take`'s states inside `RtX`**, for any program with the
function's code (`hin`) and the runtime's (`hpr`, `hab`), in any region
holding its frame, at the source control `c0` placed at no frame (`hq`,
`hpl0`), returning to `ra siteL` (`hra`) off the write abort's pcs
(`hraOff`), its phase facts (`hph`), room for the stack below `2^29` (`hk`),
its three words unmapped in private memory under the frame condition
(`hunL`, `hunN`, `hunX`) and its two written words off the arena's counter
and heap (`hoffL`, `hoffX`). -/
theorem takeW_rtX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hin : stackTakeIn prog = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {F M P : MachineData → Prop}
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -208) (hhi : 0 ≤ R.hi) (q : TakeG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra siteL).toBitVec) (hraOff : ra siteL ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hph : TakePh okPc ph Tk ownOf μ lab ra) (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hoffL : (⟨lockA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (lockA lab).toNat ∧ (lockA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffX : (⟨nextA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (nextA lab).toNat ∧ (nextA lab).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TakeW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F M q i P := by
  have h := hin
  simp only [stackTakeIn, labIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gE, bE⟩, bEn⟩, bCls⟩, bJ1⟩, ⟨bD0, bD1⟩⟩, bD2⟩, ⟨bD7, bD8⟩⟩, bD9⟩,
    ⟨bD14, bD15⟩⟩, bD16⟩, bSp0⟩, bSwp⟩, bSp3⟩, bLk0⟩, bLdn⟩, bLk2⟩, ⟨bB0, bB1⟩⟩, bB2⟩, bUnl⟩, ⟨bB6, bB7⟩⟩,
    bB8⟩, bNxt⟩, bB12⟩, bB21⟩, ⟨bOk0, bOk1⟩⟩, bOk2⟩, bTk⟩, gT⟩, bSite⟩, bRet⟩ := h
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnx := fun {l k b} (hb : blockAt prog l k b = true) hl h0 => notAb_of_blockAt hI hpr hab hb hl h0
  have hpos : ∀ {l : Label} {b : List Directive}, blockAt prog l 0 b = true → l ∉ Spike.Lib.A64.AllocG.abLabs →
      0 < b.length → PosOff prog lab (lab l) := fun hb hl h0 => by
    have := posOff_of_blockAt (lab := lab) hb hl (i := 0) h0
    rwa [Nat.add_zero, ofNat4_zero] at this
  have hc : ∀ (P : AS → Prop), ∀ σ c, (c = q.c0 ∧ P σ) → c = c0 := fun _ _ _ hJ => hJ.1.trans hq
  intro i
  cases i
  case e =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat4_zero _) stPro_ok hR hal (by omega) (by omega)
      (by have := hph.e; rw [ofNat4_zero] at this; exact this) stPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1.trans hq) hpl0
    have := hpos bEn (by decide) (by decide)
    have hg := label_labelGap hI.lays gE
    rw [hI.labOk] at hg
    rwa [hg] at this
  case entry =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bEn (ofNat4_zero _) stInit_ok hR hal (by omega) (by omega)
      (by have := hph.entry; rw [ofNat4_zero] at this; exact this) stInit_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := clsL) (by decide) (hpos bCls (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case cls =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bCls (ofNat4_zero _) stCls_ok hR hal (by omega) (by omega)
      (by have := hph.cls; rw [ofNat4_zero] at this; exact this) (by decide)
      (fun _ _ _ k hk r hr => (noRet_false stCls_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_of_blockAt (lab := lab) bJ1 (by decide) (i := 0) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    dsimp only [takeNG] at hJ ⊢
    rw [(stCls_walk lab _ hJ.2).1]
    exact posOff_of_blockAt (lab := lab) bJ1 (by decide) (i := 0) (by decide)
  case j1 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bJ1 rfl stJ1_ok hR hal (by omega) (by omega) hph.j1 stJ1_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := doneL) (by decide) (hpos bD0 (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bD0 bD1 (by decide) (hnx bD2 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bD2 rfl stFreeN_ok hR hal (by omega) (by omega) hph.d2 stFreeN_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bD7 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d7 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bD7 bD8 (by decide) (hnx bD9 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d9 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bD9 rfl stFree_ok hR hal (by omega) (by omega) hph.d9 stFree_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bD14 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d14 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bD14 bD15 (by decide) (hnx bD16 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case d16 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bD16 rfl stLock_ok hR hal (by omega) (by omega) hph.d16 stLock_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := spinL) (by decide) (hpos bSp0 (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case sp0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bSp0 (ofNat4_zero _) stSwp_ok hR hal (by omega) (by omega)
      (by have := hph.sp0; rw [ofNat4_zero] at this; exact this) stSwp_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bSwp (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case swp =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_rtX_swp (p := swpPc lab) hI bSwp rfl rfl hph.swpOk
      (by rw [ofNat4_succ']; exact hnx bSp3 (by decide) (by decide)) (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_)
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    · have h10 : (σ.regs.getXReg .X10).toBitVec = lockA lab := hJ.2.2.2
      rw [h10]; exact hunL m hF
    · have h10 : (σ.regs.getXReg .X10).toBitVec = lockA lab := hJ.2.2.2
      rw [h10]; exact hoffL
  case sp3 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bSp3 rfl stSpin_ok hR hal (by omega) (by omega) hph.sp3 (by decide)
      (fun _ _ _ k hk r hr => (noRet_false stSpin_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inr fun σ c hJ => ?_) (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    all_goals
      dsimp only [takeNG] at hJ ⊢
      rw [(stSpin_walk lab _ hJ.2.1 hJ.2.2).1]
      exact hpos bLk0 (by decide) (by decide)
  case lk0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bLk0 (ofNat4_zero _) stLdN_ok hR hal (by omega) (by omega)
      (by have := hph.lk0; rw [ofNat4_zero] at this; exact this) stLdN_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bLdn (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case ldn =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_rtX_ldr (p := freeNPc lab) hI bLdn rfl rfl hph.ldnOk
      (by rw [ofNat4_succ']; exact hnx bLk2 (by decide) (by decide)) (fun σ _ m hJ hF => ?_)
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    have h10 : (σ.regs.getXReg .X10).toBitVec = freeNA lab := hJ.2.2
    rw [Tcb.rAddr_zero, h10]; exact hunN m hF
  case lk2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bLk2 rfl stEmpty_ok hR hal (by omega) (by omega) hph.lk2 (by decide)
      (fun _ _ _ k hk r hr => (noRet_false stEmpty_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inr fun σ c hJ => ?_) (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    all_goals
      dsimp only [takeNG] at hJ ⊢
      rw [(stEmpty_walk lab _ hJ.2.1 hJ.2.2).1]
      exact hpos bB0 (by decide) (by decide)
  case b0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bB0 bB1 (by decide) (hnx bB2 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case b2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bB2 rfl stUnl_ok hR hal (by omega) (by omega) hph.b2 stUnl_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bUnl (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case unl =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_rtX_stlr (p := unlPc lab) hI bUnl rfl rfl hph.unlOk
      (by rw [ofNat4_succ']; exact hnx bB6 (by decide) (by decide)) (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_)
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    · have h10 : (σ.regs.getXReg .X10).toBitVec = lockA lab := hJ.2.2.2
      rw [h10]; exact hunL m hF
    · have h10 : (σ.regs.getXReg .X10).toBitVec = lockA lab := hJ.2.2.2
      rw [h10]; exact hoffL
  case b6 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bB6 bB7 (by decide) (hnx bB8 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case b8 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bB8 rfl stAdd_ok hR hal (by omega) (by omega) hph.b8 stAdd_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bNxt (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case nxt =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine nodeW_rtX_ldop (p := nextPc lab) hI bNxt rfl rfl hph.nxtOk
      (by rw [ofNat4_succ']; exact hnx bB12 (by decide) (by decide)) (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_)
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    · have h10 : (σ.regs.getXReg .X10).toBitVec = nextA lab := hJ.2.2.2
      rw [h10]; exact hunX m hF
    · have h10 : (σ.regs.getXReg .X10).toBitVec = nextA lab := hJ.2.2.2
      rw [h10]; exact hoffX
  case b12 =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtXG hI hpr hab bB12 rfl stBnd_ok hR hal (by omega) (by omega) hph.b12 (by decide)
      (fun _ _ _ k hk r hr => (noRet_false stBnd_noRet k hk r hr).elim) (fun h => absurd h (by decide))
      (fun _ => .inl (posOff_of_blockAt (lab := lab) bB21 (by decide) (i := 0) (by decide)))
      (fun L _ _ => .inr fun σ c hJ => ?_)
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
    dsimp only [takeNG] at hJ ⊢
    rw [(stBnd_walk lab _ hJ.2.1 hJ.2.2 hk).1, ← ofNat4_add]
    exact posOff_of_blockAt (lab := lab) bB21 (by decide) (i := 0) (by decide)
  case b21 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bB21 rfl stJ2_ok hR hal (by omega) (by omega) hph.b21 stJ2_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := okL) (by decide) (hpos bOk0 (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case ok0 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact pairW_rtX hI hpr hab bOk0 bOk1 (by decide) (hnx bOk2 (by decide) (by decide)) rfl
      (hsi _ (by simp [siPcs])).1 (hsi _ (by simp [siPcs])).1 (fun _ _ hJ => hJ.1.trans hq) hpl0
  case ok2 =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bOk2 rfl stOk_ok hR hal (by omega) (by omega) hph.ok2 stOk_noRet (by decide)
      (fun h => absurd h (by decide)) (labs_one (L0 := takenL) (by decide) (hpos bTk (by decide) (by decide)))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case tk =>
    dsimp only [TakeW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bTk (ofNat4_zero _) stSite_ok hR hal (by omega) (by omega)
      (by have := hph.tk; rw [ofNat4_zero] at this; exact this) stSite_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1.trans hq) hpl0
    have := hpos bSite (by decide) (by decide)
    have hg := label_labelGap hI.lays gT
    rw [hI.labOk] at hg
    rwa [hg] at this
  case site =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact site_rtX hI bSite (ofNat4_zero _) rfl (hnx bRet (by decide) (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case ret =>
    dsimp only [TakeW]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl stRet_ok hR hal (by omega) (by omega) hph.ret (by decide)
      (hret_of_run stRet_ok fun _ _ hJ => by
        dsimp only [takeNG] at hJ ⊢
        rw [(stRet_walk lab _ hJ.2.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (fun _ _ hJ => hJ.2.1.trans hq) hpl0

end Take

/-! ## `scc_rt_thread_init` -/

section Ti

open Spike.Lib.A64.Rt.Ti Spike.Lib.A64.Flow.Ret0.ThreadInit
open Spike.Lib.A64.Flow.Ret0 (TI TiG TiW tiN tiTake lockA freeNA nextA rAddr_x10)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

set_option hygiene false in
/-- A store of a TCB field of `scc_rt_thread_init` inside `RtX`. -/
local macro "tstX " b:term:max j:term:max nb:term:max : tactic =>
  `(tactic| focus
    dsimp only [TiW]; rw [hI.labOk]
    have hs := hph.st (storePc lab $j) (by simp [stPcs])
    have ha : q.tcb + BitVec.ofNat 64 (8 * $j) ∈ tiAddrs q.tcb := by simp [tiAddrs]
    refine nodeW_rtX_st (p := storePc lab $j) hI $b rfl rfl hs.1
      (by rw [ofNat4_succ']; exact hnx $nb (by decide) (by decide))
      (fun σ _ m hJ hF => ?_) (fun σ _ hJ => ?_) (fun _ _ hJ => hJ.1.trans hq) hpl0
    · rw [rAddr_x10 hJ.2.2.2]; exact hunF _ ha m hF.1
    · rw [rAddr_x10 hJ.2.2.2]; exact hoffF _ ha)

set_option maxHeartbeats 800000 in
/-- **`scc_rt_thread_init`'s states inside `RtX`**, for any program with the
function's code (`hin`) and the runtime's (`hpr`, `hab`), in any region
holding its frame and the take's below, at the source control `c0` placed at
no frame (`hq`, `hpl0`), returning to `ra spL` (`hra`) off the write abort's
pcs (`hraOff`), its phase facts (`hph`), the TCB's six words unmapped in
private memory under the frame condition (`hunF`) and off the arena's
counter and heap (`hoffF`), and at its call `scc_rt_stack_take`'s premises
of `takeW_rtX` (`hin'` to `hoffX`), returning to `.sp0`. -/
theorem tiW_rtX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hin : threadInitIn prog = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {F M P : MachineData → Prop}
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) (q : TiG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra spL).toBitVec) (hraOff : ra spL ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hph : TiPh okPc ph Tk lab ra)
    (hunF : ∀ a ∈ tiAddrs q.tcb, ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hoffF : ∀ a ∈ tiAddrs q.tcb, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hin' : Ret0.StackTake.stackTakeIn prog = true)
    (hphT : Spike.Lib.A64.Rt.Take.TakePh okPc ph Tk ownOf μ lab fun _ => lab spL)
    (hk : q.k0.toNat + 16384 ≤ 536870912)
    (hunL : ∀ m, F m → Mem.loadInt m.dmem (lockA lab) 8 = none)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (freeNA lab) 8 = none)
    (hunX : ∀ m, F m → Mem.loadInt m.dmem (nextA lab) 8 = none)
    (hoffL : (⟨lockA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (lockA lab).toNat ∧ (lockA lab).toNat < ar.heap + 16 * ar.cells))
    (hoffX : (⟨nextA lab, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (nextA lab).toNat ∧ (nextA lab).toNat < ar.heap + 16 * ar.cells))
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    ∀ i, TiW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F M q i P := by
  have h := hin
  simp only [threadInitIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨gE, bE⟩, bEn⟩, bSp⟩, bS0⟩, bF1⟩, bS1⟩, bF2⟩, bS2⟩, bF3⟩, bS3⟩, bF4⟩, bS4⟩, bF5⟩, bS5⟩,
    bRet⟩ := h
  rw [st0_eq] at bS0; rw [st1_eq] at bS1; rw [st2_eq] at bS2
  rw [st3_eq] at bS3; rw [st4_eq] at bS4; rw [st5_eq] at bS5
  have hnx := fun {l k b} (hb : blockAt prog l k b = true) hl h0 => notAb_of_blockAt hI hpr hab hb hl h0
  intro i
  cases i
  case e =>
    dsimp only [TiW]; rw [hI.labOk]
    refine blkW_rtX hI hpr hab bE (ofNat4_zero _) tiPro_ok hR hal (by omega) (by omega)
      (by have := hph.e; rw [ofNat4_zero] at this; exact this) tiPro_noRet (by decide) (fun _ => ?_)
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1.trans hq) hpl0
    have := posOff_of_blockAt (lab := lab) bEn (by decide) (i := 0) (by decide)
    have hg := label_labelGap hI.lays gE
    rw [hI.labOk] at hg
    rwa [Nat.add_zero, ofNat4_zero, hg] at this
  case entry =>
    dsimp only [TiW]; rw [hI.labOk]
    have ht := hin'
    simp only [Ret0.StackTake.stackTakeIn, Bool.and_eq_true] at ht
    have bT := ht.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
    exact blkW_rtX hI hpr hab bEn (ofNat4_zero _) tiCall_ok hR hal (by omega) (by omega)
      (by have := hph.entry; rw [ofNat4_zero] at this; exact this) tiCall_noRet (by decide)
      (fun h => absurd h (by decide))
      (labs_one (L0 := Ret0.StackTake.fnL) (by decide) (by
        have := posOff_of_blockAt (lab := lab) bT (by decide) (i := 0) (by decide)
        rwa [Nat.add_zero, ofNat4_zero] at this))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case call =>
    intro g hg j
    rw [hI.labOk] at hg
    have hlo' : R.lo ≤ oI.sp + -208 := by show R.lo ≤ -48 + -208; omega
    have hkc : oI.sp < R.hi := by show (-48 : Int) < R.hi; omega
    have hR' := Region.callee_ok (hi' := 0) hR hlo' (by decide) hkc (by show (-48 : Int) + 0 ≤ R.hi; omega)
    have hb' := Region.callee_base (hi' := 0) hR hlo' (by decide) hkc
    have hal' : (R.callee oI.sp (-208) 0).base.toNat % 16 = 0 := by
      have : (((R.callee oI.sp (-208) 0).base.toNat : Int)) % 16 = 0 := by
        rw [hb']; show ((R.base.toNat : Int) + -48) % 16 = 0; omega
      omega
    have hspOff : lab spL ∉ Spike.Lib.A64.WriteAb.abPcs lab := by
      have := hnx bSp (by decide) (by decide)
      rwa [ofNat4_zero] at this
    exact takeW_rtX hI hpr hab hin' hR' hal' (by show (-208 : Int) ≤ -208; omega) (by show (0 : Int) ≤ 0; omega)
      (tiTake q g) hq hg hspOff hphT hk (fun m h => hunL m h.1) (fun m h => hunN m h.1)
      (fun m h => hunX m h.1) hoffL hoffX hpl0 j
  case sp =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bSp (ofNat4_zero _) tiSp_ok hR hal (by omega) (by omega)
      (by have := hph.sp; rw [ofNat4_zero] at this; exact this) tiSp_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS0 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st0 => tstX bS0 0 bF1
  case f1 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bF1 rfl tiF1_ok hR hal (by omega) (by omega) hph.f1 tiF1_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS1 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st1 => tstX bS1 1 bF2
  case f2 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bF2 rfl tiF2_ok hR hal (by omega) (by omega) hph.f2 tiF2_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS2 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st2 => tstX bS2 2 bF3
  case f3 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bF3 rfl tiF3_ok hR hal (by omega) (by omega) hph.f3 tiF3_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS3 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st3 => tstX bS3 3 bF4
  case f4 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bF4 rfl tiF4_ok hR hal (by omega) (by omega) hph.f4 tiF4_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS4 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st4 => tstX bS4 4 bF5
  case f5 =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtX hI hpr hab bF5 rfl tiF5_ok hR hal (by omega) (by omega) hph.f5 tiF5_noRet (by decide)
      (fun _ => posOff_of_blockAt (lab := lab) bS5 (by decide) (i := 0) (by decide)) (labs_nil (by decide))
      (fun _ _ hJ => hJ.1.trans hq) hpl0
  case st5 => tstX bS5 5 bRet
  case ret =>
    dsimp only [TiW]; rw [hI.labOk]
    exact blkW_rtXG hI hpr hab bRet rfl tiRet_ok hR hal (by omega) (by omega) hph.ret (by decide)
      (hret_of_run tiRet_ok fun _ _ hJ => by
        dsimp only [tiN] at hJ ⊢
        rw [(tiRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ => hraOff) (fun h => absurd h (by decide)) (labs_nil (by decide))
      (fun _ _ _ k hk a ha hL => absurd hL (noAbt (by decide) k hk a ha)) (fun _ _ hJ => hJ.1.trans hq) hpl0

end Ti

/-! ## From the switch to `bl scc_rt_main` -/

section Sw

open Spike.Lib.A64.Flow.Ret0 (startN5 startN6 startMain startTailIn sp3L)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}

/-- **The switch and the block after it inside `RtX`** (`SwEW`), for any
program with the start's tail (`hin`) and the runtime's code (`hpr`,
`hab`): the switch off the sites (`hswOk`), the block's phase check
(`hmPh`) and `scc_rt_main` positioned off the write abort (`hmain`), in the
new region of depth `L` at the 16-aligned top `top` (`h16`, `hok`; vacuous
off it), at the source control `c0` placed at no frame (`hpl0`). -/
theorem swEW_rtX (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hin : startTailIn prog = true) {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {c0 : Ctl}
    {R : Region} {F : MachineData → Prop} {rS : Range} {tcb top : BitVec 64} {L : Int} {dead : Nat → Bool}
    {ra : Int64} (hswOk : okPc (lab sp3L + Int64.ofNat (4 * 5)).toBitVec.toNat = true)
    (hmPh : blkPh okPc ph dead lab (lab sp3L + Int64.ofNat (4 * 6)) ra startMain = true)
    (hmain : PosOff prog lab (lab "scc_rt_main")) (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    Spike.Lib.A64.Rt.SwEW (RtX Λ' μ ar lbl lab c0) (fun _ _ => False) exe endPc R F rS tcb top c0 L := by
  have h := hin
  simp only [startTailIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, bSw⟩, bMain⟩ := h
  refine ⟨?_, fun v => ?_⟩
  · rw [hI.labOk]
    exact nodeW_rtX_reg (p := lab sp3L + Int64.ofNat (4 * 5)) hI (by rfl) bSw rfl rfl hswOk
      (by rw [ofNat4_succ']; exact notAb_of_blockAt hI hpr hab bMain (by decide) (by decide))
      (fun _ _ hJ => hJ.1) hpl0
  · by_cases hv : v = top
    · subst hv
      rw [hI.labOk]
      exact blkW_rtX hI hpr hab bMain rfl (Spike.Lib.A64.Rt.startMain_okL (-L) 0) hok h16 (Int.le_refl _)
        (Int.le_refl _) hmPh (by rfl) (by decide) (fun h => absurd h (by decide))
        (labs_one (L0 := "scc_rt_main") (by decide) hmain) (fun _ _ hJ => hJ.1) hpl0
    · exact fun _ _ _ _ _ _ _ _ hD _ => (hv hD.1.1).elim

end Sw

/-! ## `scc_rt_start` from `_start` to `bl scc_rt_main` -/

section Start2

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

set_option maxHeartbeats 1600000 in
open Spike.Lib.A64.Rt.StartU PhRecOf PhOfTab in
open Spike.Lib.A64.Flow.Ret0 (pnA pinA lockA freeNA nextA stacksA StackM sp3L) in
/-- **`scc_rt_start`'s states inside `RtX`** (`StartEW`, from `_start` to
`bl scc_rt_main`), at the record of an output passing `placeOK` (its phase
table, `rtPh_of_placeOKAt`, with the switch's rows, `swPh_ofPlaceOK`), in a region holding its frame and its
callees' below, at the source control `c0` placed at no frame (`hpl0`), the
frame condition giving the runtime's words unloaded (`hFr`), the first TCB
(`hn0`) and room for the first stack (`hk`), the runtime's words off the
arena's counter and heap (`hoff`); `scc_rt_main` positioned off the write
abort (`hmain`), the new stack's top 16-aligned with its region
(`h16`, `hok`). -/
theorem startEW_rtX
    {Λ' : Scc.Sem.Layout} {lbl : Lbl} {ar : Arena} {rS : Range} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {n0 k0 : BitVec 64} {L : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m) (hn0 : n0 = 0#64) (hk : k0.toNat + 16384 ≤ 536870912)
    (hoff : ∀ a ∈ (Ly).rtWords, (⟨a, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ a.toNat ∧ a.toNat < ar.heap + 16 * ar.cells))
    (hmain : PosOff o.prog (Ly).lab ((Ly).lab "scc_rt_main"))
    (h16 : (stacksA (Ly).lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (Ly).lab + k0 + 16384#64) (-L) 0).OK)
    (hpl0 : ∀ s, PlacedS Λ' lbl s c0 []) :
    Spike.Lib.A64.Rt.StartEW (RtX Λ' (Spike.Lib.A64.PhRec.μ (Ly)) ar lbl (Ly).lab c0) (fun _ _ => False)
      (Ly).exe (Ly).endPc R F rS n0 k0 c0 L := by
  subst hn0
  have hrt : Scc.Cert.Rt.A64.rtPhOk (Ly).Λ.code.lo o.prog (Ly).Λ (rtPhTab none) = true := rtPh_of_placeOKAt h
  have hsw := swPh_ofPlaceOK h i hrt
  have hI := Spike.Lib.A64.PhRec.instOk_ofPlaceOK h i (rS := rS)
  have hpr := printIn_of_placeOKAt h
  have hab := abortIn_of_placeOKAt h
  have hrc := rtCode0_of_placeOKAt h
  have hl := hlab_ofPlaceOK h i
  have hf : ∀ f ∈ startPhTab, _ := fun f hf => Scc.Cert.Rt.A64.factOk_of_rtPhOk (f := f) hrt
    (by simp [rtPhTab, hf])
  have hn : ∀ t, Scc.Cert.Rt.A64.deadN (Scc.Cert.Link.A64.codeOf (Ly).Λ.code.lo o.prog) none t = true →
      (fun _ => false) t = true := fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, (none : Option String) = some r → (0 : Int64) = (Ly).lab r := fun _ h => nomatch h
  have hnx := fun {l k b} (hb : blockAt o.prog l k b = true) hl h0 => notAb_of_blockAt hI hpr hab hb hl h0
  have hpn : pnA (Ly).lab = (Ly).pnA := (Ly).lab_pn
  have hpin : pinA (Ly).lab = (Ly).pinA := (Ly).lab_pin
  have hlk : lockA (Ly).lab = (Ly).lockA := (Ly).lab_lock
  have hfr : freeNA (Ly).lab = (Ly).freeNA := (Ly).lab_freeN
  have hnxa : nextA (Ly).lab = (Ly).nextA := (Ly).lab_next
  have h0 : ∃ j < 7, (Ly).pinA + 0#64 = (Ly).pinA + BitVec.ofNat 64 (8 * j) := ⟨0, by decide, by simp⟩
  have hst := hrc.start
  simp only [startIn, Bool.and_eq_true] at hst
  obtain ⟨⟨⟨⟨⟨-, cb0⟩, -⟩, -⟩, -⟩, -⟩ := hst
  have htl := hrc.tail
  simp only [Ret0.startTailIn, Bool.and_eq_true] at htl
  obtain ⟨⟨⟨⟨⟨t0, -⟩, t2⟩, t3⟩, t4⟩, -⟩ := htl
  have hti := hrc.ti
  simp only [Ret0.ThreadInit.threadInitIn, Bool.and_eq_true] at hti
  have bT := hti.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨?_, ⟨startW_rtX h i hrt (rS := rS) hR hal (by omega) hhi hpl0,
    startCall_rtX h i hrt (rS := rS) hR hal (by omega) hhi hpl0, fun g hg j => ?_⟩,
    ⟨?_, fun g hg j => ?_, ?_, ?_⟩, ?_⟩
  · -- `_start`'s branch.
    rw [hI.labOk]
    refine blkW_rtX hI hpr hab hrc.entry (ofNat4_zero _) Ret0.entryB_ok hR hal (by omega) (by omega)
      (by have := blkPh_of_factOk hl hr hn (hf (.blk "_start" 0 Code.Start.entryB none none)
            (by simp [startPhTab])); rw [ofNat4_zero] at this; exact this)
      (by rfl) (by decide) (fun h => absurd h (by decide))
      (labs_one (L0 := "scc_rt_start") (by decide) ?_) (fun _ _ hJ => hJ) hpl0
    have := posOff_of_blockAt (lab := (Ly).lab) cb0 (by decide) (i := 0) (by decide)
    rwa [Nat.add_zero, ofNat4_zero] at this
  · -- `scc_rt_alloc_tcb`.
    rw [hI.labOk] at hg
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -192) hR hal
      (by show R.lo ≤ -48 + -192; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    have hsp2 : (Ly).lab Ret0.sp2L ∉ Spike.Lib.A64.WriteAb.abPcs (Ly).lab := by
      have := hnx t0 (by decide) (by decide); rwa [ofNat4_zero] at this
    exact tcbW_rtX hI hpr hab hrc.tcb hR' hal' (by show (-192 : Int) ≤ -192; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, 0#64, c0⟩ rfl hg hsp2 (tcbPh_ofPlaceOK h i hrt)
      (by show (0#64 : BitVec 64).toNat + 80 ≤ 131072; simp)
      (fun m hm => by rw [hpn]; exact Spike.Lib.A64.PhRec.rtF_pn (hFr m hm))
      (fun m hm => by rw [hpin]; exact Spike.Lib.A64.PhRec.rtF_hdr0 (hFr m hm))
      (by rw [hpn]; exact hoff _ (Ly).pn_mem)
      (by rw [hpin]; exact hoff _ (Spike.Lib.A64.PhRec.tcb_mem h0)) hpl0 j
  · -- `.sp2`'s block.
    rw [hI.labOk]
    refine blkW_rtX hI hpr hab t0 (ofNat4_zero _) Ret0.startCall2_ok hR hal (by omega) (by omega)
      (by have := blkPh_of_factOk hl hr hn
            (hf (.blk Code.Start.sp2L 0 Code.Start.startCall2 none none) (by simp [startPhTab]))
          rw [ofNat4_zero] at this; exact this)
      startCall2_noRet (by decide) (fun h => absurd h (by decide))
      (labs_one (L0 := Ret0.ThreadInit.fnL) (by decide) ?_) (fun _ _ hJ => hJ.1) hpl0
    have := posOff_of_blockAt (lab := (Ly).lab) bT (by decide) (i := 0) (by decide)
    rwa [Nat.add_zero, ofNat4_zero] at this
  · -- `scc_rt_thread_init`.
    rw [hI.labOk] at hg
    obtain ⟨hR', hal'⟩ := callee_facts (kc := Spike.Lib.A64.Abort.oI.sp) (lo' := -256) hR hal
      (by show R.lo ≤ -48 + -256; omega) (by decide) (by show (-48 : Int) < R.hi; omega) (by decide)
    have hsp3 : (Ly).lab sp3L ∉ Spike.Lib.A64.WriteAb.abPcs (Ly).lab := by
      have := hnx t2 (by decide) (by decide); rwa [ofNat4_zero] at this
    exact tiW_rtX hI hpr hab hrc.ti hR' hal' (by show (-256 : Int) ≤ -256; omega)
      (by show (0 : Int) ≤ 0; omega) ⟨g, pinA (Ly).lab + 0#64 + 8#64, k0, c0⟩ rfl hg hsp3
      (tiPh_ofPlaceOK h i hrt)
      (fun _ ha m hm => Spike.Lib.A64.PhRec.rtF_tcb (hFr m hm) (tcb_fld ha))
      (fun _ ha => hoff _ (Spike.Lib.A64.PhRec.tcb_mem (tcb_fld ha)))
      hrc.take (takePh_ofPlaceOK h i hrt) hk
      (fun m hm => by rw [hlk]; exact Spike.Lib.A64.PhRec.rtF_lock (hFr m hm))
      (fun m hm => by rw [hfr]; exact Spike.Lib.A64.PhRec.rtF_freeN (hFr m hm))
      (fun m hm => by rw [hnxa]; exact Spike.Lib.A64.PhRec.rtF_next (hFr m hm))
      (by rw [hlk]; exact hoff _ (Ly).lock_mem) (by rw [hnxa]; exact hoff _ (Ly).next_mem) hpl0 j
  · -- `.sp3`'s block.
    rw [hI.labOk]
    exact blkW_rtX hI hpr hab t2 (ofNat4_zero _) Ret0.startSw0_ok hR hal (by omega) (by omega)
      (by have := blkPh_of_factOk hl hr hn
            (hf (.blk Code.Start.sp3L 0 Code.Start.startSw0 none none) (by simp [startPhTab]))
          rw [ofNat4_zero] at this; exact this)
      startSw0_noRet (by decide) (fun _ => posOff_of_blockAt (lab := (Ly).lab) t3 (by decide) (i := 0) (by decide))
      (labs_nil (by decide)) (fun _ _ hJ => hJ.1) hpl0
  · -- The `msr`.
    rw [hI.labOk]
    have hs := step_of_factOk hl (hf (.step Code.Start.sp3L 4) (by simp [startPhTab]))
    exact nodeW_rtX_si (si := SI.msr .X10) (p := (Ly).lab sp3L + Int64.ofNat (4 * 4)) hI t3 rfl rfl hs.1
      (by rw [ofNat4_succ']; exact hnx t4 (by decide) (by decide)) (fun _ _ hJ => hJ.1) hpl0
  · -- The switch and the block after it.
    exact swEW_rtX hI hpr hab hrc.tail hsw.sw.1 hsw.main hmain h16 hok hpl0

end Start2

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.startW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startW_rtX

/-- info: 'Spike.Lib.LowerA64.startCall_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startCall_rtX

/-- info: 'Spike.Lib.LowerA64.tcbW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tcbW_rtX

/-- info: 'Spike.Lib.LowerA64.pairW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pairW_rtX

/-- info: 'Spike.Lib.LowerA64.takeW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms takeW_rtX

/-- info: 'Spike.Lib.LowerA64.tiW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tiW_rtX

/-- info: 'Spike.Lib.LowerA64.swEW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms swEW_rtX

/-- info: 'Spike.Lib.LowerA64.startEW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEW_rtX

end Spike.Lib.LowerA64
