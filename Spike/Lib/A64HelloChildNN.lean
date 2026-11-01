/-
**hello.w's worker thread and child stub off the transfer sites** (hello
plan (4b-i), `WCompatH.noSite`, AArch64): `HThrHead.seg_thrHead`,
`thr_prologue_seg`, `Child.seg_thrWorker` and `Child.seg_childStub`
(`Spike/Lib/A64HelloThr.lean`, `Spike/Lib/A64HelloChild.lean`) inside
hello's fragment `SegTC (NNZH exe endPc Z)` (`Spike/Lib/A64HelloNN.lean`).

The proofs are the originals', with the leaves off the transfer sites
(`seg_ndNNA`, `prologue_seg_ofNNA`, `HThrTail.seg_thrTailNN`, each wake's
`NNZ` then `SegTC.toH`; the call `call_ndTS` at `S := NNZH`). `wc_worker` is
given inside `NNZH` (`hwk`; `Hello.Wk.seg_wcWorkerHANN`). `Z` is asked at
every node's states (`NodeZA`) and at the prologue's (`ProW`, `hz`;
`ProW.ofPcs` from a fact of the pcs).

- `HThrHead.seg_thrHeadH`: the head, `hwk` inside `NNZH`.
- `thr_prologue_segNN`: `thr_prologue_seg` inside `NNZ`.
- `Child.seg_thrWorkerH`: the worker thread, to any fragment.
- `Child.cLen`, `Child.cBlk`, `Child.seg_childStubH`: the child's stub, to any
  fragment.
-/
import Spike.Lib.A64HelloThrNN
import Spike.Lib.A64HelloChild
import Spike.Lib.A64HelloNN

namespace Spike.Lib.A64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

namespace HThrHead

section ProofH

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {Z : Frag isaLSE2}

/-- **`seg_thrHead` inside `NNZH`** (`hwk` inside `NNZH`): the block off the
transfer sites (`seg_ndNNA`, then `SegTC.toH`), the call `call_ndTS`. -/
theorem seg_thrHeadH {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -144 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R' F' (Ne g))
          (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-144) 0).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZE : NodeZA Z exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e) thE) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e))
      (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (Q := At exe endPc R F (tN pfx lab J L .call))
    ((SegTC.toH (seg_ndNNA (N := fun _ : Unit => tN pfx lab J L .call) (E := (nofun : Empty → ND))
      (by simp [thE]) thE_ok (by simp [thE, notNop]) hF hR hal hlo hhi hcodeE (fun σ c hJ => ?_) hZE))
      |>.mono_post ?_) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTS (lo' := -144) (hi' := 0) hR hal hF (by show R.lo ≤ -80 + -144; omega) (by decide)
      (by show (-80 : Int) < R.hi; omega) (by decide) (by show (-80 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end ProofH

end HThrHead

section ProNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`thr_prologue_seg` off the transfer sites** (`prologue_seg_ofNNA`), `Z`
at the prologue's states (`hz`, `ProW`). -/
theorem thr_prologue_segNN (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".0_entry"))
    (ho : SO.le nb.o (oFr 80) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (80 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 80 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 80 σ.regs }).regs →
          σ'.slot = stSlots (-(80 : Int64).toInt) σ'.regs thrPs (frSlot σ) → nb.J σ' c)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8
      (HThrTail.pfx0 ++ ".stack_grow") thrPs J) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend hello_thrPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge hz

end ProNN

namespace Child

/-- The stub's block lengths, the `len` of its nodes' `NodeZ`. -/
def cLen : CN → Nat
  | .cb => (cb pfxM).length | .ch => chB.length

/-- The stub's blocks, the `blk` of its nodes' `NodeZA`. -/
def cBlk : CN → List Directive
  | .cb => cb pfxM | .ch => chB

theorem cLen_eq (i : CN) : cLen i = (cBlk i).length := by cases i <;> rfl

section SegH

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`seg_thrWorker` inside `NNZH`**: the original's hypotheses with
`wc_worker` inside `NNZH` (`hwk`), and `Z` at the prologue's states (`hz`),
the head's `.0_entry` block's (`hZE`) and the tail's nodes' (`hZT`). -/
theorem seg_thrWorkerH {Q : Frag isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 c1 c3 : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v → (v.setWidth 64).toNat ≤ (sp0 - (80 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p c0 c1)
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -144 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29 ra : BitVec 64,
        SegTC (NNZH exe endPc Z) p lbl ms
          (At exe endPc R' F' ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
            fun σ c => wcJE c1 w x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩)
          (fun s c => ∃ x, At exe endPc R' F' (Wake.WkTailW.E c3 x29 ra tp x) s c))
    (hK : ms.K = some Scc.Sem.A64.abi) {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hSx : StOk ms F exe endPc (tp + 24#64) 1#64)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8
      (HThrTail.pfx0 ++ ".stack_grow") thrPs (thrJE c0 w tp sp0))
    (hZE : NodeZA Z exe endPc R F (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ c0 w tp sp0)
      (fun _ c => c = c1) .e) HThrHead.thE)
    (hZT : ∀ i, NodeZA Z exe endPc R F (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (HThrTail.blkN i)) :
    SegTC (NNZH exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 w tp sp0⟩) Q := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTC.seq (SegTC.toH (thr_prologue_segNN hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := HThrHead.tN HThrTail.pfx0 lab (thrJ c0 w tp sp0) (fun _ c => c = c1) .e)
    rfl (by simp only [HThrHead.tN]; decide) (fun σ c hJ => ?_) hz)) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.2.2.2.2.1
    refine ⟨h1, h2, h3, fun v hv => ⟨?_, fun σ' hreg hsl => ?_⟩⟩
    · rw [hJ.2.2.2.2.2.2.2.2]; exact h4 v hv
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, htp, hsp⟩ := hJ
    simp only [HThrHead.tN, thrJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine SegTC.seq (HThrHead.seg_thrHeadH (N := fun _ : Unit => HThrTail.N HThrTail.pfx0 lab c3 tp .sp0)
    (E := (nofun : Empty → ND)) hF hR hal hlo hhi (fun σ c hJ => ⟨c1, hJ.1 ▸ hsplit, rfl⟩) (thECode hp hend)
    (Ne := fun g : BitVec 64 × BitVec 64 => ⟨lab "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c1 w g.1 g.2 tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩)
    (Ex := fun g y => Wake.WkTailW.E c3 g.1 g.2 tp y)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g => hwk R' F' hR' hal' hlo' hhi' hF' hFF g.1 g.2)
    (fun _ => rfl) ?_ ?_ hZE) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h0, h1, h2, h3, h4, h5, htp, hsp⟩, hc, rfl⟩
    refine ⟨(_, _), rfl, ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩ <;>
      simp only [enter, HThrHead.thE_run] <;> assumption
  · rintro ⟨x29', ra'⟩ ⟨⟩ σC c σx c' σR ⟨σ0, c0', -, -, rfl⟩ ⟨⟨-, -, -, -, -, -, -, -, h30, -⟩, -⟩
      ⟨hc', -, -, htp'⟩ hreg - -
    refine .inl ⟨(), ?_, by simp only [HThrTail.N, Wake.WkTailW.E]; decide, hc', ?_⟩
    · show (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") = Int64.ofBitVec ra'
      have h30' : ra' = _ := h30.symm
      rw [h30']
      simp only [enter, HThrHead.thE_run]
      rw [hsp0 hp, Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'
  · exact (SegTC.toH (HThrTail.seg_thrTailNN hF hR hal (Int.le_trans hlo (by decide)) hhi hK hSx hret3
      (thrCode hp hend) hZT)).mono_pre fun s c h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim

/-- **`seg_childStub` inside `NNZH`**: the stub's two blocks off the
transfer sites (`seg_ndNNA`, `Z` at their states: `hZc`), then the worker thread
inside `NNZH` (`hthr`). -/
theorem seg_childStubH {Q : Frag isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    (hthr : SegTC (NNZH exe endPc Z) p lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE cW w tp sp0⟩) Q)
    (hZc : ∀ i, NodeZA Z exe endPc R F (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i)) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label cW w tp sp0))
      Q := by
  have hin := hello_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  let nT : ND := ⟨lab "scc_rt_thr_worker", ⟨0, []⟩, thrJE cW w tp sp0⟩
  refine SegTC.seq (Q := At exe endPc R F nT) ?_ hthr
  refine SegTC.toH ((fn_segTS (N := cN pfxM lab cW w tp sp0) (E := fun _ : Unit => nT) (fun i => ?_)
    CN.cb).mono_post fun _ _ ⟨_, h⟩ => h)
  cases i
  case cb =>
    refine seg_ndNNA (by simp [cb]) cb_ok (by simp [cb, Wake.Child.cbzD, notNop]) hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]; rfl))
      (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZc .cb)
    obtain ⟨rfl, h0, h9, h10, h11, h12, h13, h14, htp, hsp⟩ := hJ
    rw [cN, childN, cb_run, cbT_run]
    refine .inl ⟨CN.ch, ?_, rfl, ⟨_, rfl, rfl, h9, h10, h11, h12, h13, h14, htp, hsp⟩⟩
    simp only [cN, rl, Reg64s.getRegOrZr] at h0 ⊢
    simp [h0, Reg64s.getRegOrZr, Reg64s.getXReg]
    all_goals rfl
  case ch =>
    refine seg_ndNNA (by simp [chB]) chB_ok (by simp [chB, notNop]) hF hR hal hlo hhi
      (code_of hp hend hch (ofNat4_zero _)) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZc .ch)
    obtain ⟨x0, rfl, -, h9, h10, h11, h12, h13, h14, htp, hsp⟩ := hJ
    rw [cN, chB_run]
    refine .inr ⟨(), rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all

end SegH

end Child

end Spike.Lib.A64.Flow.Worker.Hello

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorkerH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorkerH

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStubH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStubH
