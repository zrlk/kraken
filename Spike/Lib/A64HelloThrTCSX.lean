/-
**hello.w's thread worker and child stub at depth, landing in `X`** (hello.w, row 5j-wit-W; AArch64):
`Spike/Lib/A64HelloThrTCS.lean`'s `HThrHead.seg_thrHeadS`, `Child.seg_thrWorkerS` and `Child.seg_childStubS`
over `Spike/Lib/HelloSegTCSX.lean`'s `SegTCSX` with the fragment `SH exe endPc Z`, so every landing pair of the
spawned child's segment chain is in the landing fragment `X`. `X` at the flat pieces' pairs comes from `Z`
(`hZX`); the call of `wc_worker` is `call_ndTSSX`, the worker a `SegTCSX` callee.

Release note: when the `X` chain replaces the `SegTCS` one, `seg_thrHeadS`, `seg_thrWorkerS` and
`seg_childStubS` become one-line corollaries through `SegTCSX.toS` or are deleted; the release keeps one chain.

Differences from the `SegTCS` version: generic in the landing fragment `X` with a new premise
`hZX : ∀ s c fs, Z s c fs → X s c fs`; the worker's callee (`hwk`) and the thread worker (`hthr`) are `SegTCSX`
premises; `SegTCS.seq (SegTCS.ofTC h₁ nnzS) h₂` becomes `SegTCSX.ofTC_seq h₁ nnzS hX h₂`, the thread tail is
`SegTCSX.ofTC`, and the head's call is `call_ndTSSX`.

- `HThrHead.seg_thrHeadSX`, `Child.seg_thrWorkerSX`, `Child.seg_childStubSX`.
-/
import Spike.Lib.A64HelloThrTCS
import Spike.Lib.A64HelloCallTSSX
import Spike.Lib.HelloSegTCSXC

namespace Spike.Lib.A64.Flow.Worker.Hello

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

namespace HThrHead

section ProofSX

variable {pfx : String} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {ms : List TermRun.Frame → MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {Z X : FragS isaLSE2}

/-- **`seg_thrHeadS` landing in `X`**: the block at depth `0` (`seg_ndNNA`, `X` from `Z` by `hZX`), the call
`call_ndTSSX` to a `SegTCSX` callee at `[]`, its region 192 bytes below the call's `sp`. -/
theorem seg_thrHeadSX {ι κ : Sort _} {N : ι → ND} {E : κ → ND} (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop}
    {L : Ctl → Ctl → Prop} (hL : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ L c c')
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label (pfx ++ ".0_entry")) thE)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    {γ : Type _} {κ' : Sort _} {Ne : γ → ND} {Ex : γ → κ' → ND}
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ g,
        SegTCSX (SH exe endPc Z) X p lbl ms ((At exe endPc R' F' (Ne g)).at [])
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Ex g x) s c) []))
    (hNe : ∀ g, (Ne g).o = ⟨0, []⟩)
    (hent : ∀ σC c, (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      ∃ g, (Ne g).pc = (_root_.Executable.labels exe).label "wc_worker" ∧ (Ne g).J (enter (-80) σC) c)
    (hret : ∀ g x σC c σx c' (σR : AS), (tN pfx (_root_.Executable.labels exe).label J L .call).J σC c →
      (Ne g).J (enter (-80) σC) c → (Ex g x).J σx c' →
      σR.regs = σx.regs → σR.status = σx.status →
      (∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - (-80)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(Ex g x).pc, ⟨-80 + (Ex g x).o.sp, []⟩, σR⟩ c')
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e) thE) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F (tN pfx (_root_.Executable.labels exe).label J L .e)).at [])
      ((Next exe endPc R F N E).at []) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTCSX.ofTC_seq (Q₀ := At exe endPc R F (tN pfx lab J L .call))
    ((seg_ndNNA (ms := ms []) (N := fun _ : Unit => tN pfx lab J L .call)
      (E := (nofun : Empty → ND)) (by simp [thE]) thE_ok (by simp [thE, notNop]) hF hR hal
      (Int.le_trans hlo (by decide)) hhi hcodeE (fun σ c hJ => ?_) hZE).mono_post ?_)
    (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2) ?_
  · obtain ⟨c', hr, hl⟩ := hL σ c hJ
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, σ, c, hJ, hl, rfl⟩⟩
    · simp only [tN]; rw [thE_run]
    · simp only [tN]; rw [thE_run]; rfl
  · rintro s c (⟨_, h⟩ | ⟨y, _⟩)
    · exact h
    · exact y.elim
  · exact call_ndTSSX (lo' := -192) (hi' := 0) hR hal hF (by show R.lo ≤ -80 + -192; omega) (by decide)
      (by show (-80 : Int) < R.hi; omega) (by decide) (by show (-80 : Int) % 16 = 0; decide) (by decide)
      (by decide) hwk hNe hent hret

end ProofSX

end HThrHead

namespace Child

section SegSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z X : FragS isaLSE2}

/-- **`seg_thrWorkerS` landing in `X`**: `wc_worker` a `SegTCSX` segment at `[]` (`hwk`, asked only at the
return address `.sp0`), the prologue, head and tail at depth `0` (`X` from `Z` by `hZX`). -/
theorem seg_thrWorkerSX {Q : FragS isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 c1 c3 : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -272) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      (ms []).rt (tcbA r 8).toNat ∧ (ms []).mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA r 8, 8⟩ v → (v.setWidth 64).toNat ≤ (sp0 - (80 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p c0 c1)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    (hwk : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -192 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ x29 ra : BitVec 64,
        Int64.ofBitVec ra = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") →
        SegTCSX (SH exe endPc Z) X p lbl ms
          ((At exe endPc R' F' ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
            fun σ c => wcJE c1 w x29 ra tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩).at [])
          (Frag.at (fun s c => ∃ x, At exe endPc R' F' (Wake.WkTailW.E c3 x29 ra tp x) s c) []))
    (hK : (ms []).K = some Scc.Sem.A64.abi) {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hSx : StOk (ms []) F exe endPc (tp + 24#64) 1#64)
    (hz : ProW (fun s c => Z s c []) (fun _ _ => False) exe endPc R F (ms [])
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs
      (thrJE c0 w tp sp0))
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F
      (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ c0 w tp sp0) (fun _ c => c = c1) .e)
      HThrHead.thE)
    (hZT : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i) (HThrTail.blkN i)) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE c0 w tp sp0⟩).at []) Q := by
  let lab := (_root_.Executable.labels exe).label
  refine SegTCSX.ofTC_seq (thr_prologue_segNN (ms := ms []) (Z := fun s c => Z s c []) hp hend hF hR hal
    (Int.le_trans hlo (by decide)) hhi
    (nb := HThrHead.tN HThrTail.pfx0 lab (thrJ c0 w tp sp0) (fun _ c => c = c1) .e)
    rfl (by simp only [HThrHead.tN]; decide) (fun σ c hJ => ?_) hz) (fun _ _ h => nnzS h)
    (fun _ _ h => hZX _ _ _ h.2) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hlim σ.regs hJ.2.2.2.2.2.2.2.1
    refine ⟨h1, h2, h3, fun v hv => ⟨?_, fun σ' hreg hsl => ?_⟩⟩
    · rw [hJ.2.2.2.2.2.2.2.2]; exact h4 v hv
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, htp, hsp⟩ := hJ
    simp only [HThrHead.tN, thrJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine SegTCSX.seq (HThrHead.seg_thrHeadSX (N := fun _ : Unit => HThrTail.N HThrTail.pfx0 lab c3 tp .sp0)
    (E := (nofun : Empty → ND)) hF hR hal hlo hhi (fun σ c hJ => ⟨c1, hJ.1 ▸ hsplit, rfl⟩) (thECode hp hend) hZX
    (Ne := fun g : {g : BitVec 64 × BitVec 64 // Int64.ofBitVec g.2 = lab (HThrTail.pfx0 ++ ".sp0")} =>
      ⟨lab "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c1 w g.1.1 g.1.2 tp σ c ∧ σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec⟩)
    (Ex := fun g y => Wake.WkTailW.E c3 g.1.1 g.1.2 tp y)
    (fun R' F' hR' hal' hlo' hhi' hF' hFF g => hwk R' F' hR' hal' hlo' hhi' hF' hFF g.1.1 g.1.2 g.2)
    (fun _ => rfl) ?_ ?_ hZE) ?_
  · rintro σC c ⟨σ0, c0', ⟨-, h0, h1, h2, h3, h4, h5, htp, hsp⟩, hc, rfl⟩
    refine ⟨⟨(_, _), ?_⟩, rfl, ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩, ?_⟩
    · symm
      simp only [enter, HThrHead.thE_run]
      show (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") = _
      rw [hsp0 hp, Ret0.ofInt_bmod]
      simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt]; rfl
    all_goals simp only [enter, HThrHead.thE_run] <;> assumption
  · rintro ⟨⟨x29', ra'⟩, hpin⟩ ⟨⟩ σC c σx c' σR - - ⟨hc', -, -, htp'⟩ hreg - -
    refine .inl ⟨(), ?_, by simp only [HThrTail.N, Wake.WkTailW.E]; decide, hc', ?_⟩
    · exact hpin.symm
    · show σR.regs.TPIDR_EL0.toBitVec = tp
      rw [hreg]; exact htp'
  · refine ((SegTCSX.ofTC (HThrTail.seg_thrTailNN (Q := fun _ _ => False) hF hR hal (Int.le_trans hlo (by decide))
      hhi hK hSx hret3 (thrCode hp hend) hZT) (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2)
      ?_).mono_pre ?_).mono_post ?_
    · rintro s c ⟨⟨⟩, -⟩
    · rintro s c fs ⟨h, rfl⟩
      exact ⟨h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim, rfl⟩
    · rintro s c fs ⟨⟨⟩, -⟩

/-- **`seg_childStubS` landing in `X`**: the stub's two blocks at depth `0` (`X` from `Z` by `hZX`), then the
thread worker a `SegTCSX` segment (`hthr`). -/
theorem seg_childStubSX {Q : FragS isaLSE2} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {cW : Ctl} {w : Words} {tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi)
    (hZX : ∀ s c fs, Z s c fs → X s c fs)
    (hthr : SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_thr_worker", ⟨0, []⟩,
        thrJE cW w tp sp0⟩).at []) Q)
    (hZc : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cBlk i)) :
    SegTCSX (SH exe endPc Z) X p lbl ms
      ((At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label cW w tp sp0)).at []) Q := by
  have hin := hello_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  let nT : ND := ⟨lab "scc_rt_thr_worker", ⟨0, []⟩, thrJE cW w tp sp0⟩
  refine SegTCSX.ofTC_seq (Q₀ := At exe endPc R F nT) ((fn_segTS (S := NNZ exe endPc fun s c => Z s c [])
    (ms := ms []) (N := cN pfxM lab cW w tp sp0) (E := fun _ : Unit => nT) (fun i => ?_) CN.cb).mono_post
      fun _ _ ⟨_, h⟩ => h) (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2) hthr
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

end SegSX

end Child

end Spike.Lib.A64.Flow.Worker.Hello

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHeadSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.HThrHead.seg_thrHeadSX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorkerSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_thrWorkerSX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStubSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Child.seg_childStubSX
