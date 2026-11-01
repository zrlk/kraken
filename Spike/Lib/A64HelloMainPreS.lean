/-
**`hello.w`'s `scc_rt_main` up to `wc_rodata`'s allocator's return at depth** (AArch64,
Option A): `HelloM.hello_main_pre_segW` over segments with frames (`SegWS`, `Spike/Lib/SegS.lean`),
the source's call of `rodata` taken at `wc_rodata`'s entry.

At the real run the source is at the setup block's start (`HelloRdCf.start_ctl`, `⟨setupTerm, env, none⟩`)
up to `bl wc_rodata`, and `rodata`'s call is a frame step (`FrameStep.call`, `HelloRdCf.setup_call_run`): it
pushes the setup frame `frH env`. So `scc_rt_main`'s prologue and call block are a frameless segment (at `[]`,
`SegWS.liftS []`), and at `wc_rodata`'s entry the source takes the call and `rodata`'s first local steps as a
pending frame run (`SegWS.pre_run`, `hrun`), so `wc_rodata`'s segment up to its allocator's return
(`HelloRd.hello_rodata_pre_runW`) holds at the pushed frames `fs1` (`SegWS.liftS fs1`), under `ms fs1`. Unlike
`Hello1.hello1_main_pre_segWS` (the run at `scc_rt_main`'s entry), `scc_rt_main`'s own states stay at `[]`
with the start's control, as `MainWf.mainPreWH_W0SH` proves them.

- `blkW_at0`: a block's states inside `W` include its entry's (`k = 0`).
- `main_call_segW`: `scc_rt_main`'s prologue and call block, from its entry to `wc_rodata`'s entry (`mNC`).
- `hello_main_pre_segWS`: from `scc_rt_main`'s entry at `[]` to `wc_rodata`'s exits at `fs1`.
-/
import Spike.Lib.A64HelloMain
import Spike.Lib.SegS

namespace Spike.Lib.A64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk seg_oneW)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Flow.Hello1 (mB0 mB0_ok mB0_run mainIn mN0 mNC mR mF mRdJ0 mR_ok AG aR)
open Spike.Lib.A64.Flow.HelloRd (rN rX RdPreW hello_rodata_pre_runW)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)

set_option linter.unusedSimpArgs false

/-- **A block's entry state is among its states**: `BlkW` at `k = 0` (no instruction run, the frame
unchanged). -/
theorem blkW_at0 {W : Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} (hne : blk ≠ [])
    (h : BlkW W K exe endPc R F n blk) {s : State} {c : Ctl} (hA : At exe endPc R F n s c) : W s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hAb, hF, hJ⟩ := hA
  have hl : 0 < blk.length := List.length_pos_iff.mpr hne
  have := (h s σ c he hn hdc hpc hAb hF hJ 0 hl s.st.1 hAb (DFrame.refl R _)).1
  rw [ofNat4_zero, ← hpc] at this
  exact this

section MainPreS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main`'s prologue and call block are one segment inside `W`** in any valid layout of `helloProg`:
from its entry (invariant `J`) to `wc_rodata`'s entry at the call (`mNC`), the limit word's facts for the
frame (`hlimM`), its states inside `W` (`hpro`, `hcall`), as in `hello_main_pre_segW`. -/
theorem main_call_segW {W : Frag isaLSE2} {K : State → State → Prop} {ms : MemSide isaLSE2}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop}
    (hpro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 80 8
      ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hcall : BlkW W K exe endPc R F (mN0 (_root_.Executable.labels exe).label J) mB0)
    (hlimM : ∀ σ c, J σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec)) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F (mNC (_root_.Executable.labels exe).label J)) := by
  have hin := hello_mainIn
  simp only [mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨h0, -⟩, hg1⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have e1 : (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0" =
      (_root_.Executable.labels exe).label ".L1_scc_rt_main.0_entry" + Int64.ofNat (4 * 1) :=
    label_labelGap hp hg1
  refine SegW.seq (prologue_seg_ofW hp hend hello_mainPro (nb := mN0 lab J) (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -80; omega) hhi (by simp [Spike.Lib.offOk]) rfl
    (by show SO.le ⟨-80, []⟩ (oFr 80) = true; decide) hpro ?_)
    (seg_oneW (seg_ndW (by simp [mB0]) mB0_ok hF hR hal (by omega) hhi
      (code_of hp hend h0 (ofNat4_zero _)) hcall fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
  · intro σ c hJ
    have hl := hlimM σ c hJ
    refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ⟨σ, hJ, ?_⟩⟩⟩
    rw [hs, hr]
    simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Ret0.setXReg_TPIDR]
  · simp only [mN0, mNC]; rw [mB0_run]
  · simp only [mN0, mNC]; rw [mB0_run]; rfl
  · simp only [mN0, mNC] at hJ ⊢
    rw [mB0_run]
    obtain ⟨σe, hJe, h16, h8, h80, hsp, htp⟩ := hJ
    refine ⟨⟨σe, hJe, h16, h8, h80, hsp, htp⟩, ?_⟩
    rw [e1]
    show BitVec.ofInt 64 _ = _
    rw [Ret0.ofInt_bmod]
    simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
    rfl

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return at depth**: from its entry with no frame
(invariant `J`) to `wc_rodata`'s exits at the frames `fs1`, in its region at the call. `scc_rt_main`'s
prologue and call block at `[]` (`main_call_segW`: `hpro`, `hcall`, `hlimM` under `ms []`); at `wc_rodata`'s
entry, the call's pair inside `W` at `[]` (`hWe`, e.g. by `blkW_at0` of `wc_rodata`'s first block at the
start's control) and a frame run from every call control to one of `J'` at `fs1` (`hrun`: the source's call
of `rodata`), its controls among the call's (`hJ'`); then `wc_rodata` at `fs1` under `ms fs1`
(`hello_rodata_pre_runW` at the entry invariant `mRdJ0 J' σC`: `hrd`, `hlimR`, `hloc`, `hq`, `hmem`, `hxa`). -/
theorem hello_main_pre_segWS {W : FragS isaLSE2} {K : State → State → Prop}
    {ms : List TermRun.Frame → MemSide isaLSE2} {fs1 : List TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J J' : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop}
    (hpro : ProW (fun s c => W s c []) K exe endPc R F (ms []) ((_root_.Executable.labels exe).label "scc_rt_main")
      80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hcall : BlkW (fun s c => W s c []) K exe endPc R F (mN0 (_root_.Executable.labels exe).label J) mB0)
    (hWe : ∀ s c, At exe endPc R F (mNC (_root_.Executable.labels exe).label J) s c → W s c [])
    (hrun : ∀ σ c, (mNC (_root_.Executable.labels exe).label J).J σ c → ∃ c', FrameRun p (c, []) (c', fs1) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC (_root_.Executable.labels exe).label J).J σ c)
    (hrd : ∀ m0 σC, RdPreW (fun s c => W s c fs1) K exe endPc (mR R) (mF R F m0 σC) (ms fs1) (mRdJ0 J' σC) (J1 σC))
    (hlimM : ∀ σ c, J σ c →
      LimOk (ms []) F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk (ms fs1) F exe endPc (tcbA σ.regs 8)
      (σ.regs.SP.toBitVec - (80 : Int64).toBitVec - (48 : Int64).toBitVec))
    (hloc : ∀ σC σ c, mRdJ0 J' σC σ c → ∃ c', LocalRun p c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms fs1) = 3#64)
    (hmem : ∀ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms fs1).ctr ∨
        ∃ o, o + (ms fs1).units q.n q.τ ≤ (ms fs1).cells ∧ a.toNat = q.hdrAt (ms fs1) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG (ms fs1) (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label (ms fs1) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c →
        (ms fs1).xa l b w s c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩).at [])
      (Frag.at (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX (ms fs1) (_root_.Executable.labels exe).label lbl (J1 σC) y) s c) fs1) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegWS.seq (Q := (At exe endPc R F (mNC lab J)).at [])
    (SegWS.liftS [] (main_call_segW hp hend hF hR hal hlo hhi hpro hcall hlimM) fun _ _ h => h) ?_
  refine SegWS.pre_run (SegWS.liftS fs1 (P₀ := fun s c => ∃ G : MachineData × AS,
      At exe endPc (mR R) (mF R F G.1 G.2) ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 J' G.2⟩ s c)
    (SegW.exists_pre fun G => ?_) fun _ _ h => h) ?_
  · obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi G.1 G.2
    refine (hello_rodata_pre_runW hp hend hF' hR' hal' (by show (-208 : Int) ≤ -208; decide)
      (by show (0 : Int) ≤ 0; decide) (hrd G.1 G.2) ?_ (hloc G.2) (hq G.2) ?_ (hxa G.1 G.2)).mono_post
      fun s c ⟨y, h⟩ => ⟨G.1, G.2, y, h⟩
    · rintro σ c ⟨rfl, hJc⟩
      obtain ⟨cS, ⟨σe, hJe, -, -, -, hsp, htp⟩, -⟩ := hJ' G.2 c hJc
      have h := (hlimR σe cS hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
      have ht : tcbA (enter (-80) G.2).regs 8 = tcbA σe.regs 8 := by
        simp only [tcbA, enter, htp]
      rw [ht]
      show LimOk (ms fs1) _ exe endPc _ (G.2.regs.SP.toBitVec - _)
      rw [hsp]; exact h
    · intro q hq' a ha
      exact fun m hm => hmem q hq' a ha m hm.1
  · rintro s c fs ⟨h, rfl⟩
    refine ⟨hWe s c h, ?_⟩
    obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (lo' := -208) (hi' := 0)
      (by show R.lo ≤ -80 + -208; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 8 = 0; decide) h
    obtain ⟨c', hr, hJc⟩ := hrun σC c hJ
    exact ⟨c', fs1, hr, ⟨(m0, σC), he, hn, hdc, hpc, σ, hA, hD, hσ, hJc⟩, rfl⟩

end MainPreS

end Spike.Lib.A64.Flow.HelloM

/-- info: 'Spike.Lib.A64.Flow.HelloM.blkW_at0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.blkW_at0

/-- info: 'Spike.Lib.A64.Flow.HelloM.main_call_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.main_call_segW

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWS' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWS
