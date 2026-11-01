/-
**`hello.w`'s `scc_rt_main` up to `wc_rodata`'s allocator's return at depth, the thread pointer kept** (AArch64; the
pre-call half of the fix of `MainGlueS.MainWcPS`'s
vacuity, `A64HelloMainPostT` the post-call half).

`HelloM.hello_main_pre_segWS` with `wc_rodata`'s segment up to its allocator's return run under `tpXa` inside
`NoMsrW` (`rdPreW_noMsrH`, `rdPreW_tpH`), so `SegW.keepTPN` carries `TP t` from `wc_rodata`'s entry (where the
caller's state at the call has thread pointer `t`, `hJT`) to its exits: at `.sp0` the allocator's return is at
thread pointer `t`, as `hello_main_post_segWST`'s `hJpT` asks of `Jp`.

- `rdPreW_noMsrH`: `HelloRd.RdPreW` inside `NoMsrW W K` in any valid layout of `helloProg`
  (`Hello1.RdPreW.noMsr`'s twin).
- `rdPreW_tpH`: `HelloRd.RdPreW` under `tpXa ms t` (`Hello1.rdPreW_tp`'s twin).
- `rX_untp`, `at_rX_untp`: `wc_rodata`'s exits under `tpXa ms t` are its exits under `ms`.
- `hello_main_pre_segWST`: `hello_main_pre_segWS` with its exits at thread pointer `t`, from `hJT` and the
  memory side's kernel (`hK'`); `hxa` only at states of thread pointer `t`.
-/
import Spike.Lib.A64HelloMainPreS
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Flow.Hello1 (mB0 mN0 mNC mR mF mRdJ0 mR_ok AG aR RX callOK_tp callOK_untp limOk_tp proW_tp
  allocW_tp)
open Spike.Lib.A64.Flow.HelloRd (rN rX RdPreW hello_rodata_pre_runW rdEIn hello_rdEIn hello_rdPro hello_alloc)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)

set_option linter.unusedSimpArgs false

section Rd

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop} {ms : MemSide isaLSE2}

/-- **`wc_rodata` up to the allocator's return is inside `NoMsrW W K`** in any valid layout of `helloProg`
(`Hello1.RdPreW.noMsr`'s twin). -/
theorem rdPreW_noMsrH [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {J0 J1 : AS → Ctl → Prop}
    (h : RdPreW W K exe endPc R F ms J0 J1) : RdPreW (NoMsrW W K) K exe endPc R F ms J0 J1 := by
  have hin := hello_rdPro
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have he := hello_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at he
  refine ⟨ProW.noMsr h.pro (code_of hp hend b0 ?_) (code_of hp hend b1 ?_) (code_of hp hend b2 ?_)
    (code_of hp hend b3 ?_) (by decide) (by decide) (by decide) (by decide),
    BlkW.noMsr h.e (code_of hp hend he.1 (ofNat4_zero _)) (by decide),
    fun q hok hq => AllocW.noMsr (h.alloc q hok hq) (alloc_code_of hp hend hello_alloc)⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]

/-- **`wc_rodata` up to the allocator's return under `tpXa ms t`** (`Hello1.rdPreW_tp`'s twin). -/
theorem rdPreW_tpH {t : UInt64} {J0 J1 : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 J1) :
    RdPreW W K exe endPc R F (tpXa ms t) J0 J1 :=
  ⟨proW_tp h.pro, h.e, fun q hok hq => allocW_tp (h.alloc q (callOK_untp hok) hq)⟩

/-- **`wc_rodata`'s exits under `tpXa ms t` are its exits under `ms`**. -/
theorem rX_untp {t : UInt64} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J1 : AS → Ctl → Prop} {y : RX} {σ : AS} {c : Ctl} (h : (rX (tpXa ms t) lab lbl J1 y).J σ c) :
    (rX ms lab lbl J1 y).J σ c := by
  cases y
  · obtain ⟨q, h1, h2⟩ := h
    exact ⟨⟨q.1, callOK_untp q.2⟩, h1, h2⟩
  · obtain ⟨h0, h30, q, hf, hJ⟩ := h
    exact ⟨h0, h30, ⟨q.1, callOK_untp q.2⟩, hf, hJ⟩

/-- **At `wc_rodata`'s exits under `tpXa ms t`** is at its exits under `ms`. -/
theorem at_rX_untp {t : UInt64} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J1 : AS → Ctl → Prop} {y : RX} {s : State} {c : Ctl} (h : At exe endPc R F (rX (tpXa ms t) lab lbl J1 y) s c) :
    At exe endPc R F (rX ms lab lbl J1 y) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  cases y <;> exact ⟨he, hn, hdc, hpc, σ, hA, hD, rX_untp hJ⟩

end Rd

section MainPreT

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return at depth, the thread pointer kept**:
`hello_main_pre_segWS` with `wc_rodata`'s segment under `tpXa (ms fs1) t` inside `NoMsrW` (`SegW.keepTPN`, the
memory side's kernel `hK'`), from the caller's thread pointer `t` at the call (`hJT`; `wc_rodata`'s entry state
is the caller's with its frame entered), so that its exits are at thread pointer `t`. The allocator's landing
(`hxa`) is only asked of states at thread pointer `t`. -/
theorem hello_main_pre_segWST {W : FragS isaLSE2} {K : State → State → Prop}
    {ms : List TermRun.Frame → MemSide isaLSE2} {fs1 : List TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
    (hK' : (ms fs1).K = some Scc.Sem.A64.abi)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hhi : 0 ≤ R.hi)
    {J J' : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop} {t : UInt64}
    (hpro : ProW (fun s c => W s c []) K exe endPc R F (ms []) ((_root_.Executable.labels exe).label "scc_rt_main")
      80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hcall : BlkW (fun s c => W s c []) K exe endPc R F (mN0 (_root_.Executable.labels exe).label J) mB0)
    (hWe : ∀ s c, At exe endPc R F (mNC (_root_.Executable.labels exe).label J) s c → W s c [])
    (hJT : ∀ σ c, (mNC (_root_.Executable.labels exe).label J).J σ c → σ.regs.TPIDR_EL0 = t)
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
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c → TP t s →
        (ms fs1).xa l b w s c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩).at [])
      (Frag.at (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX (ms fs1) (_root_.Executable.labels exe).label lbl (J1 σC) y) s c ∧ TP t s) fs1) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegWS.seq (Q := (At exe endPc R F (mNC lab J)).at [])
    (SegWS.liftS [] (main_call_segW hp hend hF hR hal hlo hhi hpro hcall hlimM) fun _ _ h => h) ?_
  refine SegWS.pre_run (SegWS.liftS fs1 (P₀ := fun s c => ∃ G : MachineData × AS,
      At exe endPc (mR R) (mF R F G.1 G.2) ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 J' G.2⟩ s c ∧ TP t s)
    (SegW.exists_pre fun G => ?_) fun _ _ h => h) ?_
  · obtain ⟨hR', hal', hF'⟩ := mR_ok hR hal hF hlo hhi G.1 G.2
    have hpre := hello_rodata_pre_runW (ms := tpXa (ms fs1) t) (W := NoMsrW (fun s c => W s c fs1) K) (p := p)
      (lbl := lbl) hp hend hF' hR' hal' (by show (-208 : Int) ≤ -208; decide) (by show (0 : Int) ≤ 0; decide)
      (rdPreW_tpH (rdPreW_noMsrH hp hend (hrd G.1 G.2))) ?_ (hloc G.2)
      (fun σ c h => let ⟨q, hq1, hq2⟩ := hq G.2 σ c h; ⟨q, callOK_tp hq1, hq2⟩) ?_
      (fun q F' h1 h2 l b w s c hl hAt ht => hxa G.1 G.2 ⟨q.1, callOK_untp q.2⟩ F' h1 h2 l b w s c hl hAt ht)
    · exact (SegW.keepTPN hK' hpre).mono_post fun s c ⟨⟨y, h⟩, ht⟩ => ⟨G.1, G.2, y, at_rX_untp h, ht⟩
    · rintro σ c ⟨rfl, hJc⟩
      obtain ⟨cS, ⟨σe, hJe, -, -, -, hsp, htp⟩, -⟩ := hJ' G.2 c hJc
      have h := (hlimR σe cS hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
      have ht : tcbA (enter (-80) G.2).regs 8 = tcbA σe.regs 8 := by
        simp only [tcbA, enter, htp]
      rw [ht]
      show LimOk (tpXa (ms fs1) t) _ exe endPc _ (G.2.regs.SP.toBitVec - _)
      rw [hsp]; exact limOk_tp h
    · intro q hq' a ha
      exact fun m hm => hmem q (callOK_untp hq') a ha m hm.1
  · rintro s c fs ⟨h, rfl⟩
    refine ⟨hWe s c h, ?_⟩
    obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (lo' := -208) (hi' := 0)
      (by show R.lo ≤ -80 + -208; omega) (by show (-80 : Int) < R.hi; omega) (by decide)
      (by show (-80 : Int) % 8 = 0; decide) h
    obtain ⟨c', hr, hJc⟩ := hrun σC c hJ
    have htp : TP t s := by
      show s.st.1.regs.TPIDR_EL0 = t
      rw [hA.regs, hσ]
      exact hJT σC c hJ
    exact ⟨c', fs1, hr, ⟨(m0, σC), ⟨he, hn, hdc, hpc, σ, hA, hD, hσ, hJc⟩, htp⟩, rfl⟩

end MainPreT

end Spike.Lib.A64.Flow.HelloM

/-- info: 'Spike.Lib.A64.Flow.HelloM.rdPreW_noMsrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.rdPreW_noMsrH

/--
info: 'Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWST' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloM.hello_main_pre_segWST
