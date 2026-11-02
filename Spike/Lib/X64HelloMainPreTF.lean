/-
**`hello.w`'s `scc_rt_main` up to `wc_rodata`'s heap abort at depth, the thread pointer kept** (x86-64; twin of
`Spike/Lib/A64HelloMainPreTF.lean`): `scc_rt_main`'s prologue and call block (`main_call_segW`), then
`wc_rodata`'s segment run under `tpXa (ms fs1) t` inside `NoSetFsW` (`SegW.keepTPN'`), so the allocator's
landing is asked of `hxa` only at `%fs` base `t` (`TP t s`), the fact level 1's `hJpT` needs at the landing.
`wc_rodata`'s level obligations (`hrd`) are asked only at `%fs` base `t` too (`tpG t`), so the context at its
counter add may use `TP t`.

- `hello_main_pre_segWSTF`: from `scc_rt_main`'s entry at `[]` to `wc_rodata`'s heap abort at `fs1` (at `%fs`
  base `t`).

## Differences from the AArch64 version

- The thread pointer is `%fs`'s base, kept inside `NoSetFsW` (AArch64: `TPIDR_EL0` inside `NoMsrW`); the
  pieces are `X64HelloMainPreT`'s `rdPreW_noMsrH`, `rdPreW_tpH`, `at_rX_untp`.
- The AArch64 version inlines no dead constant; here `main_call_segW` (x86-64's `X64HelloMainPreS`) takes
  `scc_rt_main`'s five-block `XProW` prologue, `8 ≤ R.hi` and no alignment premise (AArch64: `ProW`,
  `0 ≤ R.hi`, `hal`), and the limit words are at `%fs + 8` with the frame's bounds `%rsp - 8 - 64`
  (`hlimM`) and `%rsp - 8 - 64 - 8 - 8 - 32` (`hlimR`; AArch64: `tcbA σ 8`, `SP - 80` and `SP - 80 - 48`).
- `hxa`'s kept cells are `CKept (mR R) (-48) (-160) 8` (AArch64: `0`), the regions' `hi` being x86-64's.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloMainPreT
import Spike.Lib.X64WakeTP
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.Flow.Hello1 (mB0 mN0 mNC mR mF mRdJ0 mR_ok AG aR callOK_tp callOK_untp limOk_tp)
open Spike.Lib.X64.Flow.HelloRd (rN rX RdPreW hello_rodata_pre_runWF)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)
open Scc.Cert.Rt.X64 (Lays endOf)

section MainPreTF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` up to `wc_rodata`'s heap abort at depth, level 0, the thread pointer kept**:
`main_call_segW`, then `wc_rodata`'s segment under `tpXa (ms fs1) t` inside `NoSetFsW` (`SegW.keepTPN'`, the
memory side's kernel `hK'`), from the caller's `%fs` base `t` at the call (`hJT`). The allocator's landing
(`hxa`) and `wc_rodata`'s level obligations (`hrd`, at `tpG t`) are only asked of states at `%fs` base `t`. -/
theorem hello_main_pre_segWSTF {W : FragS isa} {K : State → State → Prop}
    {ms : List TermRun.Frame → MemSide isa} {fs1 : List TermRun.Frame}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hK' : (ms fs1).K = some Scc.Sem.X64.abi)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J J' : AS → Ctl → Prop} {J1 : AS → AS → Ctl → Prop} {t : UInt64}
    (hpro : XProW (fun s c => W s c []) K exe endPc R F (ms []) ((_root_.Executable.labels exe).label "scc_rt_main")
      64 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J)
    (hcall : BlkW (fun s c => W s c []) K exe endPc R F (mN0 (_root_.Executable.labels exe).label R J) mB0)
    (hWe : ∀ s c, At exe endPc R F (mNC (_root_.Executable.labels exe).label R J) s c → W s c [])
    (hJT : ∀ σ c, (mNC (_root_.Executable.labels exe).label R J).J σ c → σ.regs.fsBase = t)
    (hrun : ∀ σ c, (mNC (_root_.Executable.labels exe).label R J).J σ c →
      ∃ c', FrameRun p (c, []) (c', fs1) ∧ J' σ c')
    (hJ' : ∀ σ c', J' σ c' → ∃ c, (mNC (_root_.Executable.labels exe).label R J).J σ c)
    (hrd : ∀ m0 σC, RdPreW (tpG t fun s c => W s c fs1) K exe endPc (mR R)
      (mF R F m0 σC) (ms fs1) (mRdJ0 J' σC) (J1 σC))
    (hlimM : ∀ σ c, J σ c → LimOk (ms []) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hlimR : ∀ σ c, J σ c → LimOk (ms fs1) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
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
        (rN (_root_.Executable.labels exe).label (mR R) (mRdJ0 J' σC) (J1 σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label (ms fs1) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c → TP t s →
        (ms fs1).xa l b w s c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩).at [])
      (Frag.at (fun s c => ∃ m0 σC, At exe endPc (mR R) (mF R F m0 σC)
        (rX (ms fs1) (_root_.Executable.labels exe).label lbl (mR R) (J1 σC) .abort) s c ∧ TP t s) fs1) := by
  let lab := (_root_.Executable.labels exe).label
  refine SegWS.seq (Q := (At exe endPc R F (mNC lab R J)).at [])
    (SegWS.liftS [] (main_call_segW hp hend hF hR hlo hhi hpro hcall hlimM) fun _ _ h => h) ?_
  refine SegWS.pre_run (SegWS.liftS fs1 (P₀ := fun s c => ∃ G : MachineData × AS,
      At exe endPc (mR R) (mF R F G.1 G.2) ⟨lab "wc_rodata", ⟨0, []⟩, mRdJ0 J' G.2⟩ s c ∧ TP t s)
    (SegW.exists_pre fun G => ?_) fun _ _ h => h) ?_
  · obtain ⟨hR', hF'⟩ := mR_ok hR hF hlo hhi G.1 G.2
    have hpre := hello_rodata_pre_runWF (ms := tpXa (ms fs1) t)
      (W := NoSetFsW (tpG t fun s c => W s c fs1) K) (p := p)
      (lbl := lbl) hp hend hF' hR' (by show (-208 : Int) ≤ -208; decide) (by show (8 : Int) ≤ 8; decide)
      (rdPreW_tpH (rdPreW_noMsrH hp hend (hrd G.1 G.2))) ?_ (hloc G.2)
      (fun σ c h => let ⟨q, hq1, hq2⟩ := hq G.2 σ c h; ⟨q, callOK_tp hq1, hq2⟩) ?_
      (fun q F' h1 h2 l b w s c hl hAt ht => hxa G.1 G.2 ⟨q.1, callOK_untp q.2⟩ F' h1 h2 l b w s c hl hAt ht)
    · exact (SegW.keepTPN' hK' hpre fun _ _ h ht => h ht).mono_post fun s c ⟨h, ht⟩ => ⟨G.1, G.2, at_rX_untp h, ht⟩
    · rintro σ c ⟨rfl, hJc⟩
      obtain ⟨cS, ⟨σe, hJe, -, -, -, hsp, hfs, -, -⟩⟩ := hJ' G.2 c hJc
      have h := (hlimR σe cS hJe).mono (F' := mF R F G.1 G.2) fun m h => h.1
      show LimOk (tpXa (ms fs1) t) _ (G.2.regs.fsBase.toBitVec + _) (G.2.regs.rsp.toBitVec - _ - _)
      rw [hfs, hsp]; exact limOk_tp h
    · intro q hq' a ha
      exact fun m hm => hmem q (callOK_untp hq') a ha m hm.1
  · rintro s c fs ⟨h, rfl⟩
    refine ⟨hWe s c h, ?_⟩
    obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, hσ, hJ⟩ := at_enter (e0 := 0) (lo' := -208) (hi' := 8)
      (by show R.lo ≤ -80 - 0 + -208; omega) (by show (-80 : Int) - 0 + 8 ≤ R.hi; omega)
      (by show ((-80 : Int) - 0) % 8 = 0; decide) h
    obtain ⟨c', hr, hJc⟩ := hrun σC c hJ
    have htp : TP t s := by
      show s.st.1.regs.fsBase = t
      rw [hA.regs, hσ]
      exact hJT σC c hJ
    exact ⟨c', fs1, hr, ⟨(m0, σC), ⟨he, hn, hdc, hpc, σ, hA, hD, hσ, hJc⟩, htp⟩, rfl⟩

end MainPreTF

end Spike.Lib.X64.Flow.HelloM

/--
info: 'Spike.Lib.X64.Flow.HelloM.hello_main_pre_segWSTF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.hello_main_pre_segWSTF
