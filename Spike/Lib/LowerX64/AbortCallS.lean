/-
**A function's overflow abort at depth, held back at depth 0** (x86-64,
H7a calls): `hab_of` (`Spike/Lib/LowerX64/AbortCall.lean`) for a callee's
`.ovf` block reached at frames `fs`, after the lag of the body's segment
(`bodyWS0_lag`, `Spike/Lib/LowerX64/BodyWS1.lean`): the abort is
discharged after the lag (`LagS p (· = cS)` of the abort label at `fs`).

The block and the abort path run at the callee's real pair `(c, fs)` (the
source not advanced: `seg_localWS_lag`, `Spike/Lib/X64AbortWS.lean`), inside
`SFactsS` at `(c, fs)`: the block's states from `blkW_postO` at the controls
without their environments (`cfacts_noEnv`), the control placed in the
frame's cells from the abort's source (`placed_of_abSrc`, the block writing
no cell, `lb_take_slot`); the abort path's from `stubW_sfacts`; both lifted
to the frames by `SFactsS.ofSFactsAt` (the pair `Good1` by `good1_run`, the
suspended frames placed in the frame condition, `hFP`, their environments
small, `hes`). The held-back pair `(cS, [])` is inside `SFactsS` at the
block's entry (`blkW_postO` at `cS`, `SFactsS.ofSFacts0`).

- `stub_sys_noK`: the stub's `write` call is not moved from outside (its pc
  in `okPc`, `abortPhOk`).
- `hab_ofS`: the held-back abort label at `fs` as a segment at depth inside
  `SFactsS … Dt`.
-/
import Spike.Lib.LowerX64.AbortCall
import Spike.Lib.LowerX64.BodyWS1
import Spike.Lib.LowerX64.NodeTp
import Spike.Lib.X64AbortWS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (blockAtB)
open Scc.Sem (Marks Range)
open Spike.Lib.X64Consumer (CFacts SFacts Own Lbl blkPh blkPh_sound noRet_false placed_of_abSrc cfacts_noEnv
  abortOk_of_ne)
open Spike.Lib.X64ConsumerS (SFactsS FramesPlaced)
open Spike.Lib.X64.Rt (InstOk blkW_postO stackOff_callee)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.StubW (abortPhOk phOne stubW_sfacts)
open Spike.Lib.AbortSrc (ovfReady_of_abSrc envSmall_of_abSrc)

section Abort

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The stub's `write` call is not moved from outside**: its pc is in
`okPc` (`abortPhOk`), off every outside move (`InstOk.off`). -/
theorem stub_sys_noK {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hphs : abortPhOk okPc ph lab = true) {R : Region} {F : MachineData → Prop} {c0 : Ctl} :
    ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys) s c →
      ∀ s', ¬ K s s' := by
  have hlab := hI.labOk
  subst hlab
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, o5, -⟩ := hphs
  intro s c hAt
  obtain ⟨-, -, -, hpc, -⟩ := hAt
  have he34 : (_root_.Executable.labels exe).label Abort.overflow.entry + Int64.ofNat 34 =
      (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .sys).pc := rfl
  rw [← he34] at hpc
  exact (hI.off s (by unfold Scc.Sem.X64.pcOf; rw [hpc]; exact o5)).2

/-- **A function's overflow abort label at frames `fs`, held back at
`(cS, [])`, is a segment at depth inside `SFactsS … Dt`** (to any `Q`):
`hab_of`'s premises with the memory side at `fs` (`hms`, `hK`), the held-back
control's facts (`hC0`), an `Accepted1` program (`hp`) with `(cS, [])` and the
function's ghost `(c0, fs)` `Good1` (`hg0`, `hg`), the suspended frames placed
at every memory of the frame condition (`hFP`) with small environments
(`hes`). -/
theorem hab_ofS {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {p : Prog} {c0 cS : Ctl}
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {Dt : State → Prop} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isa} {fs : List TermRun.Frame} {cl ctr : Nat}
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) → blockAtB cells (ovfL fr) 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (ovfL fr) + Int64.ofNat 0) 0 Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hsysIn : blockAtB cells Abort.overflow.entry 34 [(op64 .syscall, 2)] = true)
    (hphs : abortPhOk okPc ph lab = true)
    (hC0 : CFacts Λ lbl cS)
    (himm : Λ.imms = i)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.X64.pcOf s = (lab Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.overflow.exit → (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.lo ≤ -24 → 16 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (Abort.N lab Abort.overflow c .sys) s c' → Dt s)
    (hp : Scc.Lower.Accepted1 p = true) (hg0 : Good1 p (cS, [])) (hg : Good1 p (c0, fs))
    {R : Region} {F : MachineData → Prop}
    (hFP : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hlo : R.lo ≤ -(fr.size : Int) - 40) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64} {Q : FragS isa} :
    SegWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s c fs Dt) K p lbl ms
      (LagS p (· = cS)
        ((At exe endPc R F (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0)).at fs)) Q := by
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegWS.empty ?_
    rintro s c _ ⟨-, -, c', fs', ⟨⟨-, -, -, -, σ, -, -, ⟨⟨senv, hAb, -, hTc⟩, -⟩, -⟩, -⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := ovfReady_of_abSrc hAb
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  have h8 := frame_mod8 hf
  have hs8 : (oB fr).sp % 8 = 0 := by simp only [oB]; omega
  have hcode := ovfCode_codeAt hI.lays hI.endOk hblk
  rw [ovfBlk_eq_lb] at hblk
  let J := (abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0).J
  -- the block's pcs off the abort sites
  have hoff : ∀ k < Abort.Local.lb.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = (_root_.Executable.labels exe).label (ovfL fr) + Int64.ofNat (cellOff Abort.Local.lb k) →
      ∀ k' a, μ.abortAt k' = some a → Scc.Sem.X64.pcOf s ≠ a := by
    have hph' := hphA
    rw [← hI.labOk] at hph'
    have hs := blkPh_sound (μ := μ) (endPc := endPc) (K := K)
      (n := ⟨(_root_.Executable.labels exe).label (ovfL fr) + Int64.ofNat 0, oB fr, J⟩) hI.same hI.off
      (Abort.Local.lb_ok (oB fr) hs8) hph'
      (fun _ _ _ k hk hr => (noRet_false lb_noRet k hk hr).elim) (fun _ _ _ => rfl)
    intro k hk s hs' hn hpc
    exact (hs.1 k hk s hs' hn (by rw [hpc, Spike.Lib.X64.Flow.ofNat_zero'])).1.noAbort
  -- the block at the callee's controls, inside `SFactsS` at `fs`
  have hW : BlkW (fun s c => SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s c fs Dt) K exe endPc R F
      (Abort.Local.LN (_root_.Executable.labels exe).label (oB fr) ((_root_.Executable.labels exe).label (ovfL fr))
        J false) Abort.Local.lb := by
    have h0 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F)
      (n := Spike.Lib.X64.StubW.ND.noEnv ⟨(_root_.Executable.labels exe).label (ovfL fr), oB fr, J⟩)
      hI hblk (by rw [hI.labOk, Spike.Lib.X64.Flow.ofNat_zero']; rfl) (Abort.Local.lb_ok (oB fr) hs8) hR
      (by simp only [oB]; omega) (by simp only [oB]; omega) hR8 hl hh
      (fun σ c ⟨c', hc', e⟩ => by
        subst e
        obtain ⟨⟨⟨senv, hAb, -, -⟩, -⟩, -⟩ := hc'
        exact cfacts_noEnv (ovfReady_of_abSrc hAb)) hphA
      (fun _ _ _ k hk r => (noRet_false lb_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hfit hFO
    intro s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
    obtain ⟨hw, hK'⟩ := h0 s σ (X64Consumer.noEnv c) he hn hd hpc hA hD ⟨c, hJn, rfl⟩ k hk m hA' hDF
    obtain ⟨⟨⟨senv, hAb, hi, -⟩, -⟩, hr⟩ := hJn
    refine ⟨SFactsS.ofSFactsAt ((hw.dt_mono fun _ h => h.elim).ofNoEnv (ovfReady_of_abSrc hAb) ?_
      (abortOk_of_ne (hoff k hk _ he hn rfl))) hp (good1_run hp (FrameRun.ofLocal hr fs) hg)
      (hFP _ (hF _ _ hD hDF)) hes, hK'⟩
    refine placed_of_abSrc hAb (addr := R.addr) (fun r k' hr' => ?_) (himm ▸ hi)
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr'
    have hk' : R.Off k' := ⟨h2, by omega, by omega⟩
    obtain ⟨j, hj, hjs⟩ := hA'.slot k' hk'
    show (Mem.loadInt m.dmem (R.addr k') 8).map (BitVec.ofInt 64) = some (σ.slot k')
    rw [hj, Option.map_some, hjs, Abort.Local.lb_take_slot _ _ _ _ hk]
  -- the held-back pair at the block's entry, inside `SFactsS` at `(cS, [])`
  have hWl : ∀ s c', At exe endPc R F (Abort.Local.LN (_root_.Executable.labels exe).label (oB fr)
      ((_root_.Executable.labels exe).label (ovfL fr)) J false) s c' →
      FrameRun p (cS, []) (c', fs) → SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s cS [] Dt := by
    intro s c' hAt _
    have h1 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F) (own := own)
      (n := ⟨(_root_.Executable.labels exe).label (ovfL fr), oB fr, fun σ c => c = cS ∧ ∃ c1, J σ c1⟩)
      hI hblk (by rw [hI.labOk, Spike.Lib.X64.Flow.ofNat_zero']) (Abort.Local.lb_ok (oB fr) hs8) hR
      (by simp only [oB]; omega) (by simp only [oB]; omega) hR8 hl hh (by rintro σ c ⟨rfl, -⟩; exact hC0) hphA
      (fun _ _ _ k hk r => (noRet_false lb_noRet k hk r).elim) (fun _ _ _ => rfl) hsub hfit hFO
    obtain ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ := hAt
    obtain ⟨hw, -⟩ := (BlkW.nodeW h1 (by decide)) s cS ⟨he, hn, hd, hpc, σ, hA, hD, rfl, c', hJ⟩
    exact SFactsS.ofSFacts0 (hw.dt_mono fun _ h => h.elim) hp hg0
  refine Abort.Local.seg_localWS_lag (o := oB fr) (pcA := (_root_.Executable.labels exe).label (ovfL fr)) (J := J)
    hF hR (by simp only [oB]; omega) (by simp only [oB]; omega) hs8 hK hcode hW ?_ hWl
  intro R' F' hR' hlo' hhi' hF' hFF' hR'e c hJc hmem
  subst hR'e
  obtain ⟨σ0, ⟨⟨senv, hAb, -, -⟩, -⟩, hr⟩ := hJc
  have hkc8 : ((oB fr).sp - 8 - 8) % 8 = 0 := by omega
  have hb8' : (R.callee ((oB fr).sp - 8 - 8) (-24) 16).base.toNat % 8 = 0 := addr_toNat_mod8 R hR8 hkc8
  have hS := stubW_sfacts (Dt := Dt) (rS := rS) (Λ := Λ) (lbl := lbl) (p := p) (al := lbl) hI hprog hsysIn hphs hR'
    hb8' hlo' hhi' (by show (-24 : Int) % 8 = 0; decide) (by show (16 : Int) % 8 = 0; decide) hF' hsub hfit ?_
    (ovfReady_of_abSrc hAb) (envSmall_of_abSrc hAb) ?_ hrel htk hk hKex hms hK (hwr _ _ hlo' hhi' _)
  · exact hS.mapF hK hF' (fun s hs hFs => SFactsS.ofSFactsAt hs hp (good1_run hp (FrameRun.ofLocal hr fs) hg)
      (hFP s (hFF' _ hFs)) hes) (stub_sys_noK hI hphs)
  · intro m h
    refine stackOff_callee hR hR8 hl hh (by simp only [oB]; omega) (by decide) (by simp only [oB]; omega) hkc8
      (hFO m (hFF' m h)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m h
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s h
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 h
    obtain ⟨senv1, hAb1, hi1, -⟩ := hJ1.1.1
    refine placed_of_abSrc hAb1 (addr := R.addr) (fun r k hr => ?_) (himm ▸ hi1)
    obtain ⟨h1, h2, h3⟩ := rsOf_bounds hf hr
    have hk : R.Off k := ⟨h2, by omega, by omega⟩
    have hn : ¬ (R.callee ((oB fr).sp - 8 - 8) (-24) 16).Off (k - ((oB fr).sp - 8 - 8)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee, oB] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Mem.loadInt s.st.1.dmem (R.addr k) 8).map (BitVec.ofInt 64) = some (σ1.slot k)
    rw [he k hk hn, hj, Option.map_some, hjs, hsl k (by simp only [oB]; omega)]

end Abort

end Spike.Lib.LowerX64
