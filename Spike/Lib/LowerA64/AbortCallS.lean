/-
**A function's overflow abort at depth, held back at depth 0** (AArch64,
H7a calls): `hab_of` (`Spike/Lib/LowerA64/AbortCall.lean`) for a callee's
`.abort_overflow` block reached at frames `fs`, after the lag of the body's
segment (`bodyWS0_lag`, `Spike/Lib/LowerA64/BodyWS1.lean`): the abort is
discharged after the lag (`LagS p (· = cS)` of the abort label at `fs`).

The block and the abort path run at the callee's real pair `(c, fs)` (the
source not advanced: `seg_localWS_lag`, `Spike/Lib/A64AbortWS.lean`), inside
`SFactsS` at `(c, fs)`: the block's states from `blkW_postO` at the controls
without their environments (`cfacts_noEnv`), the control placed in the
frame's cells from the abort's source (`placed_of_abSrc`, the block writing
no cell, `lb_take_slot`); the abort path's from `stubW_sfacts`; both lifted
to the frames by `SFactsS.ofSFactsAt` (the pair `Good1` by `good1_run`, the
suspended frames placed in the frame condition, `hFP`, their environments
small, `hes`). The held-back pair `(cS, [])` is inside `SFactsS` at the
block's entry (`blkW_postO` at `cS`, `SFactsS.ofSFacts0`).

- `stub_svc_noK`: the stub's `write` call is not moved from outside (its pc
  in `okPc`, `abortPhOk`).
- `hab_ofS`: the held-back abort label at `fs` as a segment at depth inside
  `SFactsS … Dt`.
-/
import Spike.Lib.LowerA64.AbortCall
import Spike.Lib.LowerA64.BodyWS1
import Spike.Lib.LowerA64.NodeTp
import Spike.Lib.A64AbortWS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts SFacts Own Lbl blkPh blkPh_sound noRet_false placed_of_abSrc cfacts_noEnv
  abortOk_of_ne)
open Spike.Lib.A64ConsumerS (SFactsS FramesPlaced)
open Spike.Lib.A64.Rt (InstOk blkW_postO)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.A64.StubW (abortPhOk phOne stubW_sfacts)
open Spike.Lib.AbortSrc (ovfReady_of_abSrc envSmall_of_abSrc)

section Abort

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The stub's `write` call is not moved from outside**: its pc is in
`okPc` (`abortPhOk`), off every outside move (`InstOk.off`). -/
theorem stub_svc_noK {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hphs : abortPhOk okPc ph lab = true) {R : Region} {F : MachineData → Prop} {c0 : Ctl} :
    ∀ s c, At exe endPc R F (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .svc) s c →
      ∀ s', ¬ K s s' := by
  have hlab := hI.labOk
  subst hlab
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨-, -, -, -, -, -, -, -, -, o7, -⟩ := hphs
  intro s c hAt
  obtain ⟨-, -, -, hpc, -⟩ := hAt
  have he7 : (_root_.Executable.labels exe).label A64.Abort.overflow.entry + Int64.ofNat (4 * 7) =
      (A64.Abort.N (_root_.Executable.labels exe).label A64.Abort.overflow c0 .svc).pc := by
    simp only [A64.Abort.N, A64.Abort.pcSvc, add4, add0]
  rw [← he7] at hpc
  exact (hI.off s (by unfold Scc.Sem.A64.pcOf; rw [hpc]; exact o7)).2

/-- **A function's overflow abort label at frames `fs`, held back at
`(cS, [])`, is a segment at depth inside `SFactsS … Dt`** (to any `Q`):
`hab_of`'s premises with the memory side at `fs` (`hms`, `hK`), the held-back
control's facts (`hC0`), an `Accepted1` program (`hp`) with `(cS, [])` and the
function's ghost `(c0, fs)` `Good1` (`hg0`, `hg`), the suspended frames placed
at every memory of the frame condition (`hFP`) with small environments
(`hes`). -/
theorem hab_ofS {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {p : Prog} {c0 cS : Ctl} {cx : FnCtx}
    (hf : FrameOk cx) (h16 : cx.frame % 16 = 0)
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {Dt : State → Prop} {lbl : Lbl}
    {ms : List TermRun.Frame → MemSide isaLSE2} {fs : List TermRun.Frame} {cl ctr : Nat}
    (hab : (∃ x a b e, T (.let_ x (.add a b) e)) →
      blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true ∧
      blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow") + Int64.ofNat (4 * 0)) 0
        A64.Abort.Local.lb = true)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hphs : abortPhOk okPc ph lab = true)
    (hC0 : CFacts Λ lbl cS)
    (himm : Λ.imms = i)
    (hrel : ∀ a, μ.site .release = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat = a → k = .overflow)
    (hKex : ∀ s s', Scc.Sem.A64.pcOf s = (lab A64.Abort.overflow.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab A64.Abort.overflow.exit → (ms fs).abortAt s)
    (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hwr : ∀ (R' : Region) (F' : MachineData → Prop), R'.base.toNat % 16 = 0 → R'.lo ≤ -48 → 0 ≤ R'.hi →
      ∀ c s c', At exe endPc R' F' (A64.Abort.N lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hp : Scc.Lower.Accepted1 p = true) (hg0 : Good1 p (cS, [])) (hg : Good1 p (c0, fs))
    {R : Region} {F : MachineData → Prop}
    (hFP : ∀ s : State, F s.st.1 → FramesPlaced Λ lbl s fs) (hes : ∀ f ∈ fs, EnvSmall f.env)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {fp ra : BitVec 64} {Q : FragS isaLSE2} :
    SegWS (fun s c fs => SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s c fs Dt) K p lbl ms
      (LagS p (· = cS)
        ((At exe endPc R F (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0)).at fs)) Q := by
  by_cases hT : ∃ x a b e, T (.let_ x (.add a b) e)
  case neg =>
    refine SegWS.empty ?_
    rintro s c _ ⟨-, -, c', fs', ⟨⟨-, -, -, -, σ, -, -, ⟨⟨senv, hAb, -, hTc⟩, -⟩, -⟩, -⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := ovfReady_of_abSrc hAb
    exact hT ⟨x, a, b, e, he ▸ hTc⟩
  obtain ⟨hblk, hphA⟩ := hab hT
  have hge := frame_ge16 hf
  have hR8 : R.base.toNat % 8 = 0 := by omega
  rw [ovfBlk_eq_lb] at hblk
  have hcode := code_of hI.lays hI.endOk hblk (q := (_root_.Executable.labels exe).label (cx.local "abort_overflow"))
    (ofNat4_zero _)
  let J := (abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J
  -- the block's pcs off the abort sites
  have hoff : ∀ k < A64.Abort.Local.lb.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = (_root_.Executable.labels exe).label (cx.local "abort_overflow") + Int64.ofNat (4 * k) →
      ∀ k' a, μ.abortAt k' = some a → Scc.Sem.A64.pcOf s ≠ a := by
    have hph' := hphA
    rw [← hI.labOk, ofNat4_zero] at hph'
    have hs := blkPh_sound (μ := μ) (endPc := endPc) (K := K)
      (n := ⟨(_root_.Executable.labels exe).label (cx.local "abort_overflow"), oF cx, J⟩) hI.same hI.off
      (A64.Abort.Local.lb_ok R.lo R.hi cx.frame) hph'
      (fun _ _ _ k hk r hr => (noRet_false lb_noRet k hk r hr).elim) (fun _ _ _ => rfl)
    intro k hk s hs' hn hpc
    exact (hs.1 k hk s hs' hn hpc).1.noAbort
  -- the block at the callee's controls, inside `SFactsS` at `fs`
  have hW : BlkW (fun s c => SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s c fs Dt) K exe endPc R F
      (A64.Abort.Local.LN (_root_.Executable.labels exe).label (cx.frame : Int)
        ((_root_.Executable.labels exe).label (cx.local "abort_overflow")) J false) A64.Abort.Local.lb := by
    have h0 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F)
      (n := Spike.Lib.A64.StubW.ND.noEnv ⟨(_root_.Executable.labels exe).label (cx.local "abort_overflow"), oF cx, J⟩)
      hI hblk (by rw [hI.labOk, ofNat4_zero]; rfl) (A64.Abort.Local.lb_ok R.lo R.hi cx.frame) hR hal
      (Int.le_refl _) (Int.le_refl _)
      (fun σ c ⟨c', hc', e⟩ => by
        subst e
        obtain ⟨⟨⟨senv, hAb, -, -⟩, -⟩, -⟩ := hc'
        exact cfacts_noEnv (ovfReady_of_abSrc hAb)) hphA
      (fun _ _ _ k hk r hr => (noRet_false lb_noRet k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    intro s σ c he hn hd hpc hA hD hJn k hk m hA' hDF
    obtain ⟨hw, hK'⟩ := h0 s σ (A64Consumer.noEnv c) he hn hd hpc hA hD ⟨c, hJn, rfl⟩ k hk m hA' hDF
    obtain ⟨⟨⟨senv, hAb, hi, -⟩, -⟩, hr⟩ := hJn
    refine ⟨SFactsS.ofSFactsAt ((hw.dt_mono fun _ h => h.elim).ofNoEnv (ovfReady_of_abSrc hAb) ?_
      (abortOk_of_ne (hoff k hk _ he hn rfl))) hp (good1_run hp (FrameRun.ofLocal hr fs) hg)
      (hFP _ (hF _ _ hD hDF)) hes, hK'⟩
    refine placed_of_abSrc hAb (addr := R.addr) (fun r k' hr' => ?_) (himm ▸ hi)
    obtain ⟨h8, h1, h2, h3⟩ := rsOf_cell hf hr'
    have hk' : R.Off k' := ⟨h8, by omega, by omega⟩
    obtain ⟨j, hj, hjs⟩ := hA'.slot k' hk'
    show (Mem.loadInt m.dmem (R.addr k') 8).map (BitVec.ofInt 64) = some (σ.slot k')
    rw [hj, Option.map_some, hjs, A64.Abort.Local.lb_take_slot _ _ _ _ hk]
  -- the held-back pair at the block's entry, inside `SFactsS` at `(cS, [])`
  have hWl : ∀ s c', At exe endPc R F (A64.Abort.Local.LN (_root_.Executable.labels exe).label (cx.frame : Int)
      ((_root_.Executable.labels exe).label (cx.local "abort_overflow")) J false) s c' →
      FrameRun p (cS, []) (c', fs) → SFactsS Λ μ p (fun s _ => own s) rS Tk lbl cl ctr s cS [] Dt := by
    intro s c' hAt _
    have h1 := blkW_postO (rS := rS) (Λ := Λ) (lbl := lbl) (R := R) (F := F) (own := own)
      (n := ⟨(_root_.Executable.labels exe).label (cx.local "abort_overflow"), oF cx,
        fun σ c => c = cS ∧ ∃ c1, J σ c1⟩)
      hI hblk (by rw [hI.labOk, ofNat4_zero]) (A64.Abort.Local.lb_ok R.lo R.hi cx.frame) hR hal
      (Int.le_refl _) (Int.le_refl _) (by rintro σ c ⟨rfl, -⟩; exact hC0) hphA
      (fun _ _ _ k hk r hr => (noRet_false lb_noRet k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO
    obtain ⟨he, hn, hd, hpc, σ, hA, hD, hJ⟩ := hAt
    obtain ⟨hw, -⟩ := (BlkW.nodeW h1 (by simp [A64.Abort.Local.lb])) s cS
      ⟨he, hn, hd, hpc, σ, hA, hD, rfl, c', hJ⟩
    exact SFactsS.ofSFacts0 (hw.dt_mono fun _ h => h.elim) hp hg0
  refine A64.Abort.Local.seg_localWS_lag (fr := (cx.frame : Int))
    (pcA := (_root_.Executable.labels exe).label (cx.local "abort_overflow")) (J := J)
    hF hR hal hlo hhi (by omega) (by omega) hK hcode hW ?_ hWl
  intro R' F' hR' hal' hlo' hhi' hF' hFF' hR'e c hJc hmem
  subst hR'e
  obtain ⟨σ0, ⟨⟨senv, hAb, -, -⟩, -⟩, hr⟩ := hJc
  have hS := stubW_sfacts (Dt := Dt) (rS := rS) (Λ := Λ) (lbl := lbl) (p := p) (al := lbl) hI hprog hphs hR'
    hal' hlo' hhi' rfl rfl hF' hsub hfit ?_ (ovfReady_of_abSrc hAb) (envSmall_of_abSrc hAb) ?_ hrel htk hk hKex
    hms hK (hwr _ _ hal' hlo' hhi' _)
  · exact hS.mapF hK hF' (fun s hs hFs => SFactsS.ofSFactsAt hs hp (good1_run hp (FrameRun.ofLocal hr fs) hg)
      (hFP s (hFF' _ hFs)) hes) (stub_svc_noK hI hphs)
  · intro m h
    refine stackOff_callee hR hR8 hl hh (by omega) (by decide) (by omega) (by omega) (hFO m (hFF' m h)) ?_
    intro k hk hn
    obtain ⟨mC, σC, σ1, hA, -, -, he⟩ := hmem m h
    rw [he k hk hn]
    obtain ⟨j, hj, -⟩ := hA.slot k hk
    rw [hj]; rfl
  · intro s h
    obtain ⟨mC, σC, σ1, hA, hsl, hJ1, he⟩ := hmem s.st.1 h
    obtain ⟨senv1, hAb1, hi1, -⟩ := hJ1.1.1
    refine placed_of_abSrc hAb1 (addr := R.addr) (fun r k hr => ?_) (himm ▸ hi1)
    obtain ⟨h8, h1, h2, h3⟩ := rsOf_cell hf hr
    have hk : R.Off k := ⟨h8, by omega, by omega⟩
    have hn : ¬ (R.callee (-(cx.frame : Int)) (-48) 0).Off (k - -(cx.frame : Int)) := by
      rintro ⟨-, -, h4⟩
      simp only [Region.callee] at h4
      omega
    obtain ⟨j, hj, hjs⟩ := hA.slot k hk
    show (Mem.loadInt s.st.1.dmem (R.addr k) 8).map (BitVec.ofInt 64) = some (σ1.slot k)
    rw [he k hk hn, hj, Option.map_some, hjs, hsl]

end Abort

end Spike.Lib.LowerA64
