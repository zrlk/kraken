/-
**The start's heap abort under the take move** (AArch64): `WakePh.wc_heapAbStub`
at `PhRec.K` and the control facts at `wc_main`'s heap abort below
`scc_rt_main`'s entry at `c0W`.

- `hpathW_K`: a path obligation with no outside moves is one under `K` when
  `K` moves none of its states.
- `abort_off`, `x0W_abort`: `scc_rt_abort`'s code is off the clone and the
  take site, so `X0W` holds there.
- `wc_heapAbStubK`: `WakePh.wc_heapAbStub` under `PhRec.K` (the path is in
  `scc_rt_abort`'s code, `hpathW_hX`, off the take site).
- `hctl_c0W`: at `wX .abort` below `JS … c0W`, the control is `c0W` holding
  the counter at a crossing count (`Jfull`, one box of two units), so its
  facts and the heap abort's obligation (`HeapAbortOblA`) hold.
-/
import Spike.Lib.A64WakeHAbStub
import Spike.Lib.A64WakeMainGlue
import Spike.Lib.A64WakeC0
import Spike.Lib.A64WakeWcWf

namespace Spike.Lib.A64.WakePh.HAbStubK

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf abi textProgram)
open Spike.Lib (Arena FragS Region SegWS HeapAbortOblA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerS (PlacedSE)
open Spike.Lib.A64.Flow (ND BlkW NodeW At swR)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcHAbStub AGB wX)
open Spike.Lib.A64.Abort.Disp (HPathW)
open Spike.Lib.A64.WakeWf (DtW W0 RunWf X0W)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh.WcW (cv inCv)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

/-- **No outside moves to `K`**: a path obligation under no outside move is
one under `K` when `K` moves no state of `W`. -/
theorem hpathW_K {W : Spike.Lib.Frag isaLSE2} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : HPathW W (fun _ _ => False) exe endPc R F c0 ra) (hK : ∀ s c, W s c → ∀ s', ¬ K s s') :
    HPathW W K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List Directive}, BlkW W (fun _ _ => False) exe endPc R F n blk →
      BlkW W K exe endPc R F n blk :=
    fun h s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨(h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, hK _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1⟩
  have hn : ∀ {n : ND}, NodeW W (fun _ _ => False) exe endPc R F n → NodeW W K exe endPc R F n :=
    fun h s c hA => ⟨(h s c hA).1, hK s c (h s c hA).1⟩
  exact ⟨hb h.de, hb h.dt1, hb h.dj1, hb h.dt2, hb h.dg2, hb h.se, hn h.sn1, hn h.sn1b, hb h.sn2, hn h.ssvc,
    hb h.sn5, hn h.sex⟩

section Gen

variable {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)

include hlab in
/-- A label of wake's code at its `cv` address. -/
private theorem lab_cv' (l : Label) (h : (codeOf lo wakeProg l).isSome ∧ cv l < 2 ^ 64) :
    (L.lab l).toBitVec.toNat = cv l :=
  WcW.lab_cv hlab h.1 h.2

include hlab in
/-- **`scc_rt_abort`'s code is off the clone and the take site.** -/
theorem abort_off (s : State) (h : inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    pcOf s ≠ Spike.Lib.A64.Flow.WakeWc.clonePc L ∧
      pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  obtain ⟨h1, h2⟩ := h
  rw [lab_cv' hlab _ (by unfold cv; rw [← codeT_eq]; decide +kernel)] at h1
  rw [lab_cv' hlab _ (by unfold cv; rw [← codeT_eq]; decide +kernel)] at h2
  have hc := WcW.clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  have e : Spike.Lib.A64.Flow.WakeWc.clonePc L = cv ".L21_wc_main.sp6" + 52 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cv ".L21_wc_main.sp6" = y := by simp [cv, hy]
    rw [ey] at hb ⊢
    show (L.lab (".L21_wc_main" ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = y + 52
    rw [show (".L21_wc_main" ++ ".sp6" : String) = ".L21_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 52).toNat = y + 52
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hcl : ¬ (cv "scc_rt_abort" ≤ cv ".L21_wc_main.sp6" + 52 ∧
      cv ".L21_wc_main.sp6" + 52 < cv "scc_rt_thr_worker") := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  have hst := lab_cv' hlab Spike.Lib.A64.Flow.Ret0.StackTake.siteL
    (by unfold cv; rw [← codeT_eq]; decide +kernel)
  have hsi : ¬ (cv "scc_rt_abort" ≤ cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL ∧
      cv Spike.Lib.A64.Flow.Ret0.StackTake.siteL < cv "scc_rt_thr_worker") := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  refine ⟨fun he => hcl ?_, fun he => hsi ?_⟩
  · rw [← e, ← he]; exact ⟨h1, h2⟩
  · rw [← hst, ← he]; exact ⟨h1, h2⟩

include hlab in
/-- **`X0W` in `scc_rt_abort`'s code**, at any take address `a` resolving to
the site. -/
theorem x0W_abort {a : Int64}
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0W L a s := fun s h =>
  ⟨(abort_off hlab s h).1, fun he => absurd (he.trans ha) (abort_off hlab s h).2⟩

include hp hlo hlab in
/-- **`WcHAbStub` under the take move** (`wc_heapAbStub`'s, at `PhRec.K L rS`):
the path inside `W0` and in `scc_rt_abort`'s code (`hpathW_hX`), whose pcs
are off the take site. -/
theorem wc_heapAbStubK {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isaLSE2} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {J0 : Spike.Lib.A64.Flow.AS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.A64.Flow.FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -288)
    (hhi : 0 ≤ R.hi) (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wX (ms fs) L.lab J0 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStub (W0 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) ar p DtW (Spike.Lib.A64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.A64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.A64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J0 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hkc : (-240 : Int) < R.hi := by omega
  have hb := Region.callee_base (hi' := 0) hR (show R.lo ≤ -240 + -48 by omega) (by decide) hkc
  have hal' : (R.callee (-240) (-48) 0).base.toNat % 16 = 0 := by
    have : (((R.callee (-240) (-48) 0).base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
    omega
  have hR' := Region.callee_ok (hi' := 0) hR (show R.lo ≤ -240 + -48 by omega) (by decide) hkc (by omega)
  have h0 := hpathW_hab0 (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-240) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-240, []⟩ m0 σC) hp hlo hlab a hΛ hR' hal'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hX (F := fun m => F m ∧ Spike.Lib.A64.Flow.CKept R (-240) (-48) 0 m0 m ∧
      Spike.Lib.A64.Flow.Abs R ⟨-240, []⟩ m0 σC) (c0 := c0)
    (ra := (L.lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec) hlab hR' hal' (by simp [Region.callee])
    (by simp [Region.callee]) hp hlo
  have hpath := HPathW.map (hpathW_K (K := Spike.Lib.A64.PhRec.K L rS)
    (HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_off hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.A64.StubW.stubHRW_of_code L.lays rfl (hp ▸ abortIn_wake) hK
    (Spike.Lib.A64.Flow.fstable_enter hR hF (by omega) (by decide) hkc (by decide) (by omega) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

/-- **The control at the start's heap abort**: at `wX .abort` below
`scc_rt_main`'s entry at `c0W`, the box's call has control `c0W` (`one` box
of type `int`, two units), so the control is `c0W` holding the counter at a
count `o` crossing the cells (`Jfull`): its facts, its placement and the
heap abort's obligation hold. -/
theorem hctl_c0W {L : RuntimeLayout} {ms : MemSide isaLSE2} {Λ : Scc.Sem.Layout} {L0 : Lbl} {ar : Arena}
    {σ0 : Spike.Lib.A64.Flow.AS} (hctr : ms.ctr = ar.ctr)
    (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hpl0 : ∀ s, PlacedSE Λ L0 s c0W []) :
    ∀ σC c0, (wX ms L.lab (wJ0 (wNC L.lab (JS L 0#64 c0W)).J σ0) .abort).J σC c0 →
      ((([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf wakeSrc c0 []) ∧
        (∀ s, PlacedSE Λ L0 s c0 []) ∧ HeapAbortOblA ar.cells ar.ctr c0 := by
  rintro σ c0 ⟨-, -, q, hfull, σe, -, ⟨σ', hJ, -⟩, -⟩
  have hq : q.1.c0 = c0W := MainWf.ctl_mainE0 (P := (· = c0W)) rfl σ' _ hJ
  have ht := q.2.term; rw [hq, Spike.Lib.WakeC0.c0W_term] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have hev := q.2.ev; rw [hq, ← Op.new.inj ha] at hev
  have hz : TermRun.evalAt c0W.env (.var "z") = some (.int, [TermRun.cst (.num 0)]) := rfl
  have hτ : q.1.τ = .int := by rw [hz] at hev; exact (Prod.mk.inj (Option.some.inj hev)).1.symm
  rcases hfull with ⟨-, hn⟩ | ⟨o, rfl, -, hlt⟩
  · rw [q.2.one] at hn; exact absurd hn (by decide)
  rw [q.2.one, hτ, hu] at hlt; rw [hq]
  refine ⟨⟨fun _ => Spike.Lib.WakeC0.c0W_ctl.1, WcWf.RunWf.hold Spike.Lib.WakeC0.c0W_ctl.2⟩,
    fun s => WcWf.PlacedSE.hold.2 (hpl0 s), fun old h => ?_⟩
  obtain ⟨hle, hw⟩ := h (.inr ⟨"o", .var "z", Spike.Lib.A64.Flow.WakeWc.boxTerm, rfl⟩)
  have he := hw _ (by rw [← hctr]; rfl)
  have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he
  exact .inr ⟨"o", .var "z", _, .int, TermRun.cst (.num 0), rfl, rfl, rfl, hle, by rw [← hcells]; omega⟩

end Gen

end Spike.Lib.A64.WakePh.HAbStubK

/-- info: 'Spike.Lib.A64.WakePh.HAbStubK.wc_heapAbStubK' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.HAbStubK.wc_heapAbStubK

/-- info: 'Spike.Lib.A64.WakePh.HAbStubK.hctl_c0W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.HAbStubK.hctl_c0W
