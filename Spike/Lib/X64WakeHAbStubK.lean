/-
**The start's heap abort under the take move** (x86-64; the twin of
`Spike/Lib/A64WakeHAbStubK.lean`): `WakePh.wc_heapAbStub` at `PhRec.K` and
the control facts at `wc_main`'s heap abort below `scc_rt_main`'s entry.

- `hpathW_K`: a path obligation with no outside moves is one under `K` when
  `K` moves none of its states.
- `abort_off`, `x0W_abort`: `scc_rt_abort`'s code is off the clone and the
  take site, so `X0W` holds there.
- `wc_heapAbStubK`: `WakePh.wc_heapAbStub` under `PhRec.K` (the path is in
  `scc_rt_abort`'s code, `hpathW_hX`, off the take site).
- `hctl_c0`: at `wX .abort` below `JS … c0`, the control is `c0` holding the
  counter at a crossing count (`Jfull`, one box of two units), so its facts
  and the heap abort's obligation (`HeapAbortOblA`) hold.

**Where this differs from AArch64**: `HPathW` has no `sn1b` node (one-node
`leaq`) and its `syscall` node is `ssys`; the clone's pc is `.Lwc_main.x21 +
46` (A64's `.L21_wc_main.sp6 + 52`); the callee region is `R.callee (-240 -
8) (-24) 16`, so `R` needs `[-272, -232)` and no alignment premise (A64's
`R.lo ≤ -288`, `0 ≤ R.hi`, `hal`); x86-64 has no fixed box control `c0W`
(its consumer lives on AArch64), so `hctl_c0` is stated at any control `c0`
boxing a zero (`StartH0.C0Box`) with its facts (`hc0`) and placement
(`hpl0`), at any stack offset `k0` (A64's `0#64`); `wX .abort`'s invariant
carries no return-address conjunct, so the pattern has one field fewer.
-/
import Spike.Lib.X64WakeHAbStub
import Spike.Lib.X64WakeMainGlue
import Spike.Lib.X64WakeStartH0
import Spike.Lib.X64WakeWcWf
import Spike.Lib.X64WakeX0

namespace Spike.Lib.X64.WakePh.HAbStubK

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib (Arena FragS Frag Region HeapAbortOblA)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW At)
open Spike.Lib.X64.Flow.WakeM (wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcHAbStub wX)
open Spike.Lib.X64.Abort.Disp (HPathW)
open Spike.Lib.X64.WakeWf (DtW W0 RunWf X0W)
open Spike.Lib.X64.WakePh.MainGlue (JS)
open Spike.Lib.X64.WakePh.WcW (cv inCv)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)

/-- **No outside moves to `K`**: a path obligation under no outside move is
one under `K` when `K` moves no state of `W`. -/
theorem hpathW_K {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64}
    (h : HPathW W (fun _ _ => False) exe endPc R F c0 ra) (hK : ∀ s c, W s c → ∀ s', ¬ K s s') :
    HPathW W K exe endPc R F c0 ra := by
  have hb : ∀ {n : ND} {blk : List (Directive × Nat)}, BlkW W (fun _ _ => False) exe endPc R F n blk →
      BlkW W K exe endPc R F n blk :=
    fun h s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
      ⟨(h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, hK _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1⟩
  have hn : ∀ {n : ND}, NodeW W (fun _ _ => False) exe endPc R F n → NodeW W K exe endPc R F n :=
    fun h s c hA => ⟨(h s c hA).1, hK s c (h s c hA).1⟩
  exact ⟨hb h.de, hb h.dt1, hb h.dj1, hb h.dt2, hb h.dg2, hb h.se, hn h.sn1, hb h.sn2, hn h.ssys,
    hb h.sn5, hn h.sex⟩

section Gen

variable {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)

include hlab in
/-- A label of wake's code at its `cv` address. -/
private theorem lab_cv' (l : Label) (h : (codeLabel lo wakeCells l).isSome ∧ cv l < 2 ^ 64) :
    (L.lab l).toBitVec.toNat = cv l :=
  WcW.lab_cv hlab h.1 h.2

include hlab in
/-- **`scc_rt_abort`'s code is off the clone and the take site.** -/
theorem abort_off (s : State) (h : inPc L "scc_rt_abort" "scc_rt_thr_worker" s) :
    pcOf s ≠ Spike.Lib.X64.Flow.WakeWc.clonePc L ∧
      pcOf s ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  obtain ⟨h1, h2⟩ := h
  rw [lab_cv' hlab _ (by unfold cv; rw [← codeT_eq]; decide +kernel)] at h1
  rw [lab_cv' hlab _ (by unfold cv; rw [← codeT_eq]; decide +kernel)] at h2
  have hc := Spike.Lib.X64.Flow.WakeWc.clone_inCv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  have e : Spike.Lib.X64.Flow.WakeWc.clonePc L = cv ".Lwc_main.x21" + 46 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cv ".Lwc_main.x21" = y := by simp [cv, hy]
    rw [ey] at hb ⊢
    show (L.lab ".Lwc_main.x21" + 46).toBitVec.toNat = y + 46
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 46).toNat = y + 46
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hcl : ¬ (cv "scc_rt_abort" ≤ cv ".Lwc_main.x21" + 46 ∧
      cv ".Lwc_main.x21" + 46 < cv "scc_rt_thr_worker") := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  have hst := lab_cv' hlab Spike.Lib.X64.Flow.Ret0.StackTake.siteL
    (by unfold cv; rw [← codeT_eq]; decide +kernel)
  have hsi : ¬ (cv "scc_rt_abort" ≤ cv Spike.Lib.X64.Flow.Ret0.StackTake.siteL ∧
      cv Spike.Lib.X64.Flow.Ret0.StackTake.siteL < cv "scc_rt_thr_worker") := by
    unfold cv; rw [← codeT_eq]; decide +kernel
  refine ⟨fun he => hcl ?_, fun he => hsi ?_⟩
  · rw [← e, ← he]; exact ⟨h1, h2⟩
  · rw [← hst, ← he]; exact ⟨h1, h2⟩

include hlab in
/-- **`X0W` in `scc_rt_abort`'s code**, at any take address `a` resolving to
the site. -/
theorem x0W_abort {a : Int64}
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0W L a s := fun s h =>
  ⟨(abort_off hlab s h).1, fun he => absurd (he.trans ha) (abort_off hlab s h).2⟩

include hp hlo hlab in
/-- **`WcHAbStub` under the take move** (`wc_heapAbStub`'s, at `PhRec.K L rS`):
the path inside `W0` and in `scc_rt_abort`'s code (`hpathW_hX`), whose pcs
are off the take site. -/
theorem wc_heapAbStubK {R : Region} {F : MachineData → Prop} {ar : Arena} {p : Prog} {Cl : State → Prop}
    {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
    {fs : List TermRun.Frame} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {J0 : Spike.Lib.X64.AS → Ctl → Prop} {rS : Scc.Sem.Range} (a : BitVec 64)
    (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hF : Spike.Lib.X64.FStable R F) (hR : R.OK) (hlo' : R.lo ≤ -272) (hhi : -232 ≤ R.hi)
    (hK : (ms fs).K = some abi) (hfs : fs = [] ∨ fs = [frM])
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hctl : ∀ σC c0, (wX (ms fs) L.lab R J0 .abort).J σC c0 →
      ((fs = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 fs) ∧ (∀ s, PlacedSE L.Λ L0 s c0 fs) ∧
        HeapAbortOblA ar.cells ar.ctr c0)
    (hab : ∀ s : State, s.st.2 = L.lab "scc_rt_abort_heap_exit" → (ms fs).abortAt s)
    (hX0 : ∀ s, inPc L "scc_rt_abort" "scc_rt_thr_worker" s → X0 s) :
    WcHAbStub (W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) ar p DtW (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
      (Spike.Lib.X64.ThreadsAb.Ac L.lab pfxM) Ctx L0 ls0 frM X0) (Spike.Lib.X64.PhRec.K L rS) p lbl ms L.exe
      L.endPc R F fs J0 := by
  intro m0 σC c0 hJ
  obtain ⟨hc0, hpl, hobl⟩ := hctl σC c0 hJ
  have hsite := siteW hp hlo hlab
  have hR' : (R.callee (-240 - 8) (-24) 16).OK :=
    Region.callee_ok hR (by omega) (by decide) (by omega) (by omega)
  have h0 := hpathW_hab0 (ar := ar) (p := p) (Cl := Cl) (Ctx := Ctx) (L0 := L0) (ls0 := ls0) (frM := frM)
    (X0 := X0) (F := fun m => F m ∧ Spike.Lib.X64.CKept R (-240 - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨-240, []⟩ m0 σC) hp hlo hsite hlab a hΛ hR'
    (by simp [Region.callee]) (by simp [Region.callee]) rfl hfs hcl hc0 hpl hobl hX0
  have hX := hpathW_hX (F := fun m => F m ∧ Spike.Lib.X64.CKept R (-240 - 8) (-24) 16 m0 m ∧
      Spike.Lib.X64.Abs R ⟨-240, []⟩ m0 σC) (c0 := c0)
    (ra := Spike.Lib.X64.Flow.WakeWc.raAb L.lab) hp hlo hsite hlab hR' (by simp [Region.callee])
    (by simp [Region.callee])
  have hpath := HPathW.map (hpathW_K (K := Spike.Lib.X64.PhRec.K L rS)
    (Abort.Disp.HPathW.and h0 hX fun _ _ h₁ h₂ => And.intro h₁ h₂)
    fun s _ h s' hk => (abort_off hlab s h.2).2 (congrArg (fun x : Int64 => x.toBitVec.toNat) hk.1))
    fun _ _ h => h.1
  exact Spike.Lib.X64.StubW.stubHRW_of_code L.lays rfl (by rw [hp]; exact SccCode.wake_abort) hK
    (Spike.Lib.X64.fstable_enter hR hF (by omega) (by decide) (by omega) (by omega) (by decide) (by decide)
      (by decide)) hpath fun s _ ⟨_, _, _, hpc, _⟩ => hab s hpc

/-- **The control at the start's heap abort**: at `wX .abort` below
`scc_rt_main`'s entry at a control `cS` boxing a zero (`hbx`), the box's
call has control `cS` (`one` box of type `int`, two units), so the control
is `cS` holding the counter at a count `o` crossing the cells (`Jfull`):
its facts, its placement and the heap abort's obligation hold. -/
theorem hctl_c0 {L : RuntimeLayout} {ms : MemSide isa} {Λ : Scc.Sem.Layout} {L0 : Lbl} {ar : Arena}
    {p : Prog} {cS : Ctl} {k0 : BitVec 64} {R : Region} {σ0 : Spike.Lib.X64.AS} (hctr : ms.ctr = ar.ctr)
    (hcells : ms.cells = ar.cells) (hu : ms.units 1 .int = 2) (hbx : C0Box cS)
    (hc0 : (∀ a, cS.term ≠ .ret a) ∧ RunWf p cS []) (hpl0 : ∀ s, PlacedSE Λ L0 s cS []) :
    ∀ σC c0, (wX ms L.lab R (wJ0 (wNC L.lab (JS L k0 cS)).J σ0) .abort).J σC c0 →
      ((([] : List TermRun.Frame) = [] → ∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) ∧
        (∀ s, PlacedSE Λ L0 s c0 []) ∧ HeapAbortOblA ar.cells ar.ctr c0 := by
  rintro σ c0 ⟨-, -, q, hfull, σe, -, ⟨σ', hJ, -⟩, -⟩
  have hq : q.1.c0 = cS := MainWf.ctl_mainE0 (P := (· = cS)) rfl σ' _ hJ
  obtain ⟨e, he⟩ := hbx.term
  obtain ⟨w, hw, hw0⟩ := hbx.ev
  obtain ⟨_, ht⟩ := q.2.term; rw [hq, he] at ht
  obtain ⟨-, ha, -⟩ := Expr.let_.inj ht
  have hev := q.2.ev; rw [hq, ← (Op.new.inj ha).1] at hev
  have hτ : q.1.τ = .int := by rw [hw] at hev; exact (Prod.mk.inj (Option.some.inj hev)).1.symm
  rcases hfull with ⟨-, hn⟩ | ⟨o, rfl, -, hlt⟩
  · rw [q.2.one] at hn; exact absurd hn (by decide)
  rw [q.2.one, hτ, hu] at hlt; rw [hq]
  refine ⟨⟨fun _ => hc0.1, WcWf.RunWf.hold hc0.2⟩, fun s => WcWf.PlacedSE.hold.2 (hpl0 s), fun old h => ?_⟩
  obtain ⟨hle, hw'⟩ := h (.inr ⟨"o", .var "z", e, _, he⟩)
  have he' := hw' _ (by rw [← hctr]; rfl)
  have ho : o.toNat = old := by simpa [TermRun.cst, Promises.TVal.mk0] using he'
  exact .inr ⟨"o", .var "z", e, .int, w, ⟨_, he⟩, hw, rfl, hle, by rw [← hcells]; omega⟩

end Gen

end Spike.Lib.X64.WakePh.HAbStubK

/-- info: 'Spike.Lib.X64.WakePh.HAbStubK.x0W_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.HAbStubK.x0W_abort

/-- info: 'Spike.Lib.X64.WakePh.HAbStubK.wc_heapAbStubK' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.HAbStubK.wc_heapAbStubK

/-- info: 'Spike.Lib.X64.WakePh.HAbStubK.hctl_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.HAbStubK.hctl_c0
