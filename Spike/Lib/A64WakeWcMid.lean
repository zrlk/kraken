/-
**wake.w's `wc_main` from the box's store to its `clone`'s `svc`**
(AArch64, the pre-spawn consumer), inside `W`, in any valid layout of
`wakeProg`: the three segments past the box's store composed,

    .sp0+16 .. .sp3     wake_wc_res_segW    (publish, the reserve)
    .sp3 .. .sp4        wake_wc_sp3_segW    (the second TCB, scc_rt_alloc_tcb)
    .sp4 .. svc         wake_wc_sp4_segW    (the tid word, thread_init, the clone's arguments)

at one memory side `ms` and labels `lbl` (those after the box's `new`: the
segment before, `wake_wc_sp0_segW`, ends at the store's `Out.newStore`).
At `.sp3` the frame's words `cA` (the box) and `m` (main's `ThreadId`) and
the caller's saved `x29`, `x30` (`fr`) and the source `c0` become the later
segments' ghosts (`rX_wcN3`); the exit keeps what the source's `S l A c0`
and the box's word `cA = A` say, and that `fr` is the caller's at entry
(`FrG J0 fr`), and `m` the entry's `x0` with `fr` (`FrMG J0 fr m`), with the
frame's words (`FrW`, at the `svc`). The landing is guarded by `Q l A` (what
the instance knows of the source there), `hfr` asked only under it.

- `FrG`: the saved pair is the entry's `x29`, `x30`;
- `FrMG`: the saved pair and `m` are one entry's `x29`, `x30`, `x0`;
- `rX_wcN3`: `.sp3`'s exit of the reserve is `wcN3` at the frame's words;
- `WcMidW`: the three segments' states inside `W`, at every ghost;
- `wake_wc_mid_segW`: the composite.
-/
import Spike.Lib.A64WakeWcSp3Seg

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.WakePh.WcSp4 (FrW wcNS wcNI)
open Spike.Lib.A64.WakePh.Tcb2Call (oW wcN3 tcb2Q)
open Spike.Lib.A64.Flow.Ret0 (tiN tiX)
open Spike.Lib.A64.Rt (TcbOkGA hdrA)
open Spike.Lib.A64.Rt.Reserve (ResOkA)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **The pure facts the exit keeps**: the source `c0` at `S l A` for the
box's label `l` at `A`, the frame's word `cA` the box's address. -/
def MidG (S : WeakMem.AllocLabel → Nat → Ctl → Prop) (c0 : Ctl) (cA : BitVec 64) : Prop :=
  ∃ l A, S l A c0 ∧ cA.toNat = A

/-- **The saved pair is the caller's**: `fr` is the `x29`, `x30` of some
entry state of `J0` (the prologue's saves, `WakeWcPre.wcJ`). -/
def FrG (J0 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) : Prop :=
  ∃ σe c, J0 σe c ∧ fr = (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec)

/-- **The saved pair and main's word are the caller's**: `fr` and `m` are the
`x29`, `x30` and `x0` of one entry state of `J0` (the prologue's saves and
`[sp]`, `WakeWcPre.wcJ`). -/
def FrMG (J0 : AS → Ctl → Prop) (fr : BitVec 64 × BitVec 64) (m : BitVec 64) : Prop :=
  ∃ σe c, J0 σe c ∧ fr = (σe.regs.X29.toBitVec, σe.regs.X30.toBitVec) ∧ m = σe.regs.X0.toBitVec

/-- **`wc_main`'s states past the box's store inside `W`**: the reserve's
segment's (the fence's at the source facts `Q`), and at every ghost (`c0`,
`cA`, `m`, `fr`) with `MidG S c0 cA`, `FrG J0 fr` and `FrMG J0 fr m` (the
source `c0` some `S l A c0`, the frame the caller's, as `rX_wcN3` exits) the
second TCB's and `.sp4`'s. -/
structure WcMidW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isaLSE2) (J0 : AS → Ctl → Prop)
    (S Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  res : WcResW W K exe endPc R F ms J0 S Q
  sp3 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m → WcSp3W W K exe endPc R F c0 cA m fr
  sp4 : ∀ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    WcSp4W W K exe endPc R F F₂ c0 (t2 (_root_.Executable.labels exe).label) cA m fr

/-- From the box's store to the `svc` inside the trivial predicate, with no
outside moves. -/
theorem WcMidW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidW (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ ms J0 S Q :=
  ⟨WcResW.triv, fun _ _ _ _ _ => ⟨BlkW.triv, fun _ _ i => by
    cases i <;> dsimp only [Spike.Lib.A64.Rt.TcbWG] <;>
      first | exact BlkW.triv | exact fun _ _ _ => ⟨trivial, fun _ h => h⟩⟩, fun _ _ _ _ _ => WcSp4W.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The reserve's exit at `.sp3` is `wcN3`** at the frame's words `cA`
(`[sp, #8]`), `m` (`[sp, #0]`) and the caller's saved pair `fr`, the source
`c` its ghost, `MidG`, `FrG` and `FrMG` holding. -/
theorem rX_wcN3 {J0 : AS → Ctl → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop} {s : State} {c : Ctl}
    {x : Unit} (h : At exe endPc R F (rX ms (_root_.Executable.labels exe).label J0 S x) s c) :
    ∃ (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64), MidG S c cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
      At exe endPc R F (wcN3 (_root_.Executable.labels exe).label (j3 cA m fr) c) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, l, A, hS, ⟨q, ⟨σe, hJ0, h16, h8, h80⟩, h72⟩, hx0⟩ := h
  exact ⟨σ.slot (-72), σ.slot (-80), (σ.slot (-16), σ.slot (-8)), ⟨l, A, hS, h72⟩,
    ⟨σe, _, hJ0, Prod.ext h16 h8⟩, ⟨σe, _, hJ0, Prod.ext h16 h8, h80⟩, he, hn, hdc, hpc, σ, hA, hD, rfl, hx0, rfl,
    rfl, rfl, rfl⟩

/-- **`wc_main` from the box's store to its `clone`'s `svc` is one segment
inside `W`** in any valid layout of `wakeProg`: from the landing past the
box's store (`bX l A`, some fresh label `l`, the source at `Q l A`) to the
`svc` (`wcNS` at the second TCB `t2`, the child's stack top `kOf`, the frame's
words), the source at some `c0` with `MidG`, the caller's saved pair `fr` with
`FrG`, it and main's word `m` with `FrMG`. The
premises are the three segments' (`wake_wc_res_segW`,
`wake_wc_sp3_segW`, `wake_wc_sp4_segW`) at every ghost, the two counters'
old values owned at their `ldadd` nodes' states (`hres`, `htcb`); `K` keeps the
caller's cells outside `scc_rt_alloc_tcb`'s region (`hKR`), hence outside
`scc_rt_thread_init`'s. -/
theorem wake_wc_mid_segW {W : Frag isaLSE2} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -336) (hhi : 0 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {S : WeakMem.AllocLabel → Nat → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (hW : WcMidW W K exe endPc R F F₂ ms J0 S Q)
    (hfr : ∀ (q : AGB ms (_root_.Executable.labels exe).label) (l : WeakMem.AllocLabel) (A : Nat),
      Q l A ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ →
      ∃ c', FenceRun p ms.pub .st
        ⟨q.1.e, (q.1.x, .ptr .own q.1.τ, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: q.1.c0.env, none⟩ c' ∧ S l A c')
    (hres : ∀ g : Flow.Reserve.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, Ret0.StOk ms F exe endPc (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-80) (-192) 0) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-192) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -256 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-80) (-256) 0 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -80) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.ThreadInit.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oW mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-80) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -80) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c)
      (fun s c => ∃ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label)
          (kOf (_root_.Executable.labels exe).label) cA m fr) s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-80) (-256) 0).Off (k - -80) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- one ghost: `.sp3` to the `svc`
  have hG : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
      SegW W K p lbl ms
        (fun s c => At exe endPc R F (wcN3 lab (j3 cA m fr) c0) s c ∧ (MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m))
        (fun s c => ∃ c0 cA m fr, MidG S c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
          At exe endPc R F₂ (wcNS lab c0 (t2 lab) (kOf lab) cA m fr) s c) :=
    fun c0 cA m fr => SegW.of_imp fun hM =>
      ((wake_wc_sp3_segW hp hend hF hR hal (by omega) hhi (hW.sp3 c0 cA m fr hM) (hhdr c0) (htcb c0) hFK hKR).seq
        (wake_wc_sp4_segW hp hend hF hR hal hlo hhi hF₂s hF₂ (hW.sp4 c0 cA m fr hM) htid hFK hKR4
          (hti c0 cA m fr))).mono_post fun _ _ h => ⟨c0, cA, m, fr, hM.1, hM.2.1, hM.2.2, h⟩
  refine (wake_wc_res_segW hp hend hF hR hal (by omega) hhi hW.res hfr hres).seq ?_
  refine (SegW.exists_pre (P := fun (g : Ctl × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
    At exe endPc R F (wcN3 lab (j3 g.2.1 g.2.2.1 g.2.2.2) g.1) s c ∧
      (MidG S g.1 g.2.1 ∧ FrG J0 g.2.2.2 ∧ FrMG J0 g.2.2.2 g.2.2.1))
    fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2).mono_pre ?_
  rintro s c ⟨x, h⟩
  obtain ⟨cA, m, fr, hM, hG', hGm, h⟩ := rX_wcN3 h
  exact ⟨(c, cA, m, fr), h, hM, hG', hGm⟩

end Seg

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_mid_segW
