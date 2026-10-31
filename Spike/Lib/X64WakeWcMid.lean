/-
**wake.w's `wc_main` from the box's store to its `clone`'s `syscall`**
(x86-64; twin of `Spike/Lib/A64WakeWcMid.lean`), inside `W`, in any valid
layout of `wakeCells`: the three segments past the box's store composed,

    .x18+18 .. .x19     wake_wc_res_segW      (the reserve)
    .x19 .. .x20        wake_wc_sp3_segW      (the second TCB, scc_rt_alloc_tcb)
    .x20 .. syscall     wake_wc_sp4_pub_segW  (the tid word, thread_init, the
                                               mfence's publication, the clone's
                                               arguments)

at one memory side `ms` and labels `lbl`. At `.x19` the frame's words `cA`
(the box) and `m` (main's `ThreadId`), the caller's saved `%rbp` and return
address (`fr`) and the source `c0` become the later segments' ghosts
(`rX_wcN3`).

**Where this differs from AArch64**: the source's publication is not at a
fence past the box's store (x86-64's listing has none there, see
`X64WakeWcRes`) but at `wc_main`'s `mfence` before the `syscall`
(`X64WakeWcPub`). So the landing's guard `Q l A` holds unchanged up to
`.x20` (A64's `hfr` takes the source from `Q` to `S` at the `dmb`), and in
place of `hfr` the instance says, under `Q`, that the source is at
`boxTerm` with no hold and `o` bound to the box's owned locative (`hpub`,
what `boxPubSy` asks). The exit is at the published control
`boxPubCtl c0 ty l` with `MidPG Q c0 ty l cA` (A64's `MidG S c0 cA` at the
exit's control).

- `MidPG`: the source `c0` at `Q l A` for the box's word `cA = A`, at
  `boxTerm`, `o` bound to `l`'s owned locative at `ty`;
- `WcMidW`, `WcMidW.triv`: the three segments' states inside `W`;
- `wake_wc_mid_segW`: the composite.
-/
import Spike.Lib.X64WakeWcSp3Seg
import Spike.Lib.X64WakeWcPub

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.WakePh.WcSp4 (wcNI)
open Spike.Lib.X64.WakePh.WcClone (wcNS)
open Spike.Lib.X64.WakePh.Tcb2Call (oC wcN3 tcb2Q)
open Spike.Lib.X64.Flow.Ret0 (tiN tiX StOk)
open Spike.Lib.X64.Rt (TcbOkGA hdrA)
open Spike.Lib.X64.Rt.Reserve (ResOkA)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl)
open Scc.Cert.Rt.X64 (Lays endOf)

/-- **The pure facts the exit keeps** (x86-64's `MidG` at the published
control): the source `c0` at `Q l A` for the box's word `cA = A`, at
`boxTerm` with no hold, `o` bound to `l`'s owned locative at `ty`. -/
def MidPG (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) (c0 : Ctl) (ty : Ty) (l : WeakMem.AllocLabel)
    (cA : BitVec 64) : Prop :=
  Q l cA.toNat c0 ∧ c0.term = boxTerm ∧ c0.hold = none ∧
    TermRun.evalAt c0.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)])

/-- **`wc_main`'s states past the box's store inside `W`**: the reserve's
segment's, and at every ghost with `MidG Q c0 cA`, `FrG J0 fr` and
`FrMG J0 fr m` (as `rX_wcN3` exits) the second TCB's, and with `MidPG` the
`.x20`-to-`syscall` segment's (publishing at the `mfence`). -/
structure WcMidW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (ms : MemSide isa) (J0 : AS → Ctl → Prop)
    (Q : WeakMem.AllocLabel → Nat → Ctl → Prop) : Prop where
  res : WcResW W K exe endPc R F ms J0 Q
  sp3 : ∀ c0 cA m fr, MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m → WcSp3W W K exe endPc R F c0 cA m fr
  sp4 : ∀ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m →
    WcSp4PW W K exe endPc R F F₂ c0 ty l (t2 (_root_.Executable.labels exe).label) cA m fr

/-- From the box's store to the `syscall` inside the trivial predicate,
with no outside moves. -/
theorem WcMidW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidW (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ ms J0 Q :=
  ⟨WcResW.triv, fun _ _ _ _ _ => WcSp3W.triv, fun _ _ _ _ _ _ _ => WcSp4PW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from the box's store to its `clone`'s `syscall` is one
segment inside `W`** in any valid layout of `wakeCells`: from the landing
past the box's store (`bX l A`, some fresh label `l`, the source at
`Q l A`) to the `syscall` (`wcNS` at the second TCB `t2`, the child's stack
top `kOf`, the frame's words), the source published at `boxPubCtl c0 ty l`
with `MidPG`, the caller's saved pair `fr` with `FrG`, it and main's word
`m` with `FrMG`. The premises are the three segments' at every ghost; the
counters' old values owned at their `lock xadd` nodes' states (`hres`,
`htcb`); the source under `Q` ready to publish (`hpub`, `hP`); `K` keeps
the caller's cells outside `scc_rt_alloc_tcb`'s region (`hKR`), hence
outside `scc_rt_thread_init`'s. -/
theorem wake_wc_mid_segW {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (hW : WcMidW W K exe endPc R F F₂ ms J0 Q)
    (hpub : ∀ l A c, Q l A c → c.term = boxTerm ∧ c.hold = none ∧
      ∃ ty, TermRun.evalAt c.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub)
    (hres : ∀ g : Ret0.AllocTcb.G × Ctl, ResOkA ms F exe endPc (rAR R) F ⟨g.1, 0#64, g.2⟩)
    (hhdr : ∀ c0 g, StOk ms F (hdrA (_root_.Executable.labels exe).label (tcb2Q g c0))
      ((tcb2Q g c0).h ||| 1#64 <<< 36))
    (htcb : ∀ c0 g, TcbOkGA ms F exe endPc (R.callee (-72) (-184) 8) F (tcb2Q g c0))
    (htid : ms.rt (t2 (_root_.Executable.labels exe).label + 56#64).toNat ∧
      ms.mp ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ true ∧
      ms.G ⟨t2 (_root_.Executable.labels exe).label + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t2 (_root_.Executable.labels exe).label + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-184) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) (R' : Region) (F' : MachineData → Prop),
      R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J
            σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧
          (wcNI (_root_.Executable.labels exe).label c0 (t2 (_root_.Executable.labels exe).label) cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e).J
            (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms
          (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label
            (tiQ (t2 (_root_.Executable.labels exe).label) c0 g) x) s c ∧ M s.st.1)) :
    SegW W K p lbl ms
      (fun s c => ∃ l A, At exe endPc R F (bX ms (_root_.Executable.labels exe).label J0 l A) s c ∧ Q l A c)
      (fun s c => ∃ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
        At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label (boxPubCtl c0 ty l)
          (t2 (_root_.Executable.labels exe).label) (kOf (_root_.Executable.labels exe).label) cA m fr) s c) := by
  let lab := (_root_.Executable.labels exe).label
  have hKR4 : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8 :=
    fun s s' hk hD k hk' hn => hKR s s' hk hD k hk' fun ⟨h1, h2, h3⟩ =>
      hn ⟨h1, by simp only [Region.callee] at h2 ⊢; omega, by simp only [Region.callee] at h3 ⊢; omega⟩
  -- one ghost: `.x19` to the `syscall`
  have hG : ∀ (c0 : Ctl) (cA m : BitVec 64) (fr : BitVec 64 × BitVec 64),
      SegW W K p lbl ms
        (fun s c => At exe endPc R F (wcN3 lab (j3 cA m fr) c0) s c ∧ (MidG Q c0 cA ∧ FrG J0 fr ∧ FrMG J0 fr m))
        (fun s c => ∃ c0 ty l cA m fr, MidPG Q c0 ty l cA ∧ FrG J0 fr ∧ FrMG J0 fr m ∧
          At exe endPc R F₂ (wcNS lab (boxPubCtl c0 ty l) (t2 lab) (kOf lab) cA m fr) s c) := by
    refine fun c0 cA m fr => SegW.of_imp fun hM => ?_
    obtain ⟨⟨l, A, hQ, hA⟩, hG, hGm⟩ := hM
    obtain ⟨ht, hh, ty, ho⟩ := hpub l A c0 hQ
    have hMP : MidPG Q c0 ty l cA := ⟨hA ▸ hQ, ht, hh, ho⟩
    exact ((wake_wc_sp3_segW hp hend hF hR (by omega) hhi (hW.sp3 c0 cA m fr ⟨⟨l, A, hQ, hA⟩, hG, hGm⟩)
      (hhdr c0) (htcb c0) hFK hKR).seq
      (wake_wc_sp4_pub_segW hp hend hF hR hlo hhi hF₂s hF₂ ht hh ho hP (hW.sp4 c0 ty l cA m fr ⟨hMP, hG, hGm⟩)
        htid hFK hKR4 (hti c0 cA m fr))).mono_post fun _ _ h => ⟨c0, ty, l, cA, m, fr, hMP, hG, hGm, h⟩
  refine (wake_wc_res_segW hp hend hF hR (by omega) hhi hW.res hres).seq ?_
  refine (SegW.exists_pre (P := fun (g : Ctl × BitVec 64 × BitVec 64 × (BitVec 64 × BitVec 64)) s c =>
    At exe endPc R F (wcN3 lab (j3 g.2.1 g.2.2.1 g.2.2.2) g.1) s c ∧
      (MidG Q g.1 g.2.1 ∧ FrG J0 g.2.2.2 ∧ FrMG J0 g.2.2.2 g.2.2.1))
    fun g => hG g.1 g.2.1 g.2.2.1 g.2.2.2).mono_pre ?_
  rintro s c ⟨x, h⟩
  obtain ⟨cA, m, fr, hM, hG', hGm, h⟩ := rX_wcN3 h
  exact ⟨(c, cA, m, fr), h, hM, hG', hGm⟩

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_mid_segW
