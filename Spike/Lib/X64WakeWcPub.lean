/-
**wake.w's `wc_main` from `.x21` to its `clone`'s `syscall`, publishing the
box at the `mfence`** (x86-64; the publication of
`Spike/Lib/WakePubFence.lean`, moved): `X64WakeCloneSeg.wake_wc_clone_segW`'s
segment with the source, at `boxTerm` (`let c = publish o in …`, `o` bound
to the box's owned locative, no hold) up to the fence, taking its
publication step at `wc_main`'s `mfence` (`.Lwc_main.x21+12`,
`Out.fence .sy`, `FenceRun.pub` under `ms.pub`) and standing at
`boxPubCtl c0 ty l` (`let p = pair c me in spawnTerm`) from there to the
`syscall`.

Where this differs from AArch64 (`WakePubFence.wake_pub_fence`, the
`dmb ishst` past the box's store): wake's x86-64 listing has no fence at the
source's `publish` position (scc's `# fence st` emits no code on x86-64,
whose stores are ordered), so the publication moves from there to the
`mfence` before the clone, a stronger fence (`.sy`, which `PubStep` admits)
later in the same thread, past the reserve, `scc_rt_alloc_tcb`,
the tid store and `scc_rt_thread_init`. Until that fence the source stands
at `boxTerm`: every segment from the box's store to `.x21` is parametric in
the source control. The x86-64 consumer's `PreJA` ignores source views, so
the later publication point changes no consumer obligation.

- `pN`: the nodes, at `c0` up to the fence and at `boxPubCtl c0 ty l` past
  it; `WcClonePW`: their states inside `W`;
- `wake_wc_clone_pub_segW`: the segment from `.x21` to `wcNS` at the
  published control;
- `WcSp4PW`, `wake_wc_sp4_pub_segW`: from `.x20` (through
  `scc_rt_thread_init`, `wake_wc_sp4_ret_segW`) to the `syscall`,
  publishing at the `mfence`.
-/
import Spike.Lib.X64WakeWcSp4Seg
import Spike.Lib.X64WakeBoxDefs

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcSp4
open Spike.Lib.X64.WakePh.WcClone (oW x21L FrW wcN21 wcNf wcNa wcNd wcN10 wcNr wcNS x21A cloneLd nrB
  x21A_ok cloneLd_ok nrB_ok x21A_edge cloneLd_edge nrB_edge mfence_ndW wcCloneIn XN)
open Spike.Lib.X64.Flow.Ret0 (TiG tiN tiX stacksA)
open Spike.Lib.X64WakeBoxDefs (boxTerm boxPubCtl boxPubSy)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open SccCode (wakeCells)

section Nodes

variable (lab : Label → Int64) (c0 : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) (t k cA m : BitVec 64)
  (fr : BitVec 64 × BitVec 64)

/-- **The nodes from `.x21` to the `syscall`**: the source at `c0` up to the
fence, at `boxPubCtl c0 ty l` past it. -/
def pN : XN → ND
  | .n21 => wcN21 lab c0 t k cA m fr
  | .nf => wcNf lab c0 t k cA m fr
  | .na => wcNa lab (boxPubCtl c0 ty l) t k cA m fr
  | .nd => wcNd lab (boxPubCtl c0 ty l) t k cA m fr
  | .n10 => wcN10 lab (boxPubCtl c0 ty l) t k cA m fr
  | .nr => wcNr lab (boxPubCtl c0 ty l) t k cA m fr

end Nodes

/-- **`.x21`'s states to the `syscall` inside `W`**, none moved by `K`, the
source published past the fence. -/
structure WcClonePW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) (t k cA m : BitVec 64)
    (fr : BitVec 64 × BitVec 64) : Prop where
  n21 : BlkW W K exe endPc R F (wcN21 (_root_.Executable.labels exe).label c0 t k cA m fr) x21A
  nf : NodeW W K exe endPc R F (wcNf (_root_.Executable.labels exe).label c0 t k cA m fr)
  na : BlkW W K exe endPc R F (wcNa (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t k cA m fr) cloneLd
  nd : NodeW W K exe endPc R F (wcNd (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t k cA m fr)
  n10 : NodeW W K exe endPc R F (wcN10 (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t k cA m fr)
  nr : BlkW W K exe endPc R F (wcNr (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t k cA m fr) nrB

/-- Inside the trivial predicate, with no outside moves. -/
theorem WcClonePW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcClonePW (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 ty l t k cA m fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv⟩

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x21` to its `clone`'s `syscall`, publishing the box
at the `mfence`**, inside `W`, in any valid layout of cells holding the
blocks (`wcCloneIn`): from `.x21` with the source at `c0` (`boxTerm`, no
hold, `o` the box's owned locative `⟨l, 0⟩`) to the `syscall` with the
source at `boxPubCtl c0 ty l`, under a memory side admitting the
publication (`hP`). -/
theorem wake_wc_clone_pub_segW {W : Frag isa} {K : State → State → Prop}
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : wcCloneIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (ht : c0.term = boxTerm) (hh : c0.hold = none)
    (ho : TermRun.evalAt c0.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub) (hW : WcClonePW W K exe endPc R F c0 ty l t k cA m fr) :
    SegW W K p lbl ms (At exe endPc R F (wcN21 (_root_.Executable.labels exe).label c0 t k cA m fr))
      (At exe endPc R F (wcNS (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t k cA m fr)) := by
  simp only [wcCloneIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, bl⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt cells x21L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x21L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hA : SegW W K p lbl ms (At exe endPc R F (pN lab c0 ty l t k cA m fr .n21))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNS lab (boxPubCtl c0 ty l) t k cA m fr) x) s c) := by
    refine fn_segW (N := pN lab c0 ty l t k cA m fr) (fun i => ?_) XN.n21
    cases i
    case n21 =>
      refine seg_ndW (by simp [x21A]) x21A_ok hF hR hlo hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x21L) x21A)) hW.n21
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XN.nf, x21A_edge hJ⟩⟩
    case nf =>
      refine mfence_ndW (fun s he hn => code bf s he hn) hW.nf fun σ c hJ => ?_
      obtain ⟨hc, hA⟩ := hJ
      refine ⟨boxPubCtl c0 ty l, .pub hP (by rw [hc]; exact boxPubSy ht hh ho) (.refl _),
        .inl ⟨XN.na, ?_, rfl, rfl, hA⟩⟩
      show lab x21L + 15 = lab x21L + Int64.ofNat 12 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    case na =>
      exact seg_ndW (by simp [cloneLd]) cloneLd_ok hF hR hlo hhi (fun s he hn => code bl s he hn) hW.na
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XN.nd, cloneLd_edge hJ⟩⟩
    case nd =>
      refine flag_ndW (fi := .xor_rr32_self .rdx) rfl hF (fun s he hn => code bd s he hn) hW.nd
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XN.n10, ?_, rfl, ?_, ?_⟩⟩
      · show lab x21L + 38 = lab x21L + Int64.ofNat 36 + Int64.ofNat 2
        rw [Int64.add_assoc]; rfl
      · obtain ⟨hA, h12, hbx, hsi, h8, hdi⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsi, h8, hdi, and_self]⟩
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case n10 =>
      refine flag_ndW (fi := .xor_rr32_self .r10) rfl hF (fun s he hn => code b10 s he hn) hW.n10
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XN.nr, ?_, rfl, ?_, ?_, ?_⟩⟩
      · show lab x21L + 41 = lab x21L + Int64.ofNat 38 + Int64.ofNat 3
        rw [Int64.add_assoc]; rfl
      · obtain ⟨⟨hA, h12, hbx, hsi, h8, hdi⟩, -⟩ := hJ
        exact ⟨hA, by
          simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsi, h8, hdi, and_self]⟩
      · simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, hJ.2]
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case nr =>
      exact seg_ndW (by simp [nrB]) nrB_ok hF hR hlo hhi (fun s he hn => code br s he hn) hW.nr
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), nrB_edge hJ⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

/-- **`.x20`'s states to the `syscall` inside `W`, publishing at the
`mfence`**: up to the call (`WcSp4PreW`, at `F`) and `.x21`'s to the
`syscall` (`WcClonePW`, at `F₂`). -/
structure WcSp4PW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F F₂ : MachineData → Prop) (c0 : Ctl) (ty : Ty) (l : WeakMem.AllocLabel) (t cA m : BitVec 64)
    (fr : BitVec 64 × BitVec 64) : Prop
    extends WcSp4PreW W K exe endPc R F c0 t cA m fr where
  clone : WcClonePW W K exe endPc R F₂ c0 ty l t (kOf (_root_.Executable.labels exe).label) cA m fr

/-- From `.x20` to the `syscall` inside the trivial predicate, with no outside moves. -/
theorem WcSp4PW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop}
    {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcSp4PW (fun _ _ => True) (fun _ _ => False) exe endPc R F F₂ c0 ty l t cA m fr :=
  ⟨WcSp4PreW.triv, WcClonePW.triv⟩

/-- **`wc_main` from `.x20` to its `clone`'s `syscall`, publishing the box
at the `mfence`**: `wake_wc_sp4_segW` with the source at `c0` (`boxTerm`)
through the tid store and `scc_rt_thread_init` (neither needs the box
published: `htid` is about the TCB's word, `hti` carries `c0` in its
ghost), published past the fence (`wake_wc_clone_pub_segW`). -/
theorem wake_wc_sp4_pub_segW {W : Frag isa} {K : State → State → Prop} {M F₂ : MachineData → Prop}
    {kp : Nat} (hp : Lays exe wakeCells kp) (hend : endPc = endOf exe wakeCells kp)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -320) (hhi : 16 ≤ R.hi)
    (hF₂s : FStable R F₂) (hF₂ : ∀ m, F m → M m → F₂ m)
    {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (ht : c0.term = boxTerm) (hh : c0.hold = none)
    (ho : TermRun.evalAt c0.env (.var "o") = some (.ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hP : ms.pub) (hW : WcSp4PW W K exe endPc R F F₂ c0 ty l t cA m fr)
    (htid : ms.rt (t + 56#64).toNat ∧ ms.mp ⟨t + 56#64, 8⟩ true ∧ ms.G ⟨t + 56#64, 8⟩ ((1#64).setWidth 128) ∧
      ∀ m', F m' → Mem.loadInt m'.dmem (t + 56#64) 8 = none)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-72) (-248) 8).Off (k - -72) →
      Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hti : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -248 → 8 ≤ R'.hi →
      FStable R' F' → KStable K F' → (∀ m, F' m → F m) → R' = R.callee (-72) (-248) 8 →
      (∀ m, F' m → ∀ k, R.Off k → ¬ R'.Off (k - -72) → (Mem.loadInt m.dmem (R.addr k) 8).isSome) →
      ∀ g : Ret0.AllocTcb.G,
        (∃ σC c, (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c) →
        (∀ m', F' m' → ∃ mC σC c, Abs R oC mC σC ∧ (wcNI (_root_.Executable.labels exe).label c0 t cA m fr).J σC c ∧
          (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e).J (enter (-72) σC) c ∧
          ∀ k, R.Off k → ¬ R'.Off (k - -72) → Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
        SegW W K p lbl ms (At exe endPc R' F' (tiN (_root_.Executable.labels exe).label (tiQ t c0 g) .e))
          (fun s c => ∃ x, At exe endPc R' F' (tiX (_root_.Executable.labels exe).label (tiQ t c0 g) x) s c ∧
            M s.st.1)) :
    SegW W K p lbl ms (At exe endPc R F (aN (_root_.Executable.labels exe).label c0 t cA m fr .n20))
      (At exe endPc R F₂ (wcNS (_root_.Executable.labels exe).label (boxPubCtl c0 ty l) t
        (kOf (_root_.Executable.labels exe).label) cA m fr)) := by
  refine (wake_wc_sp4_pre_segW hp hend hF hR (by omega) hhi hW.toWcSp4PreW htid).seq ?_
  refine ((wake_wc_sp4_ret_segW (P := fun _ => True) hF hR hlo hhi hF₂ hFK hKR
      fun R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep =>
        (hti R' F' hR' hlo' hhi' hF' hK' hFF hR'e hcc g hg hkeep).mono_pre fun _ _ h => h.1).seq
    (wake_wc_clone_pub_segW hp hend WakePh.wake_wcCloneIn hF₂s hR (by omega) hhi ht hh ho hP hW.clone)).mono_pre
    fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ⟨he, hn, hdc, hpc, σ, hA, ⟨hD, trivial⟩, hJ⟩

end Seg

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_clone_pub_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_clone_pub_segW

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_pub_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_sp4_pub_segW
