/-
**wake.w's `wc_main` from `.x21` to its `clone`'s `syscall` is one
segment** (x86-64, the twin of `A64WakeWcSp4Seg.wake_wc_sp4_call_segW`'s
part after the call): `Spike/Lib/X64WakeClone.lean`'s blocks, nodes and
edges composed with its rows (`mfence_ndW`, two `flag_ndW` at the `xorl`s),
in any valid layout of cells holding them (`wcCloneIn`).

- `XN`, `xN`: the internal nodes; `WcCloneW`: their states inside `W`;
- `wake_wc_clone_segW`: the segment to `wcNS`.
-/
import Spike.Lib.X64WakeClone

namespace Spike.Lib.X64.WakePh.WcClone

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)

/-- The internal nodes from `.x21` to the `syscall`. -/
inductive XN where
  | n21 | nf | na | nd | n10 | nr

section Seg

variable (lab : Label → Int64) (c0 : Ctl) (t k cA m : BitVec 64) (fr : BitVec 64 × BitVec 64)

/-- The nodes. -/
def xN : XN → ND
  | .n21 => wcN21 lab c0 t k cA m fr
  | .nf => wcNf lab c0 t k cA m fr
  | .na => wcNa lab c0 t k cA m fr
  | .nd => wcNd lab c0 t k cA m fr
  | .n10 => wcN10 lab c0 t k cA m fr
  | .nr => wcNr lab c0 t k cA m fr

end Seg

/-- **`.x21`'s states to the `syscall` inside `W`**, none moved by `K`. -/
structure WcCloneW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (c0 : Ctl) (t k cA m : BitVec 64) (fr : BitVec 64 × BitVec 64) :
    Prop where
  n21 : BlkW W K exe endPc R F (wcN21 (_root_.Executable.labels exe).label c0 t k cA m fr) x21A
  nf : NodeW W K exe endPc R F (wcNf (_root_.Executable.labels exe).label c0 t k cA m fr)
  na : BlkW W K exe endPc R F (wcNa (_root_.Executable.labels exe).label c0 t k cA m fr) cloneLd
  nd : NodeW W K exe endPc R F (wcNd (_root_.Executable.labels exe).label c0 t k cA m fr)
  n10 : NodeW W K exe endPc R F (wcN10 (_root_.Executable.labels exe).label c0 t k cA m fr)
  nr : BlkW W K exe endPc R F (wcNr (_root_.Executable.labels exe).label c0 t k cA m fr) nrB

/-- Inside the trivial predicate, with no outside moves. -/
theorem WcCloneW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} :
    WcCloneW (fun _ _ => True) (fun _ _ => False) exe endPc R F c0 t k cA m fr :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv, NodeW.triv, BlkW.triv⟩

section SegP

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` from `.x21` to its `clone`'s `syscall` is one segment inside
`W`**, in any valid layout of cells `cells` holding the blocks
(`wcCloneIn`): from `.x21` (the stack top `k` in `%rax`, the frame's words
`FrW`, the source at `c0`) to the `syscall` (`wcNS`: `clone(855808, k, 0,
0, t)`, `%r12 = cA`, `%rbx = m`), the source stuttering at the fence. -/
theorem wake_wc_clone_segW {W : Frag isa} {K : State → State → Prop}
    {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : wcCloneIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi)
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (hW : WcCloneW W K exe endPc R F c0 t k cA m fr) :
    SegW W K p lbl ms (At exe endPc R F (wcN21 (_root_.Executable.labels exe).label c0 t k cA m fr))
      (At exe endPc R F (wcNS (_root_.Executable.labels exe).label c0 t k cA m fr)) := by
  simp only [wcCloneIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, bl⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {k off : Nat} {b : List (Directive × Nat)}, blockAt cells x21L k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab x21L + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have hA : SegW W K p lbl ms (At exe endPc R F (xN lab c0 t k cA m fr .n21))
      (fun s c => ∃ x : Unit, At exe endPc R F ((fun _ => wcNS lab c0 t k cA m fr) x) s c) := by
    refine fn_segW (N := xN lab c0 t k cA m fr) (fun i => ?_) XN.n21
    cases i
    case n21 =>
      refine seg_ndW (by simp [x21A]) x21A_ok hF hR hlo hhi
        (fun s he hn => (by simpa using code b0 s he hn : CodeAt s (lab x21L) x21A)) hW.n21
        fun σ c hJ => ⟨c, .refl c, .inl ⟨XN.nf, x21A_edge hJ⟩⟩
    case nf =>
      refine mfence_ndW (fun s he hn => code bf s he hn) hW.nf fun σ c hJ =>
        ⟨c, .loc (.refl c), .inl ⟨XN.na, ?_, rfl, hJ⟩⟩
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
        exact ⟨hA, by simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsi, h8, hdi, and_self]⟩
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case n10 =>
      refine flag_ndW (fi := .xor_rr32_self .r10) rfl hF (fun s he hn => code b10 s he hn) hW.n10
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨XN.nr, ?_, rfl, ?_, ?_, ?_⟩⟩
      · show lab x21L + 41 = lab x21L + Int64.ofNat 38 + Int64.ofNat 3
        rw [Int64.add_assoc]; rfl
      · obtain ⟨⟨hA, h12, hbx, hsi, h8, hdi⟩, -⟩ := hJ
        exact ⟨hA, by simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsi, h8, hdi, and_self]⟩
      · simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, hJ.2]
      · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
    case nr =>
      exact seg_ndW (by simp [nrB]) nrB_ok hF hR hlo hhi (fun s he hn => code br s he hn) hW.nr
        fun σ c hJ => ⟨c, .refl c, .inr ⟨(), nrB_edge hJ⟩⟩
  exact hA.mono_post fun _ _ ⟨_, h⟩ => h

end SegP

/-- info: 'Spike.Lib.X64.WakePh.WcClone.wake_wc_clone_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_wc_clone_segW

end Spike.Lib.X64.WakePh.WcClone
