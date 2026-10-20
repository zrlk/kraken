/-
**`treiber_aba_tagged.kl`, part 9: the image's
per-cell facts.**

- `abaImageV_noPieces`: every cell is piece-free (`CodeNoPieces`: the vector
  operations are `movdqa` at 16 bytes and `lock cmpxchg16b`);
- `abaImageV_phase1FX`: every cell is phase-1 (at most one access,
  deterministic), checked on the image's distinct directives `abaDirsV`;
- `abaV_stuck`: no step at the exit label `done` (the data trailer's first
  padding cell).
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARun1
import Kraken.Promising.SLR.EnvG.X64VecDeclsLinkAdj

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.VecABA

/-! ## Piece-freedom -/

theorem abaImageV_noPiecesL : ∀ d ∈ abaImageV, d.NoPieces := by
  intro d hd
  simp only [abaImageV, abaCodeV, abaDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [Directive.NoPieces, AvxOperation.NoPieces]

theorem codeNoPieces_layout [layout : _root_.Layout] {p : Program} (h : ∀ d ∈ p, d.NoPieces) :
    CodeNoPieces (layout p) := by
  intro d z hm
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi)

theorem abaImageV_noPieces [layout : _root_.Layout] : CodeNoPieces (layout abaImageV) :=
  codeNoPieces_layout abaImageV_noPiecesL

/-! ## Phase 1 -/

/-- The image's distinct directives but `lock cmpxchg16b (head)`. -/
def abaDirsA : Program := parse("
p0:
p1:
p1pop1:
p1pop2:
p1push:
p1push1:
done:
  movdqa (head),%xmm0
  movdqa %xmm0,-16(%rsp)
  movq -16(%rsp),%rax
  movq -8(%rsp),%rdx
  testq %rax,%rax
  je p0
  movq (%rax),%rbx
  leaq 1(%rdx),%rcx
  jne p0
  movq %rax,%r12
  movq %rbx,%r13
  jmp done
  movq $0,%r12
  je p1pop2
  jne p1pop1
  movq $0,%r13
  je p1push
  jne p1pop2
  movq %rax,%r13
  testq %r12,%r12
  je done
  movq %rax,(%r12)
  movq %r12,%rbx
  jne p1push1
") ++ abaDataV

/-- `lock cmpxchg16b (head)`. -/
def abaCasL : Program := parse("
  lock cmpxchg16b (head)
")

/-- The image's distinct directives. -/
def abaDirsV : Program := abaDirsA ++ abaCasL

theorem abaImageV_sub_dirs : ∀ d ∈ abaImageV, d ∈ abaDirsV := by
  have h : abaImageV.all (fun d => abaDirsV.any (fun d' => decide (d = d'))) = true := by decide
  intro d hd
  obtain ⟨d', hd', he⟩ := List.any_eq_true.mp (List.all_eq_true.mp h d hd)
  rw [of_decide_eq_true he]; exact hd'

/-- `lock cmpxchg16b` at 16-aligned addresses is one `rmw16` with `done`
continuations, or the fault (stated over the continuation, so that `simp`
does not unfold the compare-and-swap's value computations). -/
theorem cas16_shape (s : MachineData) (addr : BitVec 64) (op : BitVec 128 → Option (BitVec 128))
    (k : BitVec 128 → MachineData → Effects) (f : BitVec 128 → MachineData → MachineState)
    (hk : ∀ old s', k old s' = .done (f old s')) :
    Phase1ShapeF (toEv {} (if isAligned 16 addr then s.rmw16K .acqRel addr op k else .gp_unaligned addr 16)) := by
  split
  · simp [MachineData.rmw16K, Kraken.Promising.X64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2, hk]
    repeat' (first | split | simp [Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2, AccessFree,
      Kraken.Promising.EvTree.access_empty])
  · simp [Kraken.Promising.X64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2]

theorem abaCasL_phase1FX : ∀ d ∈ abaCasL, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [abaCasL, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  simp only [DirPhase1FX, _root_.Directive.interp, _root_.Instr.interp, _root_.AvxOperation.interp, ↓reduceIte,
    Kraken.Promising.X64.toEv]
  exact cas16_shape _ _ _ _ _ (fun _ _ => rfl)

set_option maxHeartbeats 4000000 in
theorem abaDirsA_phase1FX : ∀ d ∈ abaDirsA, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [abaDirsA, abaDataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    _root_.AvxOperation.interp, _root_.AvxRegOrMem.interp, _root_.MachineData.setAvxLegacy,
    _root_.MachineData.loadAvx, _root_.MachineData.storeAvx,
    Kraken.Promising.X64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))
  all_goals try simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]
  all_goals (refine prop_ite (P := fun x => DetAccess (toEv {} x) ∧
      SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True (toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2])

theorem abaDirsV_phase1FX : ∀ d ∈ abaDirsV, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · exact abaDirsA_phase1FX d h
  · exact abaCasL_phase1FX d h

/-- **The whole image is phase-1.** -/
theorem abaImageV_phase1FX [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)] :
    Phase1TreeFX (layout abaImageV) :=
  phase1TreeFX_of_dirs (dirsPhase1FX_layout fun d hd => abaDirsV_phase1FX d (abaImageV_sub_dirs d hd))

/-! ## The exit -/

theorem abaImageV_56 : abaImageV[56]? = some (.byteArray (.mk #[])) := by decide

set_option maxRecDepth 20000 in
/-- `done`'s address is the data trailer's first padding cell's. -/
theorem labV_done [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)] :
    labV "done" = (layout abaImageV).addrOf 56 := by
  have hd : labV "done" = (layout abaImageV).addrOf 55 :=
    Program.label_addrOf_drop abaImageV_wf.nodup (by decide) (by decide)
  have h55 : (layout abaImageV).2[55]? = some (Directive.label "done", Kraken.Layout.size Directive 55) := by
    simp [Layout.apply_snd, Layout.frag, abaImageV, abaCodeV, abaDataV]
  rw [Executable.addrOf_succ _ h55, Executable.ValidLayout.label_size 55 "done" _ h55, hd]
  simp

/-- **No step of the image at the exit label `done`.** -/
theorem abaV_stuck [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)] (env : SharedEnv) :
    ∀ x R, x.1.2 = labV "done" → ¬ (layout abaImageV).instrStepEnv env x R := by
  rw [labV_done]
  exact not_instrStepEnv_of_byteArray (i := 56) (b := .mk #[]) env abaImageV_56

end Kraken.Promising.X64.EnvG.VecABA
