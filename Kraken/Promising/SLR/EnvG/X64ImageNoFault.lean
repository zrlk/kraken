/-
**No fault for a thread running a code+data image**.

A `.kl` program's thread runs the runner's executable: its code, then the
data trailer, one `.label sym` cell per symbol behind a padding `.byteArray`
(`Kraken.Litmus.X64.prepareProgram`; `Kraken/EnvCfgAbs.lean`). A
`.byteArray` cell's tree is `unimplemented`, a fault, so `DirsNoFault` of the
whole image fails and `noFault_QX64` does not apply. But a thread never runs a
data cell: its `Safely` judgment either holds its postcondition (at its end,
no tree) or takes an instruction step, and no instruction step runs a
`.byteArray` cell (`not_instrStepEnv_of_byteArray`). So fault-freedom of
the image's non-data cells suffices (`DirsNoFaultCode`).

- `DirsNoFaultCode`, `dirsNoFaultCode_layout`, the tactic
  `dirs_no_fault_code p` (`dirs_no_fault` with the data cells excluded);
- `noFault_of_exec_step`: a state with an instruction step has a fault-free
  tree, from `DirsNoFaultCode`;
- `noFault_QX64_code`: the `HS` argument of the `noFaultRule…_struct`
  lemmas at `QX64` (no `DirsNoFault`).
-/
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.Promising.SLR.EnvG.X64RmwGhostLink

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **Every non-data cell of the executable has a fault-free tree.** -/
def DirsNoFaultCode (e : _root_.Executable) : Prop :=
  ∀ d z, (d, z) ∈ e.2 → (∀ b, d ≠ .byteArray b) → DirNoFault e d z

/-- The directives of a laid-out program are the program's
(`dirsNoFault_layout` without the data cells). -/
theorem dirsNoFaultCode_layout [layout : _root_.Layout] {p : Program}
    (h : ∀ d ∈ p, (∀ b, d ≠ .byteArray b) → ∀ (e : _root_.Executable) z, DirNoFault e d z) :
    DirsNoFaultCode (layout p) := by
  intro d z hm hb
  obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact h _ (List.getElem_mem hi) hb _ _

set_option hygiene false in
/-- `dirs_no_fault_code p q₁ … qₙ` proves `DirsNoFaultCode (layout p)`: the
`dirs_no_fault` script on every directive of `p` (unfolding `p` and the
definitions `qᵢ` it is built from) but the `.byteArray` data cells, which the
premise excludes. -/
macro "dirs_no_fault_code " p:ident ps:ident* : tactic => `(tactic| (
  refine Kraken.Promising.X64.EnvG.dirsNoFaultCode_layout (p := $p) ?_
  intro d hd hb e z s pc
  simp only [$p:ident] at hd
  try simp only [$[$ps:ident],*] at hd
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals try exact absurd rfl (hb _)
  all_goals try simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.rmwK, _root_.RegOrMem.interp, _root_.Operand.interp, _root_.MachineData.set,
    _root_.RegOrMem.rmw, Kraken.Promising.EvTree.access_empty, _root_.RelRegOrMem.interp]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault, Kraken.Promising.EvTree.access_empty]))
  all_goals try (refine Kraken.Promising.prop_ite (P := fun x =>
                Kraken.Promising.EvTree.NoFault (Kraken.Promising.X64.toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.X64.toEv, Kraken.Promising.EvTree.NoFault])))

/-- **A state with an instruction step has a fault-free tree**, for an
executable whose non-data cells are fault-free: the cell the step runs is
the cell the thread's tree comes from, and it is not a data cell. -/
theorem noFault_of_exec_step {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    (he : st.exe = e) (hds : st.decls = {}) (hnf : DirsNoFaultCode e) {E : SharedEnv} {g : E.State}
    {R : MachineState × E.State → Prop} (hR : e.instrStepEnv E (st.st, g) R) :
    ∀ tree, isa.exec st = some tree → tree.NoFault := by
  intro tree htree
  obtain ⟨d', z', rest', hcode', hstep⟩ := hR
  obtain ⟨d, z, rest, hcode⟩ := codeAt_of_exec htree
  have hdir := directive_of_codeAt hcode
  have hmem := mem_of_codeAt hcode
  rw [he] at hcode hmem
  have hdd : d = d' := by
    have := hcode.symm.trans hcode'
    simp only [List.cons.injEq, Prod.mk.injEq] at this
    exact this.1.1
  subst hdd
  have hb : ∀ b, d ≠ .byteArray b := by
    rintro b rfl
    rcases hstep with h | h <;> simp [Directive.interp, Effects.AllEnv] at h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat hdir ⊢
  subst he hds
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    refine (EvTree.noFault_map _ _).mpr ?_
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    exact hnf d z hmem hb s pc

/-- **Every tree from a `QX64`-state is fault-free**, for an executable
whose non-data cells are fault-free (`noFault_QX64` without the data
cells). -/
theorem noFault_QX64_code {A : Arch} {tid : Nat} {pl : Plan} {S : SharedEnv.Layout}
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {endPc : Int64}
    {post : MachineState × EStateX → Prop} (hnf : DirsNoFaultCode e) (hpost : ∀ y, post y → y.1.2 = endPc) :
    ∀ st σ tree, QX64 A tid pl S e endPc post st σ → isa.exec st = some tree → tree.NoFault := by
  intro st σ tree h hex
  obtain ⟨he, hds, hend, -, hsafe⟩ := h
  rcases hsafe.unfold with hp | ⟨R, hR, -⟩
  · have := exec_eq_none_of_end (st := st) (by rw [hend]; exact hpost _ hp)
    rw [this] at hex; cases hex
  · exact noFault_of_exec_step he hds hnf hR tree hex

end Kraken.Promising.X64.EnvG
