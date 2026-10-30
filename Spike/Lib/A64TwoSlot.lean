/-
**The two-slot lift on the canonical AArch64 target**: the kernel-2 load is
the kernel-1 load with one more thread, `dormantAt`, halted with no promise
and no private memory, in one more slot, dormant (`Spike.Lib.TwoSlot.up`).
So by `Spike.Lib.TwoSlot.up_step`/`step_up`/`progress_up`, the
configurations reachable on `kernel 2` without a `clone` into slot 1 are
those of `kernel 1`, lifted.
-/
import Spike.Lib.TwoSlot
import Scc.Sem.TargetA64

namespace Spike.Lib.A64TwoSlot

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Spike.Lib.TwoSlot

/-- The machines of `kernel 1` and `kernel 2` are the same: the slot count
enters only at load. -/
theorem machine_two : machine (kernel 2) = machine (kernel 1) := rfl

/-- And so are the code marks. -/
theorem marks_two (E : Entry) (asm : String) (Λ : Scc.Sem.Layout) :
    (target (kernel 2) E).marks asm Λ = (target (kernel 1) E).marks asm Λ := rfl

theorem kinit_two (E : Entry) (Λ : Scc.Sem.Layout) :
    Kernel.KState.init 2 E Λ = upX (Kernel.KState.init 1 E Λ) := rfl

/-- The dormant thread of a two-slot load. -/
abbrev dormant (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program) (syms : List (String × Nat)) :
    Thread isaLSE2 :=
  Thread.init (I := isaLSE2) (dormantAt E Λ.code.lo prog syms)

theorem dormant_inert (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program) (syms : List (String × Nat)) :
    Inert (dormant E Λ prog syms) := by
  refine ⟨?_, rfl⟩
  simp only [Thread.halted, isaLSE2, execLSE2]
  have h : ((dormant E Λ prog syms).st.st.snd == (dormant E Λ prog syms).st.endPc) = true :=
    beq_self_eq_true _
  simp only [h, Bool.true_or, ite_true]
  rfl

/-- The dormant thread has no private memory. -/
theorem dormant_privLoad (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program) (syms : List (String × Nat))
    (a : BitVec 64) : privLoad (dormant E Λ prog syms).st a = none := by
  have hd : (dormant E Λ prog syms).st.st.1.dmem = ∅ := rfl
  have he : (∅ : _root_.Mem 64).loadBytes a 8 = none := by simp [Mem.loadBytes]; rfl
  simp only [privLoad, Mem.loadInt, hd, he, Option.map_none]

theorem loadProg_two (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program) (syms : List (String × Nat))
    (mem : List (Loc × Val)) :
    loadProg (kernel 2) E Λ prog syms mem = up (loadProg (kernel 1) E Λ prog syms mem) (dormant E Λ prog syms) := by
  simp only [loadProg, up, upC, Config.init, kernel, Kernel.hooks, kinit_two]
  simp
  rfl

theorem loadProg_one_size (E : Entry) (Λ : Scc.Sem.Layout) (prog : Program) (syms : List (String × Nat))
    (mem : List (Loc × Val)) :
    (loadProg (kernel 1) E Λ prog syms mem).1.threads.size = (loadProg (kernel 1) E Λ prog syms mem).2.slots.size := by
  simp [loadProg, Config.init, kernel, Kernel.hooks, Kernel.KState.init]
  rfl

/-- **The kernel-2 target loads the kernel-1 configuration, lifted** by an
inert thread with no private memory. -/
theorem load_two {E : Entry} {asm : String} {Λ : Scc.Sem.Layout} {c : (machine (kernel 2)).Cfg}
    (h : (target (kernel 2) E).load asm Λ = some c) :
    ∃ d u, (target (kernel 1) E).load asm Λ = some d ∧ c = up d u ∧ Inert u ∧
      (∀ a, privLoad u.st a = none) ∧ d.1.threads.size = d.2.slots.size := by
  simp only [target] at h ⊢
  cases hp : (textProgram asm).toOption with
  | none => simp [hp] at h
  | some prog =>
  cases hs : dataSections asm with
  | none => simp [hp, hs] at h
  | some secs =>
  simp only [hp, hs, Option.bind_eq_bind, Option.bind_some] at h ⊢
  split at h
  · rename_i hc
    cases h
    exact ⟨_, _, by simp only [hc, ite_true], loadProg_two .., dormant_inert .., dormant_privLoad _ _ _ _, loadProg_one_size ..⟩
  · cases h

/-- **Conversely, the kernel-1 load lifts to the kernel-2 load.** -/
theorem load_one {E : Entry} {asm : String} {Λ : Scc.Sem.Layout} {d : (machine (kernel 1)).Cfg}
    (h : (target (kernel 1) E).load asm Λ = some d) :
    ∃ u, (target (kernel 2) E).load asm Λ = some (up d u) ∧ Inert u ∧
      (∀ a, privLoad u.st a = none) ∧ d.1.threads.size = d.2.slots.size := by
  simp only [target] at h ⊢
  cases hp : (textProgram asm).toOption with
  | none => simp [hp] at h
  | some prog =>
  cases hs : dataSections asm with
  | none => simp [hp, hs] at h
  | some secs =>
  simp only [hp, hs, Option.bind_eq_bind, Option.bind_some] at h ⊢
  split at h
  · rename_i hc
    cases h
    exact ⟨dormant E Λ prog (loadSyms Λ secs.rodata), by simp only [hc, ite_true, loadProg_two]; rfl, dormant_inert .., dormant_privLoad _ _ _ _,
      loadProg_one_size ..⟩
  · cases h

end Spike.Lib.A64TwoSlot
