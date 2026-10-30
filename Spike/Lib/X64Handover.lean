/-
**The clone handover on x64**: the threads after a
`clone` into the extra slot (`Spike.Lib.Handover.afterClone`) under `abi`.

- `child_st`: the child is the parent's state with `rax = 0`, `rcx` and
  `r11` as the `syscall` leaves them (`retRegs64`), `rsp = stack`,
  `fsBase = tls`, every other register the parent's (so `r12`, `rbx`,
  `r13`–`r15`, `r9` carry the spawn arguments), the pc past the `syscall`,
  and private memory empty but for the handed stack range's bytes.
- `parent_st`: the parent is its state with `retRegs64 ctid`, the pc past
  the `syscall`, private memory without the handed range.
-/
import Spike.Lib.Handover
import Scc.Sem.TargetX64

namespace Spike.Lib.X64Handover

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Spike.Lib.Handover

variable {x : Kernel.KState} {tid : Nat} {t : Thread isa} {stack tls : Nat} {r : BitVec 64}

/-- **The child after the handover.** -/
theorem child_st : ∃ m, (childAfter abi x tid t stack tls).st =
      { t.st with st := ({ t.st.st.1 with
          regs := { retRegs64 t.st 0 with rsp := UInt64.ofNat stack, fsBase := UInt64.ofNat tls },
          dmem := m }, nextPc t.st) } ∧
      (m = ∅ ∨ ∃ rg, handed x tid stack = some (tid, rg) ∧ m = Kernel.copyRange t.st.st.1.dmem ∅ rg) := by
  rcases childAfter_st (K := abi) (d := (({ threads := #[], mem := { init := [], msgs := #[] } } : Config isa), x)) (tid := tid) (t := t) (stack := stack)
    (tls := tls) with h | ⟨rg, hf, h⟩
  · exact ⟨∅, h, .inl rfl⟩
  · exact ⟨_, h, .inr ⟨rg, hf, rfl⟩⟩

/-- **The parent after the handover.** -/
theorem parent_st : ∃ m, (Kernel.retThread abi (parentPre abi x tid t stack) r).st =
      { t.st with st := ({ t.st.st.1 with
          regs := retRegs64 t.st r, dmem := m }, nextPc t.st) } ∧
      (m = t.st.st.1.dmem ∨ ∃ rg, handed x tid stack = some (tid, rg) ∧
        m = Kernel.eraseRange t.st.st.1.dmem rg) := by
  rw [Kernel.retThread_st]
  rcases parentPre_st (K := abi) (d := (({ threads := #[], mem := { init := [], msgs := #[] } } : Config isa), x)) (tid := tid) (t := t) (stack := stack)
    with h | ⟨rg, hf, h⟩
  · exact ⟨_, by rw [h]; rfl, .inl rfl⟩
  · exact ⟨_, by rw [h]; rfl, .inr ⟨rg, hf, rfl⟩⟩

/-- The child's stack pointer is `stack`. -/
theorem child_sp (h : stack < 2 ^ 64) : abi.sp (childAfter abi x tid t stack tls).st = stack := by
  obtain ⟨m, hc, -⟩ := child_st (x := x) (tid := tid) (t := t) (stack := stack) (tls := tls)
  rw [hc]
  show (UInt64.ofNat stack).toNat = stack
  simp [Nat.mod_eq_of_lt h]

/-- **The child's current stack range is the handed range** (nonempty, its
top below `2 ^ 64`). -/
theorem child_stackRange {d : Config isa × Kernel.KState} {r : BitVec 64} {rg : Range}
    (hn : d.1.threads.size = d.2.slots.size) (hf : handed d.2 tid stack = some (tid, rg)) (hs : 0 < rg.size)
    (h : stack < 2 ^ 64) :
    Kernel.stackRangeOf abi (afterClone abi d tid t stack tls r) d.1.threads.size = some rg := by
  refine afterClone_stackRange hn hf ?_
  rw [child_sp h, ← (handed_end hf).2.1]
  exact onStack_top hs

end Spike.Lib.X64Handover
