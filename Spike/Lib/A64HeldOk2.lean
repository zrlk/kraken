/-
**The ranges held by a thread that takes two stack ranges** (AArch64,
wake's main: `r0` at its own `scc_rt_thread_init`, `r1` at the second
thread's, before the clone hands `r1` over). Beside `A64Consumer.HeldOk`
(one range, a phase `Tk`), with no phase: the held list is pinned by which
ranges the private memory maps.

- `HeldOk2 Λ r0 r1 s hl`: none held and neither range mapped; `r0` held
  and owned, `r1` unmapped; both held (`r1` last) and owned.
- `HeldOk2.own`: every held range is thread 0's and owned (`HeldPathS.own`).
- `HeldOk2.of_dom`: equal private-memory domains keep it.
- `HeldOk2.instr`, `HeldOk2.sys`: off the transfer sites every instruction
  leaf and every system-call resumption keeps it (`owned_mono`,
  `owned_sys`, from `Kernel.DomHyps`).
- `HeldOk2.take0`, `HeldOk2.take1`: the first and second takes, given the
  ownership facts after them.
-/
import Spike.Lib.A64OwnedMono

namespace Spike.Lib.A64Consumer

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64

/-- **The ranges held** by a thread taking `r0` then `r1`, pinned by
ownership. -/
def HeldOk2 (Λ : Scc.Sem.Layout) (r0 r1 : Range) (s : State) (hl : List (Nat × Range)) : Prop :=
  (hl = [] ∧ Unowned r0 s ∧ Unowned r1 s) ∨
    (hl = [(0, r0)] ∧ Owned Λ r0 s ∧ Unowned r1 s) ∨
    (hl = [(0, r1), (0, r0)] ∧ Owned Λ r0 s ∧ Owned Λ r1 s)

namespace HeldOk2

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {s s' : State} {hl : List (Nat × Range)}

/-- **Every held range is thread 0's and owned.** -/
theorem own (h : HeldOk2 Λ r0 r1 s hl) : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 s := by
  rcases h with ⟨rfl, -, -⟩ | ⟨rfl, h0, -⟩ | ⟨rfl, h0, h1⟩
  · intro x hx; cases hx
  · intro x hx
    rw [List.mem_singleton] at hx; subst hx; exact ⟨rfl, h0⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨rfl, h1⟩
    · rw [List.mem_singleton] at hx; subst hx; exact ⟨rfl, h0⟩

/-- **Equal private-memory domains keep it.** -/
theorem of_dom (h : HeldOk2 Λ r0 r1 s hl) (hd : ∀ a, a ∈ s'.st.1.dmem ↔ a ∈ s.st.1.dmem) :
    HeldOk2 Λ r0 r1 s' hl := by
  simp only [HeldOk2, owned_of_dom (Λ := Λ) hd, unowned_of_dom hd]
  exact h

/-- **An instruction off the transfer sites keeps it** at every leaf. -/
theorem instr (h : HeldOk2 Λ r0 r1 s hl) (hs : WideSt s) {tree : EvTree State}
    (he : isaLSE2.exec s = some tree) : tree.AllInv (fun _ _ => True) (fun s' => HeldOk2 Λ r0 r1 s' hl) :=
  allInv_of_leaf tree fun _ hlf => h.of_dom (Scc.Cert.DomA64.domHyps.exec _ _ _ hs he hlf).2

/-- **A system call's resumptions keep it.** -/
theorem sys (h : HeldOk2 Λ r0 r1 s hl) {call : Kernel.Call} (hc : s' ∈ Kernel.certSuccs abi s call) :
    HeldOk2 Λ r0 r1 s' hl := by
  have ⟨ho, hu⟩ := owned_sys (Λ := Λ) (rS := r0) hc
  have ⟨ho1, hu1⟩ := owned_sys (Λ := Λ) (rS := r1) hc
  simp only [HeldOk2, ho, hu, ho1, hu1]
  exact h

/-- **The first take**: `r0` owned and `r1` unmapped after it. -/
theorem take0 (h0 : Owned Λ r0 s') (h1 : Unowned r1 s') : HeldOk2 Λ r0 r1 s' ((0, r0) :: []) :=
  .inr (.inl ⟨rfl, h0, h1⟩)

/-- **The second take**: both owned after it. -/
theorem take1 (h0 : Owned Λ r0 s') (h1 : Owned Λ r1 s') : HeldOk2 Λ r0 r1 s' ((0, r1) :: [(0, r0)]) :=
  .inr (.inr ⟨rfl, h0, h1⟩)

end HeldOk2

/-- info: 'Spike.Lib.A64Consumer.HeldOk2.instr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.HeldOk2.instr

/-- info: 'Spike.Lib.A64Consumer.HeldOk2.sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Consumer.HeldOk2.sys

end Spike.Lib.A64Consumer
