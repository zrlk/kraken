/-
**The stack-depth counter's invariant, one thread** (`Scc/DESIGN.md` §7.3,
item 5, *Stack*): the twin of `Scc/Sem/HeapCtr.lean` for the per-thread
depth word.

The runtime keeps a thread's depth in its control block (`Tcb.depth`,
read and written only by the thread). The caller brackets every source
non-tail call of a user block (not tail calls, runtime calls or extern
calls), `F` being the program's frames budget (an immediate):

```
d  ← load [tp + depth]
d1 ← d + 1
d1 > F → abort .stack          -- `scc_rt_abort(AbortKind.stack)`
store [tp + depth] ← d1
call f                          -- the source push (`callFrame`, `enter`)
store [tp + depth] ← d          -- after the callee's `ret` (the source pop)
```

The source push is simulated at the `call`, the source pop at the callee's
`ret`; between the store of `d1` and the `call`, and between the `ret` and
the restore, the counter is one ahead of the source depth.

**The invariant** (`StackCtr1 F ctr dep ph`, one thread, the counter's
value `ctr` the thread's last write to it or `0`): `dep` is the number of
user-block frames on the source stack (outside an extern call's window,
the source stack's length), within `F`; the phase `ph` (`DPhase`) says
where in the bracket the thread is and what the saved `d` is:

- `idle`: `ctr = dep`;
- `loaded d` (after the load): `d = dep = ctr`;
- `pushed d` (after the store of `d + 1`): `d = dep`, `ctr = dep + 1 ≤ F`;
- `popped d` (after the callee's `ret`, in the caller): `d = dep`,
  `ctr = dep + 1`.

Lemmas:

- `init`: the loaded thread (counter `0` in `.bss`, empty source stack).
- `load`: the load returns `ctr`; `branch`: from `loaded d`, the abort
  branch `d + 1 > F` is taken exactly when `dep = F`, i.e. when the source
  push crosses the frames part (`crossing`, the premises of
  `AbortJustified.stack_of_push`; `abort_justified` states it).
- `store_push`, `call`, `ret`, `restore`: the bracket's other steps; a
  callee that returns has left its depth as it found it (its own brackets
  are balanced, tail calls do not touch the word), so `ret` starts from
  `idle` one deeper.
- `within`: in every phase `dep ≤ F` (the frames part holds; no stack
  abort is inherited); `bound`: the counter is at most `F`.

Not here: that a runtime load of the depth word returns `ctr` (the
memory side, `Inv1`), and the per-frame ghost that keeps a caller's saved
`d` across the call (the consumer's frame list).
-/
import Scc.Sem.Budget

namespace Scc.Sem

/-- **Where a thread is in a call bracket**, with the saved depth `d`. -/
inductive DPhase where
  /-- Outside every bracket (or inside a callee). -/
  | idle
  /-- After the load of the counter, `d` its value. -/
  | loaded (d : Nat)
  /-- After the store of `d + 1`, before the `call`. -/
  | pushed (d : Nat)
  /-- After the callee's `ret`, before the restore of `d`. -/
  | popped (d : Nat)
  deriving DecidableEq, Repr

/-- **The depth counter's invariant, one thread**: the counter `ctr`, the
source depth `dep` (user-block frames), the frames budget `F`, the phase. -/
def StackCtr1 (F ctr dep : Nat) : DPhase → Prop
  | .idle => ctr = dep ∧ dep ≤ F
  | .loaded d => d = dep ∧ ctr = dep ∧ dep ≤ F
  | .pushed d => d = dep ∧ ctr = dep + 1 ∧ dep + 1 ≤ F
  | .popped d => d = dep ∧ ctr = dep + 1 ∧ dep + 1 ≤ F

namespace StackCtr1

variable {F ctr dep : Nat}

/-- **The loaded thread**: counter `0`, empty source stack, idle. -/
theorem init (F : Nat) : StackCtr1 F 0 0 .idle := ⟨rfl, Nat.zero_le _⟩

/-- **In every phase the source depth is within the budget.** -/
theorem within {ph : DPhase} (h : StackCtr1 F ctr dep ph) : dep ≤ F := by
  cases ph with
  | idle => exact h.2
  | loaded => exact h.2.2
  | pushed => have := h.2.2; omega
  | popped => have := h.2.2; omega

/-- **The counter is at most `F`** (it does not wrap for `F < 2^64`). -/
theorem bound {ph : DPhase} (h : StackCtr1 F ctr dep ph) : ctr ≤ F := by
  cases ph with
  | idle => have := h.1; have := h.2; omega
  | loaded => have := h.2.1; have := h.2.2; omega
  | pushed => have := h.2.1; have := h.2.2; omega
  | popped => have := h.2.1; have := h.2.2; omega

/-- **The load**: from `idle`, the value read is the counter. -/
theorem load (h : StackCtr1 F ctr dep .idle) : StackCtr1 F ctr dep (.loaded ctr) :=
  ⟨h.1, h.1, h.2⟩

/-- **The branch is the source budget**: from `loaded d`, `d + 1 > F`
(the abort branch) exactly when the source depth is `F`. -/
theorem branch {d : Nat} (h : StackCtr1 F ctr dep (.loaded d)) : F < d + 1 ↔ dep = F := by
  obtain ⟨rfl, -, hle⟩ := h; omega

/-- **At the abort branch the source push crosses the budget**: the depth
is `F`, and the push takes it to `F + 1`. -/
theorem crossing {d : Nat} (h : StackCtr1 F ctr dep (.loaded d)) (hb : F < d + 1) : dep = F :=
  (branch h).mp hb

/-- **The store of `d + 1`**, on the branch that does not abort. -/
theorem store_push {d : Nat} (h : StackCtr1 F ctr dep (.loaded d)) (hb : d + 1 ≤ F) :
    StackCtr1 F (d + 1) dep (.pushed d) := by
  obtain ⟨rfl, -, -⟩ := h; exact ⟨rfl, rfl, hb⟩

/-- **The `call`**: the source push; the callee starts idle one deeper. -/
theorem call {d : Nat} (h : StackCtr1 F ctr dep (.pushed d)) : StackCtr1 F ctr (dep + 1) .idle :=
  ⟨h.2.1, h.2.2⟩

/-- **The callee's `ret`**: the source pop; the caller, whose saved depth is
`d` (the per-frame ghost), is one ahead of its depth. -/
theorem ret {d : Nat} (h : StackCtr1 F ctr (d + 1) .idle) : StackCtr1 F ctr d (.popped d) :=
  ⟨rfl, h.1, h.2⟩

/-- **The restore** of the saved `d`: idle again. -/
theorem restore {d : Nat} (h : StackCtr1 F ctr dep (.popped d)) : StackCtr1 F d dep .idle := by
  obtain ⟨rfl, -, hle⟩ := h; exact ⟨rfl, by omega⟩

/-- **The stack abort at the branch is justified**: the source step of the
thread's call from a configuration where its stack has `dep` frames pushes
one, and `dep = B.frames` (`AbortJustified.stack_of_push`). -/
theorem abort_justified {B : Budget} {S : SrcSem} {tr : List Ev} {s s' : S.Cfg} {i : Nat} {es : List Ev}
    {d : Nat} (h : StackCtr1 B.frames ctr dep (.loaded d)) (hb : B.frames < d + 1) (hstep : S.step i s es s')
    {th th' : TermRun.TTh} (hth : (S.core s).ths[i]? = some th) (hth' : (S.core s').ths[i]? = some th')
    (hdep : th.stack.length = dep) (hlen : th'.stack.length = th.stack.length + 1) :
    AbortJustified B S tr s i .stack :=
  AbortJustified.stack_of_push hstep hth hth' hlen (hdep.trans (h.crossing hb))

/-- **The frames part holds** where the source stack's length is the
depth (outside an extern call's window). -/
theorem part {B : Budget} {s : TermRun.Cfg} {i : Nat} {ph : DPhase} (h : StackCtr1 B.frames ctr dep ph)
    (hdep : ∀ th, s.ths[i]? = some th → th.stack.length = dep) : B.Part .stack i s :=
  fun th hth => by rw [hdep th hth]; exact h.within

end StackCtr1

/-! ## Tests -/

/-- `F = 2`: two nested calls fit; the counter after both is `2`. -/
example : StackCtr1 2 2 2 .idle :=
  (((StackCtr1.init 2).load.store_push (by decide)).call.load.store_push (by decide)).call

/-- A third call at `F = 2` takes the abort branch, and the source depth is
then `F` (the crossing). -/
example (h : StackCtr1 2 2 2 (.loaded 2)) : (2 : Nat) < 2 + 1 ∧ 2 = 2 := ⟨by decide, h.crossing (by decide)⟩

/-- A call and its return leave the counter as it was. -/
example : StackCtr1 3 0 0 .idle :=
  ((((StackCtr1.init 3).load.store_push (by decide)).call).ret).restore

/-- **Rejected: a push past the budget.** `store_push` needs `d + 1 ≤ F`:
no phase has the counter pushed past `F`. -/
example : ¬ StackCtr1 2 3 2 (.pushed 2) := fun h => by have := h.2.2; omega

/-- **Rejected: a restore of a stale depth.** The saved `d` is the caller's
depth: `popped` with `d ≠ dep` is no phase. -/
example : ¬ StackCtr1 3 2 1 (.popped 0) := fun h => by have := h.1; omega

end Scc.Sem
