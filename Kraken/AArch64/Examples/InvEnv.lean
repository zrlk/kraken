import Kraken.AArch64.EnvCfg
import Kraken.AArch64.Parser
import Kraken.Promising.SeqLinkAArch64Prog
import Kraken.Promising.EnvLinkSafeAArch64
import Kraken.Promising.InvLinkAArch64

/-!
# The invariant environment, AArch64

Threads proved by one `vcgen` call each in `SharedEnv.inv S G`, carried to
every reachable configuration of the full Promising machine (any number of
threads, each running any of the programs, promises included) by
`Kraken.Promising.AArch64.inv_reachable`:

* (a) `ringNext`: one compare-and-swap attempt advancing a ring index modulo
  `8` (`ldr`, `add`, `cmp`, `csel`, `casal`). Invariant `ringG`: the index is
  below `8`. The `casal` writes only when the slot still holds the value read,
  which `ringG` bounds, so its new value is bounded too.
* (b) `toggle`: a racy plain read-modify-write flipping a flag (`ldr`, `eor`,
  `str`). Invariant `flagG`: the flag is `0` or `1`. The load may read any
  value the invariant allows (not the last write), and the store keeps it.
* (c) negative control: `setTwo` stores `2` to the flag; its `vcgen` goal is
  false (`setTwo_not_correct`): no state satisfying the precondition has an
  environment step in `inv S flagG`.

* a real fragment: `swpWorker`, the whole `worker` of
  `Kraken/Examples/LockFree/AArch64/spinlock_swp2.kl` (a loop, partial
  correctness by `cfgEnv_partial` in the counted environment): the lock word
  stays in `{0, 1}` and a finished worker took the lock (`swp_reachable`).

`ring_reachable`, `flag_reachable` and `swp_reachable` are the full-machine
conclusions: every message ever written to the slot (and its initial value)
satisfies the invariant, and every thread still satisfies its specification.
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.AArch64
open MachineWP

namespace Kraken.AArch64.Examples.InvEnv

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.AArch64.Parser

/-! ## (a) A ring index advanced by `casal` -/

/-- The ring index at `a` (8 bytes) is below `8`. -/
def ringG (a : BitVec 64) (l : Loc) (v : Val) : Prop := l = ⟨a, 8⟩ → v.toNat < 8

/-- One attempt to advance the ring index at `[x0]` modulo `8`. -/
def ringNext : Program := parseAArch64("
    ldr x1, [x0]
    add x2, x1, #1
    cmp x2, #8
    csel x2, xzr, x2, eq
    casal x1, x2, [x0]
")

section ringNext

variable [layout : _root_.Layout]

local instance ringNext.env : CodeEnv := ⟨layout ringNext⟩

theorem ringNext_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.inv [(a, 8)] (ringG a))
      (fun s _ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none)
      ringNext
      (fun s _ => s.regs.X1.toNat < 8)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold ringNext
  vcgen
  all_goals simp_all [SharedEnv.inv, ringG, rmwOpBits]
  case vc5 =>
    intro old _ _
    obtain ⟨v, hv, rfl⟩ := ‹∃ v : Val, _›
    have : (BitVec.setWidth 64 v).toNat < 8 := by simp [BitVec.toNat_setWidth]; omega
    split
    · simp
    · rw [Nat.mod_eq_of_lt (by omega)]
      bv_omega
  case vc6 => omega

variable [Executable.ValidLayout (layout ringNext)]

/-- A `ringNext` thread: code, end address and the `Safely` invariant of
`ringNext_correctEnv`, postcondition `x1 < 8` at the end. -/
abbrev ringSpec (a : BitVec 64) : ThreadSpec [(a, 8)] (ringG a) :=
  ThreadSpec.ofTripleEnv ringNext fun s _ => s.regs.X1.toNat < 8

/-- A thread about to run `ringNext` on the index at `a` (`x0 = a`, the index
outside its private memory). -/
def RingStart (a : BitVec 64) (st : State) : Prop :=
  st.exe = layout ringNext ∧ st.endPc = (layout ringNext).addrOf ringNext.length ∧ st.decls = {} ∧
    st.st.2 = Kraken.Layout.start Directive ∧ st.st.1.regs.X0.toBitVec = a ∧ Mem.loadInt st.st.1.dmem a 8 = none

/-- **The ring index on the full Promising machine.** From a message-free
memory whose initial value of the index is below `8`, with every thread about
to run `ringNext` (any number of threads), at every reachable configuration
every value ever written to the index (and its initial value) is below `8`,
and every thread satisfies `ringSpec`. -/
theorem ring_reachable (a : BitVec 64) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, ringG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → RingStart a t.st) (h : Reachable A fuel c0 c) :
    MemInv (ringG a) c.mem ∧ ∀ (tid : Nat) (t : Thread isa), c.threads[tid]? = some t → (ringSpec a).Holds t.st :=
  inv_reachable (fun _ => ringSpec a)
    (MemInv.of_init hmsgs (fun _ _ => by decide) hinit)
    (fun tid t ht => by
      obtain ⟨he, hend, hds, hpc, hx0, hd⟩ := h0 tid t ht
      exact ThreadSpec.ofTripleEnv_holds (ringNext_correctEnv a) rfl he hend hds hpc ⟨hx0, hd⟩) h

/-- Every value a thread reads from the index, at any reachable
configuration, is below `8`: and a thread that has finished `ringNext` holds
such a value in `x1`. -/
theorem ring_reachable_post (a : BitVec 64) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, ringG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → RingStart a t.st) (h : Reachable A fuel c0 c)
    {tid : Nat} {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hend : t.st.st.2 = (layout ringNext).addrOf ringNext.length) :
    t.st.st.1.regs.X1.toNat < 8 := by
  have hpost := inv_reachable_post (fun _ => ringSpec a)
    (MemInv.of_init hmsgs (fun _ _ => by decide) hinit)
    (fun tid t ht => by
      obtain ⟨he, hend, hds, hpc, hx0, hd⟩ := h0 tid t ht
      exact ThreadSpec.ofTripleEnv_holds (ringNext_correctEnv a) rfl he hend hds hpc ⟨hx0, hd⟩) h ht
    (not_instrStepEnv_of_end _) hend
  exact (hpost.resolve_right id).2

end ringNext

/-! ## (b) A racy flag -/

/-- The flag at `a` (8 bytes) is `0` or `1`. -/
def flagG (a : BitVec 64) (l : Loc) (v : Val) : Prop := l = ⟨a, 8⟩ → v = 0 ∨ v = 1

/-- Flip the flag at `[x0]` by a plain, racy read-modify-write. -/
def toggle : Program := parseAArch64("
    ldr x1, [x0]
    eor x1, x1, #1
    str x1, [x0]
")

/-- Set the flag at `[x0]`. -/
def setOne : Program := parseAArch64("
    mov x1, #1
    str x1, [x0]
")

/-- Negative control: store `2` to the flag at `[x0]`. -/
def setTwo : Program := parseAArch64("
    mov x1, #2
    str x1, [x0]
")

section toggle

variable [layout : _root_.Layout]

local instance toggle.env : CodeEnv := ⟨layout toggle⟩

/-- `toggle` in `inv`: the load may return either value the invariant allows,
whatever was written last; the store keeps the invariant. -/
theorem toggle_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.inv [(a, 8)] (flagG a))
      (fun s _ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none)
      toggle
      (fun s _ => s.regs.X1 = 0 ∨ s.regs.X1 = 1)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold toggle
  vcgen
  all_goals simp_all [SharedEnv.inv, flagG]
  all_goals (rcases ‹_ = 0#64 ∨ _ = 1#64› with h | h <;> subst h <;> decide)

end toggle

section setOne

variable [layout : _root_.Layout]

local instance setOne.env : CodeEnv := ⟨layout setOne⟩

theorem setOne_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.inv [(a, 8)] (flagG a))
      (fun s _ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none)
      setOne
      (fun _ _ => True)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold setOne
  vcgen
  all_goals simp_all [SharedEnv.inv, flagG]
  all_goals decide

end setOne

/-! ## (c) Negative control -/

/-- The obligation `setTwo`'s store leaves: the value `2` violates the
invariant. -/
theorem flagG_two (a : BitVec 64) : ¬ flagG a ⟨a, 8⟩ ((2#64).setWidth 128) := by
  simp [flagG]

section setTwo

variable [layout : _root_.Layout]

local instance setTwo.env : CodeEnv := ⟨layout setTwo⟩

set_option linter.unusedVariables false in
/-- `setTwo` does not verify in `inv`: the same script as `setOne` leaves the
store's obligation `flagG a ⟨a, 8⟩ 2`, which is false (`flagG_two`). -/
example (a : BitVec 64) : True := by
  fail_if_success
    have : TripleEnv (SharedEnv.inv [(a, 8)] (flagG a))
        (fun s _ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none)
        setTwo (fun _ _ => True) (fun _ _ _ => False) := by
      apply TripleEnv.of_triple
      unfold setTwo
      vcgen
      all_goals simp_all [SharedEnv.inv, flagG]
      all_goals decide
  trivial

end setTwo

/-! ## (a) + (b) on the full machine: togglers and setters -/

section flag

variable [layout : _root_.Layout] [Executable.ValidLayout (layout toggle)]
  [Executable.ValidLayout (layout setOne)]

/-- The specification of thread `tid`: `toggle` if `role tid`, else
`setOne`. -/
abbrev flagSpec (a : BitVec 64) (role : Nat → Bool) (tid : Nat) : ThreadSpec [(a, 8)] (flagG a) :=
  if role tid then ThreadSpec.ofTripleEnv toggle fun s _ => s.regs.X1 = 0 ∨ s.regs.X1 = 1
  else ThreadSpec.ofTripleEnv setOne fun _ _ => True

/-- A thread about to run `p` on the flag at `a`. -/
def FlagStart (a : BitVec 64) (p : Program) (st : State) : Prop :=
  st.exe = layout p ∧ st.endPc = (layout p).addrOf p.length ∧ st.decls = {} ∧
    st.st.2 = Kraken.Layout.start Directive ∧ st.st.1.regs.X0.toBitVec = a ∧ Mem.loadInt st.st.1.dmem a 8 = none

/-- **The flag on the full Promising machine.** Any number of threads, each
running `toggle` (racy plain accesses) or `setOne` as `role` says, from a
message-free memory whose initial flag is `0` or `1`: at every reachable
configuration every value ever written to the flag is `0` or `1`, and every
thread satisfies its specification. -/
theorem flag_reachable (a : BitVec 64) (role : Nat → Bool) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, flagG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t →
      FlagStart a (if role tid then toggle else setOne) t.st)
    (h : Reachable A fuel c0 c) :
    MemInv (flagG a) c.mem ∧
      ∀ (tid : Nat) (t : Thread isa), c.threads[tid]? = some t → (flagSpec a role tid).Holds t.st :=
  inv_reachable (flagSpec a role)
    (MemInv.of_init hmsgs (fun _ _ => .inl rfl) hinit)
    (fun tid t ht => by
      have h0 := h0 tid t ht
      unfold flagSpec
      split
      · rename_i hr
        simp only [hr, ite_true] at h0
        obtain ⟨he, hend, hds, hpc, hx0, hd⟩ := h0
        letI : CodeEnv := ⟨layout toggle⟩
        exact ThreadSpec.ofTripleEnv_holds (toggle_correctEnv a) rfl he hend hds hpc ⟨hx0, hd⟩
      · rename_i hr
        simp only [hr, Bool.false_eq_true, ite_false] at h0
        obtain ⟨he, hend, hds, hpc, hx0, hd⟩ := h0
        letI : CodeEnv := ⟨layout setOne⟩
        exact ThreadSpec.ofTripleEnv_holds (setOne_correctEnv a) rfl he hend hds hpc ⟨hx0, hd⟩) h

end flag

/-! ## A real fragment: the worker of `spinlock_swp2.kl`

The whole `worker` of `Kraken/Examples/LockFree/AArch64/spinlock_swp2.kl`
(test-and-test-and-set: `swpa` to acquire, a plain `ldr` spin while held, a
plain increment of the counter, `stlr wzr` to release), with the lock and the
counter shared. Invariant `lockG`: the lock is `0` or `1` (the counter is
unconstrained). The loop is proved by `cfgEnv_partial` in the counted
environment (`SharedEnv.counted`), projected by `PartialTripleEnv.uncount`:
a `Safely` judgment, hence a `ThreadSpec` (`ofSafely`). What this does *not*
give is the file's property (`counter = 2`): that needs ownership of the
counter by the lock holder (Stage 2). -/

/-- The lock at `l` (4 bytes) is `0` or `1`. -/
def lockG (l : BitVec 64) (x : Loc) (v : Val) : Prop := x = ⟨l, 4⟩ → v = 0 ∨ v = 1

/-- `worker` of `spinlock_swp2.kl`, lock at `[x0]`, counter at `[x1]`. -/
def swpWorker : Program := parseAArch64("
worker:
    mov w3, #1
try:
    swpa w3, w2, [x0]
    cbz w2, cs
spin:
    ldr w2, [x0]
    cbnz w2, spin
    b try
cs:
    ldr w5, [x1]
    add w5, w5, #1
    str w5, [x1]
    stlr wzr, [x0]
    b done
done:
")

section swpWorker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpWorker)]

local instance swpWorker.env : CodeEnv := ⟨layout swpWorker⟩

/-- The shared layout: the lock and the counter, 4 bytes each. -/
abbrev swpS (l c : BitVec 64) : SharedEnv.Layout := [(l, 4), (c, 4)]

/-- The partial table: `w3 = 1` in the loop, `w2 = 0` once the lock was
taken. -/
private abbrev swpWorker_table (l c : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.inv (swpS l c) (lockG l))).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
    Mem.loadInt s.dmem c 4 = none ∧
    (lb = "worker" ∨ ((lb = "try" ∨ lb = "spin") ∧ s.regs.X3.toBitVec = 1) ∨
      ((lb = "cs" ∨ lb = "done") ∧ s.regs.X2.toBitVec.setWidth 32 = 0))

/-- **The worker in `inv`**, partial correctness in the counted environment:
every run that reaches the end has taken the lock (`w2 = 0`). -/
theorem swpWorker_correctCounted (l c : BitVec 64) (hne : c ≠ l) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.inv (swpS l c) (lockG l)))
      (fun s _ => s.regs.X0.toBitVec = l ∧ s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem l 4 = none ∧
        Mem.loadInt s.dmem c 4 = none)
      swpWorker
      (fun s _ => s.regs.X2.toBitVec.setWidth 32 = 0)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (swpWorker_table l c)
    (hP := by funext s g; simp [swpWorker_table])
  cfg_cases_env [swpWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.inv, lockG, rmwOpBits]

/-- The end address of `swpWorker`. -/
abbrev swpEnd : Int64 := (layout swpWorker).addrOf swpWorker.length

/-- A `swpWorker` thread: the `Safely` judgment of the uncounted partial
triple; postcondition `w2 = 0` at the end. -/
abbrev swpSpec (l c : BitVec 64) : ThreadSpec (swpS l c) (lockG l) :=
  ThreadSpec.ofSafely (layout swpWorker) swpEnd
    (fun x => (x.1.2 = swpEnd ∧ ∃ _ : Nat, x.1.1.regs.X2.toBitVec.setWidth 32 = 0) ∨
      ∃ _ : Nat, False)
    (fun _ h => h.elim And.left fun ⟨_, h⟩ => h.elim)

/-- A thread about to run `swpWorker` on the lock at `l` and the counter at
`c`, both outside its private memory. -/
def SwpStart (l c : BitVec 64) (st : State) : Prop :=
  st.exe = layout swpWorker ∧ st.endPc = swpEnd ∧ st.decls = {} ∧
    st.st.2 = Kraken.Layout.start Directive ∧ st.st.1.regs.X0.toBitVec = l ∧ st.st.1.regs.X1.toBitVec = c ∧
    Mem.loadInt st.st.1.dmem l 4 = none ∧ Mem.loadInt st.st.1.dmem c 4 = none

theorem swpSpec_holds {l c : BitVec 64} (hne : c ≠ l) {st : State} (h : SwpStart l c st) :
    (swpSpec l c).Holds st := by
  obtain ⟨he, hend, hds, hpc, hx0, hx1, hl, hc⟩ := h
  refine ⟨he, hend, hds, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := Prod.ext rfl hpc
  rw [hst]
  exact Program.instrStepEnv_of_partialTripleEnv (swpWorker_correctCounted l c hne).uncount
    (s := st.st.1) (g := ()) ⟨0, hx0, hx1, hl, hc⟩

/-- **`spinlock_swp2.kl`'s workers on the full Promising machine.** Any
number of threads running `worker`, from a message-free memory whose initial
lock is `0` or `1`: at every reachable configuration every value ever
written to the lock is `0` or `1`, and a thread at the end of the text holds
`w2 = 0` (it took the lock). -/
theorem swp_reachable (l c : BitVec 64) (hne : c ≠ l) {A : Arch} {fuel : Nat} {c0 cf : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, lockG l p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → SwpStart l c t.st)
    (h : Reachable A fuel c0 cf) :
    MemInv (lockG l) cf.mem ∧
      ∀ (tid : Nat) (t : Thread isa), cf.threads[tid]? = some t → t.st.st.2 = swpEnd →
        t.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 := by
  have hm0 : MemInv (lockG l) c0.mem := MemInv.of_init hmsgs (fun _ _ => .inl rfl) hinit
  have h0' : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → (swpSpec l c).Holds t.st :=
    fun tid t ht => swpSpec_holds hne (h0 tid t ht)
  refine ⟨(inv_reachable (fun _ => swpSpec l c) hm0 h0' h).1, fun tid t ht hend => ?_⟩
  have hpost := inv_reachable_post (fun _ => swpSpec l c) hm0 h0' h ht
    (not_instrStepEnv_of_end_labels _ 1) hend
  obtain ⟨-, _, hx2⟩ := hpost.resolve_right fun ⟨_, h⟩ => h
  exact hx2

end swpWorker

end Kraken.AArch64.Examples.InvEnv
