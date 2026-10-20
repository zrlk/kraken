import Kraken.EnvVCGen
import Kraken.X64.Parser
import Kraken.Promising.SeqLinkX64Prog
import Kraken.Promising.EnvLinkSafeX64
import Kraken.Promising.InvLinkX64

/-!
# The invariant environment, x64

The x64 twin of `Kraken/AArch64/Examples/InvEnv.lean`: threads proved by one
`vcgen` call each in `SharedEnv.inv S G`, carried to every reachable
configuration of the full Promising machine (any number of threads, promises
included) by `Kraken.Promising.X64.inv_reachable`. The x64 link also needs
`Le16 S` (by `decide`) and a private memory split from `S` at the start
(`Split`, part of the start predicates; it gives the `dmem`-miss the
precondition asks for, `Split.loadInt_none`).

* (a) `ringNext`: one `lock cmpxchgq` attempt advancing a ring index modulo
  `8` (`movq`, `addq`, `andq $7`, `lock cmpxchgq`). Invariant `ringG`: the
  index is below `8`.
* (b) `toggle`: a racy plain read-modify-write flipping a flag (`movq`,
  `xorq` into `1`, `movq`), with `setOne` (`movq $1`, `movq`) in other threads.
  Invariant `flagG`: the flag is `0` or `1`.
* (c) negative control: `setTwo` stores `2`; the script that proves `setOne`
  fails on it (`fail_if_success`), its store obligation being false
  (`flagG_two`).
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.X64
open MachineWP

namespace Kraken.X64.Examples.InvEnv

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.X64.Parser

theorem le16_slot (a : BitVec 64) : Le16 [(a, 8)] := fun x hx => by
  rw [List.mem_singleton] at hx
  subst hx
  simp

/-! ## (a) A ring index advanced by `lock cmpxchgq` -/

/-- The ring index at `a` (8 bytes) is below `8`. -/
def ringG (a : BitVec 64) (l : Loc) (v : Val) : Prop := l = ⟨a, 8⟩ → v.toNat < 8

/-- One attempt to advance the ring index at `(%rdi)` modulo `8`. -/
def ringNext : Program := parse("
  movq (%rdi), %rax
  movq %rax, %rdx
  addq $1, %rdx
  andq $7, %rdx
  lock cmpxchgq %rdx, (%rdi)
")

section ringNext

variable [layout : _root_.Layout]

local instance ringNext.env : CodeEnv := ⟨layout ringNext⟩

theorem ringNext_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.inv [(a, 8)] (ringG a))
      (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none)
      ringNext
      (fun s _ => (s.regs.get64 .rax).toNat < 8)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold ringNext
  vcgen
  all_goals simp_all [SharedEnv.inv, ringG, rmwOp128]
  case vc3 => exact fun _ _ _ => Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  case vc4 =>
    obtain ⟨v, hv, rfl⟩ := ‹∃ v : Val, _›
    rw [BitVec.toNat_setWidth]
    omega
  case vc5 => omega

variable [Executable.ValidLayout (layout ringNext)]

/-- A `ringNext` thread: postcondition `rax < 8` at the end. -/
abbrev ringSpec (a : BitVec 64) : ThreadSpec [(a, 8)] (ringG a) :=
  ThreadSpec.ofTripleEnv ringNext fun s _ => (s.regs.get64 .rax).toNat < 8

/-- A thread about to run `ringNext` on the index at `a` (`rdi = a`, no byte
of the index in its private memory). -/
def RingStart (a : BitVec 64) (st : State) : Prop :=
  st.exe = layout ringNext ∧ st.endPc = (layout ringNext).addrOf ringNext.length ∧ st.decls = {} ∧
    st.st.2 = Kraken.Layout.start Directive ∧ st.st.1.regs.get64 .rdi = a ∧ Split [(a, 8)] st.st.1.dmem

theorem ringSpec_holds (a : BitVec 64) {st : State} (h : RingStart a st) : (ringSpec a).Holds st := by
  obtain ⟨he, hend, hds, hpc, hrdi, hs⟩ := h
  exact ThreadSpec.ofTripleEnv_holds (ringNext_correctEnv a) rfl he hend hds hpc
    ⟨hrdi, hs.loadInt_none (List.mem_singleton_self _) (by decide) (by decide)⟩ hs

/-- **The ring index on the full Promising machine** (x64). -/
theorem ring_reachable (a : BitVec 64) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, ringG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → RingStart a t.st)
    (h : Reachable A fuel c0 c) :
    MemInv (ringG a) c.mem ∧ ∀ (tid : Nat) (t : Thread isa), c.threads[tid]? = some t → (ringSpec a).Holds t.st :=
  inv_reachable (le16_slot a) (fun _ => ringSpec a) (MemInv.of_init hmsgs (fun _ _ => by decide) hinit)
    (fun tid t ht => ringSpec_holds a (h0 tid t ht)) h

/-- A thread that has finished `ringNext`, at any reachable configuration,
holds an index below `8` in `rax`. -/
theorem ring_reachable_post (a : BitVec 64) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, ringG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t → RingStart a t.st)
    (h : Reachable A fuel c0 c) {tid : Nat} {t : Thread isa} (ht : c.threads[tid]? = some t)
    (hend : t.st.st.2 = (layout ringNext).addrOf ringNext.length) :
    (t.st.st.1.regs.get64 .rax).toNat < 8 := by
  have hpost := inv_reachable_post (le16_slot a) (fun _ => ringSpec a)
    (MemInv.of_init hmsgs (fun _ _ => by decide) hinit)
    (fun tid t ht => ringSpec_holds a (h0 tid t ht)) h ht (not_instrStepEnv_of_end _) hend
  exact (hpost.resolve_right id).2

end ringNext

/-! ## (b) A racy flag -/

/-- The flag at `a` (8 bytes) is `0` or `1`. -/
def flagG (a : BitVec 64) (l : Loc) (v : Val) : Prop := l = ⟨a, 8⟩ → v = 0 ∨ v = 1

/-- Flip the flag at `(%rdi)` by a plain, racy read-modify-write
(`1 xor flag`). -/
def toggle : Program := parse("
  movq (%rdi), %rax
  movq $1, %rdx
  xorq %rax, %rdx
  movq %rdx, (%rdi)
")

/-- Set the flag at `(%rdi)`. -/
def setOne : Program := parse("
  movq $1, %rax
  movq %rax, (%rdi)
")

/-- Negative control: store `2` to the flag at `(%rdi)`. -/
def setTwo : Program := parse("
  movq $2, %rax
  movq %rax, (%rdi)
")

section toggle

variable [layout : _root_.Layout]

local instance toggle.env : CodeEnv := ⟨layout toggle⟩

theorem toggle_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.inv [(a, 8)] (flagG a))
      (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none)
      toggle
      (fun s _ => s.regs.get64 .rdx = 0 ∨ s.regs.get64 .rdx = 1)
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
      (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none)
      setOne
      (fun _ _ => True)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold setOne
  vcgen
  all_goals simp_all [SharedEnv.inv, flagG]

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
/-- `setTwo` does not verify in `inv`: the script that proves `setOne` leaves
the store's obligation `flagG a ⟨a, 8⟩ 2`, which is false (`flagG_two`). -/
example (a : BitVec 64) : True := by
  fail_if_success
    have : TripleEnv (SharedEnv.inv [(a, 8)] (flagG a))
        (fun s _ => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none)
        setTwo (fun _ _ => True) (fun _ _ _ => False) := by
      apply TripleEnv.of_triple
      unfold setTwo
      vcgen
      all_goals simp_all [SharedEnv.inv, flagG]
  trivial

end setTwo

/-! ## (a) + (b) on the full machine: togglers and setters -/

section flag

variable [layout : _root_.Layout] [Executable.ValidLayout (layout toggle)]
  [Executable.ValidLayout (layout setOne)]

/-- The specification of thread `tid`: `toggle` if `role tid`, else
`setOne`. -/
abbrev flagSpec (a : BitVec 64) (role : Nat → Bool) (tid : Nat) : ThreadSpec [(a, 8)] (flagG a) :=
  if role tid then ThreadSpec.ofTripleEnv toggle fun s _ => s.regs.get64 .rdx = 0 ∨ s.regs.get64 .rdx = 1
  else ThreadSpec.ofTripleEnv setOne fun _ _ => True

/-- A thread about to run `p` on the flag at `a`. -/
def FlagStart (a : BitVec 64) (p : Program) (st : State) : Prop :=
  st.exe = layout p ∧ st.endPc = (layout p).addrOf p.length ∧ st.decls = {} ∧
    st.st.2 = Kraken.Layout.start Directive ∧ st.st.1.regs.get64 .rdi = a ∧ Split [(a, 8)] st.st.1.dmem

/-- **The flag on the full Promising machine** (x64): any number of threads,
each running `toggle` or `setOne` as `role` says. -/
theorem flag_reachable (a : BitVec 64) (role : Nat → Bool) {A : Arch} {fuel : Nat} {c0 c : Config isa}
    (hmsgs : c0.mem.msgs = #[]) (hinit : ∀ p ∈ c0.mem.init, flagG a p.1 p.2)
    (h0 : ∀ (tid : Nat) (t : Thread isa), c0.threads[tid]? = some t →
      FlagStart a (if role tid then toggle else setOne) t.st)
    (h : Reachable A fuel c0 c) :
    MemInv (flagG a) c.mem ∧
      ∀ (tid : Nat) (t : Thread isa), c.threads[tid]? = some t → (flagSpec a role tid).Holds t.st :=
  inv_reachable (le16_slot a) (flagSpec a role)
    (MemInv.of_init hmsgs (fun _ _ => .inl rfl) hinit)
    (fun tid t ht => by
      have h0 := h0 tid t ht
      unfold flagSpec
      split
      · rename_i hr
        simp only [hr, ite_true] at h0
        obtain ⟨he, hend, hds, hpc, hrdi, hs⟩ := h0
        letI : CodeEnv := ⟨layout toggle⟩
        exact ThreadSpec.ofTripleEnv_holds (toggle_correctEnv a) rfl he hend hds hpc
          ⟨hrdi, hs.loadInt_none (List.mem_singleton_self _) (by decide) (by decide)⟩ hs
      · rename_i hr
        simp only [hr, Bool.false_eq_true, ite_false] at h0
        obtain ⟨he, hend, hds, hpc, hrdi, hs⟩ := h0
        letI : CodeEnv := ⟨layout setOne⟩
        exact ThreadSpec.ofTripleEnv_holds (setOne_correctEnv a) rfl he hend hds hpc
          ⟨hrdi, hs.loadInt_none (List.mem_singleton_self _) (by decide) (by decide)⟩ hs) h

end flag

end Kraken.X64.Examples.InvEnv
