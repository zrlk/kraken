import Kraken.AArch64.EnvCfg
import Kraken.AArch64.Parser
import Kraken.Promising.SeqLinkAArch64Prog
import Kraken.Promising.EnvWPAArch64
import Kraken.Promising.EnvLinkSafeAArch64
import Kraken.Promising.EnvLinkTermAArch64

/-!
# LSE loops over the AArch64 environment wp, carried to the Promising machine

The AArch64 side of the environment logic for the LSE atomics (`CAS`, `SWP`,
`LD<op>`; LL/SC is deferred in the Stage 2/3 logic).
Every slot is shared (outside `dmem`, its value the `SharedEnv.lastWrite`
environment state's), and every theorem reaches the Promising machine through
`env_link_halt` or `env_link_halt_safe`, with no access-discipline premises
(`hpres`/`hacc`/`h0`).

* `casInc`, a `casal` retry loop: total correctness by `MachineWP.cfgEnv`,
  `cfg_cases_env` and `vcgen` (`casInc_correctEnv`). The loop head `retry`
  admits any `x1`; the variant is `1` there when `x1` differs from the slot and
  `0` otherwise. A failed `casal` loads the slot's value into `x1`, so in
  `lastWrite` the back edge is taken at most once, from variant `1` to `0`.
  `casInc_terminates` is the run at the machine (`Eventually`), and
  `casInc_promising` the Promising-machine statement for runs that reach the
  end.
* `fetchInc` (`ldaddal`) and `tas` (`swpal`, a test-and-set acquire attempt):
  loop-free, by one `vcgen` call (`*_correctEnv`) and `env_link_halt`
  (`*_promising`).
* `swpAcquire`, the acquire of `spinlock_swp2.kl` (`swpa` until the old value
  is `0`, spinning on a plain `ldr` while the lock is held). In `lastWrite`,
  no other thread releases the lock, so the loop terminates exactly when the
  lock starts free: `swpAcquire_correctEnv` is total under that hypothesis
  (`cfgEnv`, variant `0`: the `spin` block is unreachable);
  `swpAcquire_terminates` and `swpAcquire_promising` follow.
  `swpAcquire_correctCounted` is the partial-correctness theorem with no
  hypothesis on the lock (`cfgEnv_partial`): every run that leaves the loop
  has taken the lock (`w2 = 0`, last write `1`). The back edges out of `spin`
  and `try` may come back in the entry state, so it is proved in
  `SharedEnv.counted (SharedEnv.lastWrite L)` (each such edge passes a shared
  access, which moves the counter), projected by `PartialTripleEnv.uncount`,
  and carried by `env_link_halt_safe` (`swpAcquire_promising_partial`).

The Promising-machine theorems constrain the runs whose thread has reached the
end of the text (`env_link_halt` and `env_link_halt_safe` are about halting
runs); termination is the `Eventually` of the `TripleEnv` at the machine
(`*_terminates`). `casInc_terminates_promising` and
`swpAcquire_terminates_promising` are termination on the Promising
machine: every maximal promise-free run of the one-thread machine is finite
and ends at the end of the text with the postcondition
(`env_link_terminates`; `dirs_no_fault` checks that no instruction faults in
the adapter).

The loops are laid out so that the last cell is an instruction: the
end-of-text facts `step1W_stop_of_end` and `not_instrStepEnv_of_end` need that
(their `hd` default rejects a trailing label), which is why `swpAcquire` puts
`spin` before `try` and enters with `b try`. `swpAcquireNat` is the same
acquire in its natural layout, ending in a `done:` label, carried by the
trailing-label variants `step1W_stop_of_end_labels` and
`not_instrStepEnv_of_end_labels`.
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.AArch64
open MachineWP

namespace MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.AArch64.Parser

/-- A difference is zero exactly when the operands agree: what the `Z` flag of
`cmp` says. -/
private theorem sub_eq_zero_iff' {a b : BitVec 64} : a - b = 0#64 ↔ a = b := by
  constructor <;> intro h <;> bv_omega

/-- A slot that `hsplit` keeps out of `dmem` does not load from it. -/
private theorem loadInt_none_of_split {d : MachineData} {a : BitVec 64} {n : Nat} (hn : 0 < n)
    (hsplit : ∀ k, SharedLayout.Covers [(a, n)] k → d.dmem.get? k = none) :
    Mem.loadInt d.dmem a n = none := by
  cases hl : Mem.loadInt d.dmem a n with
  | none => rfl
  | some x =>
    have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 hn
    rw [hsplit _ ⟨_, n, List.mem_singleton_self _, by simpa using hn⟩] at h0
    cases h0

/-- The environment state reading every address as the slot's final value in
`mem` is related to `mem`. -/
private theorem envRel_slot (a : BitVec 64) (n : Nat) (mem : Memory) :
    envRel [(a, n)] (fun _ => mem.finalVal (sharedLoc a n)) mem := by
  intro b m hb
  rw [List.mem_singleton] at hb
  cases hb
  rfl

/-- A one-slot layout of `n ∈ [1, 16]` bytes is well formed. -/
theorem slot_layout_wf (a : BitVec 64) (n : Nat) (hpos : 0 < n) (hle : n ≤ 16) :
    SharedLayout.WF [(a, n)] where
  pos _ _ h := by rw [List.mem_singleton] at h; cases h; exact hpos
  le16 _ _ h := by rw [List.mem_singleton] at h; cases h; exact hle
  disj _ _ _ _ _ ha hb _ _ := by
    rw [List.mem_singleton] at ha hb
    cases ha; cases hb
    exact ⟨rfl, rfl⟩

/-- Increment the shared counter at `[x0]` with a `casal` retry loop: load
it once, then compute the successor, compare-and-swap, and retry with the
value the `casal` returned while it differs from the expected one. -/
def casInc : Program := parseAArch64("
start:
    ldr x1, [x0]
retry:
    add x2, x1, #1
    mov x3, x1
    casal x1, x2, [x0]
    cmp x1, x3
    b.ne retry
")

section casInc

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casInc)]

local instance casInc.env : CodeEnv := ⟨layout casInc⟩

/-- The loop's table: at both labels the counter is shared and holds `v`; `x1`
is unconstrained at `retry`. -/
private abbrev casInc_table (a v : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite [(a, 8)]).State → Prop :=
  fun l s g => (l = "start" ∨ l = "retry") ∧
    s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g a).setWidth 64 = v

/-- The variant: `1` at `retry` while `x1` is stale, `0` otherwise. -/
private abbrev casInc_var (a v : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite [(a, 8)]).State → Nat :=
  fun l s _ => if l = "retry" ∧ s.regs.X1.toBitVec ≠ v then 1 else 0

/-- From a shared counter at `a = x0` holding `v`, the loop ends with `v` in
`x1` and `v + 1` in the counter: `cfgEnv` with the variant `casInc_var`, one
`vcgen` call per block. -/
theorem casInc_correctEnv (a v : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(a, 8)])
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g a).setWidth 64 = v)
      casInc
      (fun s g => s.regs.X1.toBitVec = v ∧ (g a).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv (casInc_table a v) (casInc_var a v)
    (hP := by funext s g; simp [casInc_table])
  cfg_cases_env [casInc]
  all_goals intro n
  all_goals vcgen
  all_goals obtain ⟨_, rfl⟩ := ‹_ ∧ _ = n›
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits, and_assoc, sub_eq_zero_iff']
  all_goals (repeat' split) <;> simp_all
  exact Table.ofLabelsEnv_at ⟨.inr rfl, by simp_all⟩

/-- **Termination at the machine.** From the start address, every run of
`casInc` in `lastWrite` reaches the end of the text, with `v` in `x1` and
`v + 1` as the counter's value. -/
theorem casInc_terminates (d : MachineData) (g : (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 8)]).State)
    (v : BitVec 64) (hnone : Mem.loadInt d.dmem d.regs.X0.toBitVec 8 = none)
    (h_slot : (g d.regs.X0.toBitVec).setWidth 64 = v) :
    Eventually ((layout casInc).instrStepEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 8)]))
      (fun x => x.1.2 = (layout casInc).addrOf casInc.length ∧
        x.1.1.regs.X1.toBitVec = v ∧ (x.2 d.regs.X0.toBitVec).setWidth 64 = v + 1)
      ((d, Kraken.Layout.start Directive), g) :=
  eventually_weaken _ _ _ _ (fun _ h => h.resolve_right id)
    (Program.instrStepEnv_of_tripleEnv (casInc_correctEnv d.regs.X0.toBitVec v) ⟨rfl, hnone, h_slot⟩)

/-- **The `casal` retry loop on the Promising machine.** A promise-free
one-thread run of `casInc` from `d`, the counter at `[x0]` shared (no bytes in
`dmem`, its value `v` in the message-free memory `mem`): when the thread has
reached the end of the text, `x1` is `v` and the counter's last write is
`v + 1`. `casInc_correctEnv` through `env_link_halt`; no `hpres`/`hacc`/`h0`. -/
theorem casInc_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 8)] k → d.dmem.get? k = none)
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout casInc
      endPc := (layout casInc).addrOf casInc.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout casInc).addrOf casInc.length) :
    t'.st.st.1.regs.X1.toBitVec = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v + 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
  have henv : envRel [(d.regs.X0.toBitVec, 8)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (casInc_correctEnv d.regs.X0.toBitVec v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout casInc) (slot_layout_wf _ 8 (by decide) (by decide))
    A fuel _ showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx1, hslot⟩ := hP.resolve_right id
  refine ⟨hx1, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm

/-- **The `casal` retry loop terminates on the Promising machine.** From the
same start as `casInc_promising`, every maximal promise-free run of the
one-thread machine is finite (whatever `fuel`) and ends with the thread at the
end of the text, `x1 = v` and the counter's last write `v + 1`: no run diverges
and none gets stuck. `casInc_correctEnv` through `env_link_terminates`;
`dirs_no_fault` checks that no instruction of the loop faults in the adapter. -/
theorem casInc_terminates_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String)
    (d : MachineData) (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 8)] k → d.dmem.get? k = none)
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v) :
    Eventually (StepPF' A fuel) (fun (c : Config isa) => ∃ t' : Thread isa, c.threads = #[t'] ∧
        t'.st.st.2 = (layout casInc).addrOf casInc.length ∧ t'.st.st.1.regs.X1.toBitVec = v ∧
        (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v + 1)
      (⟨#[Thread.init ({
        exe := layout casInc
        endPc := (layout casInc).addrOf casInc.length
        st := (d, Kraken.Layout.start Directive)
        showPc := showPc } : State)], mem⟩ : Config isa) := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
  have henv : envRel [(d.regs.X0.toBitVec, 8)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (casInc_correctEnv d.regs.X0.toBitVec v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  have hnf : DirsNoFault (layout casInc) := by dirs_no_fault casInc
  refine eventually_weaken _ _ _ _ ?_ (env_link_terminates _ (layout casInc)
    (slot_layout_wf _ 8 (by decide) (by decide)) A fuel _ showPc d _ mem g _ hm hsplit henv
    (fun x hx => hx.elim And.left False.elim) (not_instrStepEnv_of_end _) hnf hev)
  rintro c ⟨t', ht, hend, g', hrel', hP⟩
  obtain ⟨-, hx1, hslot⟩ := hP.resolve_right id
  refine ⟨t', ht, hend, hx1, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm

end casInc

/-! ## Loop-free LSE examples -/

/-- Fetch-and-increment of the shared counter at `[x0]`, old value to `x2`. -/
def fetchInc : Program := parseAArch64("
    mov x1, #1
    ldaddal x1, x2, [x0]
")

/-- One test-and-set attempt on the 4-byte lock at `[x0]`, old value to `w2`. -/
def tas : Program := parseAArch64("
    mov w1, #1
    swpal w1, w2, [x0]
")

section fetchInc

variable [layout : _root_.Layout]

local instance fetchInc.env : CodeEnv := ⟨layout fetchInc⟩

/-- `fetchInc` in `lastWrite`: `x2` receives `v`, the counter `v + 1`
(`ldop_shared_spec`; the `mov` by the generic rule). -/
theorem fetchInc_correctEnv (a v : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(a, 8)])
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g a).setWidth 64 = v)
      fetchInc
      (fun s g => s.regs.X2.toBitVec = v ∧ (g a).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold fetchInc
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits]

variable [Executable.ValidLayout (layout fetchInc)]

/-- **`fetchInc` on the Promising machine**, through `env_link_halt`. -/
theorem fetchInc_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 8)] k → d.dmem.get? k = none)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout fetchInc
      endPc := (layout fetchInc).addrOf fetchInc.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout fetchInc).addrOf fetchInc.length) :
    t'.st.st.1.regs.X2.toBitVec = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)).setWidth 64 = v + 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 8)
  have henv : envRel [(d.regs.X0.toBitVec, 8)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (fetchInc_correctEnv d.regs.X0.toBitVec v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout fetchInc) (slot_layout_wf _ 8 (by decide) (by decide))
    A fuel _ showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 8 (List.mem_singleton_self _)
  refine ⟨hx2, ?_⟩
  rw [← hslot]
  exact this.symm

end fetchInc

section tas

variable [layout : _root_.Layout]

local instance tas.env : CodeEnv := ⟨layout tas⟩

/-- `tas` in `lastWrite`: `w2` receives the lock's value `v`, the lock `1`
(`swp_shared_spec`). -/
theorem tas_correctEnv (a : BitVec 64) (v : BitVec 32) :
    TripleEnv (SharedEnv.lastWrite [(a, 4)])
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none ∧ (g a).setWidth 32 = v)
      tas
      (fun s g => s.regs.X2.toBitVec.setWidth 32 = v ∧ (g a).setWidth 32 = 1)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold tas
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits]

variable [Executable.ValidLayout (layout tas)]

/-- **`tas` on the Promising machine**, through `env_link_halt`. -/
theorem tas_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 32) (mem : Memory) (hm : mem.msgs = #[])
    (h_slot : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = v)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout tas
      endPc := (layout tas).addrOf tas.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout tas).addrOf tas.length) :
    t'.st.st.1.regs.X2.toBitVec.setWidth 32 = v ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (tas_correctEnv d.regs.X0.toBitVec v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout tas) (slot_layout_wf _ 4 (by decide) (by decide))
    A fuel _ showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨hx2, ?_⟩
  rw [← hslot]
  exact this.symm

end tas

/-! ## The `SWP` spinlock acquire -/

/-- The acquire of `spinlock_swp2.kl` (test-and-test-and-set): `swpa` `1`
into the lock at `[x0]` until the old value is `0`, spinning on a plain load
while it is held. -/
def swpAcquire : Program := parseAArch64("
acquire:
    mov w3, #1
    b try
spin:
    ldr w2, [x0]
    cbnz w2, spin
try:
    swpa w3, w2, [x0]
    cbnz w2, spin
")

section swpAcquire

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpAcquire)]

local instance swpAcquire.env : CodeEnv := ⟨layout swpAcquire⟩

/-- The total table: the lock is free at `acquire` and `try` (with `w3 = 1`
at `try`); `spin` is unreachable (`False`). -/
private abbrev swpAcquire_table (a : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite [(a, 4)]).State → Prop :=
  fun l s g => (l = "acquire" ∨ (l = "try" ∧ s.regs.X3.toBitVec = 1)) ∧
    s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none ∧ (g a).setWidth 32 = 0

/-- **Total correctness from a free lock.** From a free shared lock at
`a = x0`, the acquire ends with `w2 = 0` and the lock taken. -/
theorem swpAcquire_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(a, 4)])
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none ∧ (g a).setWidth 32 = 0)
      swpAcquire
      (fun s g => s.regs.X2.toBitVec.setWidth 32 = 0 ∧ (g a).setWidth 32 = 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv (swpAcquire_table a)
    (hP := by funext s g; simp [swpAcquire_table])
  cfg_cases_env [swpAcquire]
  all_goals intro n
  all_goals vcgen
  all_goals obtain ⟨_, rfl⟩ := ‹_ ∧ _ = n›
  all_goals (try refine Table.ofLabelsEnv_at ?_)
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits, and_assoc]
  -- `b try` goes forward in the text
  decide

/-- **Termination at the machine** from a free lock. -/
theorem swpAcquire_terminates (d : MachineData)
    (g : (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 4)]).State)
    (hnone : Mem.loadInt d.dmem d.regs.X0.toBitVec 4 = none)
    (h_free : (g d.regs.X0.toBitVec).setWidth 32 = 0) :
    Eventually ((layout swpAcquire).instrStepEnv (SharedEnv.lastWrite [(d.regs.X0.toBitVec, 4)]))
      (fun x => x.1.2 = (layout swpAcquire).addrOf swpAcquire.length ∧
        x.1.1.regs.X2.toBitVec.setWidth 32 = 0 ∧ (x.2 d.regs.X0.toBitVec).setWidth 32 = 1)
      ((d, Kraken.Layout.start Directive), g) :=
  eventually_weaken _ _ _ _ (fun _ h => h.resolve_right id)
    (Program.instrStepEnv_of_tripleEnv (swpAcquire_correctEnv d.regs.X0.toBitVec) ⟨rfl, hnone, h_free⟩)

/-- **The acquire on the Promising machine, from a free lock.** A promise-free
one-thread run of `swpAcquire` from `d`, the lock at `[x0]` shared and free in
the message-free memory `mem`: when the thread has reached the end of the
text, `w2` is `0` and the lock's last write is `1`. Through `env_link_halt`. -/
theorem swpAcquire_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (mem : Memory) (hm : mem.msgs = #[])
    (h_free : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 0)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout swpAcquire
      endPc := (layout swpAcquire).addrOf swpAcquire.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout swpAcquire).addrOf swpAcquire.length) :
    t'.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (swpAcquire_correctEnv d.regs.X0.toBitVec)
    (s := d) (g := g) ⟨rfl, hnone, h_free⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout swpAcquire) (slot_layout_wf _ 4 (by decide) (by decide))
    A fuel _ showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (step1W_stop_of_end _) hev c hc t' ht hend
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨hx2, ?_⟩
  rw [← hslot]
  exact this.symm

/-- **The acquire terminates on the Promising machine, from a free lock.**
Every maximal promise-free run of the one-thread machine from the start of
`swpAcquire_promising` is finite and ends at the end of the text with `w2 = 0`
and the lock's last write `1`. Through `env_link_terminates`. -/
theorem swpAcquire_terminates_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String)
    (d : MachineData) (mem : Memory) (hm : mem.msgs = #[])
    (h_free : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 0)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none) :
    Eventually (StepPF' A fuel) (fun (c : Config isa) => ∃ t' : Thread isa, c.threads = #[t'] ∧
        t'.st.st.2 = (layout swpAcquire).addrOf swpAcquire.length ∧
        t'.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 ∧
        (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1)
      (⟨#[Thread.init ({
        exe := layout swpAcquire
        endPc := (layout swpAcquire).addrOf swpAcquire.length
        st := (d, Kraken.Layout.start Directive)
        showPc := showPc } : State)], mem⟩ : Config isa) := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (swpAcquire_correctEnv d.regs.X0.toBitVec)
    (s := d) (g := g) ⟨rfl, hnone, h_free⟩
  have hnf : DirsNoFault (layout swpAcquire) := by dirs_no_fault swpAcquire
  refine eventually_weaken _ _ _ _ ?_ (env_link_terminates _ (layout swpAcquire)
    (slot_layout_wf _ 4 (by decide) (by decide)) A fuel _ showPc d _ mem g _ hm hsplit henv
    (fun x hx => hx.elim And.left False.elim) (not_instrStepEnv_of_end _) hnf hev)
  rintro c ⟨t', ht, hend, g', hrel', hP⟩
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨t', ht, hend, hx2, ?_⟩
  rw [← hslot]
  exact this.symm

end swpAcquire

/-! ## The acquire in its natural layout

The same acquire as `spinlock_swp2.kl` lays it out: the `swpa` first, a
forward `cbz` to a `done:` label at the very end of the text. The end-of-text
facts for trailing labels (`step1W_stop_of_end_labels`,
`not_instrStepEnv_of_end_labels`, with `k := 1`) carry it to the Promising
machine. -/

/-- The acquire with the exit label at the end of the text. -/
def swpAcquireNat : Program := parseAArch64("
acquire:
    mov w3, #1
try:
    swpa w3, w2, [x0]
    cbz w2, done
spin:
    ldr w2, [x0]
    cbnz w2, spin
    b try
done:
")

section swpAcquireNat

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpAcquireNat)]

local instance swpAcquireNat.env : CodeEnv := ⟨layout swpAcquireNat⟩

/-- The total table: the lock is free at `acquire` and `try` (with `w3 = 1`
at `try`), it is taken at `done` (with `w2 = 0`); `spin` is unreachable. -/
private abbrev swpAcquireNat_table (a : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite [(a, 4)]).State → Prop :=
  fun l s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none ∧
    ((l = "acquire" ∧ (g a).setWidth 32 = 0) ∨
      (l = "try" ∧ s.regs.X3.toBitVec = 1 ∧ (g a).setWidth 32 = 0) ∨
      (l = "done" ∧ s.regs.X2.toBitVec.setWidth 32 = 0 ∧ (g a).setWidth 32 = 1))

/-- **Total correctness from a free lock**, natural layout. -/
theorem swpAcquireNat_correctEnv (a : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(a, 4)])
      (fun s g => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none ∧ (g a).setWidth 32 = 0)
      swpAcquireNat
      (fun s g => s.regs.X2.toBitVec.setWidth 32 = 0 ∧ (g a).setWidth 32 = 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv (swpAcquireNat_table a)
    (hP := by funext s g; simp [swpAcquireNat_table])
  cfg_cases_env [swpAcquireNat]
  all_goals intro n
  all_goals vcgen
  all_goals obtain ⟨_, rfl⟩ := ‹_ ∧ _ = n›
  all_goals (try refine Table.ofLabelsEnv_at ?_)
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits, and_assoc]
  -- the `cbz` to `done` goes forward in the text
  decide

/-- **The natural-layout acquire terminates on the Promising machine, from a
free lock**: as `swpAcquire_terminates_promising`, with the trailing label
handled by `not_instrStepEnv_of_end_labels _ 1`. -/
theorem swpAcquireNat_terminates_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String)
    (d : MachineData) (mem : Memory) (hm : mem.msgs = #[])
    (h_free : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 0)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none) :
    Eventually (StepPF' A fuel) (fun (c : Config isa) => ∃ t' : Thread isa, c.threads = #[t'] ∧
        t'.st.st.2 = (layout swpAcquireNat).addrOf swpAcquireNat.length ∧
        t'.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 ∧
        (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1)
      (⟨#[Thread.init ({
        exe := layout swpAcquireNat
        endPc := (layout swpAcquireNat).addrOf swpAcquireNat.length
        st := (d, Kraken.Layout.start Directive)
        showPc := showPc } : State)], mem⟩ : Config isa) := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (swpAcquireNat_correctEnv d.regs.X0.toBitVec)
    (s := d) (g := g) ⟨rfl, hnone, h_free⟩
  have hnf : DirsNoFault (layout swpAcquireNat) := by dirs_no_fault swpAcquireNat
  refine eventually_weaken _ _ _ _ ?_ (env_link_terminates _ (layout swpAcquireNat)
    (slot_layout_wf _ 4 (by decide) (by decide)) A fuel _ showPc d _ mem g _ hm hsplit henv
    (fun x hx => hx.elim And.left False.elim) (not_instrStepEnv_of_end_labels _ 1) hnf hev)
  rintro c ⟨t', ht, hend, g', hrel', hP⟩
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨t', ht, hend, hx2, ?_⟩
  rw [← hslot]
  exact this.symm

/-- **The natural-layout acquire on the Promising machine** (runs that reach
the end): `env_link_halt` with `step1W_stop_of_end_labels _ 1`. -/
theorem swpAcquireNat_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (mem : Memory) (hm : mem.msgs = #[])
    (h_free : (mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 0)
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout swpAcquireNat
      endPc := (layout swpAcquireNat).addrOf swpAcquireNat.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout swpAcquireNat).addrOf swpAcquireNat.length) :
    t'.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_tripleEnv (swpAcquireNat_correctEnv d.regs.X0.toBitVec)
    (s := d) (g := g) ⟨rfl, hnone, h_free⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout swpAcquireNat)
    (slot_layout_wf _ 4 (by decide) (by decide))
    A fuel _ showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (step1W_stop_of_end_labels _ 1) hev c hc t' ht hend
  obtain ⟨-, hx2, hslot⟩ := hP.resolve_right id
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨hx2, ?_⟩
  rw [← hslot]
  exact this.symm

end swpAcquireNat

section swpAcquirePartial

variable [layout : _root_.Layout] [Executable.ValidLayout (layout swpAcquire)]

local instance swpAcquire.env' : CodeEnv := ⟨layout swpAcquire⟩

/-- The partial table: no hypothesis on the lock; `w3 = 1` once the loop is
entered. -/
private abbrev swpAcquire_ptable (a : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.lastWrite [(a, 4)])).State → Prop :=
  fun l s _ => (l = "acquire" ∨ ((l = "spin" ∨ l = "try") ∧ s.regs.X3.toBitVec = 1)) ∧
    s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none

/-- **Partial correctness, any lock value**, in the counted environment: every
run that leaves the loop has `w2 = 0` and the lock taken. -/
theorem swpAcquire_correctCounted (a : BitVec 64) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.lastWrite [(a, 4)]))
      (fun s _ => s.regs.X0.toBitVec = a ∧ Mem.loadInt s.dmem a 4 = none)
      swpAcquire
      (fun s g => s.regs.X2.toBitVec.setWidth 32 = 0 ∧ (g.1 a).setWidth 32 = 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (swpAcquire_ptable a)
    (hP := by funext s g; simp [swpAcquire_ptable])
  cfg_cases_env [swpAcquire]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨hT, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.tick_load,
    SharedEnv.tick_rmw] at *
  -- `b try` goes forward in the text; on the back edges out of `spin` and
  -- `try` the counter has moved, so the entry state is not re-entered
  -- (after `subst`, the counter equation is contradictory).
  all_goals (try refine Table.ofLabelsEnv_at ⟨?_, ?_, ?_⟩)
  all_goals (try (first | exact .inl (by decide) | (refine .inr fun ⟨_, hg⟩ => ?_; subst hg)))
  all_goals simp_all [SharedEnv.lastWrite, rmwOpBits]

/-- **The acquire on the Promising machine, any lock value.** A promise-free
one-thread run of `swpAcquire` from `d`, the lock at `[x0]` shared: if the
thread has reached the end of the text, `w2` is `0` and the lock's last write
is `1`. Runs that keep spinning are not constrained.
`swpAcquire_correctCounted`, counter projected away, through
`env_link_halt_safe`. -/
theorem swpAcquire_promising_partial (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.X0.toBitVec, 4)] k → d.dmem.get? k = none)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout swpAcquire
      endPc := (layout swpAcquire).addrOf swpAcquire.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout swpAcquire).addrOf swpAcquire.length) :
    t'.st.st.1.regs.X2.toBitVec.setWidth 32 = 0 ∧
      (c.mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)).setWidth 32 = 1 := by
  have hnone := loadInt_none_of_split (by decide) hsplit
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc d.regs.X0.toBitVec 4)
  have henv : envRel [(d.regs.X0.toBitVec, 4)] g mem := envRel_slot _ _ _
  have hev := Program.instrStepEnv_of_partialTripleEnv
    (swpAcquire_correctCounted d.regs.X0.toBitVec).uncount (s := d) (g := g) ⟨0, rfl, hnone⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt_safe _ (layout swpAcquire)
    (slot_layout_wf _ 4 (by decide) (by decide)) A fuel _ showPc d _ mem g _ hm hsplit henv
    (fun x hx => hx.elim And.left fun ⟨_, h⟩ => h.elim) (not_instrStepEnv_of_end _) hev c hc t' ht hend
  obtain ⟨-, _, hx2, hslot⟩ := hP.resolve_right fun ⟨_, h⟩ => h
  have := hrel' _ 4 (List.mem_singleton_self _)
  refine ⟨hx2, ?_⟩
  rw [← hslot]
  exact this.symm

end swpAcquirePartial

end MachineWP
