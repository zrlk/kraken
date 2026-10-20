import Kraken.EnvCfg
import Kraken.X64.Parser
import Kraken.Promising.SeqLinkX64Prog
import Kraken.Promising.EnvWPX64
import Kraken.Promising.EnvLinkTermX64

/-!
# A `lock cmpxchg` retry loop over the environment wp

`casLoop` increments a shared counter the lock-free way: load it, add one,
`lock cmpxchg` the new value in, and jump back if another thread changed the
counter in between. `casLoop_correctEnv` proves it in
`SharedEnv.lastWrite [(a, 8)]` by the control-flow rule with the environment
(`MachineWP.cfgEnv`, total correctness, variant `0`), `cfg_cases_env`, and
one `vcgen` call on the one block: the combined rule `mov_load_env_spec`
reads the counter from the environment, the generic rule steps `leaq` and
`jne`, `lock_cmpxchg_shared_spec` does the compare-and-swap. In `lastWrite`
the compare after the load always succeeds, so the back edge is taken only in
a contradictory branch, which is why the variant `0` suffices (in an
environment where the compare may fail, use `cfgEnv_partial`).

`casLoop_promising` carries it to the Promising machine through
`env_link_halt`, like `casIncr_promising`: no `hpres`/`hacc`/`h0`.
`casLoop_terminates` is termination there: every promise-free run of the
one-thread machine reaches the end of the text, with the same postcondition
(`env_link_terminates`; `dirs_no_fault` checks that no instruction of the loop
faults in the adapter).
-/

open Std.WP
open Kraken
open Kraken.Promising
open Kraken.Promising.X64
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

open Kraken.X64.Parser

/-- Increment the shared counter at `(%rdi)`: load, add one, `lock cmpxchg`,
retry if another thread changed the counter in between. -/
def casLoop : Program := parse("
retry:
  movq (%rdi), %rax
  leaq 1(%rax), %rcx
  lock cmpxchgq %rcx, (%rdi)
  jne retry
")

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casLoop)]

local instance casLoop.env : CodeEnv := ⟨layout casLoop⟩

/-- The loop's table: at `retry` the counter is shared and holds `v`. -/
private abbrev casLoop_table (a v : BitVec 64) :
    Label → MachineData → (SharedEnv.lastWrite [(a, 8)]).State → Prop
  | "retry", s, g => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g a).setWidth 64 = v
  | _, _, _ => False

/-- From a shared counter at `a = rdi` holding `v`, the loop ends with `v` in
`rax` and `v + 1` in the counter. The block's snapshot `0 = n` (the variant
is `0`) is substituted before `simp_all`, which would otherwise rewrite every
`0` to `n`. -/
theorem casLoop_correctEnv (a : BitVec 64) (v : BitVec 64) :
    TripleEnv (SharedEnv.lastWrite [(a, 8)])
      (fun s g => s.regs.get64 .rdi = a ∧ Mem.loadInt s.dmem a 8 = none ∧ (g a).setWidth 64 = v)
      casLoop
      (fun s g => s.regs.get64 .rax = v ∧ (g a).setWidth 64 = v + 1)
      (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv (casLoop_table a v)
  cfg_cases_env [casLoop]
  intro n
  vcgen
  all_goals obtain ⟨_, rfl⟩ := ‹_ ∧ (0 : Nat) = n›
  all_goals simp_all [SharedEnv.lastWrite, rmwOp128, and_assoc]

omit layout [Executable.ValidLayout (layout casLoop)] in
/-- The layout of the counter, one 8-byte location, is well formed. -/
theorem casLoop_layout_wf (a : BitVec 64) : SharedLayout.WF [(a, 8)] where
  pos _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  le16 _ _ h := by rw [List.mem_singleton] at h; cases h; decide
  disj _ _ _ _ _ ha hb _ _ := by
    rw [List.mem_singleton] at ha hb
    cases ha; cases hb
    exact ⟨rfl, rfl⟩

/-- **The retry loop on the Promising machine.** A promise-free one-thread
run of `casLoop` from `d`, the counter at `(%rdi)` shared (no bytes in
`dmem`, its value `v` in the message-free memory `mem`): when the thread has
reached the end of the text, `rax` is `v` and the counter's last write is
`v + 1`. `casLoop_correctEnv` through `env_link_halt`; no access-discipline
premises. -/
theorem casLoop_promising (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.get64 .rdi, 8)] k → d.dmem.get? k = none)
    (h_slot : (mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)).setWidth 64 = v)
    (c : Config isa)
    (hc : ReachablePF A fuel ⟨#[Thread.init ({
      exe := layout casLoop
      endPc := (layout casLoop).addrOf casLoop.length
      st := (d, Kraken.Layout.start Directive)
      showPc := showPc } : State)], mem⟩ c)
    (t' : Thread isa) (ht : c.threads = #[t'])
    (hend : t'.st.st.2 = (layout casLoop).addrOf casLoop.length) :
    t'.st.st.1.regs.get64 .rax = v ∧
      (c.mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)).setWidth 64 = v + 1 := by
  have hnone : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = none := by
    cases hl : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 with
    | none => rfl
    | some x =>
      have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 (by decide)
      rw [hsplit _ ⟨_, 8, List.mem_singleton_self _, by simp⟩] at h0
      cases h0
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)
  have henv : envRel [(d.regs.get64 .rdi, 8)] g mem := by
    intro a n ha
    rw [List.mem_singleton] at ha
    cases ha
    rfl
  have hev := Program.instrStepEnv_of_tripleEnv (casLoop_correctEnv (d.regs.get64 .rdi) v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  obtain ⟨g', hrel', hP⟩ := env_link_halt _ (layout casLoop) (casLoop_layout_wf _) A fuel _ showPc d _
    mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim) (step1W_stop_of_end _) hev c hc t'
    ht hend
  obtain ⟨-, hrax, hslot⟩ := hP.resolve_right id
  refine ⟨hrax, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm

/-- **The retry loop terminates on the Promising machine.** From the same
start as `casLoop_promising`, every maximal promise-free run of the one-thread
machine is finite (whatever `fuel`) and ends with the thread at the end of the
text, `rax = v` and the counter's last write `v + 1`: no run diverges and none
gets stuck. `casLoop_correctEnv` through `env_link_terminates`. -/
theorem casLoop_terminates (A : Arch) (fuel : Nat) (showPc : Int64 → String) (d : MachineData)
    (v : BitVec 64) (mem : Memory) (hm : mem.msgs = #[])
    (hsplit : ∀ k, SharedLayout.Covers [(d.regs.get64 .rdi, 8)] k → d.dmem.get? k = none)
    (h_slot : (mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)).setWidth 64 = v) :
    Eventually (StepPF' A fuel) (fun (c : Config isa) => ∃ t' : Thread isa, c.threads = #[t'] ∧
        t'.st.st.2 = (layout casLoop).addrOf casLoop.length ∧ t'.st.st.1.regs.get64 .rax = v ∧
        (c.mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)).setWidth 64 = v + 1)
      (⟨#[Thread.init ({
        exe := layout casLoop
        endPc := (layout casLoop).addrOf casLoop.length
        st := (d, Kraken.Layout.start Directive)
        showPc := showPc } : State)], mem⟩ : Config isa) := by
  have hnone : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 = none := by
    cases hl : Mem.loadInt d.dmem (d.regs.get64 .rdi) 8 with
    | none => rfl
    | some x =>
      have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 (by decide)
      rw [hsplit _ ⟨_, 8, List.mem_singleton_self _, by simp⟩] at h0
      cases h0
  let g : BitVec 64 → BitVec 128 := fun _ => mem.finalVal (sharedLoc (d.regs.get64 .rdi) 8)
  have henv : envRel [(d.regs.get64 .rdi, 8)] g mem := by
    intro a n ha
    rw [List.mem_singleton] at ha
    cases ha
    rfl
  have hev := Program.instrStepEnv_of_tripleEnv (casLoop_correctEnv (d.regs.get64 .rdi) v)
    (s := d) (g := g) ⟨rfl, hnone, h_slot⟩
  have hnf : DirsNoFault (layout casLoop) := by dirs_no_fault casLoop
  refine eventually_weaken _ _ _ _ ?_ (env_link_terminates _ (layout casLoop) (casLoop_layout_wf _) A fuel _
    showPc d _ mem g _ hm hsplit henv (fun x hx => hx.elim And.left False.elim)
    (not_instrStepEnv_of_end _) hnf hev)
  rintro c ⟨t', ht, hend, g', hrel', hP⟩
  obtain ⟨-, hrax, hslot⟩ := hP.resolve_right id
  refine ⟨t', ht, hend, hrax, ?_⟩
  have := hrel' _ 8 (List.mem_singleton_self _)
  rw [← hslot]
  exact this.symm
