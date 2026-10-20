/-
Lifting a sequential procedure specification to a fragment specification,
x64. Generic (no program-specific names). The x64 twin of
`Lower/FragSpecProc.lean`, with the same names in `MachineWP` (the two files
cannot be co-imported, like the rest of the two ISAs' `MachineWP` layers).

A placement-independent `ProcSpec` on x64's sequential machine-founded wp
(`Kraken/MachineWP.lean`, total correctness) is a fragment specification
(`FragSpecEnvL`, `Lower/FragSpecCallsX64.lean`, partial correctness in an
environment) wherever the environment permits every fence, by x64's
`ProcSpec.env` (`Kraken/EnvWP.lean`) with the trivial environment invariant
and `Safely.of_eventually`:

* `FragSpecEnvL.ofProcSpec`: in any environment with
  `FenceInv (fun _ => True)` (every `Skips` environment, and every
  `FenceMonoX` one by `SharedEnv.FenceMonoX.fenceInv_true` below); the
  environment state is unconstrained and unread. `FragSpecEnv.ofProcSpec` is
  the one-fragment form.
* `FragSpecEnvL.ofProcSpecLe`: in a fence-monotone environment
  (`SharedEnv.FenceMonoX`, x64's name for the class), keeping
  `FenceMonoX.le` of the environment state across the call, so that a
  caller's fence-stable protocol facts survive it.

The statements are the AArch64 ones verbatim, except that the class is
`FenceMonoX`. A use: the pc-relative counting loop
`Kraken.Examples.PcLoopCfg.count_spec`, a sequential `ProcSpec`, as a fragment
spec in every fence-monotone environment (the `example`s at the end).

Machine of the lifted statements: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness.
-/
import Kraken.Promising.Lower.FragSpecCallsX64
import Kraken.X64.Examples.PcLoopCfg

open Kraken

namespace MachineWP

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every environment whose fences are permitted** (x64), at each value `x` of
its logical variable; the environment state is unconstrained and unread. -/
theorem FragSpecEnvL.ofProcSpec {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  ⟨fun hpl ra t g hp => Safely.of_eventually (eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1⟩)
    (Kraken.Executable.ProcSpec.env (h hpl) env hI x ra t g ⟨hp, trivial⟩))⟩

/-- The one-fragment form (x64). -/
theorem FragSpecEnv.ofProcSpec {frag : Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], Program.PlacedIn frag → cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnv env frag l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  ⟨fun hpl => ((FragSpecEnvL.ofProcSpec (frags := [frag]) (fun hpl' => h (hpl' frag (by simp))) env hI x).spec
    fun p hp => by simp only [List.mem_singleton] at hp; exact hp ▸ hpl)⟩

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every fence-monotone environment** (x64), with the environment state moved
only by fences (`FenceMonoX.le`). -/
theorem FragSpecEnvL.ofProcSpecLe {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) [env.FenceMonoX] (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t)
      (fun ra t g t' g' => Post x ra t t' ∧ SharedEnv.FenceMonoX.le g g') :=
  ⟨fun hpl ra t g hp => Safely.of_eventually (eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2⟩)
    (Kraken.Executable.ProcSpec.env (h hpl) env (I := SharedEnv.FenceMonoX.le g)
      (fun k g₁ h₁ => SharedEnv.FenceMonoX.fenceInv g k g₁ h₁) x ra t g ⟨hp, SharedEnv.FenceMonoX.refl g⟩))⟩

/-! ## A use: an existing sequential x64 procedure as a fragment spec

`PcLoopCfg.count_spec` (a counting loop that reads its own pc) is a
`ProcSpec` in every ambient code placing `count_body`; through the lemmas
above it is a fragment spec in every fence-monotone environment, once with
the environment unconstrained and once keeping `FenceMonoX.le`. -/

open Kraken.Examples.PcLoopCfg in
example (env : SharedEnv) [env.FenceMonoX] :
    FragSpecEnv env count_body "count" (fun ra t _ => t.retAddr = some ra)
      (fun _ t _ s _ => s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
        ∧ s.regs.get64 .rax = t.regs.get64 .rdi) :=
  FragSpecEnv.ofProcSpec (α := Unit) (fun hpl => count_spec hpl) env
    (SharedEnv.FenceMonoX.fenceInv_true env) ()

open Kraken.Examples.PcLoopCfg in
example (env : SharedEnv) [env.FenceMonoX] :
    FragSpecEnvL env [count_body] "count" (fun ra t _ => t.retAddr = some ra)
      (fun _ t g s g' => (s.regs.get64 .rsp = t.regs.get64 .rsp + 8 ∧ s.dmem = t.dmem
        ∧ s.regs.get64 .rax = t.regs.get64 .rdi) ∧ SharedEnv.FenceMonoX.le g g') :=
  FragSpecEnvL.ofProcSpecLe (α := Unit) (fun hpl => count_spec (hpl _ (by simp))) env ()

end MachineWP
