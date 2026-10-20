/-
Lifting a sequential procedure specification to a fragment specification,
AArch64. Generic (no program-specific names).

A placement-independent `ProcSpec` on the sequential machine-founded wp
(`MachineWP`, total correctness) is a fragment specification
(`FragSpecEnvL`, partial correctness in an environment) wherever the
environment permits every fence, by `ProcSpec.env` with the trivial
environment invariant and `Safely.of_eventually`:

* `FragSpecEnvL.ofProcSpec`: in any environment with
  `FenceInv (fun _ => True)` (every `Skips` or `FenceMono` environment,
  `SLR/EnvG/FenceInvTrue.lean`); the environment state is unconstrained and
  unread. `FragSpecEnv.ofProcSpec` is the one-fragment form.
* `FragSpecEnvL.ofProcSpecLe`: in a fence-monotone environment, keeping
  `FenceMono.le` of the environment state across the call, so that a caller's
  fence-stable protocol facts survive it.

Machine of the lifted statements: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness.
-/
import Kraken.Promising.Lower.FragSpecCalls
import Kraken.Promising.SLR.EnvG.FenceInvTrue

open Kraken

namespace MachineWP

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every environment whose fences are permitted**, at each value `x` of its
logical variable; the environment state is unconstrained and unread. -/
theorem FragSpecEnvL.ofProcSpec {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  ⟨fun hpl ra t g hp => Safely.of_eventually (eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1⟩)
    (Kraken.Executable.ProcSpec.env (h hpl) env hI x ra t g ⟨hp, trivial⟩))⟩

/-- The one-fragment form. -/
theorem FragSpecEnv.ofProcSpec {frag : Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], Program.PlacedIn frag → cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnv env frag l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  ⟨fun hpl => ((FragSpecEnvL.ofProcSpec (frags := [frag]) (fun hpl' => h (hpl' frag (by simp))) env hI x).spec
    fun p hp => by simp only [List.mem_singleton] at hp; exact hp ▸ hpl)⟩

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every fence-monotone environment**, with the environment state moved only by
fences (`FenceMono.le`). -/
theorem FragSpecEnvL.ofProcSpecLe {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) [env.FenceMono] (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t)
      (fun ra t g t' g' => Post x ra t t' ∧ SharedEnv.FenceMono.le g g') :=
  ⟨fun hpl ra t g hp => Safely.of_eventually (eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2⟩)
    (Kraken.Executable.ProcSpec.env (h hpl) env (I := SharedEnv.FenceMono.le g)
      (fun k g₁ h₁ => SharedEnv.FenceMono.fenceInv g k g₁ h₁) x ra t g ⟨hp, SharedEnv.FenceMono.refl g⟩))⟩

end MachineWP
