/-
**The fragment-spec constructor with a label rank,
AArch64.** Generic. `FragSpecEnv.of_cfg`
(`Lower/FragSpec.lean`) runs `cfgEnv_partial_fun`, whose zero-step back edges
must go forward in the text. A fragment with a zero-step back edge (the MS queue pilot's
`deq`: `cbz x5, deq` from `deq_ne`) orders its exits by a label rank `ρ`
instead (`EdgeRank`, `EnvG/MsQueueCfg.lean`):

- `FragSpecEnv.of_cfgRank T ρ hp hwf hinit hblocks`: `of_cfg` through
  `cfgEnv_partial_fun_edgeRank` (`Lower/KitCfg.lean`; the statement of
  the MS queue pilot's `cfgEnv_partial_fun_rank`), with the placement abstract. The
  block obligations are those of `cfg_cases_env_rank`.

Machine: the executable machine's per-thread environment semantics
(`Executable.instrStepEnv`), partial correctness (`Safely`).
-/
import Kraken.Promising.Lower.FragSpec
import Kraken.Promising.Lower.KitCfg

open Kraken
open Std.WP
open Kraken.Promising.SLR.EnvG.MsQueue (EdgeRank)

namespace MachineWP

variable {env : SharedEnv}

/-- **The constructor with a label rank** `ρ`: as `FragSpecEnv.of_cfg`, every
exit to a label of the fragment (the fall-through included) guarded by
`EdgeRank frag ρ` (smaller rank, or the same rank and later in the text, or a
changed state). -/
theorem FragSpecEnv.of_cfgRank {frag p' : Program} {l₀ : Label} {Pre : Int64 → MachineData → env.State → Prop}
    {Post : Int64 → MachineData → env.State → MachineData → env.State → Prop}
    (T : Int64 → MachineData → env.State → Label → MachineData → env.State → Prop) (ρ : Label → Nat)
    (hp : frag = Directive.label l₀ :: p') (hwf : Program.WF frag)
    (hinit : ∀ ra t g, Pre ra t g → T ra t g l₀ t g)
    (hblocks : ∀ [CodeEnv] (ra : Int64) (t : MachineData) (g : env.State), Pre ra t g →
      ∀ l blk, Program.blockAt frag l = some blk → ∀ (s₀ : MachineData) (g₀ : env.State),
      ⦃ fun s g' => T ra t g l s g' ∧ s = s₀ ∧ g' = g₀ ⦄ (⟨blk.body⟩ : EnvProgram env)
      ⦃ (match blk.next with
         | some l' => fun _ s g' => T ra t g l' s g' ∧ EdgeRank frag ρ l s₀ g₀ l' s g'
         | none => fun _ _ _ => False);
        fun a s g' => Table.ofLabelsEnv (fun l' s g' => (Program.blockAt frag l').isSome ∧ T ra t g l' s g'
          ∧ EdgeRank frag ρ l s₀ g₀ l' s g') a s g' ∨ (a = ra ∧ Post ra t g s g') ⦄) :
    FragSpecEnv env frag l₀ Pre Post := by
  refine ⟨fun hpl ra t g hpre => ?_⟩
  exact cfgEnv_partial_fun_edgeRank (T ra t g) ρ (E := fun a s g' => a = ra ∧ Post ra t g s g')
    (hblocks ra t g hpre) hp hwf hpl t g (hinit ra t g hpre)

end MachineWP
