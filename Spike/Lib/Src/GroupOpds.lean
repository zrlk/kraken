import Spike.Lib.Src.AbortImm2
import Spike.Lib.Src.NJLB2
import Spike.Lib.Src.LitPt2
import Spike.Lib.LowerEnv
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.NJLBEnv2

/-!
**A caller's facts at a call, and freshness at `ofEnv2`** (ISA-neutral).
The groupings' lemmas (`grp_opds`, `group_opds`, `group_one`,
`sevalAt_ofEnv2_one`) are `GroupPl`'s and `NJLBEnv2`'s.

- `EnvQ`: a caller's facts against the walk at a call (`NJB` without the
  node);
- `Fresh.ofEnv2`: the placed registers are off the fresh destinations
  (`fresh_ofEnv2` under `ofEnv`'s `Fresh.ofEnv` naming).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Spike.Lib.Form (WordPl grp group sevalAt lookupS)

/-- **The caller's facts against the walk** at an environment: the walk's
layouts kept (`EnvLit`), its numbers in 64 bits (`EnvSmall`), its slices,
buffers and known values (`EnvB`, within the labels' sizes `lsize`) at some
labels and memory with `MemB`. -/
def EnvQ (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) (lsize : WeakMem.AllocLabel → Nat)
    (env : TermRun.Env) : Prop :=
  EnvLit lits env ∧ EnvSmall env ∧ ∃ L sm B, EnvB lits cs bufs L sm lsize env ∧ MemB L sm B

/-- **The placed registers of a fresh environment are off its fresh
destinations** (`Fresh.ofEnv` at the grouped `ofEnv2`). -/
theorem Fresh.ofEnv2 {env : Scc.Lower.Env} {n : Nat} (h : Fresh env n) (x : String) :
    ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ Scc.Lower.Inv.regName x n :=
  fresh_ofEnv2 h x

end Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.Fresh.ofEnv2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.Fresh.ofEnv2
