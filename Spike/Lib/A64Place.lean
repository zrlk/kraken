/-
**A node's placed environment on AArch64**: `A64Consumer.Placed` (the
`env_rep`, `env_total` and `env_imm` components of one frame) from the
lowering's symbolic environment (`Spike.Lib.Form.SRep`) through
`Spike.Lib.Place`, an immediate operand at the immediate word place the
layout's table (`Layout.imms`, the generated `<pfx>Imms`) names.
-/
import Spike.Lib.A64Consumer
import Spike.Lib.Place

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Form

/-- **The environment of a control is placed** when a symbolic environment
`sE` represents it with every register operand valued at its place `plr`
and every immediate at itself, every free variable of the term has a word
place for each word, and the layout's immediate table agrees with every
immediate operand of `sE` at the term. -/
theorem placed_of_srep {Λ : Scc.Sem.Layout} {lbl : Lbl} {s : State} {c : Ctl} {sE : SEnv}
    {val : Scc.IR.Operand → Option Nat} {plr : Scc.IR.Reg → Option (Place (machine (kernel 1)).I.RegId)}
    (h : SRep lbl val sE c.env) (hv : ∀ r p, plr r = some p → val (.reg r) = placeVal (machine (kernel 1)) s p)
    (hi : ∀ n : UInt64, val (.imm n) = some n.toNat)
    (hall : ∀ x ∈ exprFv c.term, ∃ t pls, lookupS sE x = some (t, pls) ∧ ∀ pl ∈ pls, (wordPlace plr pl).isSome)
    (himm : ∀ b ∈ sE, ∀ k (n : UInt64), b.2.2[k]? = some (.one (.imm n)) → Λ.imms c.term b.1 k = some n.toNat) :
    Placed Λ lbl s c :=
  ⟨envMap plr sE, h.env_rep hv hi, h.env_total hall, envMap_imm himm⟩

end Spike.Lib.A64Consumer
