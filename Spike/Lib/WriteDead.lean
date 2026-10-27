/-
**The output `write` is a certification dead end** (ISA-neutral; with
`write` ending a certifying run, `Kernel.prom_nil_of_write`): `certSem`
has no step at a `write` (`certStep_write_none`). The consumers'
certification premises at the output `write` follow from it:
`Spike/Lib/A64WriteDead.lean`, `Spike/Lib/X64WriteDead.lean`.

- `certStep_write_none`: no outcome of a certification step at a `write`.
-/
import Scc.Sem.CertSys

namespace Spike.Lib.WriteDead

open Kraken Kraken.Promising
open Scc.Sem Scc.Sem.Kernel

variable {I : ISA} {K : Abi I}

/-- **No certification step at a `write`**: `certSem`'s execution there is
empty (`soloExec`: a `write` ends a certifying run), so a step
has no outcome. -/
theorem certStep_write_none {A : Arch} {μ : Marks} {x : KState} {tid : Nat} {t : Thread I} {mem : Memory}
    {fd buf n : Nat} {outs : List (Except String (Outcome I))} {o : Outcome I}
    (hs : siteAt K μ t.st = none) (ha : K.atSys t.st = true)
    (hd : decode K.nrs (K.nr t.st) (K.arg t.st) = some (.write fd buf n))
    (hso : (certSem K A μ x tid).step A t tid mem = some outs) (ho : .ok o ∈ outs) : False := by
  obtain ⟨tree, st, c', hex, hr, -, -⟩ := stepOneWith_runOut A hso ho
  have hex' : (certSem K A μ x tid).exec t.st = some (leaves []) := by
    change soloExec K A μ x tid t.st = _
    simp only [soloExec, hs, ha, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, -⟩ := (Lower.run_choose_iff A tid _).mp hr
  exact i.elim0

end Spike.Lib.WriteDead
