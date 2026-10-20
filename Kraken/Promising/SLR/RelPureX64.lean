/-
Conjunct (i) of option (A) (`SLR/RelPure.lean`) for the x64 spinlock.

Under `Arch.tso` every non-NT store is a release (`tso_storeKind_rel`) and
the worker makes no NT store (`spinWorker_noNTInv`), so the worker's trees
have no non-release write at all: conjunct (i) holds in its **witness form**
for the existing rule, with no cell re-proved (`spinRuleXK`, through
`ThreadRuleRX.toK`), and in its witness-free form (`spin_relPure`). Proved, no
`sorry`.
-/
import Kraken.Promising.SLR.RelPure
import Kraken.Promising.SLR.X64SpinRule

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- **The worker's trees have no non-release write** under `Arch.tso`, at
every state its rule's `wp` is asked about. -/
theorem spin_noNonRel (P : Params) (tid : Nat) (H : HardCellsX P Arch.tso tid) :
    NoNonRel (spinRuleX P Arch.tso tid H) := by
  intro cl c₀ c r g₀ g t tree h he hle ht hex
  obtain ⟨-, t', ht', hF, -, i, hp, hph, -⟩ := inv_env h.1 he hle
  rw [ht] at ht'
  obtain rfl : t = t' := Option.some.inj ht'
  have hi : i ≤ 14 := by
    rcases Phase.pos hph with h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  have hpc : SpinPc t.st := ⟨hF.exe, hF.decls, i, hi, hp⟩
  exact EvTree.NoNT.relWrites tso_storeKind_rel (spinWorker_noNTInv.noNT t.st hpc tree hex)

/-- **(i), witness form, for the x64 spinlock**: its existing rule is a
`ThreadRuleRXK`. -/
def spinRuleXK (P : Params) (tid : Nat) (H : HardCellsX P Arch.tso tid) :
    ThreadRuleRXK (I := isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid :=
  ThreadRuleRX.toK (spinRuleX P Arch.tso tid H) (spin_noNonRel P tid H)

/-- **(i‴), witness-free, for the x64 spinlock.** -/
theorem spin_relPure (P : Params) (tid : Nat) (H : HardCellsX P Arch.tso tid) :
    RelPure (spinRuleX P Arch.tso tid H) :=
  relPure_of_noNonRel _ (spin_noNonRel P tid H)

end Kraken.Promising.SLR.X64SpinInv
