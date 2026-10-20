/-
**Helpers for concrete instances, ISA-neutral**.

- `Config.init_mem` (`@[simp]`): the memory of `Config.init states initMem`
  is `initMem` with no message, for any thread list. The initial-memory
  hypotheses of the public theorems (`(Config.init ss m).mem.initVal ⟨x, 4⟩ =
  0`) then reduce to a closed `decide` even when `ss` is not a literal (e.g.
  `List.replicate N s`): `by simp only [Config.init_mem]; decide`.
-/
import Kraken.Promising.Machine

namespace Kraken.Promising

variable {I : ISA}

/-- **The initial configuration's memory**: the initial values `initMem`, no
message (independent of the thread list). -/
@[simp] theorem Config.init_mem (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem).mem = { init := initMem, msgs := #[] } := rfl

end Kraken.Promising
