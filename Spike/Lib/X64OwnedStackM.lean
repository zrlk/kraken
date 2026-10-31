/-
**A stack range owned from its words' loads** (x86-64): `Owned` (every
aligned word of the range in the private memory, the range in the pool)
from `Ret0.StackM` (every aligned word of the range loads) on the thread's
machine data; and back.

- `owned_of_stackM`: `rS` in the pool and `StackM rS` of the thread's
  machine data give `Owned Λ rS`.
- `stackM_of_owned`: `Owned Λ rS` gives `StackM rS` of the thread's machine
  data.
- `owned_not_stackM`: `Owned Λ rS` refutes `¬ StackM rS` (a take site's
  fact that the range is not yet taken).
- `unowned_not_stackM`: `Unowned rS` gives `¬ StackM rS` (an aligned range
  of a word or more).

x86-64 twin of `Spike/Lib/A64OwnedStackM.lean` (same names, `X64` namespaces).
-/
import Spike.Lib.X64Consumer
import Spike.Lib.X64Ret0
import Spike.Lib.X64OwnedPz

namespace Spike.Lib.X64Consumer

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64

/-- **`Owned` from `StackM`**: `privLoad` is the 8-byte load, mapped. -/
theorem owned_of_stackM {Λ : Scc.Sem.Layout} {rS : Range} {s : State} (hsub : rS.Sub Λ.stackPool)
    (hm : Spike.Lib.X64.Flow.Ret0.StackM rS s.st.1) : Owned Λ rS s :=
  ⟨hsub, fun a h8 h0 h7 => by simpa [privLoad, Option.isSome_map] using hm a h8 h0 h7⟩

/-- **`StackM` from `Owned`.** -/
theorem stackM_of_owned {Λ : Scc.Sem.Layout} {rS : Range} {s : State} (h : Owned Λ rS s) :
    Spike.Lib.X64.Flow.Ret0.StackM rS s.st.1 :=
  fun a h8 h0 h7 => by simpa [privLoad, Option.isSome_map] using h.2 a h8 h0 h7

/-- **An owned range is in private memory**: `Owned` refutes `¬ StackM`. -/
theorem owned_not_stackM {Λ : Scc.Sem.Layout} {rS : Range} {s : State} (h : Owned Λ rS s)
    (hn : ¬ Spike.Lib.X64.Flow.Ret0.StackM rS s.st.1) : False :=
  hn (stackM_of_owned h)

/-- **An unowned range is not in private memory** (its first word does not
load, `pz_of_unowned`). -/
theorem unowned_not_stackM {rS : Range} {s : State} (h : Unowned rS s) (hal : rS.lo % 8 = 0)
    (h8 : 8 ≤ rS.size) : ¬ Spike.Lib.X64.Flow.Ret0.StackM rS s.st.1 := fun hs => by
  have := hs rS.lo hal ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
  rw [show Mem.loadInt s.st.1.dmem (BitVec.ofNat 64 rS.lo) 8 = none from pz_of_unowned (by omega) h] at this
  cases this

end Spike.Lib.X64Consumer

/-- info: 'Spike.Lib.X64Consumer.owned_of_stackM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Consumer.owned_of_stackM

/-- info: 'Spike.Lib.X64Consumer.stackM_of_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Consumer.stackM_of_owned

/-- info: 'Spike.Lib.X64Consumer.owned_not_stackM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Consumer.owned_not_stackM

/-- info: 'Spike.Lib.X64Consumer.unowned_not_stackM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Consumer.unowned_not_stackM
