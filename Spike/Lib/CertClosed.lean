/-
**No promise under a closed certification invariant**, ISA-free: if a
predicate `Q` of solo configurations is closed under the certification steps
(`ThreadStepC`) and no step changes the promise set, a certified thread in
`Q` has no promise (`prom_nil_of_closed`): along the certifying run the set
is constant, and the run ends with none. The abort stub's tail (after its
`write`, only private stores and `exit_group`) is such a `Q`
(`Spike/Lib/A64TailNoFul.lean`, `Spike/Lib/X64TailNoFul.lean`).
-/
import Scc.Sem.Ext

namespace Spike.Lib

open Kraken Kraken.Promising
open Scc.Sem (CertSem ThreadStepC ThreadNPC CertOkC)

/-- **A solo run inside a closed `Q` keeps the promise set.** -/
theorem ThreadNPC.prom_eq {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat} {Q : Thread I × Memory → Prop}
    (hQ : ∀ x y, Q x → ThreadStepC A cs tid x y → Q y ∧ y.1.prom = x.1.prom) {x y : Thread I × Memory}
    (h : ThreadNPC A cs tid x y) (hx : Q x) : y.1.prom = x.1.prom := by
  induction h with
  | refl => rfl
  | step hs _ ih =>
    obtain ⟨hq, hp⟩ := hQ _ _ hx hs
    rw [ih hq, hp]

/-- **A certified thread in a closed `Q` has no promise**: its certifying
run keeps the promise set (`ThreadNPC.prom_eq`) and ends with none. -/
theorem prom_nil_of_closed {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat} {Q : Thread I × Memory → Prop}
    (hQ : ∀ x y, Q x → ThreadStepC A cs tid x y → Q y ∧ y.1.prom = x.1.prom) {t : Thread I} {mem : Memory}
    (hq : Q (t, mem)) (hc : CertOkC A cs tid t mem) : t.prom = [] := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  have := ThreadNPC.prom_eq hQ hrun hq
  simp only at this
  rw [← this, hp]

end Spike.Lib
