/-
**Atomicity of a live fulfilment's write** (model-generic memory
lemmas, ISA-neutral), shared by the ticket rule link with a release-kind
ticket RMW (`EnvG/TicketRRuleLink.lean`) and the adjacency prototype
(`EnvG/AdjSpike.lean`). Moved from those files, same names and statements:

- `atomic_of_append`: an atomicity check up to the appended message is one on
  the memory before the append;
- `fulfil_write_atomicTR`: a `writeSuccs` outcome that fulfils the
  outstanding promise `ts` read at `tr` has `tr < ts` and passes `atomic` up
  to `ts`;
- `fulfil_write_atomic`: its second half (AdjSpike's statement).
-/
import Kraken.Promising.ReleasePrefixNT

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- An atomicity check up to the appended message is one on the memory
before the append. -/
theorem atomic_of_append {m : Memory} {w : Msg} {l : Loc} {tid : Nat} {tr : Time} (htr : tr ≤ m.last)
    (h : (m.append w).1.atomic l tid tr (m.last + 1) = true) : m.atomic l tid tr (m.last + 1) = true := by
  have hp := Memory.Prefix.append m w
  unfold Memory.atomic at h ⊢
  rw [hp.read? htr] at h
  cases hr : m.read? l tr with
  | none => rfl
  | some v =>
    rw [hr] at h
    simp only [List.all_eq_true, List.mem_range] at h ⊢
    intro i hi
    have := h i hi
    rwa [hp.get? (by omega_t)] at this

/-- **The fulfilling write of a live fulfilment, paired with a read at
`tr`, is atomic**: a `writeSuccs` outcome whose promise list no longer holds
the outstanding `ts` fulfils `ts`, after `tr` and atomically. -/
theorem fulfil_write_atomicTR {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {cx c' : Ctx} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {tr : Time} {extra : View}
    (hc' : c' ∈ writeSuccs A tid iv cx k xcl l v (some tr) extra) (htc : ts ∈ cx.prom) (htc' : ts ∉ c'.prom)
    (hle : ts ≤ cx.mem.last) : tr < ts ∧ cx.mem.atomic l tid tr ts = true := by
  rcases (mem_writeSuccs A tid).mp hc' with ⟨t0, -, w0, -, -, -, -, hok, rfl⟩ | ⟨-, rfl⟩
  · obtain rfl : ts = t0 := Classical.byContradiction fun hne =>
      htc' ((List.mem_erase_of_ne hne).mpr htc)
    exact hok.2 tr rfl
  · exfalso
    have hne : ts ≠ cx.mem.last + 1 := by omega_t
    exact htc' ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ htc))

/-- **A fulfilling RMW write is atomic with its read**: a `writeSuccs`
outcome with read `a` whose promise list no longer holds the outstanding
promise `ts ≤ |M|` fulfils `ts`, so `WriteOk` checked `atomic` up to `ts`. -/
theorem fulfil_write_atomic {A : Arch} {tid : Nat} {iv : InstrViews} {ts : Time} {cx c' : Ctx} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {a : Time} {extra : View}
    (hc' : c' ∈ writeSuccs A tid iv cx k xcl l v (some a) extra) (htc : ts ∈ cx.prom) (htc' : ts ∉ c'.prom)
    (hle : ts ≤ cx.mem.last) : cx.mem.atomic l tid a ts = true :=
  (fulfil_write_atomicTR hc' htc htc' hle).2

end Kraken.Promising.SLR.EnvG
