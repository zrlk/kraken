/-
Theorem 1′'s temporary scope `Config.NTFree` (`SLR/Theorem1.lean`) for any
architecture, `Arch.tso` included, for programs that make no non-temporal
store.

Under `Arch.armv8` the scope is vacuous (`Config.ntFree_armv8`): no store is
ever non-temporal. Under `Arch.tso` it fails exactly for programs that run a
non-temporal store (x86 `movnti`, Toy's `st .nt`). Whether a program does is
a property of the program, stated here semantically: a predicate `P` on
thread states that holds initially, is closed under the leaves of every
instruction's event tree, and under which the instruction's tree makes no
non-temporal store (`EvTree.NoNT`). This is a per-program fact, checked once
per program (e.g. `X64SpinNoNT.spinWorker_noNTInv` for the x64 spinlock
worker), and it is the whole content of the scope `H = Config.NTFree`: it
does not restrict the theorem any further.

## Contents

- `ISA.NoNTInv A P`: `P` is a state invariant of the ISA's thread steps
  along which no instruction makes a non-temporal store.
- `ISA.NoNTInv.top`: under `Arch.armv8`, `P := True` is one (every program).
- `Reachable.noNTInv`: along every machine path from a configuration whose
  threads satisfy `P` and have `vwOldNT = 0`, every thread satisfies `P` and
  keeps `vwOldNT = 0` (the `Reachable.vwOldNT_armv8` argument, with
  `Thread.NextNoNT` from `P` instead of from the architecture).
- `Config.ntFree_of_noNTInv`: every configuration reachable from
  `Config.init states initMem` with all `states` in `P` satisfies
  `Config.NTFree A`.
-/
import Kraken.Promising.SLR.Theorem1

namespace Kraken.Promising

variable {I : ISA}

/-- **The program makes no non-temporal store.** `P` is a predicate on
thread states that is closed under one instruction (every leaf of the
instruction's event tree satisfies `P`) and under which the instruction's
tree makes no non-temporal store. A program satisfies it when its initial
states do (`Config.ntFree_of_noNTInv`). -/
structure ISA.NoNTInv (I : ISA) (A : Arch) (P : I.State → Prop) : Prop where
  /-- The instruction at a `P` state makes no non-temporal store. -/
  noNT : ∀ s, P s → ∀ tree, I.exec s = some tree → tree.NoNT A
  /-- Every leaf of the instruction at a `P` state satisfies `P`. -/
  step : ∀ s, P s → ∀ tree, I.exec s = some tree → tree.All P

/-- Under `Arch.armv8` every program makes no non-temporal store. -/
theorem ISA.NoNTInv.top (I : ISA) : I.NoNTInv Arch.armv8 (fun _ => True) :=
  ⟨fun _ _ tree _ => tree.noNT_armv8, fun _ _ tree _ => EvTree.All.of_forall (fun _ => trivial) tree⟩

/-- The per-thread invariant of `Reachable.noNTInv`. -/
def Config.NoNTInvAt (P : I.State → Prop) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → P t.st ∧ t.views.vwOldNT = 0

/-- Along every `ReachableK` path the invariant holds and no thread makes a
non-temporal store (the `ReachableK` twin of `Reachable.noNTInv`). -/
theorem Live.Bridge.ReachableK.noNTInv {A : Arch} {P : I.State → Prop} (hP : I.NoNTInv A P)
    {c c' : Config I} (h : Live.Bridge.ReachableK A c c') (h0 : Config.NoNTInvAt P c) :
    Config.NoNTInvAt P c' := by
  induction h with
  | refl => exact h0
  | @step c c1 c2 hs _ ih =>
    apply ih
    intro i t ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        obtain ⟨hPj, hnt⟩ := h0 j tj hj
        exact ⟨stepOne_leaf A hstep ho (fun tree hex => hP.step _ hPj tree hex),
          (stepOne_vwOldNT _ hstep ho (fun tree hex => hP.noNT _ hPj tree hex)).trans hnt⟩
      · exact h0 i t ht
    | @promise j tj p hj _ =>
      rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        exact h0 j tj hj
      · exact h0 i t ht

/-- **Along every path the invariant holds and no thread makes a
non-temporal store** (`vwOldNT` stays `0`). -/
theorem Reachable.noNTInv {A : Arch} [I.LawfulState] {P : I.State → Prop} (hP : I.NoNTInv A P)
    {fuel : Nat} {c c' : Config I} (h : Reachable A fuel c c') (h0 : Config.NoNTInvAt P c) :
    Config.NoNTInvAt P c' :=
  (Live.Bridge.ReachableK.of_reachable h).noNTInv hP h0

/-- The initial configuration satisfies the invariant when its states do. -/
theorem Config.noNTInvAt_init {P : I.State → Prop} {states : List I.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, P s) :
    Config.NoNTInvAt P (Config.init states initMem) := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, hst, rfl⟩ := h
  exact ⟨hs st (List.mem_of_getElem? hst), rfl⟩

/-- `Config.ntFree_of_noNTInv` along `ReachableK` (the `ReachableK` twin, fuel-free). -/
theorem Config.ntFree_of_noNTInvK {A : Arch} {P : I.State → Prop}
    (hP : I.NoNTInv A P) {states : List I.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, P s) {c : Config I}
    (hc : Live.Bridge.ReachableK A (Config.init states initMem) c) : c.NTFree A := by
  intro i t ht
  obtain ⟨hPt, hnt⟩ := hc.noNTInv hP (Config.noNTInvAt_init hs) i t ht
  exact ⟨fun _ => .inl hnt, fun tree hex => hP.noNT _ hPt tree hex⟩

/-- **Theorem 1′'s scope for programs without non-temporal stores**, under
any architecture: every configuration reachable from `Config.init states
initMem`, with every initial state in a `ISA.NoNTInv` invariant `P`,
satisfies `Config.NTFree A`. -/
theorem Config.ntFree_of_noNTInv {A : Arch} [I.LawfulState] {P : I.State → Prop}
    (hP : I.NoNTInv A P) {fuel : Nat} {states : List I.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, P s) {c : Config I}
    (hc : Reachable A fuel (Config.init states initMem) c) : c.NTFree A :=
  Config.ntFree_of_noNTInvK hP hs (.of_reachable hc)

end Kraken.Promising
