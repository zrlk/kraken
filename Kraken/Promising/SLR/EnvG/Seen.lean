/-
Load-acquire transfer, **read side**. ISA-neutral.

A message read with an acquire id held is acquired *in the assertion
layer*, without a rule change: the erasure itself gives the slot.

- `slot_of_held`: the generic form of MP's `slot_of_seen`. Under any erasure,
  a message of `x` whose value is impure for `x`'s release predicate is in
  release mode (`Erase.pure`), so it carries a slot for every acquire id of
  `x` held (once) in the total (`Erase.slotsDom`), satisfying its predicate at
  the message (`Erase.slotsPred`).
- `slot_of_seen`: the same for a pair `((x, ts), ι)` recorded in `EnvG.State.seen`
  while thread `tid` holds `ι`.
- `read_owned`: `read_max_slot` packaged with the environment's `ReadAt`
  facts: a load of a location whose whole permission sits in a slot of a held
  id returns the slot's maximal write, under the clean erasure (`cl`).

**Write side** (writing with a permission acquired by a load): not provided.
It is not expressible additively on the existing `Erase`/`NPSafe` (§2.3), and is
recorded as a model gap.
-/
import Kraken.Promising.SLR.EnvG.Facts
import Kraken.Promising.SLR.StoreHelpers

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **The slot of a held id at an impure message** (generic `slot_of_seen`). -/
theorem slot_of_held (E : Erase rF g T c) {k : Key} {ι : PredId} (hacq : (total rF g c).acq k.1 ι = 1) {v : Val}
    (hrd : c.mem.read? k.1 k.2 = some v) (himp : ¬ Pred.Pure (g.rel k.1) v) :
    ∃ s ∈ g.u, s.key = k ∧ s.id = ι ∧ (g.acqPred ι).P v c.mem k.2 s.res := by
  have hrm : k ∈ g.relMsgs := Classical.byContradiction fun hn => himp (E.pure k.1 k.2 v hrd hn)
  obtain ⟨s, hs, hkey, hid⟩ := (E.slotsDom k ι).mpr ⟨hrm, .inl hacq⟩
  have hP := E.slotsPred s hs v (by rw [hkey]; exact hrd)
  rw [hid, hkey] at hP
  exact ⟨s, hs, hkey, hid, hP⟩

/-- An acquire id held once by a thread is held once in the total. -/
theorem total_acq_of_thread (E : Erase rF g T c) {i : Nat} (hi : i < c.threads.size) {x : Loc} {ι : PredId}
    (h : (rF i).acq x ι = 1) : (total rF g c).acq x ι = 1 := by
  have h1 := sub_acq_le (sub_total_thread (rF := rF) (g := g) (c := c) hi) x ι
  have h2 := E.valid.2 x ι
  omega

/-- **The slot of a seen message** whose id thread `tid` still holds (with
resource `r`): the read side of load-acquire transfer (§2.2). -/
theorem slot_of_seen {tid : Nat} {r : Res} (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    {k : Key} {ι : PredId} (hacq : r.acq k.1 ι = 1) {v : Val} (hrd : c.mem.read? k.1 k.2 = some v)
    (himp : ¬ Pred.Pure (g.rel k.1) v) :
    ∃ s ∈ g.u, s.key = k ∧ s.id = ι ∧ (g.acqPred ι).P v c.mem k.2 s.res :=
  slot_of_held E (total_acq_of_thread E hn (by rw [setRes_self]; exact hacq)) hrd himp

/-- `seenAfter` records exactly the held ids at the message read. -/
theorem mem_seenAfter {A : Arch} {k : LoadKind} {σ : State I} {g' : Ghost} {l : Loc} {tr : Time}
    {p : Key × PredId} (h : p ∈ seenAfter A k σ g' l tr) :
    p ∈ σ.seen ∨ ((A.loadKind k).isAcquire = true ∧ p.1 = (l, tr) ∧ p.2 ∈ g'.acqIds σ.r.acq l) := by
  unfold seenAfter at h
  split at h
  · rcases List.mem_append.mp h with h | h
    · exact .inl h
    · obtain ⟨ι, hι, rfl⟩ := List.mem_map.mp h
      exact .inr ⟨‹_›, rfl, hι⟩
  · exact .inl h

/-- **A read of an owned location** (§2.2, `read_max_slot` with the
environment's read facts): under the clean erasure at the read's anchor, if
the slot `s` holds all of `x` with maximal write `(v0, ts)`, the thread holds
`s`'s id once, and `ts` is within the read bound, the read returns
`(v0, ts)`. -/
theorem read_owned {A : Arch} {tid : Nat} {r : Res} (E : Erase (setRes rF tid r) g (fun _ => False) c)
    (hn : tid < c.threads.size) {s : Slot} (hs : s ∈ g.u) {x : Loc} (hq : (s.res.wr x).q = 1)
    (hacq : r.acq s.key.1 s.id = 1) {v0 val : Val} {ts tr : Time} (hX : (s.res.wr x).X (v0, ts))
    (hmax : ∀ p, (s.res.wr x).X p → p.2 ≤ ts) {vs : Views} {k : LoadKind}
    (hrd : ReadAt A tid vs c k x tr val) (hB : ts ≤ readBound A vs k x) : tr = ts ∧ val = v0 := by
  obtain ⟨t, ht⟩ : ∃ t, c.threads[tid]? = some t := ⟨c.threads[tid], Array.getElem?_eq_getElem hn⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  exact read_max_slot E ht hs hq (by rw [setRes_self]; exact hacq) hX hmax hrd.val hp hrd.window hB

end Kraken.Promising.SLR.EnvG
