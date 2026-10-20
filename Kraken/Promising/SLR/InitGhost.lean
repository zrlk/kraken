/-
**Program-agnostic initial erasure.** `SpinInit.erase_init` fixes one lock
(one release-mode location with update id `0`) and an initial total that
holds no acquire id; this file drops both restrictions.

- `initGhost rel acqTab rls`: release predicates `rel` (arbitrary on every
  location), acquire table `acqTab`, and a list `rls` of release-mode
  initial locations: `(x, ι, s)` puts the initial message of `x` in release
  mode with update id `ι` and slot resource `s`. No pending mark, no claim.
  `Spinlock.spinGhost` and `Mp.mpGhost` are instances.
- `erase_initGhost`: initial erasure for `initGhost`. The initial total may
  hold acquire ids anywhere except at the release-mode locations.
- `initGhostAcq rel acqTab rlocs hld` / `erase_initGhostAcq`: the
  variant for acquire-only release-mode locations: the initial messages of
  `rlocs` are in release mode, their slots `hld` (`(x, ι, s)`: a slot of
  `x`'s initial message for the **held** acquire id `ι`, resource `s`) are
  exactly the acquire ids the initial total holds there, and no location
  has update ids. `MpInc.mpGhostI` is an instance (`erase_mpIncInit`).
- `relAcq_single`: the `relAcq` side condition when every location carries
  at most one held or update id, whose predicate is the location's release
  predicate (otherwise the release predicate holds of the empty resource
  only).
-/
import Kraken.Promising.SLR.SpinInit

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- **A generic initial ghost**: release predicates `rel`, acquire table
`acqTab`, and the release-mode initial locations `rls`, each `(x, ι, s)` the
initial message of `x` with update id `ι` and slot resource `s`. -/
def initGhost (rel : Loc → Pred) (acqTab : List Pred) (rls : List (Loc × PredId × Res)) : Ghost where
  rel := rel
  acqTab := acqTab
  u := rls.map fun e => ⟨(e.1, 0), e.2.1, e.2.2⟩
  relMsgs := rls.map fun e => (e.1, 0)
  pend := []
  upd x := (rls.filter fun e => e.1 = x).map fun e => e.2.1
  claims := []

theorem initGhost_pend {rel : Loc → Pred} {acqTab : List Pred} {rls : List (Loc × PredId × Res)} :
    ∀ ts, ts ∉ (initGhost rel acqTab rls).pend := fun _ h => by cases h

/-- **`relAcq` from one id per location**: if the held and update ids of
`x` are none (and `rel x` holds of the empty resource only) or a single id
whose acquire predicate is `rel x`, the release predicate splits. -/
theorem relAcq_single {g : Ghost} {A : Loc → PredId → Nat} {x : Loc}
    (h : (g.acqIds A x ++ g.upd x = [] ∧ ∀ v m V r, (g.rel x).P v m V r → r = Res.unit) ∨
      ∃ ι, g.acqIds A x ++ g.upd x = [ι] ∧ g.acqPred ι = g.rel x) :
    ∀ v m V r, (g.rel x).P v m V r → Pred.SepList (g.acqPreds A x ++ g.updPreds x) v m V r := by
  intro v m V r hr
  have heq : g.acqPreds A x ++ g.updPreds x = (g.acqIds A x ++ g.upd x).map g.acqPred := by
    rw [List.map_append]; rfl
  rw [heq]
  rcases h with ⟨h0, hu⟩ | ⟨ι, h1, hp⟩
  · rw [h0]; exact hu v m V r hr
  · rw [h1]
    refine ⟨r, Res.unit, (Res.op_unit r).symm, ?_, rfl⟩
    rw [hp]; exact hr

/-- **Initial erasure for `initGhost`**: the release-mode locations `rls`
are distinct and hold no acquire id in the initial total; held acquire ids
and slot ids are allocated; release predicates split (`relAcq`, e.g. from
`relAcq_single`); the write set of every tracked location is its initial
message; the relaxed initial messages are pure; every slot satisfies its
acquire predicate at the initial value (view `0`). -/
theorem erase_initGhost {rF : Nat → Res} {states : List I.State} {initMem : List (Loc × Val)}
    {rel : Loc → Pred} {acqTab : List Pred} {rls : List (Loc × PredId × Res)} (T : Nat → Prop)
    (hnd : (rls.map (·.1)).Nodup)
    (hvalid : (total rF (initGhost rel acqTab rls) (Config.init states initMem)).valid)
    (hacqIds : ∀ x ι, 1 ≤ (total rF (initGhost rel acqTab rls) (Config.init states initMem)).acq x ι →
      ι < acqTab.length)
    (hrelAcq : ∀ x v m V r, (rel x).P v m V r →
      Pred.SepList ((initGhost rel acqTab rls).acqPreds
        (total rF (initGhost rel acqTab rls) (Config.init states initMem)).acq x ++
        (initGhost rel acqTab rls).updPreds x) v m V r)
    (hwrites : ∀ x, 0 < ((total rF (initGhost rel acqTab rls) (Config.init states initMem)).wr x).q → ∀ p,
      ((total rF (initGhost rel acqTab rls) (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0))
    (hpure : ∀ x, x ∉ rls.map (·.1) → Pred.Pure (rel x) ((Config.init states initMem).mem.initVal x))
    (hslotIds : ∀ e ∈ rls, e.2.1 < acqTab.length)
    (hnoacq : ∀ e ∈ rls, ∀ ι, (total rF (initGhost rel acqTab rls) (Config.init states initMem)).acq e.1 ι = 0)
    (hslots : ∀ e ∈ rls, (acqTab.getD e.2.1 Pred.bot).P ((Config.init states initMem).mem.initVal e.1)
      (Config.init states initMem).mem 0 e.2.2) :
    Erase rF (initGhost rel acqTab rls) T (Config.init states initMem) := by
  refine Erase.init hvalid ?_ hacqIds hrelAcq hwrites ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- slot ids
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact hslotIds e he
  · -- relaxed initial messages are pure
    intro x hx
    refine hpure x fun hm => hx ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact List.mem_map_of_mem (f := fun e : Loc × PredId × Res => (e.1, (0 : Time))) he
  · -- release messages are initial
    intro k hk
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hk
    rfl
  · -- slots are distinct
    show ((rls.map fun e => (⟨(e.1, 0), e.2.1, e.2.2⟩ : Slot)).map fun s => (s.key, s.id)).Nodup
    rw [List.map_map]
    exact List.pairwise_map.2 ((List.pairwise_map.1 hnd).imp fun h e =>
      h (congrArg (fun p : Key × PredId => p.1.1) e))
  · -- slot domain
    intro k ι
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
      refine ⟨List.mem_map_of_mem (f := fun e : Loc × PredId × Res => (e.1, (0 : Time))) he, .inr ?_⟩
      exact List.mem_map_of_mem (f := fun e : Loc × PredId × Res => e.2.1)
        (List.mem_filter.mpr ⟨he, by simp⟩)
    · rintro ⟨hk, h⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
      rcases h with h | h
      · rw [hnoacq e he ι] at h; cases h
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp h
        obtain ⟨he'r, he'x⟩ := List.mem_filter.mp he'
        have hx : e'.1 = e.1 := by simpa using he'x
        refine ⟨⟨(e'.1, 0), e'.2.1, e'.2.2⟩, List.mem_map_of_mem he'r, ?_, rfl⟩
        rw [hx]
  · -- slots satisfy their predicates
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact hslots e he
  · -- update ids
    intro x
    have hsub : ∀ e ∈ rls.filter (fun e => e.1 = x), e ∈ rls := fun e he => (List.mem_filter.mp he).1
    refine ⟨?_, fun ι hι => ?_⟩
    · show ((rls.filter fun e => e.1 = x).map fun e => e.2.1).Nodup
      refine List.pairwise_map.2 (List.pairwise_filter.2 ((List.pairwise_map.1 hnd).imp fun h ha hb => ?_))
      simp only [decide_eq_true_eq] at ha hb
      exact absurd (ha.trans hb.symm) h
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hι
      have hx : e.1 = x := by simpa using (List.mem_filter.mp he).2
      refine ⟨hslotIds e (hsub e he), ?_⟩
      rw [← hx]
      exact hnoacq e (hsub e he) _

/-- **The spinlock's ghost is an `initGhost`**: one release-mode location
`Lk`, update id `0`, slot `pool`. -/
theorem Spinlock.spinGhost_eq_initGhost (Lk : Loc) (φ : Pred) (pool : Res) :
    Spinlock.spinGhost Lk φ pool = initGhost (fun x => if x = Lk then φ else Pred.emp) [φ] [(Lk, 0, pool)] := by
  simp only [Spinlock.spinGhost, initGhost, List.map_cons, List.map_nil, Ghost.mk.injEq, true_and, and_true]
  funext x
  by_cases h : x = Lk
  · subst h; simp
  · simp [h, Ne.symm h]

/-! ## Release-mode initial locations with held acquire ids -/

/-- **A generic initial ghost with held acquire ids at release-mode
locations**: release predicates `rel`, acquire table `acqTab`, release-mode
initial locations `rlocs`, and the slots `hld` of their initial messages,
each `(x, ι, s)` for the held acquire id `ι` of `x` with resource `s`. No
update id, no pending mark, no claim. -/
def initGhostAcq (rel : Loc → Pred) (acqTab : List Pred) (rlocs : List Loc) (hld : List (Loc × PredId × Res)) :
    Ghost where
  rel := rel
  acqTab := acqTab
  u := hld.map fun e => ⟨(e.1, 0), e.2.1, e.2.2⟩
  relMsgs := rlocs.map fun x => (x, 0)
  pend := []
  upd _ := []
  claims := []

/-- **Initial erasure for `initGhostAcq`**: the slots `hld` are distinct per
(location, id), lie at release-mode locations, and are exactly the acquire
ids the initial total holds at the release-mode locations; their predicates
hold of the initial value at view `0`; every other initial message is pure. -/
theorem erase_initGhostAcq {rF : Nat → Res} {states : List I.State} {initMem : List (Loc × Val)}
    {rel : Loc → Pred} {acqTab : List Pred} {rlocs : List Loc} {hld : List (Loc × PredId × Res)} (T : Nat → Prop)
    (hnd : (hld.map fun e => (e.1, e.2.1)).Nodup)
    (hvalid : (total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).valid)
    (hacqIds : ∀ x ι, 1 ≤ (total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).acq x ι →
      ι < acqTab.length)
    (hrelAcq : ∀ x v m V r, (rel x).P v m V r →
      Pred.SepList ((initGhostAcq rel acqTab rlocs hld).acqPreds
        (total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).acq x) v m V r)
    (hwrites : ∀ x, 0 < ((total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).wr x).q →
      ∀ p, ((total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0))
    (hpure : ∀ x, x ∉ rlocs → Pred.Pure (rel x) ((Config.init states initMem).mem.initVal x))
    (hslotIds : ∀ e ∈ hld, e.2.1 < acqTab.length)
    (hheld : ∀ x ∈ rlocs, ∀ ι, (total rF (initGhostAcq rel acqTab rlocs hld) (Config.init states initMem)).acq x ι = 1 ↔
      ∃ e ∈ hld, e.1 = x ∧ e.2.1 = ι)
    (hloc : ∀ e ∈ hld, e.1 ∈ rlocs)
    (hslots : ∀ e ∈ hld, (acqTab.getD e.2.1 Pred.bot).P ((Config.init states initMem).mem.initVal e.1)
      (Config.init states initMem).mem 0 e.2.2) :
    Erase rF (initGhostAcq rel acqTab rlocs hld) T (Config.init states initMem) := by
  refine Erase.init hvalid ?_ hacqIds ?_ hwrites ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- slot ids
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact hslotIds e he
  · -- the release predicates split (no update ids)
    intro x v m V r h
    simpa [Ghost.updPreds, initGhostAcq] using hrelAcq x v m V r h
  · -- relaxed initial messages are pure
    intro x hx
    exact hpure x fun hm => hx (List.mem_map_of_mem (f := fun x : Loc => (x, (0 : Time))) hm)
  · -- release messages are initial
    intro k hk
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hk
    rfl
  · -- slots are distinct
    show ((hld.map fun e => (⟨(e.1, 0), e.2.1, e.2.2⟩ : Slot)).map fun s => (s.key, s.id)).Nodup
    rw [List.map_map]
    exact List.pairwise_map.2 ((List.pairwise_map.1 hnd).imp fun h e =>
      h (by simp only [Function.comp, Prod.mk.injEq, and_true] at e ⊢; exact e))
  · -- slot domain
    intro k ι
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
      exact ⟨List.mem_map_of_mem (f := fun x : Loc => (x, (0 : Time))) (hloc e he),
        .inl ((hheld e.1 (hloc e he) e.2.1).mpr ⟨e, he, rfl, rfl⟩)⟩
    · rintro ⟨hk, h⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      rcases h with h | h
      · obtain ⟨e, he, rfl, rfl⟩ := (hheld x hx ι).mp h
        exact ⟨⟨(e.1, 0), e.2.1, e.2.2⟩, List.mem_map_of_mem he, rfl, rfl⟩
      · cases h
  · -- slots satisfy their predicates
    intro s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact hslots e he
  · -- update ids
    intro x
    exact ⟨List.nodup_nil, fun _ h => by cases h⟩

end Kraken.Promising.SLR
