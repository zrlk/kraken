/-
**Part 2: the load outcome and facts with
the take**. ISA-neutral. Additive: the
frozen `LoadOut`/`LoadFacts` (`EnvG/Facts.lean`) are unchanged and follow as
the no-take case (`loadOut_of_loadOutT`, `loadFacts_of_loadFactsT`).

- `TakeCond A k vs l tr`: the load takes: it is acquire-type and its read of
  `(l, tr)` is not forwarded from the thread's own write (the floor bound
  `tr ≤ wfloor` of `take_floor_acqLoad`; forwarded reads cannot take).
- `LoadOutT`: `LoadOut` whose resource and ghost are those of the iterated
  take `takeAll` (`EnvG/TakeAll.lean`) at the anchor ghost `ga` when
  `TakeCond` holds, and unchanged otherwise (deterministic: an acquire load
  takes *all* the thread's exposed slots of the message). The clean
  knowledge `cl` gains `ClAt` at the anchor *before* the take; `seen`
  records as `seenAfter` and is then renamed along the take (`renameSeen`).
- `LoadOutT` also records `ErOwn`: validity-free erasure at the anchor with
  the thread holding `σ.r` (the link has it), so that a program proof finds
  the slots it takes without the clean flag.
- `LoadFactsT`, `loadOutT_facts`: the facts, as `LoadFacts`.
- `loadFactsT_wr_pos_of_slot`: what a program proof uses: a slot of the
  message read, for an id the thread holds, is now the thread's.

Phase-1 limits: single-access trees; read-side acquire for non-taking loads
as before; releases are stores; no take at fence nodes or forwarded reads.
-/
import Kraken.Promising.SLR.EnvG.TakeAll
import Kraken.Promising.SLR.EnvG.Env

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **The load takes**: acquire-type, and the read of `(l, tr)` is not
forwarded (from the env's views `vs`). -/
def TakeCond (A : Arch) (k : LoadKind) (vs : Views) (l : Loc) (tr : Time) : Prop :=
  (A.loadKind k).isAcquire = true ∧ ¬ Fwded vs l tr

/-- A `seen` entry of `l` whose id was swapped by the take gets the new id. -/
def renameSeen (l : Loc) (ren : List (PredId × PredId)) (p : Key × PredId) : Key × PredId :=
  if p.1.1 = l then (p.1, (ren.lookup p.2).getD p.2) else p

@[simp] theorem renameSeen_nil (l : Loc) (p : Key × PredId) : renameSeen l [] p = p := by
  unfold renameSeen; split <;> rfl

theorem map_renameSeen_nil (l : Loc) (L : List (Key × PredId)) : L.map (renameSeen l []) = L := by
  have e : renameSeen l [] = id := funext (renameSeen_nil l)
  rw [e, List.map_id]

/-- **The resource/ghost effect of a load** reading `(l, tr)` from views
`vs`, at anchor ghost `ga`, thread resource `r`: the iterated take if the load
takes, else nothing. -/
def TakeEff (A : Arch) (k : LoadKind) (vs : Views) (l : Loc) (tr : Time) (r : Res) (ga : Ghost) (a : TakeAcc) :
    Prop :=
  (TakeCond A k vs l tr → a = takeAll l tr r ga) ∧ (¬ TakeCond A k vs l tr → a = ⟨r, ga, []⟩)

theorem TakeEff.exists (A : Arch) (k : LoadKind) (vs : Views) (l : Loc) (tr : Time) (r : Res) (ga : Ghost) :
    ∃ a, TakeEff A k vs l tr r ga a := by
  by_cases h : TakeCond A k vs l tr
  · exact ⟨_, fun _ => rfl, fun h' => absurd h h'⟩
  · exact ⟨_, fun h' => absurd h' h, fun _ => rfl⟩

/-- With no take (no exposed slot, or the load does not take) the effect is
the identity. -/
theorem TakeEff.eq_of_noTake {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (h : TakeEff A k vs l tr r ga a) (hn : TakeCond A k vs l tr → takeAll l tr r ga = ⟨r, ga, []⟩) :
    a = ⟨r, ga, []⟩ := by
  by_cases hc : TakeCond A k vs l tr
  · rw [h.1 hc, hn hc]
  · exact h.2 hc

/-- **Validity-free erasure at the anchor with the thread holding `r`**
(stronger than `AnchorOk.erase`, which is for *some* resource assignment):
what a program proof needs to find the slots of a held acquire id
(`slot_of_held`, `Erase.slotsDom`/`slotsPred` hold without validity), so that
a take's gain is known without the clean flag. -/
def ErOwn (tid : Nat) (r : Res) (g : Ghost) (c : Config I) : Prop :=
  ∃ rF, Erase (setRes rF tid r) g (fun _ => True) c

/-- **A load outcome with the take** (`LoadOut` whose resource, ghost and
`seen` follow `TakeEff` at the anchor ghost `ga`). -/
def LoadOutT (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (xcl : Bool) (l : Loc) (v : Val) : Prop :=
  ∃ ga : Ghost, AnchorOk tid σ σ'.snap ga ∧ ErOwn tid σ.r ga σ'.snap ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r ga σ'.snap) ∧
    ∃ tr cx', (tr, v, cx') ∈ readSuccs A iv0 (envCtx tid σ.vs σ'.snap) k xcl l ∧ σ'.vs = cx'.views ∧
      ∃ a : TakeAcc, TakeEff A k σ.vs l tr σ.r ga a ∧ σ'.r = a.r ∧ σ'.g = a.g ∧
        σ'.seen = (seenAfter A k σ ga l tr).map (renameSeen l a.ren) ∧ σ'.fencedR = false ∧
        σ'.fencedW = σ.fencedW

/-- **What a load with the take exposes** (`LoadFacts` with `TakeEff`). -/
def LoadFactsT (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (l : Loc) (v : Val) : Prop :=
  ∃ ga : Ghost, AnchorOk tid σ σ'.snap ga ∧ ErOwn tid σ.r ga σ'.snap ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r ga σ'.snap) ∧
    ∃ tr, ReadAt A tid σ.vs σ'.snap k l tr v ∧ LoadViews A σ.vs σ'.vs k l tr ∧
      ∃ a : TakeAcc, TakeEff A k σ.vs l tr σ.r ga a ∧ σ'.r = a.r ∧ σ'.g = a.g ∧
        σ'.seen = (seenAfter A k σ ga l tr).map (renameSeen l a.ren) ∧ σ'.fencedR = false ∧
        σ'.fencedW = σ.fencedW

theorem loadOutT_facts {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOutT A tid σ σ' k xcl l v) : LoadFactsT A tid σ σ' k l v := by
  obtain ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, ha, hr, hg, hseen, hfR, hfW⟩ := h
  obtain ⟨t, v', he, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [readBound_eq] at hwi
  exact ⟨ga, hanc, hown, hcl, tr, ⟨hrd, hp, hwi⟩,
    by rw [hvs]; exact loadViews_readNext A (envCtx tid σ.vs σ'.snap) k xcl l tr v, a, ha, hr, hg, hseen, hfR, hfW⟩

/-! ## The existing outcome is the no-take case -/

/-- **`LoadOut` from `LoadOutT`** when nothing can be taken (the hypothesis
holds e.g. when the thread holds no acquire id of `l`, `takeAll_of_no_ids`,
or for loads that are not acquire-type). -/
theorem loadOut_of_loadOutT {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (hn : ∀ ga tr, TakeCond A k σ.vs l tr → takeAll l tr σ.r ga = ⟨σ.r, ga, []⟩)
    (h : LoadOutT A tid σ σ' k xcl l v) : LoadOut A tid σ σ' k xcl l v := by
  obtain ⟨ga, hanc, -, hcl, tr, cx', hx, hvs, a, ha, hr, hg, hseen, hfR, hfW⟩ := h
  obtain rfl := ha.eq_of_noTake (hn ga tr)
  simp only at hr hg hseen
  subst hg
  exact ⟨hanc, hr, hcl, tr, cx', hx, hvs, by rw [hseen, map_renameSeen_nil], hfR, hfW⟩

/-- **`LoadFacts` from `LoadFactsT`** when nothing can be taken. -/
theorem loadFacts_of_loadFactsT {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {l : Loc} {v : Val}
    (hn : ∀ ga tr, TakeCond A k σ.vs l tr → takeAll l tr σ.r ga = ⟨σ.r, ga, []⟩)
    (h : LoadFactsT A tid σ σ' k l v) : LoadFacts A tid σ σ' k l v := by
  obtain ⟨ga, hanc, -, hcl, tr, hrd, hlv, a, ha, hr, hg, hseen, hfR, hfW⟩ := h
  obtain rfl := ha.eq_of_noTake (hn ga tr)
  simp only at hr hg hseen
  subst hg
  exact ⟨hanc, hr, hcl, tr, hrd, hlv, by rw [hseen, map_renameSeen_nil], hfR, hfW⟩

/-- Holding no acquire id of `l` (in the env's resource), nothing is taken. -/
theorem noTake_of_no_ids {A : Arch} {k : LoadKind} {σ : State I} {l : Loc} (h : ∀ ι, σ.r.acq l ι ≠ 1) :
    ∀ ga tr, TakeCond A k σ.vs l tr → takeAll l tr σ.r ga = ⟨σ.r, ga, []⟩ :=
  fun _ _ _ => takeAll_of_no_ids h

/-- A load that is not acquire-type takes nothing. -/
theorem noTake_of_not_acq {A : Arch} {k : LoadKind} {σ : State I} {l : Loc} (h : (A.loadKind k).isAcquire = false) :
    ∀ ga tr, TakeCond A k σ.vs l tr → takeAll l tr σ.r ga = ⟨σ.r, ga, []⟩ :=
  fun _ _ hc => absurd hc.1 (by rw [h]; decide)

/-! ## What a program proof uses -/

/-- **The taken slot's write permissions are the thread's**: after a taking
load of `(l, tr)`, if at the anchor ghost `ga` the message has a slot `s`
for an id the thread held once, its positive write permissions are in the
new resource (the slot is unique under erasure: `slotAt_of_mem`). With
`slot_of_seen`/`slot_of_held` (under `cl`) this gives a write permission for
the location the slot's acquire predicate hands over. -/
theorem loadFactsT_wr_pos_of_slot {A : Arch} {σ σ' : State I} {k : LoadKind} {l : Loc}
    {ga : Ghost} {tr : Time} {a : TakeAcc} (ha : TakeEff A k σ.vs l tr σ.r ga a) (hr : σ'.r = a.r)
    (hc : TakeCond A k σ.vs l tr) {s : Slot} (hnd : (ga.u.map fun s => (s.key, s.id)).Nodup) (hs : s ∈ ga.u)
    (hk : s.key = (l, tr)) (hι : σ.r.acq l s.id = 1) (hlt : s.id < ga.acqTab.length) {x : Loc}
    (hx : 0 < (s.res.wr x).q) : 0 < (σ'.r.wr x).q := by
  rw [hr, ha.1 hc]
  have hsl := slotAt_of_mem hnd hs
  rw [hk] at hsl
  refine takeAll_wr_pos_of_slot ?_ hsl hx
  unfold Ghost.acqIds
  exact List.mem_filter.mpr ⟨List.mem_range.mpr hlt, by simp [hι]⟩

/-- The ghost after a load extends the anchor ghost. -/
theorem TakeEff.ghost_le {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) : ga.Le a.g := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeFold_le l tr (ga.acqIds r.acq l) ⟨r, ga, []⟩
  · rw [ha.2 hc]; exact Ghost.Le.refl ga

/-- Write permissions held before a load are held after it. -/
theorem takeEff_wr_pos {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) {x : Loc} (h : 0 < (r.wr x).q) : 0 < (a.r.wr x).q := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeAll_wr_pos h
  · rw [ha.2 hc]; exact h

end Kraken.Promising.SLR.EnvG
