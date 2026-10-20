/-
**Part 2: the load outcome, facts and
environment with the cumulative take.** ISA-neutral. Adapted from
`EnvG/TakeFacts.lean`, `EnvG/TakeEnv.lean` and
`EnvG/TakeVCGenCommon.lean` (all unchanged) with `takeUpTo`
(`EnvG/TakeUAll.lean`) in place of `takeAll`.

- `TakeEffU`, `LoadOutTU`, `LoadFactsTU`, `loadOutTU_facts`: as
  `TakeEff`/`LoadOutT`/`LoadFactsT`, with the cumulative take: a
  non-forwarded acquire load of `(l, tr)` (`TakeCond`, unchanged) takes the
  thread's exposed slots of `(l, ts)` for every `ts ≤ tr`. The clean
  knowledge, `ErOwn` and `seen` (`seenAfter` renamed by the composed
  renaming, `renameSeen`) are as in `LoadOutT`.
- **The original take is the special case**: `takeEff_of_takeEffU` /
  `takeEffU_of_takeEff`, `loadOutT_of_loadOutTU` / `loadOutTU_of_loadOutT`:
  when the thread has no exposed slot of `l` below the message read, the two
  outcomes coincide (`takeUpTo_eq_takeAll`). `loadOut_of_loadOutTU`: the
  frozen `LoadOut` when nothing can be taken.
- **`EnvGTU I A tid pl`**: `EnvGT` with `LoadOutTU` as its load step; state,
  `ok`, store/RMW/fence steps are `EnvG`'s definitionally (`envGTU_ok`,
  `envGTU_step_store`, …). `step_loadFactsTU`, `step_storeFactsTU`, …
- `vcgen` support: `@[simp]` `ok`/`step` at `(EnvGTU I A tid pl).State`,
  `SharedEnv.FenceMono (EnvGTU I A tid pl)` (fences are `EnvG`'s,
  `fenceInv_fenceLe`), `takeEffU_of_not_acq`.
- What a program proof uses: `loadFactsTU_wr_full` (a slot of `(l, ts)`,
  `ts ≤ tr`, holding all of `x` for an id the thread held once makes all of
  `x` the thread's; in particular the slot of a **skipped** message),
  `TakeEffU.ghost_le`, `takeEffU_wr_pos`, `takeEffU_held`.

Phase-1 limits as `EnvG/TakeEnv.lean`.
-/
import Kraken.Promising.SLR.EnvG.TakeUAll
import Kraken.Promising.SLR.EnvG.TakeVCGenCommon

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## The effect and the outcome -/

/-- **The resource/ghost effect of a load with the cumulative take**: if
the load takes, `takeUpTo` at the anchor ghost, else nothing. -/
def TakeEffU (A : Arch) (k : LoadKind) (vs : Views) (l : Loc) (tr : Time) (r : Res) (ga : Ghost) (a : TakeAcc) :
    Prop :=
  (TakeCond A k vs l tr → a = takeUpTo l tr r ga) ∧ (¬ TakeCond A k vs l tr → a = ⟨r, ga, []⟩)

theorem TakeEffU.exists (A : Arch) (k : LoadKind) (vs : Views) (l : Loc) (tr : Time) (r : Res) (ga : Ghost) :
    ∃ a, TakeEffU A k vs l tr r ga a := by
  by_cases h : TakeCond A k vs l tr
  · exact ⟨_, fun _ => rfl, fun h' => absurd h h'⟩
  · exact ⟨_, fun h' => absurd h' h, fun _ => rfl⟩

/-- **A load outcome with the cumulative take** (`LoadOutT` with
`TakeEffU`). -/
def LoadOutTU (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (xcl : Bool) (l : Loc) (v : Val) : Prop :=
  ∃ ga : Ghost, AnchorOk tid σ σ'.snap ga ∧ ErOwn tid σ.r ga σ'.snap ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r ga σ'.snap) ∧
    ∃ tr cx', (tr, v, cx') ∈ readSuccs A iv0 (envCtx tid σ.vs σ'.snap) k xcl l ∧ σ'.vs = cx'.views ∧
      ∃ a : TakeAcc, TakeEffU A k σ.vs l tr σ.r ga a ∧ σ'.r = a.r ∧ σ'.g = a.g ∧
        σ'.seen = (seenAfter A k σ ga l tr).map (renameSeen l a.ren) ∧ σ'.fencedR = false ∧
        σ'.fencedW = σ.fencedW

/-- **What a load with the cumulative take exposes** (`LoadFactsT` with
`TakeEffU`). -/
def LoadFactsTU (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (l : Loc) (v : Val) : Prop :=
  ∃ ga : Ghost, AnchorOk tid σ σ'.snap ga ∧ ErOwn tid σ.r ga σ'.snap ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r ga σ'.snap) ∧
    ∃ tr, ReadAt A tid σ.vs σ'.snap k l tr v ∧ LoadViews A σ.vs σ'.vs k l tr ∧
      ∃ a : TakeAcc, TakeEffU A k σ.vs l tr σ.r ga a ∧ σ'.r = a.r ∧ σ'.g = a.g ∧
        σ'.seen = (seenAfter A k σ ga l tr).map (renameSeen l a.ren) ∧ σ'.fencedR = false ∧
        σ'.fencedW = σ.fencedW

theorem loadOutTU_facts {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOutTU A tid σ σ' k xcl l v) : LoadFactsTU A tid σ σ' k l v := by
  obtain ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, ha, hr, hg, hseen, hfR, hfW⟩ := h
  obtain ⟨t, v', he, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [readBound_eq] at hwi
  exact ⟨ga, hanc, hown, hcl, tr, ⟨hrd, hp, hwi⟩,
    by rw [hvs]; exact loadViews_readNext A (envCtx tid σ.vs σ'.snap) k xcl l tr v, a, ha, hr, hg, hseen, hfR, hfW⟩

/-! ## The original take is the special case -/

/-- Nothing of `l` exposed below `tr` for the ids `r` holds once. -/
def NoSlotBelow (l : Loc) (tr : Time) (r : Res) (g : Ghost) : Prop :=
  ∀ ts < tr, ∀ ι ∈ g.acqIds r.acq l, slotAt g (l, ts) ι = none

theorem takeEff_of_takeEffU {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (hn : TakeCond A k vs l tr → NoSlotBelow l tr r ga) (h : TakeEffU A k vs l tr r ga a) :
    TakeEff A k vs l tr r ga a :=
  ⟨fun hc => (h.1 hc).trans (takeUpTo_eq_takeAll (hn hc)), h.2⟩

theorem takeEffU_of_takeEff {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (hn : TakeCond A k vs l tr → NoSlotBelow l tr r ga) (h : TakeEff A k vs l tr r ga a) :
    TakeEffU A k vs l tr r ga a :=
  ⟨fun hc => (h.1 hc).trans (takeUpTo_eq_takeAll (hn hc)).symm, h.2⟩

/-- **`LoadOutT` is `LoadOutTU` without skipped slots** (one direction). -/
theorem loadOutT_of_loadOutTU {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (hn : ∀ ga tr, TakeCond A k σ.vs l tr → NoSlotBelow l tr σ.r ga)
    (h : LoadOutTU A tid σ σ' k xcl l v) : LoadOutT A tid σ σ' k xcl l v := by
  obtain ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, ha, rest⟩ := h
  exact ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, takeEff_of_takeEffU (hn ga tr) ha, rest⟩

/-- **`LoadOutT` is `LoadOutTU` without skipped slots** (the other). -/
theorem loadOutTU_of_loadOutT {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (hn : ∀ ga tr, TakeCond A k σ.vs l tr → NoSlotBelow l tr σ.r ga)
    (h : LoadOutT A tid σ σ' k xcl l v) : LoadOutTU A tid σ σ' k xcl l v := by
  obtain ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, ha, rest⟩ := h
  exact ⟨ga, hanc, hown, hcl, tr, cx', hx, hvs, a, takeEffU_of_takeEff (hn ga tr) ha, rest⟩

/-- Holding no acquire id of `l`, the cumulative take changes nothing. -/
theorem takeUpTo_of_no_ids {l : Loc} {tr : Time} {r : Res} {g : Ghost} (h : ∀ ι, r.acq l ι ≠ 1) :
    takeUpTo l tr r g = ⟨r, g, []⟩ := by
  have hnil : ∀ ι, ι ∉ g.acqIds r.acq l := fun ι hι => h ι (mem_acqIds hι).1
  rw [takeUpTo_eq_takeAll (fun _ _ ι hι => absurd hι (hnil ι)), takeAll_of_no_ids h]

/-- **The frozen `LoadOut` from `LoadOutTU`** when the thread holds no
acquire id of `l` (or more generally takes nothing). -/
theorem loadOut_of_loadOutTU {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (hn : ∀ ga tr, TakeCond A k σ.vs l tr → takeUpTo l tr σ.r ga = ⟨σ.r, ga, []⟩)
    (h : LoadOutTU A tid σ σ' k xcl l v) : LoadOut A tid σ σ' k xcl l v := by
  obtain ⟨ga, hanc, -, hcl, tr, cx', hx, hvs, a, ha, hr, hg, hseen, hfR, hfW⟩ := h
  have ha' : a = ⟨σ.r, ga, []⟩ := by
    by_cases hc : TakeCond A k σ.vs l tr
    · rw [ha.1 hc, hn ga tr hc]
    · exact ha.2 hc
  subst ha'
  simp only at hr hg hseen
  subst hg
  exact ⟨hanc, hr, hcl, tr, cx', hx, hvs, by rw [hseen, map_renameSeen_nil], hfR, hfW⟩

/-! ## The environment -/

/-- **The whole-thread SLR environment with cumulatively taking loads** of
thread `tid` under the plan `pl`. -/
def _root_.Kraken.Promising.SLR.EnvGTU (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := (EnvG I A tid pl).ok a σ
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutTU A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

theorem envGTU_ok (A : Arch) (tid : Nat) (pl : Plan) (a : SharedAccess) (σ : State I) :
    (EnvGTU I A tid pl).ok a σ = (EnvG I A tid pl).ok a σ := rfl

theorem envGTU_step_store {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (EnvGTU I A tid pl).step (.store k xcl addr n v) σ b σ' = (EnvG I A tid pl).step (.store k xcl addr n v) σ b σ' :=
  rfl

theorem envGTU_step_rmw {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} :
    (EnvGTU I A tid pl).step (.rmw k addr n op) σ old σ' = (EnvG I A tid pl).step (.rmw k addr n op) σ old σ' := rfl

theorem envGTU_step_fence {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : FenceKind} {u : Unit} :
    (EnvGTU I A tid pl).step (.fence k) σ u σ' = (EnvG I A tid pl).step (.fence k) σ u σ' := rfl

theorem step_loadFactsTU {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvGTU I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFactsTU A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutTU_facts h

theorem step_storeFactsTU {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGTU I A tid pl).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

theorem step_rmwFactsTU {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvGTU I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFacts A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOut_facts h

/-! ## `vcgen` support -/

@[simp] theorem envGTU_ok_load_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTU I A tid pl).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) : (EnvGTU I A tid pl).ok (.load k xcl addr n) σ :=
  trivial

@[simp] theorem envGTU_ok_fence_st (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTU I A tid pl).State)
    (k : FenceKind) : (EnvGTU I A tid pl).ok (.fence k) σ := trivial

@[simp] theorem envGTU_ok_store (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTU I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTU I A tid pl).ok (.store k xcl addr n v) σ = StoreOk A tid pl σ k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTU_ok_rmw (A : Arch) (tid : Nat) (pl : Plan) (σ : (EnvGTU I A tid pl).State) (k : RmwKind)
    (addr : BitVec 64) (n : Nat) (op : Val → Option Val) :
    (EnvGTU I A tid pl).ok (.rmw k addr n op) σ = RmwOk A tid pl σ k ⟨addr, n⟩ op := rfl

@[simp] theorem envGTU_step_load (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTU I A tid pl).State)
    (k : LoadKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) :
    (EnvGTU I A tid pl).step (.load k xcl addr n) σ v σ' = LoadOutTU A tid σ σ' k xcl ⟨addr, n⟩ v := rfl

@[simp] theorem envGTU_step_store' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTU I A tid pl).State)
    (k : StoreKind) (xcl : Bool) (addr : BitVec 64) (n : Nat) (v : Val) (b : Bool) :
    (EnvGTU I A tid pl).step (.store k xcl addr n v) σ b σ' = StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b := rfl

@[simp] theorem envGTU_step_rmw' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTU I A tid pl).State)
    (k : RmwKind) (addr : BitVec 64) (n : Nat) (op : Val → Option Val) (old : Val) :
    (EnvGTU I A tid pl).step (.rmw k addr n op) σ old σ' = RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old := rfl

@[simp] theorem envGTU_step_fence' (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : (EnvGTU I A tid pl).State)
    (k : FenceKind) (u : Unit) : (EnvGTU I A tid pl).step (.fence k) σ u σ' = FenceOut σ σ' k := rfl

/-- Every `EnvGTU` fence is permitted and stays in `FenceLe σ`. -/
theorem fenceInv_fenceLeTU (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) :
    (EnvGTU I A tid pl).FenceInv (FenceLe σ) :=
  fenceInv_fenceLe A tid pl σ

instance (A : Arch) (tid : Nat) (pl : Plan) : (EnvGTU I A tid pl).FenceMono :=
  ⟨FenceLe, FenceLe.refl, fenceInv_fenceLeTU A tid pl⟩

@[simp] theorem fenceMono_le_envGTU (A : Arch) (tid : Nat) (pl : Plan) :
    (SharedEnv.FenceMono.le (env := EnvGTU I A tid pl)) = FenceLe := rfl

/-! ## What a program proof uses -/

/-- A non-acquire load takes nothing. -/
theorem takeEffU_of_not_acq {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (h : TakeEffU A k vs l tr r ga a) (hk : (A.loadKind k).isAcquire = false) : a = ⟨r, ga, []⟩ :=
  h.2 fun hc => absurd hc.1 (by rw [hk]; decide)

/-- The ghost after a load extends the anchor ghost. -/
theorem TakeEffU.ghost_le {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEffU A k vs l tr r ga a) : ga.Le a.g := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeUpTo_le l tr r ga
  · rw [ha.2 hc]; exact Ghost.Le.refl ga

/-- Write permissions held before a load are held after it. -/
theorem takeEffU_wr_pos {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEffU A k vs l tr r ga a) {x : Loc} (h : 0 < (r.wr x).q) : 0 < (a.r.wr x).q := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeUpTo_wr_pos l tr ga h
  · rw [ha.2 hc]; exact h

/-- The fractions held before a load are at most those after it. -/
theorem takeEffU_q_ge {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEffU A k vs l tr r ga a) (x : Loc) : (r.wr x).q ≤ (a.r.wr x).q := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeUpTo_q_ge l tr r ga x
  · rw [ha.2 hc]; exact Rat.le_refl

/-- **A held id survives a load**, its predicate relaxed at some timestamps
`≤ tr` (none if the load does not take). -/
theorem takeEffU_held {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEffU A k vs l tr r ga a) {ι : PredId} (h1 : 1 ≤ r.acq l ι) (h2 : ι < ga.acqTab.length) :
    ∃ ι' K, (∀ t ∈ K, t ≤ tr) ∧ 1 ≤ a.r.acq l ι' ∧ ι' < a.g.acqTab.length ∧ a.g.acqPred ι' = (ga.acqPred ι).takeAtL K := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeUpTo_held h1 h2
  · rw [ha.2 hc]; exact ⟨ι, [], fun _ h => absurd h List.not_mem_nil, h1, h2, rfl⟩

/-- **A taken slot holding all of `x` is all of the thread's `x`** after a
taking load of `(l, tr)`: any slot of `(l, ts)` with `ts ≤ tr` (a message
read or **skipped**) for an id the thread held once at the anchor. -/
theorem loadFactsTU_wr_full {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {l : Loc} {ga : Ghost}
    {c : Config I} {tr : Time} {a : TakeAcc} (hown : ErOwn tid σ.r ga c) (hn : tid < c.threads.size)
    (ha : TakeEffU A k σ.vs l tr σ.r ga a) (hr : σ'.r = a.r) (hc : TakeCond A k σ.vs l tr) {s : Slot}
    (hs : s ∈ ga.u) {ts : Time} (hk : s.key = (l, ts)) (hts : ts ≤ tr) (hι : σ.r.acq l s.id = 1) {x : Loc}
    (hq : (s.res.wr x).q = 1) : (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (s.res.wr x).X p := by
  obtain ⟨rF, E⟩ := hown
  rw [hr, ha.1 hc]
  exact takeUpTo_wr_full hn E hs hk hts hι hq

/-- **A load keeps a full write permission** (`takeEff_wr_full` for the
cumulative take; ISA-neutral: `TakeUX64.takeEffU_wr_full` and
`SpscA.takeEffU_full` are its aliases). -/
theorem takeEffU_keepsFull {rF : Nat → Res} {c : Config I} {tid : Nat} {A : Arch} {k : LoadKind}
    {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost} {a : TakeAcc} (hn : tid < c.threads.size)
    (E : Erase (setRes rF tid r) ga (fun _ => True) c) (ha : TakeEffU A k vs l tr r ga a) {x : Loc}
    (hq : (r.wr x).q = 1) : (a.r.wr x).q = 1 ∧ ∀ p, (a.r.wr x).X p ↔ (r.wr x).X p := by
  by_cases hc : TakeCond A k vs l tr
  · obtain rfl := ha.1 hc
    obtain ⟨d, hd, hXd⟩ := takeUpTo_wr l tr r ga x
    have hle := (takeUpTo_erase (l := l) (tr := tr) hn E).thread_q_le hn x
    have h1 := d.nonneg
    have hd0 : d.q = 0 := by grind
    refine ⟨by grind, fun p => ?_⟩
    rw [hXd]
    exact ⟨fun h => h.elim id fun h' => absurd h' (d.zero hd0 p), .inl⟩
  · obtain rfl := ha.2 hc
    exact ⟨hq, fun _ => Iff.rfl⟩

end Kraken.Promising.SLR.EnvG
