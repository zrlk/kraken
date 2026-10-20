/-
**Context invariants along event trees, and
the machine facts they use.** ISA-neutral.

The operational route to `ticketlock2.kl` (an unlocked `incl (owner)` release,
see `EnvG/TicketX2Env.lean`) carries, for each thread, an invariant `JC g cx`
of its environment state `g` (a phase of the program's protocol, tracked by a
`vcgen` run in an environment `E`) and of the Promising context `cx` (views,
promises, memory). This file has the generic parts:

- `RunSim A tid E JC`: every access `E` permits, run by the machine
  (`readSuccs`, `writeSuccs`, `fenceStep`, an RMW's read, write and fences)
  from a context satisfying `JC g`, ends in a context satisfying `JC g'` for
  an environment answer `g'` (the per-access obligations);
- `RunOK A tid JC Post t g`: every run of the tree `t` (`runTree`, any
  instruction views) from a `JC g` context ends at a leaf `s` with `Post s g'`
  in a `JC g'` context;
- **`TreeJ.runJ`**: `RunOK` is a tree judgment of `E` (`EnvSpike.TreeJ`), so
  a `Safely` judgment in `E` gives it for every tree the thread runs
  (`exec_treeJ_of_instrStepEnv`);
- the machine facts of one access used by such invariants: `readSuccs_spec`
  (the read's timestamp is readable, not an own promise, no write to its
  location up to the read's bound; the context after it), `VLe` (the view
  components only grow) for reads, writes, fences and the RMW's after-steps,
  and `NoWriteInX` (no write to a location in a timestamp interval, stable
  under memory extension, `Memory.Prefix`).
-/
import Kraken.Promising.SLR.EnvG.MemValsBase
import Kraken.Promising.SLR.Lift
import Kraken.Promising.ReleasePrefixNT
import Kraken.Promising.Conservative

namespace Kraken.Promising.SLR.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Context invariants along event trees -/

/-- **Per-access simulation of an environment by a context invariant**: each
access `E` permits in `g`, run by the machine from a context `c` with
`JC g c`, ends in a context `c'` with `JC g' c'` for an answer `g'` of `E`
(`E.step`) to the machine's outcome. The fields follow `runTree`'s cases. -/
structure RunSim (A : Arch) (tid : Nat) (E : SharedEnv) (JC : E.State → Ctx → Prop) : Prop where
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {g : E.State} {iv : InstrViews} {c : Ctx},
    E.ok (.load k xcl addr n) g → JC g c →
    ∀ x ∈ readSuccs A iv c k xcl ⟨addr, n⟩, ∃ g', E.step (.load k xcl addr n) g x.2.1 g' ∧ JC g' x.2.2
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {g : E.State} {iv : InstrViews}
    {c : Ctx}, E.ok (.store k xcl addr n v) g → JC g c →
    (∀ c' ∈ writeSuccs A tid iv c k xcl ⟨addr, n⟩ v (if xcl then c.views.xclb.map (·.1) else none) 0 (if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0),
      ∃ g', E.step (.store k xcl addr n v) g true g' ∧ JC g' c') ∧
    (xcl = true → ∃ g', E.step (.store k xcl addr n v) g false g' ∧ JC g' (xclFailCtx c ⟨addr, n⟩))
  fence : ∀ {k : FenceKind} {g : E.State} {c : Ctx}, E.ok (.fence k) g → JC g c →
    ∃ g', E.step (.fence k) g () g' ∧ JC g' (fenceStep c k)
  rmw : ∀ {k : RmwKind} {noRet : Bool} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {g : E.State}
    {iv : InstrViews} {c : Ctx}, E.ok (.rmw k addr n op) g → JC g c →
    ∀ x ∈ readSuccs A iv (fenceOptCtx A c) (if noRet then .plain else (A.rmwKind k).loadKind) false ⟨addr, n⟩ noRet,
      (op x.2.1 = none → ∃ g', E.step (.rmw k addr n op) g x.2.1 g' ∧ JC g' (fenceOptCtx A x.2.2)) ∧
      ∀ new, op x.2.1 = some new →
        ∀ c' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0),
          ∃ g', E.step (.rmw k addr n op) g x.2.1 g' ∧ JC g' (rmwAfter A k noRet ⟨addr, n⟩ c')

/-- **Every run of a tree keeps the context invariant**: from a context with
`JC g`, under any instruction views, every successful run of `t` ends at a
leaf `s` with `Post s g'` in a context with `JC g'`. -/
def RunOK (A : Arch) (tid : Nat) {E : SharedEnv} (JC : E.State → Ctx → Prop) {σ : Type}
    (Post : σ → E.State → Prop) (t : EvTree σ) (g : E.State) : Prop :=
  ∀ iv c, JC g c → ∀ s c', .ok (s, c') ∈ runTree A tid iv c t → ∃ g', Post s g' ∧ JC g' c'

/-- **`RunOK` is a tree judgment of `E`** under a per-access simulation. -/
def TreeJ.runJ {A : Arch} {tid : Nat} {E : SharedEnv} {JC : E.State → Ctx → Prop} (hS : RunSim A tid E JC)
    {σ : Type} (Post : σ → E.State → Prop) : TreeJ E σ where
  W := RunOK A tid JC Post
  Post := Post
  done hP := by
    intro iv c hJ s c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, hP, hJ⟩
  fault := by
    intro _ _ iv c _ s c' h
    simp [runTree] at h
  choose hk := by
    intro iv c hJ s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact hk i iv c hJ s c' h
  load hok hk := by
    intro iv c hJ s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨g', hs, hJ'⟩ := hS.load hok hJ x hx
    exact hk _ _ hs iv _ hJ' s c' h
  store hok hk := by
    intro iv c hJ s c' h
    simp only [runTree, List.mem_append] at h
    obtain ⟨hw, hf⟩ := hS.store (iv := iv.forStore c.stores) hok hJ
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨g', hs, hJ'⟩ := hw c0 hc0
      exact hk _ _ hs iv _ hJ' s c' h
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨g', hs, hJ'⟩ := hf h.1
      exact hk _ _ hs iv _ hJ' s c' h.2
  fence hok hk := by
    intro iv c hJ s c' h
    simp only [runTree] at h
    obtain ⟨g', hs, hJ'⟩ := hS.fence hok hJ
    exact hk _ hs iv _ hJ' s c' h
  rmw hok hk := by
    intro iv c hJ s c' h
    simp only [runTree] at h
    change Except.ok (s, c') ∈ (readSuccs A iv (fenceOptCtx A c) _ false _ _).flatMap _ at h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hn, hw⟩ := hS.rmw (iv := iv) hok hJ x hx
    obtain ⟨tr, old, c2⟩ := x
    simp only at h hn hw
    split at h
    · next hop =>
      obtain ⟨g', hs, hJ'⟩ := hn hop
      exact hk _ _ hs iv _ hJ' s c' h
    · next new hop =>
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      obtain ⟨g', hs, hJ'⟩ := hw new hop c3 hc3
      exact hk _ _ hs iv _ hJ' s c' h

/-! ## Machine facts of one access -/

/-- No write to `l` with a timestamp in `(lo, hi]` (a copy of
`EnvG.NoWriteIn` of `EnvG/DekkerCore.lean`, which imports the ghost layer). -/
def NoWriteInX (m : Memory) (l : Loc) (lo hi : Time) : Prop :=
  ∀ ts w, lo < ts → ts ≤ hi → m.get? ts = some w → w.loc ≠ l

theorem noWriteInX_of_writeIn {m : Memory} {l : Loc} {lo hi : Time} (h : m.writeIn l lo hi = false) :
    NoWriteInX m l lo hi := by
  intro ts w h1 h2 hg hl
  have ht : m.writeIn l lo hi = true := (Memory.writeIn_iff m l lo hi).mpr ⟨ts, w, h1, h2, hg, hl⟩
  rw [h] at ht; cases ht

theorem NoWriteInX.mono {m : Memory} {l : Loc} {lo hi hi' : Time} (h : NoWriteInX m l lo hi) (hle : hi' ≤ hi) :
    NoWriteInX m l lo hi' :=
  fun ts w h1 h2 hg => h ts w h1 (Nat.le_trans h2 hle) hg

/-- `NoWriteInX` up to a timestamp of the memory survives extension. -/
theorem NoWriteInX.prefix {m m' : Memory} (hp : m.Prefix m') {l : Loc} {lo hi : Time} (hhi : hi ≤ m.last)
    (h : NoWriteInX m l lo hi) : NoWriteInX m' l lo hi := by
  intro ts w h1 h2 hg
  rw [hp.get? (Nat.le_trans h2 hhi)] at hg
  exact h ts w h1 h2 hg

/-- A timestamp a location reads at is in the memory. -/
theorem read?_le_last {m : Memory} {l : Loc} {ts : Time} {v : Val} (h : m.read? l ts = some v) : ts ≤ m.last := by
  unfold Memory.read? at h
  split at h
  · omega_t
  · split at h
    · next w hw => exact Memory.last_le_of_get?_eq_some m hw
    · cases h

/-- A read of the memory survives extension. -/
theorem read?_prefix {m m' : Memory} (hp : m.Prefix m') {l : Loc} {ts : Time} {v : Val}
    (h : m.read? l ts = some v) : m'.read? l ts = some v := by
  rw [hp.read? (read?_le_last h)]; exact h

/-- A message of the memory survives extension. -/
theorem get?_prefix {m m' : Memory} (hp : m.Prefix m') {ts : Time} {w : Msg} (h : m.get? ts = some w) :
    m'.get? ts = some w := by
  rw [hp.get? (Memory.last_le_of_get?_eq_some m h)]; exact h

/-- **The `read` rule, unfolded**: the timestamp read is readable at the
value, not an own outstanding promise, with no write to the location in
`(ts, bound]`; the context after it raises `coh l`, `vrOld` (or `vrOldNR`),
and, for an acquire, `vrNew` and `vwNew`, to the post-view, which is at
least the timestamp unless forwarded. -/
theorem readSuccs_spec (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    c.mem.read? l x.1 = some x.2.1 ∧
      NoWriteInX c.mem l x.1 (max (max iv.addrR (max c.views.vrNew
        (if A.loadKind k == .acq then c.views.vRel else 0))) (c.views.getCoh l)) ∧
      x.1 ∉ c.prom ∧ x.2.2.mem = c.mem ∧ x.2.2.prom = c.prom ∧
      ∃ νpost : View,
        (c.views.getFwd l = none → x.1 ≤ νpost) ∧
        x.2.2.views.getCoh = (c.views.setCoh l νpost).getCoh ∧
        x.2.2.views.vrOld = (if noRet then c.views.vrOld else max c.views.vrOld νpost) ∧
        x.2.2.views.vrNew = (if (A.loadKind k).isAcquire then max c.views.vrNew νpost else c.views.vrNew) ∧
        x.2.2.views.vwOld = c.views.vwOld ∧ x.2.2.views.fwdb = c.views.fwdb := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rename_i v hv
    rw [Option.ite_none_left_eq_some] at ht
    obtain ⟨hc, ht⟩ := ht
    cases ht
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    refine ⟨hv, noWriteInX_of_writeIn hc.1, ?_, rfl, rfl, _, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · intro hm; rw [List.contains_iff_mem.mpr hm] at hc; exact absurd hc.2 (by simp)
    · intro hf
      simp only [readView, hf]
      omega_t

/-- The view components a thread's invariants bound from below: they only
grow. -/
structure VLe (V V' : Views) : Prop where
  vrNew : V.vrNew ≤ V'.vrNew
  vrOld : V.vrOld ≤ V'.vrOld
  vwOld : V.vwOld ≤ V'.vwOld
  coh : ∀ l, V.getCoh l ≤ V'.getCoh l

theorem VLe.refl (V : Views) : VLe V V := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem VLe.trans {V V' V'' : Views} (h₁ : VLe V V') (h₂ : VLe V' V'') : VLe V V'' :=
  ⟨Nat.le_trans h₁.vrNew h₂.vrNew, Nat.le_trans h₁.vrOld h₂.vrOld, Nat.le_trans h₁.vwOld h₂.vwOld,
    fun l => Nat.le_trans (h₁.coh l) (h₂.coh l)⟩

theorem getCoh_le_setCoh (V : Views) (l l' : Loc) (t : View) : V.getCoh l' ≤ (V.setCoh l t).getCoh l' := by
  rw [Views.getCoh_setCoh]; split
  · subst l'; omega_t
  · exact Nat.le_refl _

theorem readSuccs_vle (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : VLe c.views x.2.2.views := by
  obtain ⟨-, -, -, -, -, ν, -, hcoh, hro, hrn, hwo, -⟩ := readSuccs_spec A iv hx
  refine ⟨?_, ?_, ?_, fun l' => ?_⟩
  · rw [hrn]; split <;> omega_t
  · rw [hro]; split <;> omega_t
  · rw [hwo]; exact Nat.le_refl _
  · rw [hcoh]; exact getCoh_le_setCoh _ _ _ _

theorem fenceStep_vle (c : Ctx) (k : FenceKind) : VLe c.views (fenceStep c k).views := by
  cases k <;> refine ⟨?_, ?_, ?_, fun _ => ?_⟩ <;> simp [fenceStep, Views.getCoh] <;> omega_t

theorem fenceStep_fwdb (c : Ctx) (k : FenceKind) : (fenceStep c k).views.fwdb = c.views.fwdb := by
  cases k <;> rfl

theorem fenceOptCtx_vle (A : Arch) (c : Ctx) : VLe c.views (fenceOptCtx A c).views := by
  unfold fenceOptCtx; split
  · exact fenceStep_vle c .sy
  · exact VLe.refl _

theorem fenceOptCtx_fwdb (A : Arch) (c : Ctx) : (fenceOptCtx A c).views.fwdb = c.views.fwdb := by
  unfold fenceOptCtx; split
  · exact fenceStep_fwdb c .sy
  · rfl

theorem rmwAfter_vle (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    VLe c.views (rmwAfter A k noRet l c).views := by
  have hp : VLe c.views (rmwPost A k noRet l c).views := by
    unfold rmwPost; split
    · refine ⟨?_, Nat.le_refl _, Nat.le_refl _, fun _ => Nat.le_refl _⟩
      show c.views.vrNew ≤ max c.views.vrNew _; omega_t
    · exact VLe.refl _
  unfold rmwAfter; split
  · exact hp.trans (fenceStep_vle _ .sy)
  · exact hp

theorem rmwAfter_fwdb (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwAfter A k noRet l c).views.fwdb = c.views.fwdb := by
  have hp : (rmwPost A k noRet l c).views.fwdb = c.views.fwdb := by unfold rmwPost; split <;> rfl
  unfold rmwAfter; split
  · rw [fenceStep_fwdb]; exact hp
  · exact hp

theorem rmwAfter_mem_prom (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwAfter A k noRet l c).mem = c.mem ∧ (rmwAfter A k noRet l c).prom = c.prom :=
  Kraken.Promising.SLR.rmwAfter_memProm A k noRet l c

/-- **The `fulfil` rule, unfolded** (`mem_writeSuccs`): the write's timestamp
`w` is above the write's bound (`coh l` and the pre-view, which for a release
takes `vrOld` and `vwOld`) and atomic with `tr`; the message at `w` is
`⟨l, v, tid⟩` in the memory after (a fulfilled promise, or appended); the
memory grows, `w` leaves the promises and nothing else does, and the views
grow, `vwOld` (for a non-NT store) and `coh l` to at least `w`. -/
theorem writeSuccs_spec (A : Arch) (tid : Nat) (iv : InstrViews) {c c' : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (hc : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) :
    ∃ w, max (writePre A iv c k extra) (c.views.getCoh l) < w ∧ (∀ a, tr = some a → a < w ∧ c.mem.atomic l tid a w) ∧
      c'.mem.get? w = some ⟨l, v, tid⟩ ∧ c.mem.Prefix c'.mem ∧
      (∀ ts, c.mem.last < ts → ts ≤ c'.mem.last → ts = w) ∧
      ((w ∈ c.prom ∧ c'.prom = c.prom.erase w) ∨ (w = c.mem.last + 1 ∧ c'.prom = (c.prom ++ [w]).erase w)) ∧
      c'.views.getCoh = (c.views.setCoh l w).getCoh ∧ c'.views.vrOld = c.views.vrOld ∧
      c'.views.vrNew = c.views.vrNew ∧
      (A.storeKind k ≠ .nt → c'.views.vwOld = max c.views.vwOld w) ∧
      (∀ l', l' ≠ l → c'.views.getFwd l' = c.views.getFwd l') := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨w, hwp, m, hm, hl, hv, ht, hok, rfl⟩ | ⟨hok, rfl⟩
  · refine ⟨w, hok.1, hok.2, ?_, Memory.Prefix.refl _, fun ts h1 h2 => absurd h2 (by simp only [afterWrite]; omega_t),
      .inl ⟨hwp, rfl⟩, rfl, rfl, rfl, ?_, fun l' hl' => ?_⟩
    · simp only [afterWrite, hm]; subst hl hv ht; rfl
    · intro hk; simp only [afterWrite]; cases hs : A.storeKind k <;> first | exact absurd hs hk | rfl
    · show (c.views.setFwd l _).getFwd l' = _
      rw [Views.getFwd_setFwd]; simp [hl']
  · refine ⟨c.mem.last + 1, hok.1, hok.2, ?_, Memory.Prefix.append _ _, fun ts h1 h2 => ?_,
      .inr ⟨rfl, rfl⟩, rfl, rfl, rfl, ?_, fun l' hl' => ?_⟩
    · simp only [afterWrite, Memory.append, Memory.get?, Memory.last]
      simp
    · simp only [afterWrite, Memory.append, Memory.last, Array.size_push] at h2 h1 ⊢; omega_t
    · intro hk; simp only [afterWrite]; cases hs : A.storeKind k <;> first | exact absurd hs hk | rfl
    · show (c.views.setFwd l _).getFwd l' = _
      rw [Views.getFwd_setFwd]; simp [hl']

end Kraken.Promising.SLR.EnvG.TicketX2

#print axioms Kraken.Promising.SLR.EnvG.TicketX2.TreeJ.runJ
#print axioms Kraken.Promising.SLR.EnvG.TicketX2.writeSuccs_spec
