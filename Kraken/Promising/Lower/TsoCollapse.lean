/-
**Which x64 ordering annotations change nothing
on `Arch.tso`** (ISA-neutral, at the event level).

The x64 lowering of WeakCore erases source annotations: `cas` of every kind
becomes `lock cmpxchg` (Kraken `.rmw .acqRel`), `load acq` and `store rel`
become `mov` (`.load .plain`, `.store .plain`), and `fence st` becomes
nothing. This file states, on `Arch.tso`, for `runTree` (and so for `RunOut`
and `InstrSemInf`), which of these erasures leave a tree's outcomes unchanged,
and gives the exact difference where they do not.

## Results

- **(B2) loads.** `.plain` and `.acqPc` are the same load
  (`readSuccs_plain_eq_acqPc`, `runTree_load_plain_eq_acqPc`; `rfl`:
  `Arch.tso.plainLoad = .acqPc`). **`.acq` is not**: `readSuccs_acq_eq`, the
  exact difference, says a `.acq` load is the `.acqPc` load with the thread's
  `vRel` joined into its address view. On TSO every ordinary store is a
  release (`plainStore = .rel`), so `vRel` is the thread's last non-NT store,
  and a `.acq` load is ordered after the thread's own earlier stores (RCsc).
  It is **stricter** than `.acqPc` and than x86 `mov`. Witness (SB):
  `T0: st x=1; ld.acq y || T1: st y=1; ld.acq x`, outcome `y=0 ∧ x=0`.
  Forbidden with `.acq`: whichever store has the larger timestamp, its
  thread's load has its pre-view at or above it and cannot read the initial
  value of the other location. Allowed with `.plain`/`.acqPc`. The two
  `example`s at the end compute one half on a concrete context (`decide`).
  `X64.isa` never emits `.load .acq`: every x64 load is `.load .plain`
  (`Promising/X64.lean` `toEv`: `nonmem_load`, the AVX loads and
  `loadPieces`; `sync_load` exists but no x64 instruction emits it,
  `X64/Semantics.lean`). So Kraken's x64 machine is not stricter than the
  hardware. The consequence is for the source model: if WeakCore's
  `load acq` is RCsc on TSO, the row `load acq → mov` does not simulate
  backward. If it is RCpc, `.plain` is the exact image.
- **(B3) stores.** `.plain` and `.rel` are the same store, exclusive or not
  (`writeSuccs_plain_eq_rel`, `runTree_store_plain_eq_rel`; `rfl`:
  `Arch.tso.plainStore = .rel`).
- **(B4) RMWs.** `.plain` and `.acqRel` are the same (`rfl`). For a `noRet`
  RMW all four kinds are the same (`runTree_rmw_noRet_eq`: the read is plain
  whatever `k`, the write is `.rel` after `storeKind`, and `rmwBump` is off).
  With `noRet = false` all four kinds are the same from every context with
  `RelLeOld` (`vRel ≤ vwOld`): `runTree_rmw_eq`. The leading `fence .sy`
  (`rmwFenceOpt`) raises `vrNew` to `vwOld ≥ vRel`, which removes the
  `.acq`/`.acqPc` difference of the read (`readSuccs_acq_eq_of_le`). The
  trailing `fence .sy` absorbs `rmwBump`, because the write leaves
  `coh l = t ≤ vwOld` (`writeSuccs_coh_le_vwOld`, `fenceStep_bump`). Every
  reachable configuration of the fuel-free machine satisfies `RelLeOld` in
  every thread, under any `Arch`: `cfgRelLeOld_init`,
  `reachableSemInf_relLeOld`. Machine level: `instrSemInf_rmw_tso_congr`.
  (x64 emits only `.acqRel`, and `noRet = false`.)
- **(B1) `fence .st`.** It is not a literal stutter. `fenceStep_st`: it sets
  `vwNew := vwNew ⊔ vwOld ⊔ vwOldNT` and changes nothing else (memory,
  promises and state are kept). `instrSemInf_fence_st_iff` is the
  `InstrSemInf` form. `instrSemInf_fence_st_stutter`: when
  `vwOld ⊔ vwOldNT ≤ vwNew` the step is exactly the no-event step
  (`instrSemInf_done_iff`'s right-hand side). In general the views differ.
  - With non-temporal stores it is **observable** (x86 `sfence` is
    `.fence .st`): `movnti x; sfence; mov y || mov y; mov x` forbids
    `y=1 ∧ x=0`.
  - Without them (`vwOldNT = 0`) the raised `vwNew` is dominated in every
    later write's pre-view, since every TSO write is `.rel` and takes the
    monotone `vwOld`. So it should be unobservable, but that is a multi-step
    simulation and is not proved here.
- Generic plumbing: `runOut_congr` and `instrSemInf_iff_of_exec_congr`
  transport an equation of trees' runs from `ctx0` to `InstrSemInf`.

**AArch64 counterpart (recorded, not proved).** On `Arch.armv8`, `ldar`
(`.acq`) and `ldapr` (`.acqPc`) differ in the same way (`vRel` in the
pre-view: `stlr; ldar` is ordered, `stlr; ldapr` is not). `.store .plain`
and `.store .rel` differ (the release pre-view takes `vrOld`, `vrOldNR`,
`vwOld`), and RMW kinds differ (no `rmwFence`). None of the B collapses hold
there, as expected.
-/
import Kraken.Promising.Lower.Events
import Kraken.Promising.AcqFloor

namespace Kraken.Promising.Lower.Tso

open Kraken.Promising

variable (tid : Nat) (iv : InstrViews)

/-- **(B2)** On TSO a plain load is an `.acqPc` load (`Arch.tso.plainLoad`). -/
theorem readSuccs_plain_eq_acqPc (c : Ctx) (xcl : Bool) (l : Loc) (noRet : Bool) :
    readSuccs Arch.tso iv c .plain xcl l noRet = readSuccs Arch.tso iv c .acqPc xcl l noRet := rfl

/-- **(B2), the exact difference**: an `.acq` load on TSO is the `.acqPc`
load with the thread's `vRel` joined into the address view, so its pre-view
takes the thread's own last release store (every ordinary TSO store). -/
theorem readSuccs_acq_eq (c : Ctx) (xcl : Bool) (l : Loc) (noRet : Bool) :
    readSuccs Arch.tso iv c .acq xcl l noRet =
      readSuccs Arch.tso { iv with addrR := max iv.addrR c.views.vRel } c .acqPc xcl l noRet := by
  have h : max iv.addrR (max c.views.vrNew c.views.vRel) = max (max iv.addrR c.views.vRel) (max c.views.vrNew 0) := by
    simp only [View] at *; omega
  have hv : ∀ f t, readView Arch.tso .acq f t = readView Arch.tso .acqPc f t := by
    intro f t; unfold readView; rfl
  have e1 : (LoadKind.acq == LoadKind.acq) = true := rfl
  have e2 : (LoadKind.acqPc == LoadKind.acq) = false := rfl
  simp only [readSuccs, Arch.loadKind, e1, e2, ite_true, Bool.false_eq_true, ite_false, hv, h, LoadKind.isAcquire]

/-- **(B3)** On TSO a plain write is a release write (`Arch.tso.plainStore`). -/
theorem writeSuccs_plain_eq_rel (c : Ctx) (xcl : Bool) (l : Loc) (v : Val) (tr : Option Time) (extra : View) :
    writeSuccs Arch.tso tid iv c .plain xcl l v tr extra = writeSuccs Arch.tso tid iv c .rel xcl l v tr extra := rfl

/-- **(B3)** A plain store tree and a release store tree have the same runs
on TSO (exclusive or not). -/
theorem runTree_store_plain_eq_rel {σ : Type} (c : Ctx) (xcl : Bool) (l : Loc) (v : Val) (ret : Bool → EvTree σ) :
    runTree Arch.tso tid iv c (.store .plain xcl l v ret) = runTree Arch.tso tid iv c (.store .rel xcl l v ret) := rfl

/-- **(B2)** A plain load tree and an `.acqPc` load tree have the same runs on
TSO. -/
theorem runTree_load_plain_eq_acqPc {σ : Type} (c : Ctx) (xcl : Bool) (l : Loc) (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.load .plain xcl l ret) = runTree Arch.tso tid iv c (.load .acqPc xcl l ret) := rfl

/-- **(B4)** A plain RMW is an acquire-release RMW on TSO (`plainRmw`), any
`noRet`. -/
theorem runTree_rmw_plain_eq_acqRel {σ : Type} (c : Ctx) (noRet : Bool) (l : Loc) (op : Val → Option Val)
    (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.rmw .plain noRet l op ret) = runTree Arch.tso tid iv c (.rmw .acqRel noRet l op ret) := rfl

/-- **(B4), `noRet`**: every RMW kind has the same runs on TSO. The read is
plain, the write is `.rel` after `storeKind`, and there is no bump. -/
theorem runTree_rmw_noRet_eq {σ : Type} (c : Ctx) (k k' : RmwKind) (l : Loc) (op : Val → Option Val)
    (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.rmw k true l op ret) = runTree Arch.tso tid iv c (.rmw k' true l op ret) := by
  have : ∀ k, runTree Arch.tso tid iv c (.rmw k true l op ret) = runTree Arch.tso tid iv c (.rmw .rel true l op ret) := by
    intro k; cases k <;> rfl
  rw [this k, this k']

/-- **`vRel ≤ vwOld`**: the thread's release view is below its write view.
It holds because `vRel` is raised only by a release write (`afterWrite` with
`k = .rel`), which raises `vwOld` by the same timestamp, and nothing lowers
either. It holds initially (all views `0`) and in every reachable
configuration (`reachableSemInf_relLeOld`), under any `Arch`. -/
def RelLeOld (vs : Views) : Prop := vs.vRel ≤ vs.vwOld

/-- With `vRel ≤ vrNew`, an `.acq` load and an `.acqPc` load are the same on
TSO. -/
theorem readSuccs_acq_eq_of_le {c : Ctx} (h : c.views.vRel ≤ c.views.vrNew) (xcl : Bool) (l : Loc) (noRet : Bool) :
    readSuccs Arch.tso iv c .acq xcl l noRet = readSuccs Arch.tso iv c .acqPc xcl l noRet := by
  have h' : max iv.addrR (max c.views.vrNew c.views.vRel) = max iv.addrR (max c.views.vrNew 0) := by
    simp only [View] at *; omega
  have hv : ∀ f t, readView Arch.tso .acq f t = readView Arch.tso .acqPc f t := by
    intro f t; unfold readView; rfl
  have e1 : (LoadKind.acq == LoadKind.acq) = true := rfl
  have e2 : (LoadKind.acqPc == LoadKind.acq) = false := rfl
  simp only [readSuccs, Arch.loadKind, e1, e2, ite_true, Bool.false_eq_true, ite_false, hv, h', LoadKind.isAcquire]

/-- `fence .sy`'s views, in closed form. -/
theorem fenceStep_sy_views (c : Ctx) :
    (fenceStep c .sy).views = { c.views with
      vrNew := max c.views.vrNew (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT))
      vwNew := max c.views.vwNew (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) } :=
  rfl

/-- After `fence .sy`, `vRel ≤ vrNew` (from `RelLeOld`). -/
theorem fenceStep_sy_relLe {c : Ctx} (h : RelLeOld c.views) : (fenceStep c .sy).views.vRel ≤ (fenceStep c .sy).views.vrNew := by
  rw [fenceStep_sy_views]; simp only [RelLeOld, View] at *; omega

/-- After a release write to `l`, `coh l` (the write's timestamp) is at most
`vwOld`. -/
theorem writeSuccs_coh_le_vwOld {c c2 : Ctx} {sk : StoreKind} (hsk : Arch.tso.storeKind sk = .rel) {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View}
    (h : c2 ∈ writeSuccs Arch.tso tid iv c sk xcl l v tr extra) : c2.views.getCoh l ≤ c2.views.vwOld := by
  have key : ∀ (c1 : Ctx) t νf b, c1.views.getCoh l < t →
      (afterWrite Arch.tso iv c1 .rel xcl l v t νf b).views.getCoh l ≤
        (afterWrite Arch.tso iv c1 .rel xcl l v t νf b).views.vwOld := by
    intro c1 t νf b hlt
    have e : (afterWrite Arch.tso iv c1 .rel xcl l v t νf b).views.getCoh l = (c1.views.setCoh l t).getCoh l := rfl
    rw [e, Views.getCoh_setCoh]
    simp only [afterWrite, ite_true]
    have e2 : (StoreKind.rel == StoreKind.nt) = false := rfl
    simp only [e2, Bool.false_eq_true, ite_false]
    simp only [View] at *; omega
  rcases (mem_writeSuccs_iff Arch.tso tid iv).mp h with ⟨t, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · simp only [writeOk, hsk, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [hsk]; exact key _ _ _ _ (by simp only [View, Time] at *; omega)
  · simp only [writeOk, hsk, Bool.and_eq_true, decide_eq_true_eq] at hok
    rw [hsk]; exact key _ _ _ _ (by simp only [promiseNowCtx, View, Time] at *; omega)

/-- **`fence .sy` absorbs the acquire-release bump** when `coh l ≤ vwOld`. -/
theorem fenceStep_bump {c : Ctx} {l : Loc} (h : c.views.getCoh l ≤ c.views.vwOld) :
    fenceStep { c with views := { c.views with vrNew := max c.views.vrNew (c.views.getCoh l),
                                               vwNew := max c.views.vwNew (c.views.getCoh l) } } .sy =
      fenceStep c .sy := by
  have h1 : max (max c.views.vrNew (c.views.getCoh l))
      (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) =
      max c.views.vrNew (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) := by
    simp only [View] at *; omega
  have h2 : max (max c.views.vwNew (c.views.getCoh l))
      (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) =
      max c.views.vwNew (max (max c.views.vrOld c.views.vrOldNR) (max c.views.vwOld c.views.vwOldNT)) := by
    simp only [View] at *; omega
  simp only [fenceStep, h1, h2]

private theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self ..), ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **(B4)** Under `RelLeOld`, an acquire-release RMW has the runs of a
release RMW on TSO. -/
theorem runTree_rmw_acqRel_eq_rel {σ : Type} {c : Ctx} (h : RelLeOld c.views) (noRet : Bool) (l : Loc)
    (op : Val → Option Val) (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.rmw .acqRel noRet l op ret) = runTree Arch.tso tid iv c (.rmw .rel noRet l op ret) := by
  cases noRet
  · have hf : Arch.tso.rmwFence = true := rfl
    simp only [runTree, Arch.rmwKind, RmwKind.loadKind, RmwKind.storeKind, Bool.false_eq_true, ite_false, hf,
      ite_true]
    rw [readSuccs_acq_eq_of_le _ (fenceStep_sy_relLe h)]
    apply flatMap_congr'
    rintro ⟨tr, old, c1⟩ -
    simp only
    split
    · rfl
    · apply flatMap_congr'
      intro c2 hc2
      have e : (RmwKind.acqRel == RmwKind.acqRel && !false) = true := rfl
      have e' : (RmwKind.rel == RmwKind.acqRel && !false) = false := rfl
      simp only [e, e', ite_true, Bool.false_eq_true, ite_false]
      have hb : c2.views.getCoh l ≤ c2.views.vwOld := writeSuccs_coh_le_vwOld tid iv rfl hc2
      congr 1
      exact fenceStep_bump (c := { c2 with rmwWrote := true }) hb
  · exact runTree_rmw_noRet_eq tid iv c _ _ l op ret

/-- **(B4)** Under `RelLeOld`, an acquire RMW has the runs of a release RMW on
TSO. -/
theorem runTree_rmw_acq_eq_rel {σ : Type} {c : Ctx} (h : RelLeOld c.views) (noRet : Bool) (l : Loc)
    (op : Val → Option Val) (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.rmw .acq noRet l op ret) = runTree Arch.tso tid iv c (.rmw .rel noRet l op ret) := by
  cases noRet
  · have hf : Arch.tso.rmwFence = true := rfl
    simp only [runTree, Arch.rmwKind, RmwKind.loadKind, RmwKind.storeKind, Bool.false_eq_true, ite_false, hf,
      ite_true]
    rw [readSuccs_acq_eq_of_le _ (fenceStep_sy_relLe h)]
    rfl
  · exact runTree_rmw_noRet_eq tid iv c _ _ l op ret

/-- **(B4), the collapse**: under `RelLeOld`, every two RMW kinds have the same
runs on TSO, any `noRet`, any operation, any continuation. -/
theorem runTree_rmw_eq {σ : Type} {c : Ctx} (h : RelLeOld c.views) (k k' : RmwKind) (noRet : Bool) (l : Loc)
    (op : Val → Option Val) (ret : Val → EvTree σ) :
    runTree Arch.tso tid iv c (.rmw k noRet l op ret) = runTree Arch.tso tid iv c (.rmw k' noRet l op ret) := by
  have : ∀ k, runTree Arch.tso tid iv c (.rmw k noRet l op ret) = runTree Arch.tso tid iv c (.rmw .rel noRet l op ret) := by
    intro k
    cases k
    · exact (runTree_rmw_plain_eq_acqRel tid iv c noRet l op ret).trans (runTree_rmw_acqRel_eq_rel tid iv h noRet l op ret)
    · exact runTree_rmw_acq_eq_rel tid iv h noRet l op ret
    · rfl
    · exact runTree_rmw_acqRel_eq_rel tid iv h noRet l op ret
  rw [this k, this k']

section Inv

variable {A : Arch}

/-- A read keeps `vRel` and `vwOld` (any `Arch`). -/
theorem readSuccs_relLe {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.views.vRel = c.views.vRel ∧ x.2.2.views.vwOld = c.views.vwOld := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rw [Option.ite_none_left_eq_some] at ht
    obtain ⟨-, ht⟩ := ht
    obtain rfl := Option.some.inj ht
    exact ⟨rfl, rfl⟩

/-- A write keeps `RelLeOld` (any `Arch`, any kind). -/
theorem writeSuccs_relLe {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr)
    (hc : RelLeOld c.views) : RelLeOld c'.views := by
  have key : ∀ (c1 : Ctx) t νf b, RelLeOld c1.views →
      RelLeOld (afterWrite A iv' c1 (A.storeKind k) xcl l v t νf b xr).views := by
    intro c1 t νf b h1
    unfold RelLeOld at *
    simp only [afterWrite]
    have e1 : (StoreKind.plain == StoreKind.rel) = false := rfl
    have e2 : (StoreKind.plain == StoreKind.nt) = false := rfl
    have e3 : (StoreKind.rel == StoreKind.rel) = true := rfl
    have e4 : (StoreKind.rel == StoreKind.nt) = false := rfl
    have e5 : (StoreKind.nt == StoreKind.rel) = false := rfl
    have e6 : (StoreKind.nt == StoreKind.nt) = true := rfl
    cases A.storeKind k <;>
      simp only [e1, e2, e3, e4, e5, e6, ite_true, ite_false, Bool.false_eq_true, View] at * <;> omega
  rcases (mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact key _ _ _ _ hc
  · exact key _ _ _ _ hc

/-- A run of any tree keeps `RelLeOld` (any `Arch`). -/
theorem runTree_relLe {σ : Type} (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx)
    (h : .ok (s, c') ∈ runTree A tid iv c tree) (hc : RelLeOld c.views) : RelLeOld c'.views := by
  refine runTree_preserves A tid iv (fun c c' => RelLeOld c.views → RelLeOld c'.views) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ ?_ ?_ ?_ tree c s c' h hc
  · intro c k xcl l noRet x hx h
    obtain ⟨e1, e2⟩ := readSuccs_relLe iv hx
    unfold RelLeOld at *; rw [e1, e2]; exact h
  · intro c iv' k xcl l v tr extra xr c' hc' h
    exact writeSuccs_relLe tid hc' h
  · intro c k h
    cases k <;> exact h
  · intro c l h; exact h
  · intro c k noRet l h
    unfold rmwPost; split <;> exact h

end Inv

section Machine

open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

variable {I : ISA} {A : Arch}

/-- Every thread of the configuration satisfies `RelLeOld`. -/
def CfgRelLeOld (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → RelLeOld t.views

/-- The initial configuration satisfies `CfgRelLeOld`. -/
theorem cfgRelLeOld_init (states : List I.State) (initMem : List (Loc × Val)) :
    CfgRelLeOld (Config.init states initMem : Config I) := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  exact Nat.le_refl _

/-- Installing a thread that satisfies `RelLeOld` keeps `CfgRelLeOld`. -/
theorem CfgRelLeOld.withThread {c : Config I} (hc : CfgRelLeOld c) {tid : Nat} {t th : Thread I}
    (ht : c.threads[tid]? = some t) {mem : Memory} (hth : RelLeOld th.views) :
    CfgRelLeOld (c.withThread tid th mem) := by
  intro i t' h
  rw [Config.withThread_get? c th mem (lt_size_of_get? ht)] at h
  split at h
  · obtain rfl := Option.some.inj h; exact hth
  · exact hc i t' h

/-- An instruction step keeps `CfgRelLeOld` (any `Arch`). -/
theorem instrSemInf_relLeOld {tid : Nat} {c c' : Config I} (hc : CfgRelLeOld c)
    (h : InstrSemInf A tid c c') : CfgRelLeOld c' := by
  obtain ⟨t, outs, o, ht, hs, ho, -, rfl⟩ := h
  refine hc.withThread ht ?_
  cases hex : I.exec t.st with
  | none => simp [stepOne, hex] at hs
  | some tree =>
    obtain ⟨st, c1, hr, hth, -⟩ := (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
    have h1 := runTree_relLe tid _ tree _ st c1 hr (hc tid t ht)
    rcases CertCut.finishInstr_views hth with e | e <;> rw [e] <;> exact h1

/-- A promise step keeps `CfgRelLeOld` (views unchanged). -/
theorem promSemInf_relLeOld {tid : Nat} {c c' : Config I} (hc : CfgRelLeOld c)
    (h : PromSemInf A tid c c') : CfgRelLeOld c' := by
  obtain ⟨t, w, ht, -, -, rfl⟩ := h
  exact hc.withThread ht (hc tid t ht)

/-- **`RelLeOld` is an invariant of the fuel-free machine** (any `Arch`). -/
theorem reachableSemInf_relLeOld {c c' : Config I} (h : ReachableSemInf A c c') (hc : CfgRelLeOld c) :
    CfgRelLeOld c' := by
  induction h with
  | refl => exact hc
  | step tid hs _ ih =>
    rcases hs with hs | hs
    · exact ih (instrSemInf_relLeOld hc hs)
    · exact ih (promSemInf_relLeOld hc hs)

/-- `fence .st` in closed form: it raises `vwNew` by `vwOld ⊔ vwOldNT` and
logs the fence; nothing else changes (any `Arch`). -/
theorem fenceStep_st (c : Ctx) :
    fenceStep c .st = { c with
      views := { c.views with vwNew := max c.views.vwNew (max c.views.vwOld c.views.vwOldNT) }
      log := c.log ++ [.fence .st] } := rfl

/-- `finishInstr` ignores the context's log. -/
theorem finishInstr_log (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (s : I.State) (c : Ctx)
    (L : List TraceEv) : finishInstr t d iv s { c with log := L } = finishInstr t d iv s c := rfl

variable (A) (tid : Nat) {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
include ht

/-- **(B1) `fence .st` at the machine level**: the outcome is `finishInstr` at
the thread's own context with `vwNew` raised by `vwOld ⊔ vwOldNT`; memory
and promises are unchanged. -/
theorem instrSemInf_fence_st_iff {s : I.State} (hex : I.exec t.st = some (.fence .st fun _ => .done s)) :
    InstrSemInf A tid c c' ↔ ∃ th,
      th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        { ctx0 tid t c.mem with
          views := { t.views with vwNew := max t.views.vwNew (max t.views.vwOld t.views.vwOldNT) } } ∧
      CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  rw [instrSemInf_fence_iff A tid ht hex, fenceStep_st]
  rfl

/-- **(B1), the stutter case**: when `vwOld ⊔ vwOldNT ≤ vwNew`, a `fence .st`
step is exactly a no-event step (the right-hand side of
`instrSemInf_done_iff`). -/
theorem instrSemInf_fence_st_stutter {s : I.State} (hex : I.exec t.st = some (.fence .st fun _ => .done s))
    (hle : max t.views.vwOld t.views.vwOldNT ≤ t.views.vwNew) :
    InstrSemInf A tid c c' ↔ ∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        (ctx0 tid t c.mem) ∧ CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  rw [instrSemInf_fence_st_iff A tid ht hex]
  have e : max t.views.vwNew (max t.views.vwOld t.views.vwOldNT) = t.views.vwNew := by
    simp only [View] at *; omega
  simp only [e]

omit ht in
/-- Trees with the same runs from `ctx0` have the same `RunOut`. -/
theorem runOut_congr {tree tree' : EvTree I.State}
    (h : runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) tree =
      runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) tree') (th : Thread I) (mem' : Memory) :
    RunOut A tid t c.mem tree th mem' ↔ RunOut A tid t c.mem tree' th mem' := by
  unfold RunOut; rw [h]

/-- `instrSemInf_iff_of_exec`, stated with any tree whose runs from `ctx0`
equal those of the thread's tree. -/
theorem instrSemInf_iff_of_exec_congr {tree tree' : EvTree I.State} (hex : I.exec t.st = some tree)
    (h : runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) tree =
      runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) tree') :
    InstrSemInf A tid c c' ↔ ∃ th mem', RunOut A tid t c.mem tree' th mem' ∧ CertOk A tid th mem' ∧
      c' = c.withThread tid th mem' := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  simp only [runOut_congr A tid h]

/-- **(B4) at the machine level**: an RMW step on TSO from a thread with
`RelLeOld` is the step of the same RMW with any other kind (e.g. a source
`cas.acq` and Kraken's `lock cmpxchg` `.acqRel`). -/
theorem instrSemInf_rmw_tso_congr {k k' : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {ret : Val → EvTree I.State} (hex : I.exec t.st = some (.rmw k noRet l op ret)) (hr : RelLeOld t.views) :
    InstrSemInf Arch.tso tid c c' ↔ ∃ th mem', RunOut Arch.tso tid t c.mem (.rmw k' noRet l op ret) th mem' ∧
      CertOk Arch.tso tid th mem' ∧ c' = c.withThread tid th mem' :=
  instrSemInf_iff_of_exec_congr Arch.tso tid ht hex (runTree_rmw_eq tid _ (c := ctx0 tid t c.mem) hr k k' noRet l op ret)

end Machine

section Witness

/-! Concrete half of the SB witness for (B2): memory `[y := 1 (T1), x := 1
(T0)]`, T0 after its store of `x` (`vRel = vwOld = coh x = 2`). T0's `.acq`
load of `y` can only read `1`; an `.acqPc` (plain) load can read `0` or `1`.
The other memory order is symmetric (T1 cannot read `x = 0`). -/

def sbX : Loc := ⟨0x100, 8⟩
def sbY : Loc := ⟨0x200, 8⟩

def sbMem : Memory := { init := [], msgs := #[⟨sbY, 1, 1⟩, ⟨sbX, 1, 0⟩] }

def sbCtx : Ctx := { views := { coh := [(sbX, 2)], vwOld := 2, vRel := 2 }, prom := [], mem := sbMem }

def sbIv : InstrViews := { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 }

example : (readSuccs Arch.tso sbIv sbCtx .acq false sbY).map (·.2.1) = [1] := by decide
example : (readSuccs Arch.tso sbIv sbCtx .acqPc false sbY).map (·.2.1) = [0, 1] := by decide

end Witness

end Kraken.Promising.Lower.Tso
