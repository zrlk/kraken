/-
**The heap relation along a consumer's steps** (any ISA): how the
allocation invariant at the source's heap use (`AllocInvAt … (heapUse s)`,
`Spike/Lib/HeapObl.lean`) and the thread's fresh labels (`FreshInv`) move
with the steps of a buffer allocation (`newBuf_callWS`, `newBuf_blkWS`), a
lane store (`lane_storeWS`), and every other source step of a body.

**The allocation** (the steps `newBuf_callWS`/`newBuf_blkWS` take, in order;
the source does not move until the landing):

- `AllocInvAt.ctrAdd`: the counter's add, idle at `hu` to pending at `hu`
  (the control holding the old count `hu`);
- `AllocInvAt.header`: the header store, pending at `hu` kept;
- `AllocInvAt.ctrAdd_fulfil`: the counter's add fulfilling a promise at
  the counter (the counter's value is its latest write not outstanding as a
  promise, `CtrAt`), idle at `hu` to pending at `hu`;
- `AllocInvAt.idle_append_out`, `AllocInvAt.pending_keep`: any other
  message outside the free range and off the counter (a runtime word), in
  either phase; `AllocInvAt.promise`: a promise anywhere, in either phase;
- `AllocInvAt.land`: the landing (`AllocRow.row_alloc`'s source step at
  the fresh label): pending at `heapUse s` to idle at `heapUse s'`,
  `heapUse s' = heapUse s + units` (`heapUse_newBuf`, given `units k τ =
  k · nWords us + 1`), the label placed (`FreshInv.place` moves the count
  on).

**The lane store** (`lane_storeWS`): the exchange's message is outside the
free range and off the counter, so `AllocInvAt` is kept
(`AllocInvAt.idle_append_out`); the source exchange appends a message at a
location the memory already has, and the thread allocates nothing, so
`heapUse` is kept (`heapUse_push_old`, `heapUse_swap`; the exchange step
with its allocation count, `SrcMem.src_swap_step_cfg_n`).

**Every other step**: a source step that leaves the memory and the
threads' allocation counts as they were keeps `heapUse` (`heapUse_congr`,
`heapUse_set`): the local steps (`heapUse_local`: `LocalRunS.run_source`
and `run_source_top` land at `s.ths.set! 0 { th with term, env }`), a call
and a return (`{ th with term, env, σs, stack }`). `print` (`outCfg`: the
trace grows, the memory is kept) is in `Spike/Lib/HeapPres.lean`
(`heapUse_outCfg`), which needs `Spike/Lib/SrcCalls.lean`.
-/
import Spike.Lib.HeapObl
import Spike.Lib.FreshSrc
import Spike.Lib.SrcMem
import Scc.Sem.Budget
import Spike.Lib.Src.BoxCount

namespace Spike.Lib.HeapPres

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (heapUse cellCount allocCount boxCount Fresh Inv1 ValRep wordLoc)
open Spike.Lib (AllocInvAt)
open Spike.Lib.AllocInv (CtrAt Pending FreshInv)
open Spike.Lib.AllocRow (ArenaOK freeR)

/-! ## Heap use of steps that allocate nothing -/

/-- **Heap use depends on the memory, the allocation counts and the box
count only.** -/
theorem heapUse_congr {s s' : Cfg} (hm : s'.mem = s.mem) (hn : allocCount s' = allocCount s)
    (hb : boxCount s' = boxCount s) : heapUse s' = heapUse s := by
  unfold heapUse cellCount
  rw [hm, hn, hb]

/-- Replacing a thread by one with the same allocation count keeps the
allocation count. -/
theorem allocCount_set {s : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    (hn : th'.nalloc = th.nalloc) : allocCount { s with ths := s.ths.set! i th' } = allocCount s := by
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [Scc.Sem.allocCount_eq, Scc.Sem.allocCount_eq]
  unfold Scc.Sem.nallocSum
  simp only [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt, dite_true, Array.toList_set]
  have := Scc.Sem.list_sum_set (l := s.ths.toList) (by simpa using hlt) th'
  simp only [Array.getElem_toList] at this
  omega

/-- **A thread replaced by one with the same allocation count and box
label, the memory kept**, keeps the heap use (local steps, calls, returns). -/
theorem heapUse_set {s s' : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    (hm : s'.mem = s.mem) (hths : s'.ths = s.ths.set! i th') (hn : th'.nalloc = th.nalloc)
    (ht : th'.tidLbl = th.tidLbl) : heapUse s' = heapUse s := by
  refine heapUse_congr hm ?_ (BoxCount.boxCount_set hi hths ht)
  have : allocCount s' = allocCount { s with ths := s.ths.set! i th' } := by
    rw [Scc.Sem.allocCount_eq, Scc.Sem.allocCount_eq, hths]
  rw [this, allocCount_set hi hn]

/-- **The landing of a local run** (`LocalRunS.run_source`,
`LocalRunS.run_source_top`) has the heap use it started with. -/
theorem heapUse_local {s : Cfg} {i : Nat} {th : TTh} (hi : s.ths[i]? = some th) (term : Expr) (env : Env) :
    heapUse { s with ths := s.ths.set! i { th with term := term, env := env } } = heapUse s :=
  heapUse_set hi rfl rfl rfl rfl

/-! ## Heap use of the exchange -/

/-- Deduplicating a list with one more element that it already has changes
nothing. -/
theorem eraseDups_append_mem {α : Type} [DecidableEq α] :
    ∀ {l : List α} {x : α}, x ∈ l → (l ++ [x]).eraseDups = l.eraseDups
  | [], _, h => by cases h
  | a :: l, x, h => by
    rw [List.cons_append, List.eraseDups_cons, List.eraseDups_cons, List.filter_append]
    by_cases hx : x = a
    · subst hx
      have : List.filter (fun b => !b == x) [x] = [] := by simp
      rw [this, List.append_nil]
    · have hm : x ∈ l.filter (fun b => !b == a) := List.mem_filter.mpr ⟨by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h hx
        · exact h, by simpa using hx⟩
      have : List.filter (fun b => !b == a) [x] = [x] := by simp [hx]
      rw [this, eraseDups_append_mem hm]
  termination_by l => l.length
  decreasing_by
    all_goals simp_wf
    all_goals have := List.length_filter_le (fun b => !b == a) l; omega

/-- **A message at a location the memory has** adds no cell. -/
theorem heapUse_push_old {s s' : Cfg} {m : WeakMem.Msg} (hm : s'.mem = s.mem.push m)
    (hl : ∃ m' ∈ s.mem.toList, m'.loc = m.loc) (hn : allocCount s' = allocCount s)
    (hb : boxCount s' = boxCount s) : heapUse s' = heapUse s := by
  unfold heapUse cellCount
  rw [hm, hn, hb, Array.toList_push, List.map_append, List.map_singleton]
  obtain ⟨m', hm', he⟩ := hl
  rw [eraseDups_append_mem (List.mem_map.mpr ⟨m', hm', he⟩)]

/-- **The source exchange keeps the heap use**: the message appended at a
location with a latest message (`SLatest`), the thread's allocation count
kept (and its box label). -/
theorem heapUse_swap {s : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th)
    {sa : WeakMem.Address} {j : Nat} (hj : Scc.Sem.MemRel.SLatest s.mem sa j) {v : WeakMem.Val} {mv : Nat}
    (hn : th'.nalloc = th.nalloc) (ht : th'.tidLbl = th.tidLbl) :
    heapUse { s with mem := s.mem.push ⟨sa, v, mv⟩, ths := s.ths.set! i th' } = heapUse s := by
  refine heapUse_push_old rfl ?_ ?_ (BoxCount.boxCount_set hi rfl ht)
  · obtain ⟨⟨m, hm, hl⟩, -⟩ := hj
    exact ⟨m, Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm), hl⟩
  · have : allocCount { s with mem := s.mem.push ⟨sa, v, mv⟩, ths := s.ths.set! i th' } =
        allocCount { s with ths := s.ths.set! i th' } := rfl
    rw [this, allocCount_set hi hn]

/-! ## The allocation's phases at the source's heap use -/

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory} {heap cells ctr : Nat}
  {units off : Nat → Ty → Nat} {hu : Nat} {c : Spike.Lib.Ctl}

/-- **Idle, a message outside the free range and off the counter** keeps
`AllocInvAt` at the same heap use (a lane store, a store to a placed word
or a runtime word), for any control not holding the counter. -/
theorem _root_.Spike.Lib.AllocInvAt.idle_append_out (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hc : ∀ w', c.hold ≠ some (ctr, w')) {t' : Thread I} {w : Msg}
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hw : w.loc ≠ wordLoc ctr)
    (hp : t'.prom = t.prom) {c' : Spike.Lib.Ctl} (hc' : ∀ w', c'.hold ≠ some (ctr, w')) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c' := by
  rcases h with ⟨hh, -⟩ | ⟨-, hctr, ha⟩
  · exact absurd hh (hc _)
  · exact .inr ⟨hc', hp ▸ hctr.append_ne hw, ha.store_out hfree hp⟩

/-- **The counter's add**, idle at `hu` to pending at `hu`: the message at
the counter of `hu` plus the buffer's units, the control now holding the
old count `hu` at the allocation. -/
theorem _root_.Spike.Lib.AllocInvAt.ctrAdd (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hc : ∀ w', c.hold ≠ some (ctr, w')) {t' : Thread I} {w : Msg} (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hp : t'.prom = t.prom)
    (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    {c' : Spike.Lib.Ctl} {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat}
    (ht : c'.term = .let_ x (.newBuf a τ) e) (hea : evalAt c'.env a = some (ta, ws)) (hk : numOf ws = some k)
    (hv : w.val.toNat = hu + units k τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c' := by
  rcases h with ⟨hh0, -⟩ | ⟨-, -, ha⟩
  · exact absurd hh0 (hc _)
  · exact .inl ⟨hh, fun _ => False,
      Pending.of_newBuf ht hea hk (hp ▸ hv ▸ CtrAt.append_self hw hpl) fun _ h => h.elim,
      ha.store_out hfree hp⟩

/-- **The header store while pending** at `hu`: a message off the counter,
below the pending buffer's base, is recorded as an exception; pending at
`hu` kept. -/
theorem _root_.Spike.Lib.AllocInvAt.header (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hh : c.hold = some (ctr, cst (.num hu))) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws))
    (hk : numOf ws = some k) {t' : Thread I} {w : Msg} (hw : w.loc ≠ wordLoc ctr)
    (hlt : w.loc.addr.toNat < heap + 16 * hu + off k τ) (hp : t'.prom = t.prom) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c := by
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · obtain ⟨hctr, hex⟩ := hpd.newBuf ht hea hk
    refine .inl ⟨hh, fun a' => ex a' ∨ a' = w.loc.addr.toNat,
      Pending.of_newBuf ht hea hk (hp ▸ hctr.append_ne hw) ?_, ha.store_ex hp⟩
    rintro a' (h | rfl)
    · exact hex a' h
    · exact hlt
  · exact absurd hh (hn _)

/-- **The box header store while pending** at `hu` (`AllocInvAt.header` at
`let x = new a in e`): a message off the counter below the pending box's
base is recorded as an exception. -/
theorem _root_.Spike.Lib.AllocInvAt.headerBox (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hh : c.hold = some (ctr, cst (.num hu))) {x : String} {a : At} {e : Expr} {ty : Ty}
    {ws : List Word} (ht : c.term = .let_ x (.new a) e) (hea : evalAt c.env a = some (ty, ws))
    {t' : Thread I} {w : Msg} (hw : w.loc ≠ wordLoc ctr)
    (hlt : w.loc.addr.toNat < heap + 16 * hu + off 1 ty) (hp : t'.prom = t.prom) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c := by
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · obtain ⟨hctr, hex⟩ := hpd.box ht hea
    refine .inl ⟨hh, fun a' => ex a' ∨ a' = w.loc.addr.toNat,
      Pending.of_box ht hea (hp ▸ hctr.append_ne hw) ?_, ha.store_ex hp⟩
    rintro a' (h | rfl)
    · exact hex a' h
    · exact hlt
  · exact absurd hh (hn _)

/-- **Pending, a message outside the free range and off the counter** (a
runtime word other than the header) keeps pending at `hu`. -/
theorem _root_.Spike.Lib.AllocInvAt.pending_keep (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hh : c.hold = some (ctr, cst (.num hu))) {t' : Thread I} {w : Msg}
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hw : w.loc ≠ wordLoc ctr)
    (hp : t'.prom = t.prom) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c := by
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · exact .inl ⟨hh, ex, hpd.keep fun _ hctr => hp ▸ hctr.append_ne hw, ha.store_out hfree hp⟩
  · exact absurd hh (hn _)

/-- **Pending at `hu` gives the counter and the contract** the landing
needs (`AllocRow.row_alloc`'s premises): the counter at `hu` plus the
buffer's units, and the contract at `hu` with its exceptions below the
buffer's base. -/
theorem _root_.Spike.Lib.AllocInvAt.pending (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hh : c.hold = some (ctr, cst (.num hu))) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws))
    (hk : numOf ws = some k) :
    CtrAt tm t.prom ctr (hu + units k τ) ∧ ∃ ex, ArenaOK Λ lbl lsize t tm heap cells hu ex ∧
      ∀ a', ex a' → a' < heap + 16 * hu + off k τ := by
  rcases h with ⟨-, ex, hpd, ha⟩ | ⟨hn, -⟩
  · obtain ⟨hctr, hex⟩ := hpd.newBuf ht hea hk
    exact ⟨hctr, ex, ha, hex⟩
  · exact absurd hh (hn _)

/-- **The landing**, pending at `hu` to idle at `hu + units k τ`: the
contract there with the label placed (`row_alloc`'s), the control holding
nothing. -/
theorem _root_.Spike.Lib.AllocInvAt.land (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hh : c.hold = some (ctr, cst (.num hu))) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws))
    (hk : numOf ws = some k) {lbl' : WeakMem.AllocLabel → Option Nat} {lsize' : WeakMem.AllocLabel → Nat}
    (ha : ArenaOK Λ lbl' lsize' t tm heap cells (hu + units k τ) (fun _ => False))
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) :
    AllocInvAt Λ lbl' lsize' t tm heap cells ctr units off (hu + units k τ) c' :=
  .inr ⟨fun w h => (by rw [hc'] at h; cases h), (h.pending hh ht hea hk).1, ha⟩

/-- **A promise**, in either phase, keeps `AllocInvAt` at the same heap use:
the promised message is outstanding, so the counter's value
(`CtrAt.promise`) and the contract (a message in the free range is a
promise) are kept. -/
theorem _root_.Spike.Lib.AllocInvAt.promise (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    {t' : Thread I} (w : Msg) (hp : t'.prom = t.prom ++ [(tm.append w).2]) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c := by
  have hk : ∀ {ex : Nat → Prop}, ArenaOK Λ lbl lsize t tm heap cells hu ex →
      ArenaOK Λ lbl lsize t' (tm.append w).1 heap cells hu ex := fun ha =>
    ha.keep (fun _ _ => rfl) (fun k' w' hg _ hx => by
        rw [Spike.Lib.AllocRow.get?_append] at hg
        split at hg
        · rename_i he; exact .inr (hp ▸ List.mem_append_right _ (List.mem_singleton.mpr he))
        · exact .inl ⟨hg, hx⟩)
      fun _ _ _ _ hm => hp ▸ List.mem_append_left _ hm
  rcases h with ⟨hh, ex, hpd, ha⟩ | ⟨hn, hctr, ha⟩
  · exact .inl ⟨hh, ex, hpd.keep fun _ hctr => hp ▸ hctr.promise w, hk ha⟩
  · exact .inr ⟨hn, hp ▸ hctr.promise w, hk ha⟩

/-- **The counter's add fulfilling a promise**, idle at `hu` to pending at
`hu`: the promised message `q` at the counter (outside the free range) of
`hu` plus the buffer's units, above the latest message not outstanding
(`stepOne_rmw_cases`' fulfilment), the memory unchanged and `q` no longer
outstanding (`CtrAt.fulfil`); the control holding the old count `hu`. -/
theorem _root_.Spike.Lib.AllocInvAt.ctrAdd_fulfil
    (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c) (hc : ∀ w', c.hold ≠ some (ctr, w'))
    {q : Time} {w : Msg} (hq : tm.get? q = some w) (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat)
    (hgt : ∀ k', Scc.Sem.TLatestP tm t.prom ctr k' → k' < q) (hnd : t.prom.Nodup)
    {t' : Thread I} (hp : t'.prom = t.prom.erase q)
    {c' : Spike.Lib.Ctl} {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat}
    (ht : c'.term = .let_ x (.newBuf a τ) e) (hea : evalAt c'.env a = some (ta, ws)) (hk : numOf ws = some k)
    (hv : w.val.toNat = hu + units k τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInvAt Λ lbl lsize t' tm heap cells ctr units off hu c' := by
  rcases h with ⟨hh0, -⟩ | ⟨-, hctr, ha⟩
  · exact absurd hh0 (hc _)
  · refine .inl ⟨hh, fun _ => False,
      Pending.of_newBuf ht hea hk (hp ▸ hv ▸ hctr.fulfil hq hw hgt hnd) fun _ h => h.elim,
      ha.keep (fun _ _ => rfl) (fun _ _ hg _ hx => .inl ⟨hg, hx⟩) fun k' w' hg hfr hm => ?_⟩
    have hne : k' ≠ q := by
      rintro rfl
      rw [hq] at hg
      cases hg
      exact hfree hfr
    exact hp ▸ (List.Nodup.mem_erase_iff hnd).mpr ⟨hne, hm⟩

/-- **The counter's add at any allocation site** (`ctrAdd` over
`AllocSite True`: a buffer or a box), idle at `hu` to pending at `hu`. -/
theorem _root_.Spike.Lib.AllocInvAt.ctrAddS (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c)
    (hc : ∀ w', c.hold ≠ some (ctr, w')) {t' : Thread I} {w : Msg} (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hp : t'.prom = t.prom)
    (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    {c' : Spike.Lib.Ctl} {x : String} {n : Nat} {τ : Ty} {e : Expr}
    (hs : Spike.Lib.AllocSite True c' x n τ e)
    (hv : w.val.toNat = hu + units n τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInvAt Λ lbl lsize t' (tm.append w).1 heap cells ctr units off hu c' := by
  rcases h with ⟨hh0, -⟩ | ⟨-, -, ha⟩
  · exact absurd hh0 (hc _)
  · exact .inl ⟨hh, fun _ => False,
      ⟨x, n, τ, e, hs, hp ▸ hv ▸ CtrAt.append_self hw hpl, fun _ h => h.elim⟩,
      ha.store_out hfree hp⟩

/-- **The counter's add fulfilling a promise at any allocation site**
(`ctrAdd_fulfil` over `AllocSite True`). -/
theorem _root_.Spike.Lib.AllocInvAt.ctrAdd_fulfilS
    (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off hu c) (hc : ∀ w', c.hold ≠ some (ctr, w'))
    {q : Time} {w : Msg} (hq : tm.get? q = some w) (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat)
    (hgt : ∀ k', Scc.Sem.TLatestP tm t.prom ctr k' → k' < q) (hnd : t.prom.Nodup)
    {t' : Thread I} (hp : t'.prom = t.prom.erase q)
    {c' : Spike.Lib.Ctl} {x : String} {n : Nat} {τ : Ty} {e : Expr}
    (hs : Spike.Lib.AllocSite True c' x n τ e)
    (hv : w.val.toNat = hu + units n τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInvAt Λ lbl lsize t' tm heap cells ctr units off hu c' := by
  rcases h with ⟨hh0, -⟩ | ⟨-, hctr, ha⟩
  · exact absurd hh0 (hc _)
  · refine .inl ⟨hh, fun _ => False,
      ⟨x, n, τ, e, hs, hp ▸ hv ▸ hctr.fulfil hq hw hgt hnd, fun _ h => h.elim⟩,
      ha.keep (fun _ _ => rfl) (fun _ _ hg _ hx => .inl ⟨hg, hx⟩) fun k' w' hg hfr hm => ?_⟩
    have hne : k' ≠ q := by
      rintro rfl
      rw [hq] at hg
      cases hg
      exact hfree hfr
    exact hp ▸ (List.Nodup.mem_erase_iff hnd).mpr ⟨hne, hm⟩

/-! ## The landing's source step -/

/-- **The thread's next label is fresh** under the one-thread invariant
(its memory relation places every message's label) and `FreshInv`. -/
theorem fresh_of_inv1 {ts : Nat → Option Nat} {s : Cfg} (h : Inv1 Λ lbl lsize ts t tm s.mem) {base n i na : Nat}
    (hf : FreshInv lbl base n i na) : Fresh s (freshLabel base n i na) :=
  Spike.Lib.fresh_of_placed (fun m hm => (h.mem.lbl_mem m hm).imp fun _ h => h.1) hf.fresh

/-- **The heap use after the allocation**: the memory with the buffer of
`n` words at a fresh label, the thread's allocation count bumped and its
box label kept: `n` words plus the header (the boxes counted by the
allocations, `hle`). -/
theorem heapUse_alloc {s : Cfg} {i : Nat} {th th' : TTh} (hi : s.ths[i]? = some th) {l : WeakMem.AllocLabel}
    (hfresh : Fresh s l) {n : Nat} {z : Option (List WeakMem.Val)} (hn : th'.nalloc = th.nalloc + 1)
    (ht : th'.tidLbl = th.tidLbl) (hle : boxCount s ≤ allocCount s) :
    heapUse { s with mem := (allocBuf l n z (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! i th' } =
      heapUse s + (n + 1) := by
  have hb := BoxCount.boxCount_set
    (s' := { s with mem := (allocBuf l n z (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! i th' }) hi rfl ht
  have ha := BoxCount.allocCount_succ
    (s' := { s with mem := (allocBuf l n z (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! i th' }) hi rfl hn
  obtain ⟨hlt, rfl⟩ := Array.getElem?_eq_some_iff.mp hi
  refine BoxCount.heapUse_add (Scc.Sem.heapUse_newBuf (st := stOf s.mem s.pairs s.ths[i]) rfl rfl hfresh hlt ?_ hn)
    (by omega) hb hle
  simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hlt]

/-- **The landing at the source's heap use**: from pending at `heapUse s`
(the control `c` at `let x = newBuf a τ in e` holding the old count), the
boxes counted by the allocations (`boxCount s ≤ allocCount s`), the
one-thread invariant, the thread `th` at `c` with its next label fresh
(`FreshInv`), and the allocation's sizes (`units k τ` its `k · nWords us`
words plus the header, fitting the arena): the source steps at the fresh
label (`row_alloc`), the heap use grows by the units, `AllocInvAt` is idle
at the new heap use with the label placed, and `FreshInv` moves on. -/
theorem land_step {p : Prog} {kn : Promises.Knobs} {arch : WeakMem.Arch} {ts : Nat → Option Nat} {s : Cfg}
    {i : Nat} {th : TTh}
    (h : AllocInvAt Λ lbl lsize t tm heap cells ctr units off (heapUse s) c)
    (hh : c.hold = some (ctr, cst (.num (heapUse s)))) (h1 : Inv1 Λ lbl lsize ts t tm s.mem)
    (hi : s.ths[i]? = some th) (htc : th.term = c.term) (hec : th.env = c.env)
    {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat} {us : List Acc}
    (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws)) (hk : numOf ws = some k)
    (hus : accs (close th.σs τ) = some us) (hfr : FreshInv lbl s.lbase s.n i th.nalloc) (hn0 : 0 < s.n)
    (hun : units k τ = k * nWords us + 1) (hoff : off k τ % 8 = 0)
    (hfit : off k τ + 8 * (k * nWords us) ≤ 16 * units k τ) (hle : heapUse s + units k τ ≤ cells)
    (hz : ∀ vs, zeroWords (close th.σs τ) = some vs → ∀ v ∈ vs,
      ValRep (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then
        some (heap + 16 * heapUse s + off k τ) else lbl l') v 0)
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) (hbx : boxCount s ≤ allocCount s) :
    ∃ th', { s with mem := (allocBuf (freshLabel s.lbase s.n i th.nalloc) (k * nWords us)
        (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! i th' } ∈
          threadSteps p kn arch s i ∧ th'.term = e ∧
      th'.env = (x, .refine (.loc .own (.array (.lit k) (close th.σs τ)))
          (.ini (.lit (if (AllocSrc.newBufZero (close th.σs τ)).isSome then k else 0))),
        [cst (.loc ⟨freshLabel s.lbase s.n i th.nalloc, 0⟩ 0)]) :: th.env ∧
      th'.promises = th.promises ∧ th'.σs = th.σs ∧ th'.stack = th.stack ∧ th'.nalloc = th.nalloc + 1 ∧
      heapUse { s with mem := (allocBuf (freshLabel s.lbase s.n i th.nalloc) (k * nWords us)
        (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem, ths := s.ths.set! i th' } =
        heapUse s + units k τ ∧
      Inv1 Λ (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l')
        (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then k * nWords us else lsize l')
        (fun k' => if s.mem.size ≤ k' ∧ k' < s.mem.size + k * nWords us then some 0 else ts k') t tm
        (allocBuf (freshLabel s.lbase s.n i th.nalloc) (k * nWords us)
          (AllocSrc.newBufZero (close th.σs τ)) (stOf s.mem s.pairs th)).1.mem ∧
      AllocInvAt Λ (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l')
        (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then k * nWords us else lsize l') t tm heap cells
        ctr units off (heapUse s + units k τ) c' ∧
      FreshInv (fun l' => if l' = freshLabel s.lbase s.n i th.nalloc then
          some (heap + 16 * heapUse s + off k τ) else lbl l') s.lbase s.n i (th.nalloc + 1) := by
  obtain ⟨-, ex, ha, hex⟩ := h.pending hh ht hea hk
  have ht' : th.term = .let_ x (.newBuf a τ) e := htc.trans ht
  have hea' : evalAt th.env a = some (ta, ws) := hec ▸ hea
  obtain ⟨th', hs, h1', h2, h3, h4, h5, h6, hinv, ha'⟩ :=
    Spike.Lib.AllocRow.row_alloc (p := p) (kn := kn) (arch := arch) h1 ha hi ht' hea' hk hus hfr.fresh
      hoff hfit hle hex hz
  refine ⟨th', hs, h1', h2, h3, h4, h5, h6, ?_, hinv, h.land hh ht hea hk ha' hc', hfr.place hn0 _⟩
  rw [heapUse_alloc hi (fresh_of_inv1 h1 hfr) h6 (BoxCount.threadSteps_tidLbl hs hi rfl) hbx, hun]

end Spike.Lib.HeapPres
