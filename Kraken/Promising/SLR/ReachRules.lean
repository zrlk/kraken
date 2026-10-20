/-
Bounded reach (`K1`/`K2`, `NPSafe`'s step and prepay conjuncts)
for the event rules of the SLR-adapted resource model, and
their composition through an instruction's event tree.

`NPSafe` asks every step and every prepayment from `c₁` (ghost `g₁`, the
thread holding `r`) to `(r', g')` to satisfy, for every `b ≤ c₁.mem.last`,

- **K2** (`ReachFrame g₁ g' c₁.mem.last`, `SLR/Cond3.lean`): no resource's
  bounded reach through messages `≤ b` grows;
- **K1**: if the thread's write floor `max vwNew vCAP` after the step is
  `≤ b`, its own bounded reach through messages `≤ b` did not grow.

## The event rules (`RStep`)

`RStep B r g r' g' cx` is the pair K2/K1 for one ghost change inside an
instruction, with K1's floor taken from the context `cx` the instruction
continues from (views only grow along an instruction, `Ctx.VMono`, and
`finishInstr` keeps `vwNew` and raises `vCAP`, so the floor of a context
bounds the floor of the thread after the instruction, `RStep.finish`).

- **stores** (`RStep.store`): the slots `ss` of a release write are on its
  message; for an appended message that is `|M| + 1 > B`, so K2 holds; a
  write that fulfils an (old, non-pending) promise must attach no slot
  (`ss = []`: it is relaxed, or a release with no acquire or update id; the
  "no retroactive release mode" discipline, `SLR/Cond3.lean`). K1 holds
  with no floor hypothesis: the resource only loses slots and gains a
  write-set entry.
- **RMWs** (`RStep.rmw`): as stores, and the claimed update slots of the
  message read, `(l, tr)`, move into the thread. They are acquirable by
  everybody through `CanAcqB.upd` as long as `tr ≤ b`, so K1 needs
  `tr ≤ wfloor` after the RMW when something is claimed: an acquire RMW
  (`rmw_tr_le_wfloor_acq`, from `readSuccs_acq_vwNew`) or an
  acquire-release RMW (`rmw_tr_le_wfloor_acqRel`, from `rmwPost_vwNew`). A
  relaxed RMW that claims slots does not satisfy K1 in general.
- **fulfilling a pending promise** (`RStep.unpend`): only `pend` changes.
- **reads and fences** keep `(r, g)` in the erasure WP (`EvTree.EraseWP`:
  SLR's read rules transfer in the assertion layer, not in erasure), so they
  satisfy K1/K2 trivially (`RStep.refl`, `RStep.mono`). The reach-level
  lemma for a ghost **acquisition** (a slot moved from `u` into the thread
  at an acquire-type event, should a future WP do that) is
  `RStep.acquire`/`RStep.acquire_of_acqStep` (`AcqStep.le_wfloor`).
- **prepayments** (`prepay_K2`/`prepay_K1`, `prepayRmw_K2`/`prepayRmw_K1`,
  in `NPSafe`'s shape): the slots sit at `c₁.mem.last + 1`; a prepaid RMW's
  claims need `tr ≤` the thread's floor *before* the promise (`NPSafe`'s K1
  for a prepayment looks at `c₁`'s thread).

## Composition (`EvTree.EraseWPR`)

`EvTree.EraseWPR` is `EvTree.EraseWP` with, at every write, the obligation
`RStep c.mem.last r g r' g' cx'` next to erasure, and the extra hypothesis
`c.mem.last ≤ cx.mem.last` (memory only grows along an instruction).
`EvTree.EraseWPR.toEraseWP` turns it into an ordinary `EvTree.EraseWP` whose
postcondition also carries `RStep` from the instruction's start, so
instruction rules get K1/K2 for free: `runTree_eraseWPR` (the frame),
`Erase.npStepR` (the per-instruction lemma with `NPSafe`'s K1/K2), and the
node shapes `EvTree.eraseWPR_access/load/fence/store/rmw/store_pend/
rmw_pend` (and `caspHalf/caspTree` in `SLR/ReachRulesCasp.lean`, which keeps
this file free of the AArch64 ISA), whose remaining obligations are those of the
`EraseWP` shapes plus `tw ∈ prom → ss = []` and, for an RMW that claims, the
floor bound.
-/
import Kraken.Promising.SLR.Escrow
import Kraken.Promising.SLR.Cond3

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Products of slot resources -/

theorem acq_prod_slots {L : List Slot} {y : Loc} {ι : PredId}
    (h : 1 ≤ (Res.prod (L.map (·.res))).acq y ι) : ∃ s ∈ L, 1 ≤ s.res.acq y ι := by
  induction L with
  | nil => simp [Res.prod, Res.unit] at h
  | cons s L ih =>
    simp only [List.map_cons, Res.prod_cons, Res.op] at h
    by_cases hs : 1 ≤ s.res.acq y ι
    · exact ⟨s, List.mem_cons_self, hs⟩
    · obtain ⟨s', hs', h'⟩ := ih (by omega)
      exact ⟨s', List.mem_cons_of_mem _ hs', h'⟩

theorem pos_prod_slots {L : List Slot} {y : Loc}
    (h : 0 < ((Res.prod (L.map (·.res))).wr y).q) : ∃ s ∈ L, 0 < (s.res.wr y).q := by
  induction L with
  | nil => simp [Res.prod, Res.unit, Perm.unit] at h
  | cons s L ih =>
    simp only [List.map_cons, Res.prod_cons] at h
    rcases Res.pos_op.mp h with h | h
    · exact ⟨s, List.mem_cons_self, h⟩
    · obtain ⟨s', hs', h'⟩ := ih h
      exact ⟨s', List.mem_cons_of_mem _ hs', h'⟩

/-! ## The core of K1 for a write event -/

/-- **A write event's own reach.** The thread's resource after the event,
`r'`, together with the slots `ss` it attaches to its message, is its
resource before, `r`, plus `extra` slots (the claimed slots of an RMW) plus
a write-set entry. If no slot at or below `b` appears, no update id is
added, and every `extra` slot is acquirable by `r` through messages `≤ b`,
then the bounded reach of `r'` is covered by that of `r`. -/
theorem reachB_of_split {g g' : Ghost} {r r' : Res} {b : Time} {ss extra : List Slot} {x : Loc}
    {p : Val × Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ y ι, ι ∈ g'.upd y → ι ∈ g.upd y)
    (hres : r'.op (Res.prod (ss.map (·.res))) = (r.op (Res.prod (extra.map (·.res)))).addW x p)
    (hext : ∀ s ∈ extra, s ∈ g.u ∧ CanAcqB g.u g.upd r.acq b s.key s.id)
    {y : Loc} (h : reachB r' g' y b) : reachB r g y b := by
  refine h.cover hu hU (fun z ι ha => ?_) (fun z hz => ?_)
  · have he := congrArg (fun R => R.acq z ι) hres
    simp only [Res.op, Res.addW_acq] at he
    by_cases h1 : 1 ≤ r.acq z ι
    · exact .inl h1
    · obtain ⟨s, hs, hsa⟩ := acq_prod_slots (L := extra) (y := z) (ι := ι) (by omega)
      exact .inr ⟨s, (hext s hs).1, (hext s hs).2, hsa⟩
  · have h1 : 0 < ((r'.op (Res.prod (ss.map (·.res)))).wr z).q :=
      Res.pos_op.mpr (.inl hz)
    rw [hres, Res.addW_q] at h1
    rcases Res.pos_op.mp h1 with h1 | h1
    · exact .inl h1
    · obtain ⟨s, hs, hq⟩ := pos_prod_slots h1
      exact .inr ⟨s, (hext s hs).1, (hext s hs).2.key_le, (hext s hs).2, hq⟩

/-- `reachB_of_split` with nothing extra (a store, a prepaid store). -/
theorem reachB_of_split0 {g g' : Ghost} {r r' : Res} {b : Time} {ss : List Slot} {x : Loc} {p : Val × Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ y ι, ι ∈ g'.upd y → ι ∈ g.upd y)
    (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW x p) {y : Loc} (h : reachB r' g' y b) :
    reachB r g y b :=
  reachB_of_split (extra := []) hu hU (by simp only [List.map_nil, Res.prod_nil, Res.op_unit]; exact hres)
    (fun _ h => by cases h) h

/-- The claimed slots of an RMW reading `(x, tr)` are update slots of that
message: acquirable by everybody through messages `≤ b` once `tr ≤ b`. -/
theorem claimedSlots_canAcqB {g : Ghost} {x : Loc} {tr b : Time} (A : Loc → PredId → Nat) (htr : tr ≤ b) :
    ∀ s ∈ claimedSlots g x tr, s ∈ g.u ∧ CanAcqB g.u g.upd A b s.key s.id := by
  intro s hs
  simp only [claimedSlots, List.mem_filter, updSlot, decide_eq_true_eq] at hs
  obtain ⟨hs, hk, hid⟩ := hs
  refine ⟨hs, .upd hs (by rw [hk]; exact htr) (by rw [hk]; exact hid)⟩

/-! ## K2 for the ghost changes of the event rules -/

section Frame

variable {g : Ghost} {x : Loc} {tr tw : Time} {rel : Bool} {ss : List Slot} {B : Time}

/-- The slots of a release write are fresh for the bound `B`: every one is
on a message above `B`. -/
def FreshSlots (B : Time) (ss : List Slot) : Prop := ∀ s ∈ ss, B < s.key.2

theorem FreshSlots.nil (B : Time) : FreshSlots B [] := fun _ h => by cases h

theorem FreshSlots.of_key {B : Time} {ss : List Slot} {x : Loc} {tw : Time} (hk : ∀ s ∈ ss, s.key = (x, tw))
    (hlt : B < tw) : FreshSlots B ss :=
  fun s hs => by rw [hk s hs]; exact hlt

/-- **K2 for a store** (plain or release): the new slots are fresh. -/
theorem ReachFrame.store (hss : FreshSlots B ss) : ReachFrame g (storeGhost g x tw rel ss) B :=
  ReachFrame.of_slots (fun s hs hk => (mem_store_u.mp hs).elim id fun h => absurd hk (by have := hss s h; omega_t))
    (fun _ _ h => h)

/-- **K2 for a successful RMW**: claims only remove slots, the new ones are
fresh. -/
theorem ReachFrame.rmw (hss : FreshSlots B ss) : ReachFrame g (rmwGhost g x tr tw rel ss) B :=
  ReachFrame.of_slots
    (fun s hs hk => (mem_rmw_u.mp hs).elim (fun h => h.1) fun h => absurd hk (by have := hss s h; omega_t))
    (fun _ _ h => h)

/-- **K2 for fulfilling a pending promise**: only `pend` changes. -/
theorem ReachFrame.unpend (ts : Time) : ReachFrame g (unpend g ts) B := fun _ _ _ _ h => h

/-- **K2 for a prepaid release store**. -/
theorem ReachFrame.prepay (hss : FreshSlots B ss) : ReachFrame g (prepayGhost g x tw ss) B :=
  ReachFrame.store (x := x) (tw := tw) (rel := true) hss

/-- **K2 for a prepaid release RMW half**. -/
theorem ReachFrame.prepayRmw (hss : FreshSlots B ss) : ReachFrame g (prepayRmwGhost g x tr tw ss) B :=
  ReachFrame.rmw (x := x) (tr := tr) (tw := tw) (rel := true) hss

end Frame

/-! ## K1/K2 for one ghost change inside an instruction -/

/-- **K2 and K1 for one ghost change `(r, g) ↦ (r', g')`** inside an
instruction of a configuration with `|M| = B`, the instruction continuing
from context `cx` (K1's floor: `cx.views.wfloor`). -/
def RStep (B : Time) (r : Res) (g : Ghost) (r' : Res) (g' : Ghost) (cx : Ctx) : Prop :=
  ReachFrame g g' B ∧ ∀ b, b ≤ B → cx.views.wfloor ≤ b → ∀ x, reachB r' g' x b → reachB r g x b

namespace RStep

variable {B : Time} {r r₁ r₂ r' : Res} {g g₁ g₂ g' : Ghost} {cx cx' : Ctx}

theorem refl (B : Time) (r : Res) (g : Ghost) (cx : Ctx) : RStep B r g r g cx :=
  ⟨ReachFrame.refl g B, fun _ _ _ _ h => h⟩

/-- A later context (higher floor) weakens K1's hypothesis. -/
theorem mono (h : RStep B r g r' g' cx) (hf : cx.views.wfloor ≤ cx'.views.wfloor) : RStep B r g r' g' cx' :=
  ⟨h.1, fun b hb hb' => h.2 b hb (Nat.le_trans hf hb')⟩

theorem trans (h₁ : RStep B r g r₁ g₁ cx) (h₂ : RStep B r₁ g₁ r₂ g₂ cx') (hf : cx.views.wfloor ≤ cx'.views.wfloor) :
    RStep B r g r₂ g₂ cx' :=
  ⟨h₁.1.trans h₂.1, fun b hb hb' x h => h₁.2 b hb (Nat.le_trans hf hb') x (h₂.2 b hb hb' x h)⟩

/-- K1 after the instruction: the thread `th` that `finishInstr` produces
from the final context has a floor at least the context's. -/
theorem finish (h : RStep B r g r' g' cx) {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews}
    {st : I.State} {th : Thread I} (hth : th ∈ finishInstr t d iv st cx) :
    ∀ b, b ≤ B → max th.views.vwNew th.views.vCAP ≤ b → ∀ x, reachB r' g' x b → reachB r g x b := by
  intro b hb hf
  obtain ⟨e1, -, -, e4⟩ := finishInstr_vmono hth
  refine h.2 b hb ?_
  simp only [Views.wfloor] at hf ⊢
  omega_t

/-- **A store** (plain or release): fresh slots, the resource only loses
slots. K1 needs no floor. -/
theorem store {x : Loc} {tw : Time} {rel : Bool} {ss : List Slot} {p : Val × Time} (hss : FreshSlots B ss)
    (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW x p) (cx : Ctx) :
    RStep B r g r' (storeGhost g x tw rel ss) cx := by
  refine ⟨ReachFrame.store hss, fun b hb _ y h =>
    reachB_of_split0 (g := g) (g' := storeGhost g x tw rel ss) (fun s hs hk => ?_) (fun _ _ h => h) hres h⟩
  rcases mem_store_u.mp hs with hs | hs
  · exact hs
  · have := hss s hs; omega_t

/-- **A successful RMW**: fresh slots; the claimed update slots of `(x, tr)`
move into the thread, which K1 allows when `tr` is at most the floor after
the RMW (or nothing is claimed). -/
theorem rmw {x : Loc} {tr tw : Time} {rel : Bool} {ss : List Slot} {p : Val × Time} (hss : FreshSlots B ss)
    (hres : r'.op (Res.prod (ss.map (·.res))) = (r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p)
    (htr : claimedSlots g x tr ≠ [] → tr ≤ cx.views.wfloor) :
    RStep B r g r' (rmwGhost g x tr tw rel ss) cx := by
  refine ⟨ReachFrame.rmw hss, fun b hb hf y h =>
    reachB_of_split (g := g) (g' := rmwGhost g x tr tw rel ss) (fun s hs hk => ?_) (fun _ _ h => h) hres ?_ h⟩
  · rcases mem_rmw_u.mp hs with hs | hs
    · exact hs.1
    · have := hss s hs; omega_t
  · by_cases hc : claimedSlots g x tr = []
    · rw [hc]; intro _ h; cases h
    · exact claimedSlots_canAcqB r.acq (Nat.le_trans (htr hc) hf)

/-- **Fulfilling a pending promise**: resource unchanged, only `pend`
changes. -/
theorem unpend (ts : Time) (cx : Ctx) : RStep B r g r (unpend g ts) cx :=
  ⟨ReachFrame.unpend ts, fun _ _ _ _ h => h⟩

/-- **An acquisition** (reach level; not a step of the current erasure WP,
whose reads keep `(r, g)`): the thread takes the slot `s` from `u`, which it
may acquire through messages up to any `b` above the floor (e.g. it holds
`s.id` for `s.key.1`, or `s.id` is an update id, and `s.key.2 ≤ floor`);
no slot at or below `B` appears and no update id is added. -/
theorem acquire {s : Slot} (hs : s ∈ g.u) (hc : ∀ b, cx.views.wfloor ≤ b → CanAcqB g.u g.upd r.acq b s.key s.id)
    (hu : ∀ s' ∈ g'.u, s'.key.2 ≤ B → s' ∈ g.u) (hU : ∀ y ι, ι ∈ g'.upd y → ι ∈ g.upd y) :
    RStep B r g (r.op s.res) g' cx :=
  ⟨ReachFrame.of_slots hu hU, fun b hb hf _ h =>
    reachB.acquire hs (hc b hf) (fun s' hs' hk => hu s' hs' (Nat.le_trans hk hb)) hU h⟩

/-- An acquisition at an acquire-type step (`AcqStep`, `AcqFloor.lean`) of a
slot of the message `q` it acquires from, which the thread holds the id of
or which is an update slot. -/
theorem acquire_of_acqStep {A : Arch} {iv : InstrViews} {c₀ : Ctx} {s : Slot} (hstep : AcqStep A iv c₀ cx s.key.2)
    (hs : s ∈ g.u) (hown : 1 ≤ r.acq s.key.1 s.id ∨ s.id ∈ g.upd s.key.1)
    (hu : ∀ s' ∈ g'.u, s'.key.2 ≤ B → s' ∈ g.u) (hU : ∀ y ι, ι ∈ g'.upd y → ι ∈ g.upd y) :
    RStep B r g (r.op s.res) g' cx := by
  refine acquire hs (fun b hb => ?_) hu hU
  have hq := Nat.le_trans hstep.le_wfloor hb
  rcases hown with h | h
  · exact .base hs hq h
  · exact .upd hs hq h

end RStep

/-! ## Discharging an RMW claim's floor bound -/

section Floor

variable {A : Arch} {tid : Nat} {iv : InstrViews}

theorem fenceOptCtx_vmono (A : Arch) (cx : Ctx) : cx.VMono (fenceOptCtx A cx) := by
  unfold fenceOptCtx; split
  · exact fenceStep_vmono cx .sy
  · exact .refl cx

theorem rmwAfter_vmono (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    cx.VMono (rmwAfter A k noRet l cx) := by
  unfold rmwAfter; split
  · exact (rmwPost_vmono A cx k noRet l).trans (fenceStep_vmono _ .sy)
  · exact rmwPost_vmono A cx k noRet l

/-- **An acquire RMW's read bounds the floor after it** (the read is not
forwarded from the thread's own write): `tr ≤ vwNew` after the read
(`readSuccs_acq_vwNew`), and views only grow. -/
theorem rmw_tr_le_wfloor_acq {cx₀ : Ctx} {kk : LoadKind} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx₀ kk false l noRet) (hk : (A.loadKind kk).isAcquire = true)
    (hfw : ∀ f, cx₀.views.getFwd l = some f → f.time ≠ x.1)
    {iv' : InstrViews} {sk : StoreKind} {new : Val} {νr : View} {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv' x.2.2 sk true l new (some x.1) νr) (k : RmwKind) (noRet' : Bool) :
    x.1 ≤ (rmwAfter A k noRet' l cx').views.wfloor := by
  have h1 := readSuccs_acq_vwNew A iv hx hk hfw
  have h2 := ((writeSuccs_vmono A tid hc).trans (rmwAfter_vmono A k noRet' l cx')).vwNew
  simp only [Views.wfloor]; omega_t

/-- **An acquire-release RMW bounds the floor after it**: its write raises
`coh l` above `tr` and `rmwPost` folds `coh l` into `vwNew`. -/
theorem rmw_tr_le_wfloor_acqRel {cx₀ : Ctx} {k : RmwKind} {noRet : Bool} {l : Loc} {tr : Time}
    {iv' : InstrViews} {sk : StoreKind} {new : Val} {νr : View} {cx' : Ctx}
    (hc : cx' ∈ writeSuccs A tid iv' cx₀ sk true l new (some tr) νr) (hk : (A.rmwKind k == .acqRel && !noRet) = true) :
    tr ≤ (rmwAfter A k noRet l cx').views.wfloor := by
  have h1 := writeSuccs_tr_lt_coh A tid hc
  have h2 := rmwPost_vwNew A cx' l hk
  have h3 : (rmwPost A k noRet l cx').views.wfloor ≤ (rmwAfter A k noRet l cx').views.wfloor := by
    unfold rmwAfter; split
    · exact (fenceStep_vmono _ .sy).wfloor
    · exact Nat.le_refl _
  simp only [Views.wfloor] at h3 ⊢; omega_t

end Floor

/-! ## Prepayments in `NPSafe`'s shape -/

section Prepay

variable {c : Config I} {tid : Nat} {g : Ghost} {r r' : Res} {x : Loc} {v : Val} {ss : List Slot}

/-- **K2 of a prepaid release store** (`NPSafe`'s prepay conjunct, with
`Erase.prepay`): the slots are on the promised message `|M| + 1`. -/
theorem prepay_K2 {A : Loc → PredId → Nat} {m : Memory} (hss : SlotsFor g A x (c.mem.last + 1) v m ss) :
    ∀ b, b ≤ c.mem.last → ∀ ρ y, reachB ρ (prepayGhost g x (c.mem.last + 1) ss) y b → reachB ρ g y b :=
  ReachFrame.prepay (FreshSlots.of_key hss.key (Nat.lt_succ_self _))

/-- **K1 of a prepaid release store**: the thread only lost slots (no floor
hypothesis needed). -/
theorem prepay_K1 {A : Loc → PredId → Nat} {m : Memory} (hss : SlotsFor g A x (c.mem.last + 1) v m ss)
    {p : Val × Time} (hres : r'.op (Res.prod (ss.map (·.res))) = r.addW x p) :
    ∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
      ∀ y, reachB r' (prepayGhost g x (c.mem.last + 1) ss) y b → reachB r g y b :=
  fun b hb _ _ h => reachB_of_split0 (g := g) (g' := prepayGhost g x (c.mem.last + 1) ss)
    (fun s hs hk => ((mem_store_u (x := x) (tw := c.mem.last + 1) (rel := true)).mp hs).elim id fun h' => by
      have h2 : c.mem.last + 1 ≤ b := by rw [hss.key s h'] at hk; exact hk
      omega_t) (fun _ _ h => h) hres h

/-- **K2 of a prepaid release RMW half** (`prepayRmwGhost`; its erasure law
`Erase.prepayRmw` is retired, `Erase.claimFulf`). -/
theorem prepayRmw_K2 {A : Loc → PredId → Nat} {m : Memory} {tr : Time}
    (hss : SlotsFor g A x (c.mem.last + 1) v m ss) :
    ∀ b, b ≤ c.mem.last → ∀ ρ y, reachB ρ (prepayRmwGhost g x tr (c.mem.last + 1) ss) y b → reachB ρ g y b :=
  ReachFrame.prepayRmw (FreshSlots.of_key hss.key (Nat.lt_succ_self _))

/-- **K1 of a prepaid release RMW half**: the claimed update slots of
`(x, tr)` move into the thread, so (when something is claimed) `tr` must be
at most the thread's floor at the promise (`NPSafe`'s K1 for a prepayment
looks at the thread in `c`, before the promise). -/
theorem prepayRmw_K1 {A : Loc → PredId → Nat} {m : Memory} {tr : Time} {t₁ : Thread I}
    (ht : c.threads[tid]? = some t₁) (hss : SlotsFor g A x (c.mem.last + 1) v m ss) {p : Val × Time}
    (hres : r'.op (Res.prod (ss.map (·.res))) = (r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p)
    (htr : claimedSlots g x tr ≠ [] → tr ≤ t₁.views.wfloor) :
    ∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
      ∀ y, reachB r' (prepayRmwGhost g x tr (c.mem.last + 1) ss) y b → reachB r g y b := by
  intro b hb hf _ h
  refine reachB_of_split (g := g) (g' := prepayRmwGhost g x tr (c.mem.last + 1) ss)
    (fun s hs hk => ?_) (fun _ _ h => h) hres ?_ h
  · rcases (mem_rmw_u (rel := true) (tw := c.mem.last + 1)).mp hs with hs | hs
    · exact hs.1
    · have h2 : c.mem.last + 1 ≤ b := by rw [hss.key s hs] at hk; exact hk
      omega_t
  · by_cases hc : claimedSlots g x tr = []
    · rw [hc]; intro _ h; cases h
    · exact claimedSlots_canAcqB r.acq (Nat.le_trans (htr hc) (hf t₁ ht))

end Prepay


/-! ## The erasure WP with bounded reach -/

/-- A write event never shrinks the memory. -/
theorem WriteEv.last_le {tid : Nat} {cx cx' : Ctx} {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time}
    (h : WriteEv tid cx cx' l v trOpt tw) : cx.mem.last ≤ cx'.mem.last := by
  rcases h.cases with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact Nat.le_refl _
  · rw [hm, Memory.last_append]; exact Nat.le_succ _

/-- The slots of a write event's message are fresh for the instruction's
start memory when the write appends, and the rule attaches none when it
fulfils a promise. -/
theorem WriteEv.freshSlots {tid : Nat} {cx cx' : Ctx} {l : Loc} {v : Val} {trOpt : Option Time} {tw : Time}
    (h : WriteEv tid cx cx' l v trOpt tw) {B : Time} (hB : B ≤ cx.mem.last) {ss : List Slot}
    (hk : ∀ s ∈ ss, s.key = (l, tw)) (hf : tw ∈ cx.prom → ss = []) : FreshSlots B ss := by
  rcases h.cases with ⟨-, hp, -⟩ | ⟨-, rfl⟩
  · rw [hf hp]; exact FreshSlots.nil B
  · exact FreshSlots.of_key hk (by omega_t)

/-- The slots of a store rule's write are on its message (`SlotsFor.key`,
or none for a relaxed write). -/
theorem slots_key {g : Ghost} {A : Loc → PredId → Nat} {l : Loc} {tw : Time} {v : Val} {m : Memory}
    {rel : Bool} {ss : List Slot} {P : Prop} (hrel : rel = true → SlotsFor g A l tw v m ss ∧ P)
    (hrlx : rel = false → ss = [] ∧ Pred.Pure (g.rel l) v) : ∀ s ∈ ss, s.key = (l, tw) := by
  cases rel with
  | true => exact (hrel rfl).1.key
  | false => rw [(hrlx rfl).1]; intro _ h; cases h

/-- **Erasure WP with bounded reach**: `EvTree.EraseWP` where every write
also establishes `RStep` (K2, and K1 at the context the instruction
continues from) for the bound `c.mem.last`, given in addition that the
memory has not shrunk since the instruction started. -/
def _root_.Kraken.Promising.EvTree.EraseWPR (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res)
    (T : Nat → Prop) (c : Config I) (t : Thread I) {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) :
    EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWPR A tid iv rF T c t Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l,
      EvTree.EraseWPR A tid iv rF T c t Post (ret x.2.1) r g x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
        ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
          EvTree.EraseWPR A tid iv rF T c t Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWPR A tid iv rF T c t Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWPR A tid iv rF T c t Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWPR A tid iv rF T c t Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
            ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' (rmwAfter A k noRet l cx') ∧
              EvTree.EraseWPR A tid iv rF T c t Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section WPR

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type}

/-- `EvTree.EraseWP` is monotone in its postcondition. -/
theorem _root_.Kraken.Promising.EvTree.EraseWP.mono {Post Post' : σ → Res → Ghost → Ctx → Prop}
    (hP : ∀ s r g cx, Post s r g cx → Post' s r g cx) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWP A tid iv rF T c t Post r g cx → tree.EraseWP A tid iv rF T c t Post' r g cx := by
  induction tree with
  | done s => exact fun r g cx h => hP s r g cx h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih => exact fun r g cx h x hx => ih x.2.1 r g x.2.2 (h x hx)
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    obtain ⟨r', g', E', hw⟩ := h.1 cx' hc E hi
    exact ⟨r', g', E', ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi => ?_⟩
    obtain ⟨r', g', E', hw⟩ := (h x hx).2 new hop cx' hc E hi
    exact ⟨r', g', E', ih x.2.1 r' g' _ hw⟩

/-- The invariant `EvTree.EraseWPR.toEraseWP` carries along the tree: the
memory has not shrunk since the start (`c.mem.last`), and `RStep` from the
start `(r₀, g₀)`. -/
def KAcc (c : Config I) (r₀ : Res) (g₀ : Ghost) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  c.mem.last ≤ cx.mem.last ∧ RStep c.mem.last r₀ g₀ r g cx

theorem KAcc.move {r₀ r : Res} {g₀ g : Ghost} {cx cx' : Ctx} (h : KAcc c r₀ g₀ r g cx)
    (hm : cx.mem.last ≤ cx'.mem.last) (hv : cx.VMono cx') : KAcc c r₀ g₀ r g cx' :=
  ⟨Nat.le_trans h.1 hm, h.2.mono hv.wfloor⟩

/-- **`EraseWPR` gives `EraseWP` with K1/K2 in the postcondition**: from a
point where the invariant `KAcc` holds w.r.t. the instruction's start
`(r₀, g₀)`, the erasure WP holds with postcondition `Post` plus `RStep` from
`(r₀, g₀)` to the final `(r', g')` at the final context. -/
theorem _root_.Kraken.Promising.EvTree.EraseWPR.toEraseWP {Post : σ → Res → Ghost → Ctx → Prop} (r₀ : Res)
    (g₀ : Ghost) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPR A tid iv rF T c t Post r g cx → KAcc c r₀ g₀ r g cx →
      tree.EraseWP A tid iv rF T c t (fun s r' g' cx' => Post s r' g' cx' ∧ RStep c.mem.last r₀ g₀ r' g' cx')
        r g cx := by
  induction tree with
  | done s => exact fun r g cx h hk => ⟨h, hk.2⟩
  | fault _ => exact fun _ _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h hk i => ih i r g cx (h i) hk
  | load k xcl l ret ih =>
    intro r g cx h hk x hx
    obtain ⟨hm, -⟩ := readSuccs_memProm A iv hx
    exact ih x.2.1 r g x.2.2 (h x hx) (hk.move (by rw [hm]; exact Nat.le_refl _) (readSuccs_vmono A iv hx))
  | store k xcl l v ret ih =>
    intro r g cx h hk
    refine ⟨fun cx' hc E hi => ?_, fun hx => ih false r g _ (h.2 hx)
      (hk.move (Nat.le_refl _) ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)⟩
    obtain ⟨r', g', E', hR, hw⟩ := h.1 cx' hc E hi hk.1
    obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
    have hv := writeSuccs_vmono A tid hc
    exact ⟨r', g', E', ih true r' g' cx' hw ⟨Nat.le_trans hk.1 hev.last_le, hk.2.trans hR hv.wfloor⟩⟩
  | fence k ret ih =>
    intro r g cx h hk
    exact ih () r g _ h (hk.move (by rw [fenceStep_mem]; exact Nat.le_refl _) (fenceStep_vmono cx k))
  | rmw k noRet l op ret ih =>
    intro r g cx h hk x hx
    obtain ⟨hm1, -⟩ := fenceOptCtx_memProm A cx
    obtain ⟨hm2, -⟩ := readSuccs_memProm A iv hx
    have hv2 : cx.VMono x.2.2 := (fenceOptCtx_vmono A cx).trans (readSuccs_vmono A iv hx)
    have hk2 : KAcc c r₀ g₀ r g x.2.2 := hk.move (by rw [hm2, hm1]; exact Nat.le_refl _) hv2
    refine ⟨fun hop => ?_, fun new hop cx' hc E hi => ?_⟩
    · obtain ⟨hm3, -⟩ := fenceOptCtx_memProm A x.2.2
      exact ih x.2.1 r g _ ((h x hx).1 hop) (hk2.move (by rw [hm3]; exact Nat.le_refl _) (fenceOptCtx_vmono A _))
    · obtain ⟨r', g', E', hR, hw⟩ := (h x hx).2 new hop cx' hc E hi hk.1
      have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
      obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi2
      obtain ⟨hm4, -⟩ := rmwAfter_memProm A k noRet l cx'
      have hv := (writeSuccs_vmono A tid hc).trans (rmwAfter_vmono A k noRet l cx')
      refine ⟨r', g', E', ih x.2.1 r' g' _ hw ⟨?_, hk2.2.trans hR hv.wfloor⟩⟩
      rw [hm4]; exact Nat.le_trans hk2.1 hev.last_le

/-- `EvTree.EraseWPR.toEraseWP` at the start of an instruction, into any
postcondition that follows from `Post` and `RStep` (e.g. the spinlock proof's `WpPost`,
whose K1/K2 conjuncts follow from `RStep` and `RStep.finish`). -/
theorem _root_.Kraken.Promising.EvTree.EraseWPR.toEraseWP_start {Post Q : σ → Res → Ghost → Ctx → Prop}
    {tree : EvTree σ} {r : Res} {g : Ghost} {cx : Ctx} (h : tree.EraseWPR A tid iv rF T c t Post r g cx)
    (hm : c.mem.last ≤ cx.mem.last)
    (hQ : ∀ s r' g' cx', Post s r' g' cx' → RStep c.mem.last r g r' g' cx' → Q s r' g' cx') :
    tree.EraseWP A tid iv rF T c t Q r g cx :=
  EvTree.EraseWP.mono (fun s r' g' cx' h => hQ s r' g' cx' h.1 h.2) tree r g cx
    (EvTree.EraseWPR.toEraseWP r g tree r g cx h ⟨hm, RStep.refl _ _ _ _⟩)

/-- **The frame with bounded reach**: a run of an event tree with
`EraseWPR` ends in erasure, the postcondition, and `RStep` from the start. -/
theorem runTree_eraseWPR {Post : σ → Res → Ghost → Ctx → Prop} (tree : EvTree σ) {r : Res} {g : Ghost}
    {cx : Ctx} {s : σ} {cx' : Ctx} (hrun : .ok (s, cx') ∈ runTree A tid iv cx tree)
    (E : ErAt rF T c t tid r g cx) (hi : cx.Inv tid) (hm : c.mem.last ≤ cx.mem.last)
    (hw : tree.EraseWPR A tid iv rF T c t Post r g cx) :
    ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ Post s r' g' cx' ∧ RStep c.mem.last r g r' g' cx' := by
  obtain ⟨r', g', E', hp, hR⟩ := runTree_eraseWP A tid iv rF T c t _ tree r g cx s cx' hrun E hi
    (EvTree.EraseWPR.toEraseWP r g tree r g cx hw ⟨hm, RStep.refl _ _ _ _⟩)
  exact ⟨r', g', E', hp, hR⟩

end WPR

/-- **Erasure and bounded reach across one instruction**: `Erase.npStep`
for `EvTree.EraseWPR`, with `NPSafe`'s K2 and K1 (at the thread after the
step) for the instruction's resource change. -/
theorem Erase.npStepR {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    {r : Res} {Post : I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hs : NPStepBy A tid c c')
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWPR A tid (instrViews t (I.deps t.st)) rF T c t Post r g (ctx₀ t tid c.mem)) :
    ∃ st r' g' cx', Post st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hn := lt_size_of_get? ht
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨res, hr, ho⟩ := ho
    cases res with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, cx'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have E0 : ErAt rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAt
        rw [Config.withThread_self c ht]
        exact E
      obtain ⟨r', g', E', hpost, hR⟩ := runTree_eraseWPR tree hr E0 (hinv.ctxInv ht _) (Nat.le_refl _)
        (hwp t tree ht hex)
      refine ⟨st, r', g', cx', hpost, Erase.withThread_prom E' hn (finishInstr_relKey hth).1, hR.1, ?_⟩
      intro b hb hf
      have hth' : (c.withThread tid th cx'.mem).threads[tid]? = some th := by
        rw [Config.withThread_get? c th cx'.mem hn, ite_eq_left rfl]
      exact hR.finish hth b hb (hf th hth')

/-! ## Node shapes of the erasure WP with bounded reach -/

section Shapes

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type} {Post : σ → Res → Ghost → Ctx → Prop} {r : Res} {g : Ghost} {cx : Ctx}

theorem _root_.Kraken.Promising.EvTree.eraseWPR_access {ds : Decls} {addr : BitVec 64} {n : Nat}
    {k : Loc → EvTree σ} (h : ∀ l, (k l).EraseWPR A tid iv rF T c t Post r g cx) :
    (EvTree.access ds addr n k).EraseWPR A tid iv rF T c t Post r g cx := by
  unfold EvTree.access
  split
  · exact h _
  · trivial

/-- **A load (plain or acquire)**: its continuation's WP, same resources. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_load {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ}
    (h : ∀ x ∈ readSuccs A iv cx k xcl l, (ret x.2.1).EraseWPR A tid iv rF T c t Post r g x.2.2) :
    (EvTree.load k xcl l ret).EraseWPR A tid iv rF T c t Post r g cx := h

/-- **A fence.** -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_fence {k : FenceKind} {ret : Unit → EvTree σ}
    (h : (ret ()).EraseWPR A tid iv rF T c t Post r g (fenceStep cx k)) :
    (EvTree.fence k ret).EraseWPR A tid iv rF T c t Post r g cx := h

/-- **A (non-exclusive) store, plain or release, with bounded reach**: the
obligations of `EvTree.eraseWP_store`, plus `hfresh`: a write that fulfils
a promise attaches no slot. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_store (hn : tid < c.threads.size) {k : StoreKind} {l : Loc}
    {v : Val} {ret : Bool → EvTree σ}
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), tw ∉ g.pend ∧ 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw v cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) v) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW l (v, tw) ∧
        (tw ∈ cx.prom → ss = []) ∧
        HVal rF T c t tid cx' r' (storeGhost g l tw rel ss) ∧
        (ret true).EraseWPR A tid iv rF T c t Post r' (storeGhost g l tw rel ss) cx') :
    (EvTree.store k false l v ret).EraseWPR A tid iv rF T c t Post r g cx := by
  refine ⟨fun cx' hc E hi hm => ?_, fun h => absurd h (by decide)⟩
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  obtain ⟨rel, ss, r', hpend, hpos, hrel, hrlx, hres, hf, hval, hwp⟩ := h cx' tw hc hev E hi
  exact ⟨r', _, ErAt.store E hn hi hev hpend hpos hrel hrlx hres hval,
    RStep.store (hev.freshSlots hm (slots_key hrel hrlx) hf) hres cx', hwp⟩

/-- **An RMW with bounded reach**: the obligations of `EvTree.eraseWP_rmw`,
plus `hfresh` (a write fulfilling a promise attaches no slot) and, when the
RMW claims something, the floor bound `x.1 ≤ wfloor` after it
(`rmw_tr_le_wfloor_acq`, `rmw_tr_le_wfloor_acqRel`). -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_rmw (hn : tid < c.threads.size) {k : RmwKind} {noRet : Bool}
    {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWPR A tid iv rF T c t Post r g (fenceOptCtx A x.2.2))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → ErAt rF T c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), (∀ p ∈ x.2.2.prom, p ∉ g.pend) ∧ 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) new) ∧
        r'.op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw) ∧
        (tw ∈ x.2.2.prom → ss = []) ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        HVal rF T c t tid cx' r' (rmwGhost g l x.1 tw rel ss) ∧
        (ret x.2.1).EraseWPR A tid iv rF T c t Post r' (rmwGhost g l x.1 tw rel ss) (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWPR A tid iv rF T c t Post r g cx := by
  intro x hx
  refine ⟨hfail x hx, fun new hop cx' hc E hi hm => ?_⟩
  obtain ⟨tw, hev, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  obtain ⟨hm1, -⟩ := fenceOptCtx_memProm A cx
  obtain ⟨hm2, -⟩ := readSuccs_memProm A iv hx
  have hm' : c.mem.last ≤ x.2.2.mem.last := by rw [hm2, hm1]; exact hm
  obtain ⟨rel, ss, r', hnp, hpos, hrel, hrlx, hres, hf, htr, hval, hwp⟩ := hok x hx new hop cx' tw hc hev E
  exact ⟨r', _, ErAt.rmw E hn hi2 hev hrd hseen hnp hpos hrel hrlx hres hval,
    RStep.rmw (hev.freshSlots hm' (slots_key hrel hrlx) hf) hres htr, hwp⟩

/-- **A store with pending promises, with bounded reach** (fallback (iii)):
`EvTree.eraseWP_store_pend`; the pending branch needs nothing more
(`RStep.unpend`). -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_store_pend (hn : tid < c.threads.size) {k : StoreKind} {l : Loc}
    {v : Val} {ret : Bool → EvTree σ}
    (hp : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∈ g.pend →
      (ret true).EraseWPR A tid iv rF T c t Post r (unpend g tw) cx')
    (h : ∀ cx' tw, cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k false l v none →
      WriteEv tid cx cx' l v none tw → tw ∉ g.pend → ErAt rF T c t tid r g cx → cx.Inv tid →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res), 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw v cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) v) ∧
        r'.op (Res.prod (ss.map (·.res))) = r.addW l (v, tw) ∧
        (tw ∈ cx.prom → ss = []) ∧
        HVal rF T c t tid cx' r' (storeGhost g l tw rel ss) ∧
        (ret true).EraseWPR A tid iv rF T c t Post r' (storeGhost g l tw rel ss) cx') :
    (EvTree.store k false l v ret).EraseWPR A tid iv rF T c t Post r g cx := by
  refine ⟨fun cx' hc E hi hm => ?_, fun h => absurd h (by decide)⟩
  obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc hi
  by_cases hpd : tw ∈ g.pend
  · exact ⟨r, _, ErAt.fulfilPend E hn hi hev hpd, RStep.unpend tw cx', hp cx' tw hc hev hpd⟩
  · obtain ⟨rel, ss, r', hpos, hrel, hrlx, hres, hf, hval, hwp⟩ := h cx' tw hc hev hpd E hi
    exact ⟨r', _, ErAt.store E hn hi hev hpd hpos hrel hrlx hres hval,
      RStep.store (hev.freshSlots hm (slots_key hrel hrlx) hf) hres cx', hwp⟩

/-- **An RMW with pending promises, with bounded reach** (fallback (iii)):
`EvTree.eraseWP_rmw_pend`, plus `eraseWPR_rmw`'s `hfresh` and floor bound
in the non-pending branch. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_rmw_pend (hn : tid < c.threads.size) {k : RmwKind} {noRet : Bool}
    {l : Loc} {op : Val → Option Val} {ret : Val → EvTree σ}
    (hfail : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      op x.2.1 = none → (ret x.2.1).EraseWPR A tid iv rF T c t Post r g (fenceOptCtx A x.2.2))
    (hp : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∈ g.pend →
      (ret x.2.1).EraseWPR A tid iv rF T c t Post r (unpend g tw) (rmwAfter A k noRet l cx'))
    (hok : ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
      ∀ new, op x.2.1 = some new → ∀ cx' tw,
      cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) →
      WriteEv tid x.2.2 cx' l new (some x.1) tw → tw ∉ g.pend → ErAt rF T c t tid r g x.2.2 →
      ∃ (rel : Bool) (ss : List Slot) (r' : Res),
        (∀ p ∈ x.2.2.prom, p ∈ g.pend → ∀ w, x.2.2.mem.get? p = some w → w.loc ≠ l) ∧ 0 < (r.wr l).q ∧
        (rel = true → SlotsFor g (total (setRes rF tid r) g c).acq l tw new cx'.mem ss ∧ ¬ g.Claimed (l, tw)) ∧
        (rel = false → ss = [] ∧ Pred.Pure (g.rel l) new) ∧
        r'.op (Res.prod (ss.map (·.res))) =
          (r.op (Res.prod ((claimedSlots g l x.1).map (·.res)))).addW l (new, tw) ∧
        (tw ∈ x.2.2.prom → ss = []) ∧
        (claimedSlots g l x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet l cx').views.wfloor) ∧
        HVal rF T c t tid cx' r' (rmwGhost g l x.1 tw rel ss) ∧
        (ret x.2.1).EraseWPR A tid iv rF T c t Post r' (rmwGhost g l x.1 tw rel ss) (rmwAfter A k noRet l cx')) :
    (EvTree.rmw k noRet l op ret).EraseWPR A tid iv rF T c t Post r g cx := by
  intro x hx
  refine ⟨hfail x hx, fun new hop cx' hc E hi hm => ?_⟩
  obtain ⟨tw, hev, hrd, hseen⟩ := rmw_event A tid iv hx hi hc
  have hi2 := (readSuccs_inv A tid iv hx (fenceOpt_inv tid hi A.rmwFence .sy).1).1
  by_cases hpd : tw ∈ g.pend
  · exact ⟨r, _, ErAt.fulfilPend E hn hi2 hev hpd, RStep.unpend tw _, hp x hx new hop cx' tw hc hev hpd⟩
  · obtain ⟨hm1, -⟩ := fenceOptCtx_memProm A cx
    obtain ⟨hm2, -⟩ := readSuccs_memProm A iv hx
    have hm' : c.mem.last ≤ x.2.2.mem.last := by rw [hm2, hm1]; exact hm
    obtain ⟨rel, ss, r', hnp, hpos, hrel, hrlx, hres, hf, htr, hval, hwp⟩ := hok x hx new hop cx' tw hc hev hpd E
    exact ⟨r', _, ErAt.rmw_loc E hn hi2 hev hrd hseen hnp hpd hpos hrel hrlx hres hval,
      RStep.rmw (hev.freshSlots hm' (slots_key hrel hrlx) hf) hres htr, hwp⟩

end Shapes

end Kraken.Promising.SLR
