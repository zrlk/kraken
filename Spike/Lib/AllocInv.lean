/-
**The allocation invariants of a one-thread run**: the heap counter's
value against the arena's cursor, the thread's fresh labels, and the two
phases of an allocation (idle, and pending between the counter's add and
the landing), for a consumer whose pairs may be at `newBuf`
(`Spike/Lib/AllocRow.lean` for the arena contract and the allocation row).

- `CtrAt tm prom ctr v`: the latest target write of the counter word `ctr`
  not outstanding as a promise of `prom` (`TLatestP`, what the counter's
  read-modify-write reads) holds `v`; `CtrAt.init` at load,
  `CtrAt.append_ne` kept by a message elsewhere, `CtrAt.append_self` set by
  one there, `CtrAt.promise` kept by a promise, `CtrAt.fulfil` set by
  fulfilling a promise there.
- `FreshInv lbl base n i na`: no label of thread `i` from its `na`-th on is
  placed; `FreshInv.init`, `FreshInv.fresh` (the next label is unplaced),
  `FreshInv.place` (placing it moves `na` on).
- `Pending`: the control at a buffer allocation whose units the counter
  has already added past the old count, the contract's exceptions below the
  buffer's base (`ms.off`, which `Call.OK.off` fixes at `8·k·m + 8`, the
  header at `8·k·m`); `AllocInv`: idle (the counter at the cursor, the
  contract with no exception) unless the control holds the counter, then
  pending (the held word the old count, the contract at it); `AllocInv.init`,
  `AllocInv.idle_append_out` (kept by a message outside the free range and
  off the counter), `AllocInv.ctrAdd` (the counter's add from idle to
  pending), `AllocInv.header` (the header store while pending),
  `AllocInv.land` (the landing back to idle at the new cursor).
-/
import Spike.Lib.AllocRow

namespace Spike.Lib.AllocInv

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (wordLoc wordAt wordAt_of_read)
open Scc.Sem (TLatestP)
open Spike.Lib.AllocRow (ArenaOK freeR get?_append)

/-! ## The counter's value -/

/-- **The counter word `ctr` holds `v`**: its latest target write not
outstanding as a promise of `prom` (the initial one or a message;
`TLatestP`, what the counter's read-modify-write reads,
`stepOne_rmw_cases`) reads `v`. -/
def CtrAt (tm : Memory) (prom : List Time) (ctr v : Nat) : Prop :=
  ∃ k', TLatestP tm prom ctr k' ∧ wordAt tm ctr k' = some v

theorem last_append (tm : Memory) (w : Msg) : (tm.append w).1.last = tm.last + 1 := by
  simp [Memory.last, Memory.append]

/-- **At load**: no message, the counter's initial value. -/
theorem CtrAt.init {tm : Memory} {prom : List Time} {ctr : Nat} (hm : ∀ k', 0 < k' → tm.get? k' = none) :
    CtrAt tm prom ctr (tm.initVal (wordLoc ctr)).toNat :=
  ⟨0, ⟨.inl rfl, fun k'' w hk hg => by rw [hm k'' hk] at hg; cases hg⟩,
    wordAt_of_read (by simp [Memory.read?])⟩

/-- **A message elsewhere keeps the counter's value.** -/
theorem CtrAt.append_ne {tm : Memory} {prom : List Time} {ctr v : Nat} (h : CtrAt tm prom ctr v) {w : Msg}
    (hw : w.loc ≠ wordLoc ctr) : CtrAt (tm.append w).1 prom ctr v := by
  obtain ⟨k', ⟨h1, h2⟩, hv⟩ := h
  have hk : k' ≤ tm.last := by
    rcases h1 with rfl | ⟨w', hg, -⟩
    · exact Nat.zero_le _
    · exact Scc.Sem.Memory.le_last_of_get? hg
  refine ⟨k', ⟨?_, fun k'' w'' hlt hg hl => ?_⟩, by rw [Scc.Sem.wordAt_append_le hk]; exact hv⟩
  · rcases h1 with rfl | ⟨w', hg, hl, hp⟩
    · exact .inl rfl
    · exact .inr ⟨w', by rw [Scc.Sem.Memory.get?_append_le hk]; exact hg, hl, hp⟩
  · rw [get?_append] at hg
    split at hg
    · cases hg; exact absurd hl hw
    · exact h2 k'' w'' hlt hg hl

/-- **A message at the counter sets its value** (not a promise: every
outstanding promise is an older message). -/
theorem CtrAt.append_self {tm : Memory} {prom : List Time} {ctr : Nat} {w : Msg} (hw : w.loc = wordLoc ctr)
    (hpl : ∀ q ∈ prom, q ≤ tm.last) : CtrAt (tm.append w).1 prom ctr w.val.toNat := by
  refine ⟨tm.last + 1, ⟨.inr ⟨w, Scc.Sem.Memory.get?_append_new, hw, fun h => Nat.not_succ_le_self _ (hpl _ h)⟩,
    fun k'' w'' hlt hg _ => ?_⟩, wordAt_of_read ?_⟩
  · have := Scc.Sem.Memory.le_last_of_get? hg
    rw [last_append] at this
    omega
  · simp [Memory.read?, Scc.Sem.Memory.get?_append_new, hw]

/-- **A promise keeps the counter's value**: the promised message, wherever
it is, is outstanding. -/
theorem CtrAt.promise {tm : Memory} {prom : List Time} {ctr v : Nat} (h : CtrAt tm prom ctr v) (w : Msg) :
    CtrAt (tm.append w).1 (prom ++ [(tm.append w).2]) ctr v := by
  obtain ⟨k', ⟨h1, h2⟩, hv⟩ := h
  have hk : k' ≤ tm.last := by
    rcases h1 with rfl | ⟨w', hg, -⟩
    · exact Nat.zero_le _
    · exact Scc.Sem.Memory.le_last_of_get? hg
  have hn : (tm.append w).2 = tm.last + 1 := rfl
  refine ⟨k', ⟨?_, fun k'' w'' hlt hg hl => ?_⟩, by rw [Scc.Sem.wordAt_append_le hk]; exact hv⟩
  · rcases h1 with rfl | ⟨w', hg, hl, hp⟩
    · exact .inl rfl
    · refine .inr ⟨w', by rw [Scc.Sem.Memory.get?_append_le hk]; exact hg, hl, fun hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hp hm
      · rw [List.mem_singleton, hn] at hm; omega
  · rw [get?_append] at hg
    split at hg
    · rename_i he; exact List.mem_append_right _ (List.mem_singleton.mpr (he.trans hn.symm))
    · exact List.mem_append_left _ (h2 k'' w'' hlt hg hl)

/-- **Fulfilling a promise at the counter sets its value**: the promised
message `q` at the counter, above the latest one not outstanding (the
fulfilment's view, `stepOne_rmw_cases`), `q` no longer outstanding. -/
theorem CtrAt.fulfil {tm : Memory} {prom : List Time} {ctr v : Nat} (h : CtrAt tm prom ctr v) {q : Time}
    {w : Msg} (hq : tm.get? q = some w) (hw : w.loc = wordLoc ctr)
    (hgt : ∀ k', TLatestP tm prom ctr k' → k' < q) (hnd : prom.Nodup) :
    CtrAt tm (prom.erase q) ctr w.val.toNat := by
  obtain ⟨k', hl, -⟩ := h
  have hlt := hgt k' hl
  refine ⟨q, ⟨.inr ⟨w, hq, hw, fun hm => ((List.Nodup.mem_erase_iff hnd).mp hm).1 rfl⟩,
    fun k'' w'' hk hg hl' => ?_⟩, wordAt_of_read ?_⟩
  · exact (List.Nodup.mem_erase_iff hnd).mpr ⟨Nat.ne_of_gt hk, hl.2 k'' w'' (Nat.lt_trans hlt hk) hg hl'⟩
  · have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
    simp [Memory.read?, hq0, hq, hw]

/-! ## Fresh labels -/

/-- **Thread `i`'s labels from its `na`-th on are unplaced** (the label
stripe `n`, base `base`: `freshLabel`). -/
def FreshInv (lbl : WeakMem.AllocLabel → Option Nat) (base n i na : Nat) : Prop :=
  ∀ k, na ≤ k → lbl (freshLabel base n i k) = none

theorem FreshInv.init (base n i : Nat) : FreshInv (fun _ => none) base n i 0 := fun _ _ => rfl

/-- The thread's next label is unplaced. -/
theorem FreshInv.fresh {lbl : WeakMem.AllocLabel → Option Nat} {base n i na : Nat}
    (h : FreshInv lbl base n i na) : lbl (freshLabel base n i na) = none :=
  h na (Nat.le_refl _)

/-- **Placing the next label** moves the count on. -/
theorem FreshInv.place {lbl : WeakMem.AllocLabel → Option Nat} {base n i na : Nat}
    (h : FreshInv lbl base n i na) (hn : 0 < n) (A : Nat) :
    FreshInv (fun l' => if l' = freshLabel base n i na then some A else lbl l') base n i (na + 1) := by
  intro k hk
  have hne : freshLabel base n i k ≠ freshLabel base n i na := fun he => by
    have h0 : base + i + n * k = base + i + n * na := he
    have := Nat.eq_of_mul_eq_mul_left hn (show n * k = n * na by omega)
    omega
  simp only [hne, ite_false]
  exact h k (by omega)

/-! ## The allocation's phases -/

/-- **A pending allocation** (units `units`, base offsets `off`, the arena
at `heap`, the contract's exceptions `ex`): the control at `let x = newBuf a
τ in e`, `a` the number `k`; the counter at the old count `old` plus the
buffer's units; every exception below the buffer's base `heap + 16·old +
off k τ` (the header; `Call.OK.off`: `off = 8·k·m + 8`, the header at
`8·k·m` from the cell, so below the base). -/
def Pending (units off : Nat → Ty → Nat) (tm : Memory) (prom : List Time) (heap ctr old : Nat)
    (ex : Nat → Prop) (c : Spike.Lib.Ctl) : Prop :=
  ∃ (x : String) (a : At) (τ : Ty) (e : Expr) (ta : Ty) (ws : List Word) (k : Nat),
    c.term = .let_ x (.newBuf a τ) e ∧ evalAt c.env a = some (ta, ws) ∧ numOf ws = some k ∧
    CtrAt tm prom ctr (old + units k τ) ∧ ∀ a', ex a' → a' < heap + 16 * old + off k τ

/-- **The allocation invariant** (layout `Λ`, placement `lbl`/`lsize`,
thread `t`, target memory `tm`, the arena at `heap` of `cells` cells, the
counter word `ctr`, units `units`, base offsets `off`, the control `c`): if
`c` holds the counter, the allocation is pending from the held old count,
the contract at it; else the counter is at the cursor and the contract holds
there with no exception. -/
def AllocInv {I : ISA} (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (t : Thread I) (tm : Memory) (heap cells ctr : Nat)
    (units off : Nat → Ty → Nat) (c : Spike.Lib.Ctl) : Prop :=
  (∃ w, c.hold = some (ctr, w) ∧ ∃ old ex, numOf [w] = some old ∧ Pending units off tm t.prom heap ctr old ex c ∧
      ArenaOK Λ lbl lsize t tm heap cells old ex) ∨
    ((∀ w, c.hold ≠ some (ctr, w)) ∧ ∃ hu, CtrAt tm t.prom ctr hu ∧
      ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False))

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {tm : Memory} {heap cells ctr : Nat}
  {units off : Nat → Ty → Nat} {c : Spike.Lib.Ctl}

/-- **At load**: no hold, the counter at the cursor `0` (its initial value
zero) and the contract at load. -/
theorem AllocInv.init (hc : c.hold = none) (hctr : CtrAt tm t.prom ctr 0)
    (ha : ArenaOK Λ lbl lsize t tm heap cells 0 (fun _ => False)) :
    AllocInv Λ lbl lsize t tm heap cells ctr units off c :=
  .inr ⟨fun w h => (by rw [hc] at h; cases h), 0, hctr, ha⟩

/-- **Idle, a message outside the free range and off the counter** (a store
to a placed word or a runtime word, a promise elsewhere) keeps the
invariant, for any control not holding the counter. -/
theorem AllocInv.idle_append_out {hu : Nat} (hctr : CtrAt tm t.prom ctr hu)
    (ha : ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False)) {t' : Thread I} {w : Msg}
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hw : w.loc ≠ wordLoc ctr)
    (hp : t'.prom = t.prom) {c' : Spike.Lib.Ctl} (hc' : ∀ w', c'.hold ≠ some (ctr, w')) :
    AllocInv Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c' :=
  .inr ⟨hc', hu, hp ▸ hctr.append_ne hw, ha.store_out hfree hp⟩

/-- **The counter's add**, from idle at cursor `hu`: the message at the
counter of `hu` plus the buffer's units, the control now holding the
counter with the old count `hu` at the allocation, gives the pending
phase (the counter outside the free range). -/
theorem AllocInv.ctrAdd {hu : Nat} (ha : ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False))
    {t' : Thread I} {w : Msg} (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hp : t'.prom = t.prom)
    (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    {c' : Spike.Lib.Ctl} {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List Word} {k : Nat}
    (ht : c'.term = .let_ x (.newBuf a τ) e) (hea : evalAt c'.env a = some (ta, ws)) (hk : numOf ws = some k)
    (hv : w.val.toNat = hu + units k τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInv Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c' :=
  .inl ⟨_, hh, hu, fun _ => False, rfl,
    ⟨x, a, τ, e, ta, ws, k, ht, hea, hk, hv ▸ hp ▸ CtrAt.append_self hw hpl, fun _ h => h.elim⟩,
    ha.store_out hfree hp⟩

/-- **The header store while pending**: a message off the counter, below
the pending buffer's base (the control at `newBuf a τ`, `a` the number `k`),
is recorded as an exception. -/
theorem AllocInv.header {wh : Word} {old : Nat} {ex : Nat → Prop} (hh : c.hold = some (ctr, wh))
    (ho : numOf [wh] = some old) (hpd : Pending units off tm t.prom heap ctr old ex c)
    (ha : ArenaOK Λ lbl lsize t tm heap cells old ex) {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty}
    {ws : List Word} {k : Nat} (ht : c.term = .let_ x (.newBuf a τ) e) (hea : evalAt c.env a = some (ta, ws))
    (hk : numOf ws = some k) {t' : Thread I} {w : Msg} (hw : w.loc ≠ wordLoc ctr)
    (hlt : w.loc.addr.toNat < heap + 16 * old + off k τ) (hp : t'.prom = t.prom) :
    AllocInv Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c := by
  obtain ⟨x', a', τ', e', ta', ws', k', ht', hea', hk', hctr, hex⟩ := hpd
  rw [ht] at ht'
  simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht'
  obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := ht'
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  rw [hk] at hk'
  cases hk'
  refine .inl ⟨wh, hh, old, _, ho, ⟨x, a, τ, e, ta, ws, k, ht, hea, hk, hp ▸ hctr.append_ne hw, ?_⟩,
    ha.store_ex hp⟩
  rintro a' (h | rfl)
  · exact hex a' h
  · exact hlt

/-- **The landing**, from pending at `old` with the buffer's `u` units:
after the label is placed at the cursor and the cursor moved past its cells
(`ArenaOK.place`, `AllocRow.row_alloc`'s contract), the control holding
nothing, the invariant is idle at `old + u`. -/
theorem AllocInv.land {old u : Nat} (hctr : CtrAt tm t.prom ctr (old + u)) {lbl' : WeakMem.AllocLabel → Option Nat}
    {lsize' : WeakMem.AllocLabel → Nat} (ha : ArenaOK Λ lbl' lsize' t tm heap cells (old + u) (fun _ => False))
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) :
    AllocInv Λ lbl' lsize' t tm heap cells ctr units off c' :=
  .inr ⟨fun w h => (by rw [hc'] at h; cases h), old + u, hctr, ha⟩

/-! ## The header's place

`Call.OK.off` fixes a buffer's base offset at `8·k·m + 8` and `Call.hdrAt`
puts its header at `8·k·m` from the cell (`m` the header's trace-word
field). The header is below the base, but not within the cell's first
word once `m > 0`: the exceptions' bound is the base, not `heap + 16·old +
8`. -/

/-- With `k = 2` elements and `m = 1` trace word, the header lies at or past
the cell's second word. -/
example : ∀ heap old : Nat, ¬ heap + 16 * old + 8 * (2 * 1) < heap + 16 * old + 8 := by
  intro heap old; omega

/-- The header is always below the base. -/
example : ∀ heap old k m : Nat, heap + 16 * old + 8 * (k * m) < heap + 16 * old + (8 * (k * m) + 8) := by
  intro heap old k m; omega

end Spike.Lib.AllocInv
