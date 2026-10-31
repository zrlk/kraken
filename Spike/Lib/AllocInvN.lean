/-
**The allocation invariant where box allocations are admitted**:
`AllocInv.AllocInv` with its pending phase at an allocation site
(`AllocSite N`: a buffer, or, under `N`, a box `let x = new a in e`), and
the box's landing at its initialising store (`Out.newStore`) rather than
at the allocator's last instruction.

- `PendingS N`: `AllocInv.Pending` over `AllocSite N`; `pendingS_of` from
  `Pending` (`AllocSite True`) where `N` holds; `PendingS.box`: at a box, the counter at the old count plus
  one object's units and the exceptions below the box's base.
- `AllocInvS N`: `AllocInv` with `PendingS N`; `allocInvS_of` from
  `AllocInv`; `AllocInvS.init`, `idle_append_out`, `ctrAdd` (over
  `AllocSite N`), `header`, `land`: as `AllocInv`'s.
- `CtrAt.erase_ne`: fulfilling a promise elsewhere keeps the counter's
  value; `ctrAt_store_ne`: a plain store elsewhere (appended or fulfilling)
  keeps it.
- `AllocInvS.newStore`: **the box's landing at its initialising store**:
  from pending at a box, the store to the box's base (off the counter), the
  contract at the new cursor after it (`NewRow.row_newStore`'s), the
  control holding nothing: idle at `old + units 1 t`.
-/
import Spike.Lib.AllocInv

namespace Spike.Lib.AllocInvN

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising
open Scc.Sem (wordLoc TLatestP)
open Spike.Lib (AllocSite)
open Spike.Lib.AllocRow (ArenaOK freeR)
open Spike.Lib.AllocInv (CtrAt Pending AllocInv)

/-! ## The counter's value across a store elsewhere -/

/-- **Fulfilling a promise elsewhere keeps the counter's value**: the
promise `q` erased is of a message off the counter word. -/
theorem CtrAt.erase_ne {tm : Memory} {prom : List Time} {ctr v : Nat} (h : CtrAt tm prom ctr v) {q : Time}
    {w : Msg} (hq : tm.get? q = some w) (hw : w.loc ≠ wordLoc ctr) : CtrAt tm (prom.erase q) ctr v := by
  obtain ⟨k', ⟨h1, h2⟩, hv⟩ := h
  refine ⟨k', ⟨?_, fun k'' w'' hlt hg hl => ?_⟩, hv⟩
  · rcases h1 with rfl | ⟨w', hg, hl, hp⟩
    · exact .inl rfl
    · exact .inr ⟨w', hg, hl, fun hm => hp (List.mem_of_mem_erase hm)⟩
  · refine (List.mem_erase_of_ne fun he => ?_).mpr (h2 k'' w'' hlt hg hl)
    subst he
    rw [hq] at hg
    cases hg
    exact hw hl

/-- **A plain store elsewhere keeps the counter's value**: the outcome of
a store to `wordLoc b`, off the counter word, appended or fulfilling. -/
theorem ctrAt_store_ne {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {tm : Memory} {ctr v : Nat}
    (h : CtrAt tm t.prom ctr v) {kr : StoreKind} {b : Nat} {V : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc b) V fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    (hb : wordLoc b ≠ wordLoc ctr) : CtrAt o.mem o.thread.prom ctr v := by
  rcases (Scc.Sem.stepOne_store_cases A hex hstep ho hpl).2 with ⟨q, -, hg, -, hm, hp⟩ | ⟨hm, hp⟩
  · rw [hm, hp]
    exact CtrAt.erase_ne h hg hb
  · rw [hm, hp]
    exact h.append_ne hb

/-! ## The pending phase at an allocation site -/

/-- **A pending allocation at an allocation site** (`AllocSite N`):
`Pending` with the control at a buffer or, under `N`, at a box of one
object of type `τ`; the counter at the old count `old` plus the object's
units, every exception below its base. -/
def PendingS (N : Prop) (units off : Nat → Ty → Nat) (tm : Memory) (prom : List Time) (heap ctr old : Nat)
    (ex : Nat → Prop) (c : Spike.Lib.Ctl) : Prop :=
  ∃ (x : String) (n : Nat) (τ : Ty) (e : Expr), AllocSite N c x n τ e ∧
    CtrAt tm prom ctr (old + units n τ) ∧ ∀ a', ex a' → a' < heap + 16 * old + off n τ

variable {N : Prop} {units off : Nat → Ty → Nat} {tm : Memory} {prom : List Time} {heap ctr old : Nat}
  {ex : Nat → Prop} {c : Spike.Lib.Ctl}

/-- `Pending` (over `AllocSite True`) is `PendingS N` where `N` holds. -/
theorem pendingS_of (hN : N) (h : Pending units off tm prom heap ctr old ex c) :
    PendingS N units off tm prom heap ctr old ex c := by
  obtain ⟨x, n, τ, e, hs, hctr, hex⟩ := h
  exact ⟨x, n, τ, e, hs.elim .inl fun ⟨_, h⟩ => .inr ⟨hN, h⟩, hctr, hex⟩

/-- **At a box**: the pending phase's site is the box's (one object of
`a`'s type `ty`), so the counter is at `old` plus one object's units and
every exception is below the box's base. -/
theorem PendingS.box (h : PendingS N units off tm prom heap ctr old ex c) {x : String} {a : At} {T : Option Ty} {e : Expr}
    {ty : Ty} {ws : List Word} (ht : c.term = .let_ x (.new a T) e) (hea : evalAt c.env a = some (ty, ws)) :
    CtrAt tm prom ctr (old + units 1 ty) ∧ ∀ a', ex a' → a' < heap + 16 * old + off 1 ty := by
  obtain ⟨x', n, τ, e', hs, hctr, hex⟩ := h
  rcases hs with ⟨a', ta, ws', ht', -⟩ | ⟨-, a', ws', ⟨_, ht'⟩, hea', rfl⟩
  · rw [ht] at ht'
    simp at ht'
  · rw [ht] at ht'
    simp only [Expr.let_.injEq, Op.new.injEq] at ht'
    obtain ⟨-, ⟨rfl, -⟩, -⟩ := ht'
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq] at hea'
    obtain ⟨rfl, -⟩ := hea'
    exact ⟨hctr, hex⟩

/-! ## The invariant -/

/-- **The allocation invariant at allocation sites** (`AllocInv` with the
pending phase `PendingS N`). -/
def AllocInvS {I : ISA} (N : Prop) (Λ : Scc.Sem.Layout) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (t : Thread I) (tm : Memory) (heap cells ctr : Nat)
    (units off : Nat → Ty → Nat) (c : Spike.Lib.Ctl) : Prop :=
  (∃ w, c.hold = some (ctr, w) ∧ ∃ old ex, numOf [w] = some old ∧ PendingS N units off tm t.prom heap ctr old ex c ∧
      ArenaOK Λ lbl lsize t tm heap cells old ex) ∨
    ((∀ w, c.hold ≠ some (ctr, w)) ∧ ∃ hu, CtrAt tm t.prom ctr hu ∧
      ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False))

variable {I : ISA} {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {t : Thread I} {cells : Nat}

/-- `AllocInv` is `AllocInvS N` where `N` holds. -/
theorem allocInvS_of (hN : N) (h : AllocInv Λ lbl lsize t tm heap cells ctr units off c) :
    AllocInvS N Λ lbl lsize t tm heap cells ctr units off c := by
  rcases h with ⟨w, hh, old, ex, ho, hp, ha⟩ | h
  · exact .inl ⟨w, hh, old, ex, ho, pendingS_of hN hp, ha⟩
  · exact .inr h

/-- **At load** (`AllocInv.init`). -/
theorem AllocInvS.init (hc : c.hold = none) (hctr : CtrAt tm t.prom ctr 0)
    (ha : ArenaOK Λ lbl lsize t tm heap cells 0 (fun _ => False)) :
    AllocInvS N Λ lbl lsize t tm heap cells ctr units off c :=
  .inr ⟨fun w h => (by rw [hc] at h; cases h), 0, hctr, ha⟩

/-- **Idle, a message outside the free range and off the counter**
(`AllocInv.idle_append_out`). -/
theorem AllocInvS.idle_append_out {hu : Nat} (hctr : CtrAt tm t.prom ctr hu)
    (ha : ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False)) {t' : Thread I} {w : Msg}
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hw : w.loc ≠ wordLoc ctr)
    (hp : t'.prom = t.prom) {c' : Spike.Lib.Ctl} (hc' : ∀ w', c'.hold ≠ some (ctr, w')) :
    AllocInvS N Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c' :=
  .inr ⟨hc', hu, hp ▸ hctr.append_ne hw, ha.store_out hfree hp⟩

/-- **The counter's add at an allocation site**, from idle at cursor `hu`
(`AllocInv.ctrAdd` over `AllocSite N`). -/
theorem AllocInvS.ctrAdd {hu : Nat} (ha : ArenaOK Λ lbl lsize t tm heap cells hu (fun _ => False))
    {t' : Thread I} {w : Msg} (hw : w.loc = wordLoc ctr)
    (hfree : ¬ (freeR heap cells hu).contains w.loc.addr.toNat) (hp : t'.prom = t.prom)
    (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    {c' : Spike.Lib.Ctl} {x : String} {n : Nat} {τ : Ty} {e : Expr} (hs : AllocSite N c' x n τ e)
    (hv : w.val.toNat = hu + units n τ) (hh : c'.hold = some (ctr, cst (.num hu))) :
    AllocInvS N Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c' :=
  .inl ⟨_, hh, hu, fun _ => False, rfl,
    ⟨x, n, τ, e, hs, hv ▸ hp ▸ CtrAt.append_self hw hpl, fun _ h => h.elim⟩,
    ha.store_out hfree hp⟩

/-- **A store while pending** below the pending object's base, off the
counter (the allocator's header store), is recorded as an exception
(`AllocInv.header`, the bound for whichever site is pending). -/
theorem AllocInvS.header {wh : Word} {ex : Nat → Prop} (hh : c.hold = some (ctr, wh))
    (ho : numOf [wh] = some old) (hpd : PendingS N units off tm t.prom heap ctr old ex c)
    (ha : ArenaOK Λ lbl lsize t tm heap cells old ex) {t' : Thread I} {w : Msg} (hw : w.loc ≠ wordLoc ctr)
    (hlt : ∀ x n τ e, AllocSite N c x n τ e → w.loc.addr.toNat < heap + 16 * old + off n τ)
    (hp : t'.prom = t.prom) :
    AllocInvS N Λ lbl lsize t' (tm.append w).1 heap cells ctr units off c := by
  obtain ⟨x, n, τ, e, hs, hctr, hex⟩ := hpd
  refine .inl ⟨wh, hh, old, _, ho, ⟨x, n, τ, e, hs, hp ▸ hctr.append_ne hw, ?_⟩, ha.store_ex hp⟩
  rintro a' (h | rfl)
  · exact hex a' h
  · exact hlt x n τ e hs

/-- **The landing** (`AllocInv.land`). -/
theorem AllocInvS.land {hu : Nat} (hctr : CtrAt tm t.prom ctr hu) {lbl' : WeakMem.AllocLabel → Option Nat}
    {lsize' : WeakMem.AllocLabel → Nat} (ha : ArenaOK Λ lbl' lsize' t tm heap cells hu (fun _ => False))
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) :
    AllocInvS N Λ lbl' lsize' t tm heap cells ctr units off c' :=
  .inr ⟨fun w h => (by rw [hc'] at h; cases h), hu, hctr, ha⟩

/-- **The box's landing at its initialising store**: the invariant with
the control holding the counter's old count `old` at a box `let x = new a
in e` (`a`'s type `ty`), so pending there; the
target's plain store to `wordLoc b` off the counter word; the contract after
it at `old` plus one object's units with no exception (over any placement,
`NewRow.row_newStore`'s with the box's label placed); the control after
holding nothing. Then the invariant is idle at `old + units 1 ty`. -/
theorem AllocInvS.newStore (A : Arch) {tid : Nat} {wh : Word}
    (hinv : AllocInvS N Λ lbl lsize t tm heap cells ctr units off c)
    (hh : c.hold = some (ctr, wh)) (ho : numOf [wh] = some old) {x : String} {a : At} {T : Option Ty} {e : Expr} {ty : Ty}
    {ws : List Word} (ht : c.term = .let_ x (.new a T) e) (hea : evalAt c.env a = some (ty, ws))
    {kr : StoreKind} {b : Nat} {V : Val} {s : I.State}
    (hex : I.exec t.st = some (.store kr false (wordLoc b) V fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho' : .ok o ∈ outs) (hpl : ∀ q ∈ t.prom, q ≤ tm.last)
    (hb : wordLoc b ≠ wordLoc ctr) {lbl' : WeakMem.AllocLabel → Option Nat} {lsize' : WeakMem.AllocLabel → Nat}
    (ha : ArenaOK Λ lbl' lsize' o.thread o.mem heap cells (old + units 1 ty) (fun _ => False))
    {c' : Spike.Lib.Ctl} (hc' : c'.hold = none) :
    AllocInvS N Λ lbl' lsize' o.thread o.mem heap cells ctr units off c' := by
  rcases hinv with ⟨w, hh', old', ex, ho', hpd, -⟩ | ⟨hn, -⟩
  · rw [hh] at hh'
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hh'
    subst hh'
    rw [ho] at ho'
    cases ho'
    obtain ⟨hctr, -⟩ := hpd.box ht hea
    exact AllocInvS.land (ctrAt_store_ne A hctr hex hstep ho' hpl hb) ha hc'
  · exact absurd hh (hn wh)

/-! ## Axioms -/

/-- info: 'Spike.Lib.AllocInvN.AllocInvS.newStore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocInvS.newStore

/-- info: 'Spike.Lib.AllocInvN.AllocInvS.header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocInvS.header

/-- info: 'Spike.Lib.AllocInvN.AllocInvS.ctrAdd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms AllocInvS.ctrAdd

end Spike.Lib.AllocInvN
