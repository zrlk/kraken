/-
**The allocation invariant along an instruction's outcome** for the
allocation-capable one-thread consumer (`Spike/Lib/A64ConsumerA.lean`):
`AllocInvAt` at the same heap use after an outcome that writes no word or a
word the arena allows other than the counter (`allocInvAt_out`), and after
the counter's add, idle to pending (`allocInvAt_ctr`).

- `AllocInvAt.arenaOK`, `AllocInvAt.idle_of_term`, `AllocInvAt.retarget`:
  the contract at the heap use; a control off an allocation site holds no
  counter word; idle, the control may change to another holding none.
- `ArenaW.out_free`: a word the arena allows, off the counter and outside
  the pending header, is outside the free range.
- `allocInvAt_out`: an outcome writing nothing (memory and promises
  unchanged) or one word `L` (`Writes`) off the counter the arena allows
  (`ArenaW`) keeps `AllocInvAt` (`idle_append_out`, `pending_keep`,
  `header`, `header_fulfil`, `prom_keep`).
- `allocInvAt_ctr`: the counter's add (`CtrRows.CtrW`), the counter read
  at its latest write not promised: the old count is the heap use, and
  `AllocInvAt` is pending at it with the control holding it (`ctrAdd`,
  `ctrAdd_fulfil`).
-/
import Spike.Lib.A64ConsumerA
import Spike.Lib.CtrRows

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.AllocRow (freeR ArenaOK)
open Spike.Lib.CtrRows (CtrW)

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : Lsize} {th : Thread isaLSE2} {tm : Memory} {ar : Arena}
  {hu : Nat} {c : Ctl}

/-- `AllocInvAt`'s contract at the heap use. -/
theorem _root_.Spike.Lib.AllocInvAt.arenaOK
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c) :
    ∃ ex, ArenaOK Λ lbl lsize th tm ar.heap ar.cells hu ex := by
  rcases h with ⟨-, ex, -, ha⟩ | ⟨-, -, ha⟩
  · exact ⟨ex, ha⟩
  · exact ⟨_, ha⟩

/-- **A control off an allocation site holds no counter word** under
`AllocInvAt` (pending is at the allocation): a control at `let x = o in e`
with `o` neither a buffer nor a box allocation. -/
theorem _root_.Spike.Lib.AllocInvAt.idle_of_term
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (ht : ∃ x o e, c.term = .let_ x o e ∧ (∀ a τ, o ≠ .newBuf a τ) ∧ ∀ a, o ≠ .new a) :
    ∀ w, c.hold ≠ some (ar.ctr, w) := by
  obtain ⟨x0, o, e0, ht, hb, hn⟩ := ht
  rcases h with ⟨-, -, ⟨x, n, τ, e, ⟨a, -, -, hc, -⟩ | ⟨-, a, -, hc, -⟩, -⟩, -⟩ | ⟨hn', -⟩
  · rw [ht] at hc; simp only [Expr.let_.injEq] at hc; exact absurd hc.2.1 (hb a τ)
  · rw [ht] at hc; simp only [Expr.let_.injEq] at hc; exact absurd hc.2.1 (hn a)
  · exact hn'

/-- **A control at `let x = o in e`, `o` neither a buffer nor a box
allocation**, as `AllocInvAt.idle_of_term` takes it. -/
theorem notAlloc_let {c : Ctl} {x : String} {o : Op} {e : Expr} (ht : c.term = .let_ x o e)
    (hb : ∀ a τ, o ≠ .newBuf a τ) (hn : ∀ a, o ≠ .new a) :
    ∃ x o e, c.term = .let_ x o e ∧ (∀ a τ, o ≠ .newBuf a τ) ∧ ∀ a, o ≠ .new a :=
  ⟨x, o, e, ht, hb, hn⟩

/-- **Idle, the control may change** to another holding no counter word. -/
theorem _root_.Spike.Lib.AllocInvAt.retarget
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hc : ∀ w, c.hold ≠ some (ar.ctr, w)) {c' : Ctl} (hc' : ∀ w, c'.hold ≠ some (ar.ctr, w)) :
    AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c' := by
  rcases h with ⟨hh, -⟩ | ⟨-, hctr, ha⟩
  · exact absurd hh (hc _)
  · exact .inr ⟨hc', hctr, ha⟩

/-- **Off the arena is off the free range** (the cursor within the
cells). -/
theorem out_free_of_arena {a : Nat} (hle : hu ≤ ar.cells)
    (ha : ¬ (ar.heap ≤ a ∧ a < ar.heap + 16 * ar.cells)) : ¬ (freeR ar.heap ar.cells hu).contains a := by
  intro ⟨h1, h2⟩
  simp only [freeR] at h1 h2
  exact ha ⟨by omega, by omega⟩

/-- **A word the arena allows, off the counter and outside the pending
header, is outside the free range**: off the arena, or in a placed label
(`ArenaOK.disj`); else below a pending buffer's or box's base. -/
theorem ArenaW.out_free {ex : Nat → Prop} (ha : ArenaOK Λ lbl lsize th tm ar.heap ar.cells hu ex) {L : Loc}
    (hL : ArenaW ar lbl lsize c L) (hne : L ≠ ar.ctrLoc) :
    ¬ (freeR ar.heap ar.cells hu).contains L.addr.toNat ∨
      (∃ old x a τ e ta ws k, c.hold = some (ar.ctr, TermRun.cst (.num old)) ∧ c.term = .let_ x (.newBuf a τ) e ∧
        TermRun.evalAt c.env a = some (ta, ws) ∧ TermRun.numOf ws = some k ∧
        L.addr.toNat < ar.heap + 16 * old + ar.off k τ) ∨
      ∃ old x a e ty ws, c.hold = some (ar.ctr, TermRun.cst (.num old)) ∧ c.term = .let_ x (.new a) e ∧
        TermRun.evalAt c.env a = some (ty, ws) ∧ L.addr.toNat < ar.heap + 16 * old + ar.off 1 ty := by
  rcases hL with he | hout | ⟨l, b, hb, hc⟩ | hh | ⟨-, hh⟩
  · exact absurd he hne
  · exact .inl (out_free_of_arena ha.hu_le hout)
  · exact .inl fun hf => (ha.disj l b hb).not_both hf hc
  · exact .inr (.inl hh)
  · exact .inr (.inr hh)

/-- The held count of a pending control is the heap use. -/
theorem held_num (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c) {old : Nat}
    (hh : c.hold = some (ar.ctr, TermRun.cst (.num old))) : old = hu := by
  have := congrArg (fun w : TermRun.Word => w.val) (h.held hh)
  simp only [TermRun.cst, Promises.TVal.mk0] at this
  cases this
  rfl

/-- **An outcome writing nothing, or one word off the counter that the
arena allows, keeps `AllocInvAt`** at the same heap use and control: an
append outside the free range (`idle_append_out`, `pending_keep`) or of the
pending header (`header`, `headerBox`); a fulfilment outside the free range
(`prom_keep`) or of the pending header (`header_fulfil`, `header_fulfilBox`); memory and
promises unchanged (`prom_keep`). -/
theorem allocInvAt_out (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hnd : th.prom.Nodup) {o : Outcome isaLSE2}
    (hm : (o.mem = tm ∧ o.thread.prom = th.prom) ∨
      ∃ L, Writes th tm o L ∧ L ≠ ar.ctrLoc ∧ ArenaW ar lbl lsize c L) :
    AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off hu c := by
  have hmem : ∀ q k', k' ≠ q → (k' ∈ th.prom.erase q ↔ k' ∈ th.prom) := fun q k' hne =>
    (List.Nodup.mem_erase_iff hnd).trans (and_iff_right hne)
  rcases hm with ⟨hm, hp⟩ | ⟨L, ⟨V, ⟨hm, hp⟩ | ⟨q, hq, hg, hm, hp⟩⟩, hne, hL⟩
  · rw [hm]
    exact h.prom_keep (fun _ _ _ _ => by rw [hp]) fun _ _ _ _ hk => hp ▸ hk
  · obtain ⟨ex, ha⟩ := h.arenaOK
    rw [hm]
    rcases ArenaW.out_free ha hL hne with hf | ⟨old, x, a, τ, e, ta, ws, k, hh, ht, hea, hk, hlt⟩ |
        ⟨old, x, a, e, ty, ws, hh, ht, hea, hlt⟩
    · by_cases hc : ∃ w, c.hold = some (ar.ctr, w)
      · obtain ⟨w, hw⟩ := hc
        have := h.held hw
        subst this
        exact h.pending_keep hw hf hne hp
      · exact h.idle_append_out (fun w hw => hc ⟨w, hw⟩) hf hne hp fun w hw => hc ⟨w, hw⟩
    · have := held_num h hh
      subst this
      exact h.header hh ht hea hk hne hlt hp
    · have := held_num h hh
      subst this
      exact h.headerBox hh ht hea hne hlt hp
  · obtain ⟨ex, ha⟩ := h.arenaOK
    rw [hm]
    rcases ArenaW.out_free ha hL hne with hf | ⟨old, x, a, τ, e, ta, ws, k, hh, ht, hea, hk, hlt⟩ |
        ⟨old, x, a, e, ty, ws, hh, ht, hea, hlt⟩
    · refine h.prom_keep (fun k' w hg' hl => ?_) fun k' w hg' hfr hk' => ?_
      · have hne' : k' ≠ q := by
          rintro rfl
          rw [hg] at hg'
          cases hg'
          exact hne hl
        rw [hp]; exact hmem q k' hne'
      · have hne' : k' ≠ q := by
          rintro rfl
          rw [hg] at hg'
          cases hg'
          exact hf hfr
        rw [hp]; exact (hmem q k' hne').mpr hk'
    · have := held_num h hh
      subst this
      exact h.header_fulfil hh ht hea hk hg hne hlt hnd hp
    · have := held_num h hh
      subst this
      exact h.header_fulfilBox hh ht hea hg hne hlt hnd hp

/-- **The counter's add**, idle at `hu` to pending: the counter read at its
latest write not promised (`old`), the outcome writing the old count plus
the buffer's units (`CtrW`): the old count is `hu`, and `AllocInvAt` is
pending at `hu` with the control now holding it (`ctrAdd`,
`ctrAdd_fulfil`). -/
theorem allocInvAt_ctr (hok : ar.OK)
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hc0 : c.hold = none) (hnd : th.prom.Nodup) (hpl : ∀ q ∈ th.prom, q ≤ tm.last) {tr : Nat} {old : Val}
    (hlat : TLatestP tm th.prom ar.ctr tr) (hr : tm.read? (wordLoc ar.ctr) tr = some old)
    {x : String} {a : At} {τ : Ty} {e : Expr} {ta : Ty} {ws : List TermRun.Word} {n : Nat}
    (ht : c.term = .let_ x (.newBuf a τ) e) (hea : TermRun.evalAt c.env a = some (ta, ws))
    (hk : TermRun.numOf ws = some n) {o : Outcome isaLSE2}
    (hw : CtrW th tm o 0 ar.ctr ((old.setWidth 64 + BitVec.ofNat 64 (ar.units n τ)).setWidth 128)) :
    (old.setWidth 64).toNat = hu ∧
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off hu
        { c with hold := some (ar.ctr, TermRun.cst (.num hu)) } := by
  have hn : ∀ w, c.hold ≠ some (ar.ctr, w) := fun w hw => by rw [hc0] at hw; cases hw
  obtain ⟨ex, ha⟩ := h.arenaOK
  have hle := ha.hu_le
  have hcl := hok.cells_lt
  have hul := hok.units_lt n τ
  -- the old count is `hu`
  have hold : old.toNat = hu := by
    rcases h with ⟨hh, -⟩ | ⟨-, ⟨k', hl', hv⟩, -⟩
    · exact absurd hh (hn _)
    · rw [← hlat.unique hl', wordAt_of_read hr] at hv
      exact Option.some.inj hv
  have hold64 : (old.setWidth 64).toNat = hu := by
    rw [BitVec.toNat_setWidth, hold]; exact Nat.mod_eq_of_lt (by omega)
  have hnew : ((old.setWidth 64 + BitVec.ofNat 64 (ar.units n τ)).setWidth 128).toNat = hu + ar.units n τ := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, hold64, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := ar.units n τ) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hfree : ¬ (freeR ar.heap ar.cells hu).contains (wordLoc ar.ctr).addr.toNat := by
    refine out_free_of_arena hle ?_
    have : (wordLoc ar.ctr).addr.toNat = ar.ctr := by
      simp only [wordLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hok.ctr_lt
    rw [this]; exact hok.ctr_out
  refine ⟨hold64, ?_⟩
  rcases hw with ⟨q, hq, hg, ⟨vs, hcv, hlt⟩, hm, hp⟩ | ⟨hm, hp⟩
  · rw [hm]
    refine h.ctrAdd_fulfil hn hg rfl hfree (fun k' hk' => ?_) hnd hp (c' := { c with hold := _ }) ht hea hk hnew rfl
    rcases hk'.1 with rfl | ⟨w, hgw, hlw, hpw⟩
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    · have := hcv k' w hgw hpw
      rw [hlw] at this
      exact Nat.lt_of_le_of_lt this hlt
  · rw [hm]
    exact h.ctrAdd hn rfl hfree hp hpl (c' := { c with hold := _ }) ht hea hk hnew rfl

/-- **The counter's add at any allocation site** (`allocInvAt_ctr` over
`AllocSite True`: a buffer or a box; `ctrAddS`, `ctrAdd_fulfilS`). -/
theorem allocInvAt_ctrS (hok : ar.OK)
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c)
    (hc0 : c.hold = none) (hnd : th.prom.Nodup) (hpl : ∀ q ∈ th.prom, q ≤ tm.last) {tr : Nat} {old : Val}
    (hlat : TLatestP tm th.prom ar.ctr tr) (hr : tm.read? (wordLoc ar.ctr) tr = some old)
    {x : String} {τ : Ty} {e : Expr} {n : Nat} (hs : AllocSite True c x n τ e) {o : Outcome isaLSE2}
    (hw : CtrW th tm o 0 ar.ctr ((old.setWidth 64 + BitVec.ofNat 64 (ar.units n τ)).setWidth 128)) :
    (old.setWidth 64).toNat = hu ∧
      AllocInvAt Λ lbl lsize o.thread o.mem ar.heap ar.cells ar.ctr ar.units ar.off hu
        { c with hold := some (ar.ctr, TermRun.cst (.num hu)) } := by
  have hn : ∀ w, c.hold ≠ some (ar.ctr, w) := fun w hw => by rw [hc0] at hw; cases hw
  obtain ⟨ex, ha⟩ := h.arenaOK
  have hle := ha.hu_le
  have hcl := hok.cells_lt
  have hul := hok.units_lt n τ
  -- the old count is `hu`
  have hold : old.toNat = hu := by
    rcases h with ⟨hh, -⟩ | ⟨-, ⟨k', hl', hv⟩, -⟩
    · exact absurd hh (hn _)
    · rw [← hlat.unique hl', wordAt_of_read hr] at hv
      exact Option.some.inj hv
  have hold64 : (old.setWidth 64).toNat = hu := by
    rw [BitVec.toNat_setWidth, hold]; exact Nat.mod_eq_of_lt (by omega)
  have hnew : ((old.setWidth 64 + BitVec.ofNat 64 (ar.units n τ)).setWidth 128).toNat = hu + ar.units n τ := by
    rw [BitVec.toNat_setWidth, BitVec.toNat_add, hold64, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := ar.units n τ) (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hfree : ¬ (freeR ar.heap ar.cells hu).contains (wordLoc ar.ctr).addr.toNat := by
    refine out_free_of_arena hle ?_
    have : (wordLoc ar.ctr).addr.toNat = ar.ctr := by
      simp only [wordLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hok.ctr_lt
    rw [this]; exact hok.ctr_out
  refine ⟨hold64, ?_⟩
  rcases hw with ⟨q, hq, hg, ⟨vs, hcv, hlt⟩, hm, hp⟩ | ⟨hm, hp⟩
  · rw [hm]
    refine h.ctrAdd_fulfilS hn hg rfl hfree (fun k' hk' => ?_) hnd hp (c' := { c with hold := _ }) hs hnew rfl
    rcases hk'.1 with rfl | ⟨w, hgw, hlw, hpw⟩
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
    · have := hcv k' w hgw hpw
      rw [hlw] at this
      exact Nat.lt_of_le_of_lt this hlt
  · rw [hm]
    exact h.ctrAddS hn rfl hfree hp hpl (c' := { c with hold := _ }) hs hnew rfl

end Spike.Lib.A64ConsumerA
