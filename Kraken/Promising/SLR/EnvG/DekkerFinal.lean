/-
**Dekker's final argument at the memory
level**. ISA-neutral.

`dekker_mfence.kl`: each thread raises its flag (`F_i := 1`), fences, reads
the other flag; if it read `0` it increments `C` non-atomically
(`a := C; C := a + 1`) and lowers its flag (`F_i := 0`). The property: not
both entered with `C = 1` at the end.

This file proves the property from facts each thread's `EnvG` proof can
carry to the final memory (`DekkerCore.lean`: `SBFact` and its re-anchoring
and final transport), plus each location's history (`Hist`), which at a
final configuration is the total write set (`Erase.X_iff_of_final`; the
threads' write sets are tracked by `Plan.after`).

- `Entered m j Fj Fo C t r trc a tc u`: thread `j`'s end facts when it
  entered: its raise at `t`, its read of the other flag at `r` (value `0`,
  no write to `Fo` in `(r, t]`: the `SBFact`), its read of `C` at `trc`
  (value `a`, no write to `C` in `(trc, r]`: the acquire load of `Fo` raised
  `vrNew` to `r`), its write of `inc a` at `tc > trc` (coherence) and its
  lowering at `u > tc` (TSO: every store is a release, `WriteBound.rel`).
- `dekker_final`: with the histories of `F0`, `F1`, `C` (only the threads'
  own messages), two entered threads leave `C = 2`, not `1`.

The SB step is `sb_key`'s argument (one read is at or above the other's
raise); the rest is message passing through the lowering store.
-/
import Kraken.Promising.SLR.EnvG.DekkerCore
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR.EnvG.Dekker

open Kraken Kraken.Promising

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The non-atomic increment's written value (a 32-bit `addl`, zero-extended). -/
def inc (a : Val) : Val := (a.setWidth 32 + 1).setWidth 128

/-- **Thread `j`'s end facts when it entered** (all in the final memory `m`). -/
structure Entered (m : Memory) (j : Nat) (Fj Fo C : Loc) (t r trc : Time) (a : Val) (tc u : Time) : Prop where
  raise : m.get? t = some ⟨Fj, 1, j⟩
  readF : ∃ v : Val, m.read? Fo r = some v ∧ v.setWidth 32 = 0
  winF : NoWriteIn m Fo r t
  readC : m.read? C trc = some a
  winC : NoWriteIn m C trc r
  write : m.get? tc = some ⟨C, inc a, j⟩
  coh : trc < tc
  lower : m.get? u = some ⟨Fj, 0, j⟩
  rel : tc < u

/-- The history of a flag `F` of thread `j` raised at `t` (and, if it
entered, lowered at `u`). -/
def FlagHist (m : Memory) (F : Loc) (t : Time) (u : Option Time) : Prop :=
  ∀ ts v, m.read? F ts = some v → (ts = 0 ∧ v = 0) ∨ (ts = t ∧ v = 1) ∨ (u = some ts ∧ v = 0)

/-- The history of the counter: the initial `0` and the two increments. -/
def CntHist (m : Memory) (C : Loc) (w0 w1 : Val × Time) : Prop :=
  ∀ ts v, m.read? C ts = some v → (ts = 0 ∧ v = 0) ∨ (ts = w0.2 ∧ v = w0.1) ∨ (ts = w1.2 ∧ v = w1.1)

theorem ne_zero_of_get? {m : Memory} {ts : Time} {w : Msg} (h : m.get? ts = some w) : ts ≠ 0 := by
  rintro rfl; simp [Memory.get?] at h

theorem read?_of_get? {m : Memory} {ts : Time} {w : Msg} (h : m.get? ts = some w) : m.read? w.loc ts = some w.val := by
  simp [Memory.read?, ne_zero_of_get? h, h]

/-- **One orientation**: thread 0 raised first (`t0 < t1`). Thread 1 read
`F0` after `t0`, hence the lowering `u0`; its counter read is then at or
above `tc0`, so it read `inc a0`; thread 0 read the initial `0`. The last
counter write is thread 1's, `inc (inc 0)`. -/
theorem dekker_final_lt {m : Memory} {j0 j1 : Nat} {F0 F1 C : Loc}
    {t0 r0 trc0 tc0 u0 t1 r1 trc1 tc1 u1 : Time} {a0 a1 : Val}
    (e0 : Entered m j0 F0 F1 C t0 r0 trc0 a0 tc0 u0) (e1 : Entered m j1 F1 F0 C t1 r1 trc1 a1 tc1 u1)
    (hF0 : FlagHist m F0 t0 (some u0)) (hC : CntHist m C (inc a0, tc0) (inc a1, tc1)) (hlt : t0 < t1) :
    m.finalVal C = inc (inc 0) := by
  -- thread 1 read the lowering of `F0`
  have hr1 : r1 = u0 := by
    obtain ⟨v, hv, hz⟩ := e1.readF
    rcases hF0 r1 v hv with ⟨rfl, -⟩ | ⟨rfl, rfl⟩ | ⟨hu, -⟩
    · exact absurd rfl (e1.winF t0 _ (Nat.pos_of_ne_zero (ne_zero_of_get? e0.raise)) (Nat.le_of_lt hlt) e0.raise)
    · exact absurd hz (by decide)
    · exact (Option.some.inj hu).symm
  subst hr1
  -- its counter read is at or above `tc0`
  have hge : tc0 ≤ trc1 :=
    Nat.le_of_not_lt fun h => e1.winC tc0 _ h (Nat.le_of_lt e0.rel) e0.write rfl
  have hc1 : trc1 = tc0 ∧ a1 = inc a0 := by
    rcases hC trc1 a1 e1.readC with ⟨rfl, -⟩ | ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact absurd hge (by have := ne_zero_of_get? e0.write; omega_t)
    · exact ⟨h1, h2⟩
    · simp only at h1; have := e1.coh; omega_t
  obtain ⟨rfl, rfl⟩ := hc1
  -- thread 0 read the initial `0`
  have ha0 : a0 = 0 := by
    rcases hC trc0 a0 e0.readC with ⟨-, h⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h
    · simp only at h1; have := e0.coh; omega_t
    · simp only at h1; have := e0.coh; have := e1.coh; omega_t
  subst ha0
  -- the last counter write is thread 1's
  refine SLR.Memory.finalVal_of_max (read?_of_get? e1.write) fun ts v h => ?_
  rcases hC ts v h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Nat.zero_le _
  · exact Nat.le_of_lt e1.coh
  · exact Nat.le_refl _

/-- **Dekker with `mfence`, the final argument**: two entered threads (with
the histories of both flags and the counter) leave `C = 2`, so not `1`. -/
theorem dekker_final {m : Memory} {F0 F1 C : Loc} (h01 : F0 ≠ F1)
    {t0 r0 trc0 tc0 u0 t1 r1 trc1 tc1 u1 : Time} {a0 a1 : Val}
    (e0 : Entered m 0 F0 F1 C t0 r0 trc0 a0 tc0 u0) (e1 : Entered m 1 F1 F0 C t1 r1 trc1 a1 tc1 u1)
    (hF0 : FlagHist m F0 t0 (some u0)) (hF1 : FlagHist m F1 t1 (some u1))
    (hC : CntHist m C (inc a0, tc0) (inc a1, tc1)) : m.finalVal C ≠ 1 := by
  have hval : m.finalVal C = inc (inc 0) := by
    rcases Nat.lt_trichotomy t0 t1 with h | h | h
    · exact dekker_final_lt e0 e1 hF0 hC h
    · subst h
      have := e0.raise.symm.trans e1.raise
      simp only [Option.some.injEq, Msg.mk.injEq] at this
      exact absurd this.1 h01
    · exact dekker_final_lt e1 e0 hF1
        (fun ts v hv => by rcases hC ts v hv with h | h | h <;> simp_all) h
  rw [hval]
  decide

/-! ## The histories from erasure at a final configuration

The histories are the total write sets (`Erase.X_iff_of_final`); a thread
holding all of a flag, or the two threads holding halves of the counter,
hold the whole total write set (no other thread and no slot holds a
positive share, so their write sets are empty). -/

section Hist

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **A flag's history**: thread `j` holds all of `F`, with write set the
initial `0`, its raise at `t` and (if it entered) its lowering at `u`. -/
theorem flagHist_of_erase (E : Erase rF g T c) (hf : c.final = true) {j : Nat} (hj : j < c.threads.size)
    {F : Loc} (hq : ((rF j).wr F).q = 1) {t : Time} {u : Option Time}
    (hX : ∀ p, ((rF j).wr F).X p → (p.2 = 0 ∧ p.1 = 0) ∨ (p.2 = t ∧ p.1 = 1) ∨ (u = some p.2 ∧ p.1 = 0)) :
    FlagHist c.mem F t u := by
  have hpos : 0 < ((total rF g c).wr F).q := by
    have := (sub_total_thread (rF := rF) (g := g) hj).q_le F
    rw [hq] at this
    grind
  obtain ⟨hth, hsl⟩ := E.unique_holder hj hq
  intro ts v hr
  rcases X_total_cases ((E.X_iff_of_final hf hpos (v, ts)).mpr hr) with ⟨i, hi, hXi⟩ | ⟨s, hs, hXs⟩
  · by_cases hij : i = j
    · subst hij; exact hX _ hXi
    · exact (((rF i).wr F).zero (hth i hi hij) _ hXi).elim
  · exact ((s.res.wr F).zero (hsl s hs) _ hXs).elim

/-- **The counter's history**: two threads hold half of `C` each, with write
sets the initial `0` and (if it entered) the thread's increment. -/
theorem cntHist_of_erase (E : Erase rF g T c) (hf : c.final = true) (hsize : c.threads.size = 2) {C : Loc}
    (hq0 : ((rF 0).wr C).q = 1 / 2) (hq1 : ((rF 1).wr C).q = 1 / 2) {w0 w1 : Val × Time}
    (hX0 : ∀ p, ((rF 0).wr C).X p → (p.2 = 0 ∧ p.1 = 0) ∨ p = w0)
    (hX1 : ∀ p, ((rF 1).wr C).X p → (p.2 = 0 ∧ p.1 = 0) ∨ p = w1) :
    CntHist c.mem C w0 w1 := by
  have hth : ((threadsRes rF c.threads.size).wr C).q = 1 := by
    rw [q_threadsRes, hsize]
    show ((List.range 2).map fun j => ((rF j).wr C).q).sum = 1
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, List.map_append, List.sum_append, hq0, hq1]
    grind
  have hpos : 0 < ((total rF g c).wr C).q := by
    rw [q_total, hth]
    have := (g.slotsRes.wr C).nonneg
    grind
  have hsl : ∀ s ∈ g.u, (s.res.wr C).q = 0 := fun s hs => by
    have h1 := E.q_le_one C
    rw [q_total, hth] at h1
    have h2 := (slotsRes_sub hs).q_le C
    have := (s.res.wr C).nonneg
    grind
  have hrd : ∀ p, (∃ v ts, p = (v, ts) ∧ ((p.2 = 0 ∧ p.1 = 0) ∨ p = w0 ∨ p = w1)) →
      (p.2 = 0 ∧ p.1 = 0) ∨ (p.2 = w0.2 ∧ p.1 = w0.1) ∨ (p.2 = w1.2 ∧ p.1 = w1.1) := by
    rintro p ⟨-, -, -, h | rfl | rfl⟩
    · exact .inl h
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · exact .inr (.inr ⟨rfl, rfl⟩)
  intro ts v hr
  refine hrd (v, ts) ⟨v, ts, rfl, ?_⟩
  rcases X_total_cases ((E.X_iff_of_final hf hpos (v, ts)).mpr hr) with ⟨i, hi, hXi⟩ | ⟨s, hs, hXs⟩
  · rw [hsize] at hi
    match i, hi with
    | 0, _ => rcases hX0 _ hXi with h | h
              · exact .inl h
              · exact .inr (.inl h)
    | 1, _ => rcases hX1 _ hXi with h | h
              · exact .inl h
              · exact .inr (.inr h)
  · exact ((s.res.wr C).zero (hsl s hs) _ hXs).elim

end Hist

end Kraken.Promising.SLR.EnvG.Dekker
