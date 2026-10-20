/-
**Part 4: the consumer's invariants and
VCs** on `EnvGTU isa Arch.armv8` (the cumulative take route).

**Consumer** (round `j = 1, 2, 3`: `X4 = j - 1`; the round reads `slot j`
(`B0`, `B1`, `B0`) and then releases `head := j`):
- `CE j` (at `cj`): all of `H`; spin facts at `T` (last message read `K`);
  round 1: `GB`, `K = 0` and `tail`'s initial message `0`; rounds 2, 3:
  `GA` (so no new `tail = 1` message can be seen: its slot holds `GA`), the
  own `head = 1` message (`MsgAt`, for the `Prev` of `head := 2, 3`), the
  last read is `≥ j - 1` (`KLow`), and the **cumulative knowledge** of
  every message up to `K`: `Got2` (all of `B1`, maximal write `2`) or every
  message `≤ 1`; `Got3` (all of `B0` with maximal write `3`, and `GB`) or
  every message `≤ 2`.
- `CX j` (after the spin's exit): the round's slot with maximal write `j`
  below `min vrNew vwNew` (`Mn`), and the facts the rest of the round needs.
- `scanT`: the spin read through `spinU_read`, decoded with `psiT` (every
  message in `(K, tr]` has a positive timestamp, so its value is `1`, `2`
  or `3`, with that slot's resources collected).
- `vcC_spin` (`LDAR X5, [X2]`): round 1 exits with `B0`, `GA` from the
  `tail = 1` slot, read or **skipped** (a read `tail = 2` has a `tail = 1`
  message below it, `Prev`); a `tail = 3` slot needs `GB`, which the
  consumer holds. Round 2 exits with `Got2` (a `tail = 3` message has a
  `tail = 2` one below it). Round 3 exits on `tail = 3` with `Got3`.
- `vcC_data` (`LDR W1x, [X7]`): under the clean flag the load returns `j`
  (`read_max`).
- `vcC_storeH` (`STLR X4, [X1]`): `head := 1` gives `B0`, `GB` (`psiH`);
  `head := 2, 3` give nothing and need `Prev H 1` (`prev_of_snap`).
-/
import Kraken.Promising.SLR.EnvG.A64SpscVCP

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The plans at the consumer's stores -/

section Plans

variable {P : SP}

theorem cons_whole (l : Loc) (v : Val) : (consPlan P).Whole l v :=
  Plan.Whole.of_entries (fun e he => by
    simp only [consPlan, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rfl) l v

theorem cons_rel_H1 : (consPlan P).rel P.H 1#128 = true := by simp [consPlan, Plan.rel, Plan.find?]
theorem cons_gives_H1 : (consPlan P).gives P.H 1#128 = [P.B0, GB] := by simp [consPlan, Plan.gives, Plan.find?]
theorem cons_rel_H2 : (consPlan P).rel P.H 2#128 = true := by simp [consPlan, Plan.rel, Plan.find?]
theorem cons_gives_H2 : (consPlan P).gives P.H 2#128 = [] := by simp [consPlan, Plan.gives, Plan.find?]
theorem cons_rel_H3 : (consPlan P).rel P.H 3#128 = true := by simp [consPlan, Plan.rel, Plan.find?]
theorem cons_gives_H3 : (consPlan P).gives P.H 3#128 = [] := by simp [consPlan, Plan.gives, Plan.find?]

end Plans

/-! ## Small `BitVec` facts -/

theorem bv_one_le {x : BitVec 64} (h : x ≠ 0) : 1 ≤ x := by bv_omega
theorem bv_two_le {x : BitVec 64} (h1 : 1 ≤ x) (h : x ≠ 1) : 2 ≤ x := by bv_omega
theorem bv_three_le {x : BitVec 64} (h1 : 2 ≤ x) (h : x ≠ 2) : 3 ≤ x := by bv_omega
theorem bv_not_le1 {x : BitVec 64} (h1 : x ≤ 1) (h2 : 2 ≤ x) : False := by bv_omega
theorem bv_not_le2 {x : BitVec 64} (h1 : x ≤ 2) (h2 : 3 ≤ x) : False := by bv_omega

/-! ## The consumer's knowledge -/

/-- The bound of the consumer's slots: `min vrNew vwNew`. -/
abbrev Mn (σ : State isa) : View := min σ.vs.vrNew σ.vs.vwNew

/-- The `tail` message at `K` has low word at least `j`. -/
def KLow (P : SP) (j : BitVec 64) (K : Time) (σ : State isa) : Prop :=
  ∀ u, σ.snap.mem.read? P.T K = some u → j ≤ lo u

/-- All of `B1`, maximal write `2`. -/
def Got2 (P : SP) (σ : State isa) : Prop := Full P.B1 2#128 (Mn σ) σ.r

/-- All of `B0`, maximal write `3`, and `GB`. -/
def Got3 (P : SP) (σ : State isa) : Prop := Full P.B0 3#128 (Mn σ) σ.r ∧ (σ.r.wr GB).q = 1

/-- **At `cj`** (consumer round `j`). -/
def CE (P : SP) (j : Nat) (σ : State isa) : Prop :=
  σ.g.rel = relS P ∧ (σ.r.wr P.H).q = 1 ∧
    (j = 1 → (σ.r.wr GB).q = 1 ∧ SpinU P.T (psiT P) 0 σ ∧ UpTo σ.snap.mem P.T 0 (· = 0)) ∧
    (j = 2 → (σ.r.wr GA).q = 1 ∧ MsgAt σ P.H 1 ∧ ∃ K, SpinU P.T (psiT P) K σ ∧ KLow P 1 K σ ∧
      (Got2 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 1)) ∧ (Got3 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 2))) ∧
    (j = 3 → (σ.r.wr GA).q = 1 ∧ MsgAt σ P.H 1 ∧ ∃ K, SpinU P.T (psiT P) K σ ∧ KLow P 2 K σ ∧
      (Got3 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 2)))

/-- **After the spin's exit** in consumer round `j`. -/
def CX (P : SP) (j : Nat) (σ : State isa) : Prop :=
  σ.g.rel = relS P ∧ (σ.r.wr P.H).q = 1 ∧ Full (slot P j) (nv j) (Mn σ) σ.r ∧
    (j = 1 → (σ.r.wr GB).q = 1 ∧ (σ.r.wr GA).q = 1 ∧ ∃ K, SpinU P.T (psiT P) K σ ∧ KLow P 1 K σ ∧
      (Got2 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 1)) ∧ UpTo σ.snap.mem P.T K (· ≤ 2)) ∧
    (j = 2 → (σ.r.wr GA).q = 1 ∧ MsgAt σ P.H 1 ∧ ∃ K, SpinU P.T (psiT P) K σ ∧ KLow P 2 K σ ∧
      (Got3 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 2))) ∧
    (j = 3 → MsgAt σ P.H 1)

/-! ## Keeping the consumer's facts -/

/-- **What a step keeps** for the consumer: every fully held location
outside `D`, the bound `Mn`, the snapshot, the `tail` spin facts. -/
structure CKeep (P : SP) (D : Loc → Prop) (σ σ' : State isa) : Prop where
  rel : σ'.g.rel = σ.g.rel
  full : ∀ x, ¬ D x → (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p
  mn : Mn σ ≤ Mn σ'
  pre : σ.snap.mem.Prefix σ'.snap.mem
  spin : ∀ K, SpinU P.T (psiT P) K σ → SpinU P.T (psiT P) K σ'
  cl : σ'.cl → σ.cl

section Keep

variable {P : SP} {D : Loc → Prop} {σ σ' : State isa}

theorem CKeep.fence (hf : FenceLe σ σ') : CKeep P D σ σ' :=
  ⟨by rw [hf.g], fun _ _ h => by rw [hf.r]; exact ⟨h, fun _ => Iff.rfl⟩, min_mono hf.vrNew hf.vwNew,
    by rw [hf.snap]; exact ⟨rfl, List.prefix_refl _⟩, fun _ h => h.fence hf, fun h => by rw [← hf.cl]; exact h⟩

theorem CKeep.loadPlain {tid : Nat} {a : BitVec 64} {n : Nat} {v : Val}
    (hs : (EC P tid).step (.load .plain false a n) σ v σ') : CKeep P D σ σ' := by
  have hk := loadKeepU hs
  have hr := load_r_eq (by decide) hs
  exact ⟨hk.rel, fun x _ h => hk.full x h, min_mono hk.vs.vrNew hk.vs.vwNew, ⟨hk.snap.init, hk.snap.msgs⟩,
    fun _ h => h.load_keep hk hr, hk.cl⟩

theorem Full.ckeep {x : Loc} {w : Val} (h : Full x w (Mn σ) σ.r) (hk : CKeep P D σ σ') (hx : ¬ D x) :
    Full x w (Mn σ') σ'.r := by
  obtain ⟨hq, ts, hX, hm, hts⟩ := h
  obtain ⟨hq', hX'⟩ := hk.full x hx hq
  exact ⟨hq', ts, (hX' _).mpr hX, fun p hp => hm p ((hX' p).mp hp), Nat.le_trans hts hk.mn⟩

theorem q_ckeep {x : Loc} (h : (σ.r.wr x).q = 1) (hk : CKeep P D σ σ') (hx : ¬ D x) : (σ'.r.wr x).q = 1 :=
  (hk.full x hx h).1

theorem Got2.ckeep (h : Got2 P σ) (hk : CKeep P D σ σ') (hx : ¬ D P.B1) : Got2 P σ' := Full.ckeep h hk hx

theorem Got3.ckeep (h : Got3 P σ) (hk : CKeep P D σ σ') (h0 : ¬ D P.B0) (hg : ¬ D GB) : Got3 P σ' :=
  ⟨Full.ckeep h.1 hk h0, q_ckeep h.2 hk hg⟩

theorem MsgAt.ckeep {l : Loc} {k : BitVec 64} (h : MsgAt σ l k) (hk : CKeep P D σ σ') : MsgAt σ' l k :=
  h.elim fun t ⟨u, hr, hu⟩ => ⟨t, u, read?_prefix hk.pre hr, hu⟩

theorem UpTo.ckeep {K : Time} {Q : BitVec 64 → Prop} (h : UpTo σ.snap.mem P.T K Q)
    (hsp : SpinU P.T (psiT P) K σ) (hk : CKeep P D σ σ') : UpTo σ'.snap.mem P.T K Q :=
  h.prefix hk.pre (hsp.msg.elim fun _ hr => read?_le_last hr)

theorem KLow.prefix {j : BitVec 64} {K : Time} (h : KLow P j K σ) (hsp : SpinU P.T (psiT P) K σ)
    (hpre : σ.snap.mem.Prefix σ'.snap.mem) : KLow P j K σ' := fun u hu => by
  obtain ⟨vK, hr⟩ := hsp.msg
  rw [read?_prefix hpre hr] at hu
  cases hu
  exact h _ hr

theorem KLow.ckeep {j : BitVec 64} {K : Time} (h : KLow P j K σ) (hsp : SpinU P.T (psiT P) K σ)
    (hk : CKeep P D σ σ') : KLow P j K σ' := h.prefix hsp hk.pre

theorem klow_of {j : BitVec 64} {tr : Time} {v : Val} (hrd : σ.snap.mem.read? P.T tr = some v) (h : j ≤ lo v) :
    KLow P j tr σ := fun u hu => by rw [hrd] at hu; cases hu; exact h

theorem CE.ckeep {j : Nat} (h : CE P j σ) (hk : CKeep P (fun _ => False) σ σ') : CE P j σ' := by
  obtain ⟨hrel, hH, h1, h2, h3⟩ := h
  refine ⟨by rw [hk.rel]; exact hrel, q_ckeep hH hk (fun h => h), fun e => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨a, b, c⟩ := h1 e
    exact ⟨q_ckeep a hk (fun h => h), hk.spin _ b, c.ckeep b hk⟩
  · obtain ⟨a, m, K, b, c, d, f⟩ := h2 e
    exact ⟨q_ckeep a hk (fun h => h), m.ckeep hk, K, hk.spin _ b, c.ckeep b hk,
      d.imp (fun g => Got2.ckeep g hk (fun h => h)) (fun u => u.ckeep b hk),
      f.imp (fun g => Got3.ckeep g hk (fun h => h) (fun h => h)) (fun u => u.ckeep b hk)⟩
  · obtain ⟨a, m, K, b, c, f⟩ := h3 e
    exact ⟨q_ckeep a hk (fun h => h), m.ckeep hk, K, hk.spin _ b, c.ckeep b hk,
      f.imp (fun g => Got3.ckeep g hk (fun h => h) (fun h => h)) (fun u => u.ckeep b hk)⟩

theorem CX.ckeep {j : Nat} (h : CX P j σ) (hk : CKeep P (fun _ => False) σ σ') : CX P j σ' := by
  obtain ⟨hrel, hH, hS, h1, h2, h3⟩ := h
  refine ⟨by rw [hk.rel]; exact hrel, q_ckeep hH hk (fun h => h), hS.ckeep hk (fun h => h), fun e => ?_, fun e => ?_,
    fun e => (h3 e).ckeep hk⟩
  · obtain ⟨a, a', K, b, c, d, f⟩ := h1 e
    exact ⟨q_ckeep a hk (fun h => h), q_ckeep a' hk (fun h => h), K, hk.spin _ b, c.ckeep b hk,
      d.imp (fun g => Got2.ckeep g hk (fun h => h)) (fun u => u.ckeep b hk), f.ckeep b hk⟩
  · obtain ⟨a, m, K, b, c, f⟩ := h2 e
    exact ⟨q_ckeep a hk (fun h => h), m.ckeep hk, K, hk.spin _ b, c.ckeep b hk,
      f.imp (fun g => Got3.ckeep g hk (fun h => h) (fun h => h)) (fun u => u.ckeep b hk)⟩

end Keep

/-! ## The `tail` spin -/

/-- **The decoded `tail` messages in `(K, tr]`**: value `1`, `2` or `3`
with `psiT`'s slot, whose fully held locations the consumer now holds (and
did not before), with the slot's maximal writes below `Mn`. -/
def NewT (P : SP) (K tr : Time) (σ σ' : State isa) : Prop :=
  ∀ t u, K < t → t ≤ tr → σ'.snap.mem.read? P.T t = some u →
    ∃ R, ((lo u = 1 ∧ Full P.B0 1#128 t R ∧ (R.wr GA).q = 1) ∨
        (lo u = 2 ∧ Full P.B1 2#128 t R ∧ Prev σ'.snap.mem P.T 1 t) ∨
        (lo u = 3 ∧ Full P.B0 3#128 t R ∧ (R.wr GB).q = 1 ∧ Prev σ'.snap.mem P.T 2 t)) ∧
      (∀ x, (R.wr x).q = 1 → (σ.r.wr x).q = 0 ∧ (σ'.r.wr x).q = 1) ∧
      (∀ x w, Full x w t R → Full x w (Mn σ') σ'.r)

/-- **The scan of a `tail` spin read** (`LDAR X5, [X2]`). -/
theorem scanT {P : SP} {tid : Nat} {K : Time} {σ σ' : State isa} {v : Val} (hrel : σ.g.rel = relS P)
    (hsp : SpinU P.T (psiT P) K σ) (hs : (EC P tid).step (.load .acq false P.t 8) σ v σ') :
    ∃ tr, SpinU P.T (psiT P) tr σ' ∧ K ≤ tr ∧ σ'.snap.mem.read? P.T tr = some v ∧ NewT P K tr σ σ' := by
  obtain ⟨tr, hsp', hKtr, hrd, hvr, hvw, hnew⟩ := spinU_read (k := .acq) rfl
    (by rw [hrel]; exact relS_T P) hsp hs
  refine ⟨tr, hsp', hKtr, hrd, fun t u hKt htr hr => ?_⟩
  obtain ⟨R, hR, hcol⟩ := hnew t u hKt htr hr (psiT_impure P u)
  refine ⟨R, ?_, fun x hx => ⟨(hcol x hx).1, (hcol x hx).2.1⟩, fun x w ⟨hq, ts, hX, hm, hts⟩ => ?_⟩
  · rcases hR with ⟨-, h0, -⟩ | h
    · exact absurd h0 (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hKt))
    · exact h
  · obtain ⟨-, hq', hX'⟩ := hcol x hq
    exact ⟨hq', ts, (hX' _).mpr hX, fun p hp => hm p ((hX' p).mp hp),
      Nat.le_trans hts (Nat.le_trans htr (Nat.le_min.mpr ⟨hvr, hvw⟩))⟩

/-- Holding `GA`, no new `tail = 1` message is seen. -/
theorem NewT.noGA {P : SP} {K tr : Time} {σ σ' : State isa} (hn : NewT P K tr σ σ') (hGA : (σ.r.wr GA).q = 1) :
    ∀ t u, K < t → t ≤ tr → σ'.snap.mem.read? P.T t = some u → lo u ≠ 1 := fun t u hKt ht hr h1 => by
  obtain ⟨R, hR, hcol, -⟩ := hn t u hKt ht hr
  rcases hR with ⟨-, -, hG⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · have := (hcol GA hG).1; rw [hGA] at this; exact absurd this (by decide)
  · rw [h1] at h; exact absurd h (by decide)
  · rw [h1] at h; exact absurd h (by decide)

/-- **`Got3` or every message `≤ 2`**, through a scan. -/
theorem got3_scan {P : SP} {tid : Nat} {K tr : Time} {σ σ' : State isa} (hk : LoadKeepU tid σ σ')
    (hsp : SpinU P.T (psiT P) K σ) (hn : NewT P K tr σ σ') (hG3 : Got3 P σ ∨ UpTo σ.snap.mem P.T K (· ≤ 2)) :
    Got3 P σ' ∨ UpTo σ'.snap.mem P.T tr (· ≤ 2) := by
  have hmn : Mn σ ≤ Mn σ' := min_mono hk.vs.vrNew hk.vs.vwNew
  rcases hG3 with ⟨hF, hG⟩ | hu
  · exact .inl ⟨Full.keep hF hk.full hmn, q_keep hG hk.full⟩
  · by_cases h3 : ∃ t u, K < t ∧ t ≤ tr ∧ σ'.snap.mem.read? P.T t = some u ∧ lo u = 3
    · obtain ⟨t, u, hKt, ht, hr, hu3⟩ := h3
      obtain ⟨R, hR, hcol, hfull⟩ := hn t u hKt ht hr
      rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hF, hG, -⟩
      · rw [hu3] at h; exact absurd h (by decide)
      · rw [hu3] at h; exact absurd h (by decide)
      · exact .inl ⟨hfull _ _ hF, (hcol GB hG).2⟩
    · refine .inr (UpTo.extend (hu.prefix ⟨hk.snap.init, hk.snap.msgs⟩
        (hsp.msg.elim fun _ hr => read?_le_last hr)) fun t hKt ht u hr => ?_)
      obtain ⟨R, hR, -⟩ := hn t u hKt ht hr
      rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; decide
      · rw [h]; decide
      · exact absurd ⟨t, u, hKt, ht, hr, h⟩ h3

/-- **VC `LDAR X5, [X2]`** (the `tail` spin of consumer round `j`, with
`X4 = j - 1`): the back edge (`tail = X4`) keeps `CE j`; the exit gives
`CX j`. -/
theorem vcC_spin {P : SP} {tid j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) {σ σ' : State isa} {v : Val}
    (h : CE P j σ) (hs : (EC P tid).step (.load .acq false P.t 8) σ v σ') :
    (lo v = BitVec.ofNat 64 (j - 1) → CE P j σ') ∧ (lo v ≠ BitVec.ofNat 64 (j - 1) → CX P j σ') := by
  obtain ⟨hrel, hH, h1, h2, h3⟩ := h
  have hk := loadKeepU hs
  have hrel' : σ'.g.rel = relS P := by rw [hk.rel]; exact hrel
  have hH' := q_keep hH hk.full
  have hpre : σ.snap.mem.Prefix σ'.snap.mem := ⟨hk.snap.init, hk.snap.msgs⟩
  have upK : ∀ {K : Time} {Q : BitVec 64 → Prop}, SpinU P.T (psiT P) K σ → UpTo σ.snap.mem P.T K Q →
      UpTo σ'.snap.mem P.T K Q := fun hsp hu => hu.prefix hpre (hsp.msg.elim fun _ hr => read?_le_last hr)
  rcases hj with rfl | rfl | rfl
  · -- round 1
    obtain ⟨hGB, hsp, hz⟩ := h1 rfl
    obtain ⟨tr, hsp', -, hrd, hnew⟩ := scanT hrel hsp hs
    have hz' : UpTo σ'.snap.mem P.T 0 (· = 0) := upK hsp hz
    have hgb : ∀ t u, 0 < t → t ≤ tr → σ'.snap.mem.read? P.T t = some u → lo u ≠ 3 := fun t u h0 ht hr h3 => by
      obtain ⟨R, hR, hcol, -⟩ := hnew t u h0 ht hr
      rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, hG, -⟩
      · rw [h3] at h; exact absurd h (by decide)
      · rw [h3] at h; exact absurd h (by decide)
      · have := (hcol GB hG).1; rw [hGB] at this; exact absurd this (by decide)
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have htr : tr = 0 := by
        refine Classical.byContradiction fun hne => ?_
        obtain ⟨R, hR, -⟩ := hnew tr v (Nat.pos_of_ne_zero hne) (Nat.le_refl _) hrd
        rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [hv] at h <;> exact absurd h (by decide)
      subst htr
      exact ⟨hrel', hH', fun _ => ⟨q_keep hGB hk.full, hsp', hz'⟩, fun e => absurd e (by decide),
        fun e => absurd e (by decide)⟩
    · have hv0 : lo v ≠ 0 := hv
      have htr : 0 < tr := Nat.pos_of_ne_zero fun h0 => hv0 (by subst h0; exact hz' 0 (Nat.le_refl _) v hrd)
      obtain ⟨R, hR, hcol, hfull⟩ := hnew tr v htr (Nat.le_refl _) hrd
      have hB0GA : Full P.B0 1#128 (Mn σ') σ'.r ∧ (σ'.r.wr GA).q = 1 := by
        rcases hR with ⟨-, hF, hG⟩ | ⟨-, -, t1, ht1, u1, hr1, hu1⟩ | ⟨-, -, hG, -⟩
        · exact ⟨hfull _ _ hF, (hcol GA hG).2⟩
        · have h1pos : 0 < t1 := Nat.pos_of_ne_zero fun h0 => by
            subst h0
            have := hz' 0 (Nat.le_refl _) u1 hr1
            rw [hu1] at this; exact absurd this (by decide)
          obtain ⟨R1, hR1, hcol1, hfull1⟩ := hnew t1 u1 h1pos (Nat.le_of_lt ht1) hr1
          rcases hR1 with ⟨-, hF, hG⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · exact ⟨hfull1 _ _ hF, (hcol1 GA hG).2⟩
          · rw [hu1] at h; exact absurd h (by decide)
          · rw [hu1] at h; exact absurd h (by decide)
        · have := (hcol GB hG).1; rw [hGB] at this; exact absurd this (by decide)
      have hG2 : Got2 P σ' ∨ UpTo σ'.snap.mem P.T tr (· ≤ 1) := by
        by_cases h2 : ∃ t u, 0 < t ∧ t ≤ tr ∧ σ'.snap.mem.read? P.T t = some u ∧ lo u = 2
        · obtain ⟨t, u, h0, ht, hr, hu⟩ := h2
          obtain ⟨R, hR, -, hfull⟩ := hnew t u h0 ht hr
          rcases hR with ⟨h, -⟩ | ⟨-, hF, -⟩ | ⟨h, -⟩
          · rw [hu] at h; exact absurd h (by decide)
          · exact .inl (hfull _ _ hF)
          · rw [hu] at h; exact absurd h (by decide)
        · refine .inr (UpTo.extend (hz'.mono fun x hx => by rw [hx]; decide) fun t h0 ht u hr => ?_)
          obtain ⟨R, hR, -⟩ := hnew t u h0 ht hr
          rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · rw [h]; decide
          · exact absurd ⟨t, u, h0, ht, hr, h⟩ h2
          · exact absurd h (hgb t u h0 ht hr)
      have hU2 : UpTo σ'.snap.mem P.T tr (· ≤ 2) :=
        UpTo.extend (hz'.mono fun x hx => by rw [hx]; decide) fun t h0 ht u hr => by
          obtain ⟨R, hR, -⟩ := hnew t u h0 ht hr
          rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
          · rw [h]; decide
          · rw [h]; decide
          · exact absurd h (hgb t u h0 ht hr)
      exact ⟨hrel', hH', by rw [show slot P 1 = P.B0 from rfl]; exact hB0GA.1,
        fun _ => ⟨q_keep hGB hk.full, hB0GA.2, tr, hsp', klow_of hrd (bv_one_le hv0), hG2, hU2⟩,
        fun e => absurd e (by decide), fun e => absurd e (by decide)⟩
  · -- round 2
    obtain ⟨hGA, hM, K, hsp, hkl, hG2, hG3⟩ := h2 rfl
    obtain ⟨tr, hsp', hKtr, hrd, hnew⟩ := scanT hrel hsp hs
    have hga := hnew.noGA hGA
    have hlo : 1 ≤ lo v ∧ (lo v ≠ 1 → 2 ≤ lo v) := by
      rcases Nat.eq_or_lt_of_le hKtr with e | hlt
      · subst e
        have h1 := hkl.prefix hsp hpre v hrd
        exact ⟨h1, bv_two_le h1⟩
      · obtain ⟨R, hR, -⟩ := hnew tr v hlt (Nat.le_refl _) hrd
        rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h (hga tr v hlt (Nat.le_refl _) hrd)
        · rw [h]; exact ⟨by decide, fun _ => by decide⟩
        · rw [h]; exact ⟨by decide, fun _ => by decide⟩
    have hG2' : Got2 P σ' ∨ UpTo σ'.snap.mem P.T tr (· ≤ 1) := by
      rcases hG2 with g | hu1
      · exact .inl (Full.keep g hk.full (min_mono hk.vs.vrNew hk.vs.vwNew))
      · have hu1' := upK hsp hu1
        by_cases h2 : ∃ t u, K < t ∧ t ≤ tr ∧ σ'.snap.mem.read? P.T t = some u ∧ lo u = 2
        · obtain ⟨t, u, hKt, ht, hr, hu⟩ := h2
          obtain ⟨R, hR, -, hfull⟩ := hnew t u hKt ht hr
          rcases hR with ⟨h, -⟩ | ⟨-, hF, -⟩ | ⟨h, -⟩
          · rw [hu] at h; exact absurd h (by decide)
          · exact .inl (hfull _ _ hF)
          · rw [hu] at h; exact absurd h (by decide)
        · refine .inr (UpTo.extend hu1' fun t hKt ht u hr => ?_)
          obtain ⟨R, hR, -⟩ := hnew t u hKt ht hr
          rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, t2, ht2, u2, hr2, hu2⟩
          · exact absurd h (hga t u hKt ht hr)
          · exact absurd ⟨t, u, hKt, ht, hr, h⟩ h2
          · rcases Nat.lt_or_ge K t2 with hK2 | hK2
            · exact absurd ⟨t2, u2, hK2, Nat.le_trans (Nat.le_of_lt ht2) ht, hr2, hu2⟩ h2
            · have := hu1' t2 hK2 u2 hr2; rw [hu2] at this; exact absurd this (by decide)
    have hG3' := got3_scan hk hsp hnew hG3
    refine ⟨fun hv => ⟨hrel', hH', fun e => absurd e (by decide),
      fun _ => ⟨q_keep hGA hk.full, hM.load hk, tr, hsp', klow_of hrd (by rw [hv]; decide), hG2', hG3'⟩,
      fun e => absurd e (by decide)⟩, fun hv => ?_⟩
    have hv1 : lo v ≠ 1 := hv
    have h2le := hlo.2 hv1
    have hg : Got2 P σ' := hG2'.resolve_right fun hu => bv_not_le1 (hu tr (Nat.le_refl _) v hrd) h2le
    exact ⟨hrel', hH', by rw [show slot P 2 = P.B1 from rfl]; exact hg, fun e => absurd e (by decide),
      fun _ => ⟨q_keep hGA hk.full, hM.load hk, tr, hsp', klow_of hrd h2le, hG3'⟩, fun e => absurd e (by decide)⟩
  · -- round 3
    obtain ⟨hGA, hM, K, hsp, hkl, hG3⟩ := h3 rfl
    obtain ⟨tr, hsp', hKtr, hrd, hnew⟩ := scanT hrel hsp hs
    have hga := hnew.noGA hGA
    have hlo : 2 ≤ lo v := by
      rcases Nat.eq_or_lt_of_le hKtr with e | hlt
      · subst e; exact hkl.prefix hsp hpre v hrd
      · obtain ⟨R, hR, -⟩ := hnew tr v hlt (Nat.le_refl _) hrd
        rcases hR with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · exact absurd h (hga tr v hlt (Nat.le_refl _) hrd)
        · rw [h]; decide
        · rw [h]; decide
    have hG3' := got3_scan hk hsp hnew hG3
    refine ⟨fun hv => ⟨hrel', hH', fun e => absurd e (by decide), fun e => absurd e (by decide),
      fun _ => ⟨q_keep hGA hk.full, hM.load hk, tr, hsp', klow_of hrd hlo, hG3'⟩⟩, fun hv => ?_⟩
    have hv2 : lo v ≠ 2 := hv
    have h3le := bv_three_le hlo hv2
    have hg : Got3 P σ' := hG3'.resolve_right fun hu => bv_not_le2 (hu tr (Nat.le_refl _) v hrd) h3le
    exact ⟨hrel', hH', by rw [show slot P 3 = P.B0 from rfl]; exact hg.1, fun e => absurd e (by decide),
      fun e => absurd e (by decide), fun _ => hM.load hk⟩

/-! ## The data load -/

/-- **VC `LDR W1x, [X7]`** (the data load of round `j`): `CX j` is kept and,
under the clean flag, the load returns `j` (`read_max`). -/
theorem vcC_data {P : SP} {tid j : Nat} {σ σ' : State isa} {v : Val} (h : CX P j σ)
    (hs : (EC P tid).step (.load .plain false (slot P j).addr 4) σ v σ') : CX P j σ' ∧ (σ'.cl → v = nv j) := by
  refine ⟨h.ckeep (CKeep.loadPlain hs), fun hc => ?_⟩
  have hsl : (⟨(slot P j).addr, 4⟩ : Loc) = slot P j := by unfold slot; split <;> rfl
  obtain ⟨ga, hanc, -, hcl, tr, hrd, -⟩ := step_loadFactsTU hs
  rw [hcl] at hc
  obtain ⟨-, rF, E'⟩ := hc
  obtain ⟨t, ht⟩ : ∃ t, σ'.snap.threads[tid]? = some t :=
    ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
  have hp : t.prom.contains tr = false := by
    have := hrd.notOwn
    simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
    exact this
  obtain ⟨-, -, ⟨hq, ts, hX, hmax, hts⟩, -⟩ := h
  have hrd' := hrd.val
  have hwi := hrd.window
  rw [hsl] at hrd' hwi
  exact (read_max E' ht hq hX hmax hrd' hp hwi
    (Nat.le_trans hts (Nat.le_trans (Nat.min_le_left _ _) (le_readBound_vrNew _ _ _ _)))).2

/-! ## The `head` release -/

/-- **VC `STLR X4, [X1]`** (the `head` release of round `j`, value `j`):
permitted (planned; `head := 1` gives `B0` and `GB`, `psiH`'s second case;
`head := 2, 3` give nothing and need the own `head = 1` message below the
fresh timestamp, `prev_of_snap`), and gives `CE (j + 1)` (rounds 1, 2). -/
theorem vcC_storeH {P : SP} (hL : SpscLocs P) {tid j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) {σ : State isa}
    (h : CX P j σ) :
    (EC P tid).ok (.store .rel false P.h 8 (nv j)) σ ∧
      ∀ b (σ' : State isa), (EC P tid).step (.store .rel false P.h 8 (nv j)) σ b σ' →
        (j = 1 → CE P 2 σ') ∧ (j = 2 → CE P 3 σ') := by
  obtain ⟨hrel, hH, hS, h1, h2, h3⟩ := h
  have hrl : (consPlan P).rel P.H (nv j) = true := by
    rcases hj with rfl | rfl | rfl
    · exact cons_rel_H1
    · exact cons_rel_H2
    · exact cons_rel_H3
  have hwh := cons_whole (P := P) P.H (nv j)
  have hHg : P.H ∉ (consPlan P).gives P.H (nv j) := (consPlan_valid hL).not_mem_gives _ _
  refine ⟨⟨rfl, by show 0 < (σ.r.wr P.H).q; rw [hH]; decide,
    fun hr => absurd (hr.symm.trans hrl) Bool.false_ne_true, fun _ => ⟨effRel_rel _ _, ?_, hHg, ?_⟩⟩, ?_⟩
  · show ¬ Pred.Pure (σ.g.rel P.H) _
    rw [hrel, relS_H hL]
    intro hp
    have := psiH_pure P hp
    rcases hj with rfl | rfl | rfl <;> exact absurd this (by decide)
  · intro c g hanc hwb
    show (σ.g.rel P.H).P _ _ _ _
    rw [hrel, relS_H hL, Plan.give_of_whole _ hwh]
    rcases hj with rfl | rfl | rfl
    · obtain ⟨hGB, -⟩ := h1 rfl
      rw [show nv 1 = 1#128 from rfl, cons_gives_H1]
      rw [show slot P 1 = P.B0 from rfl] at hS
      obtain ⟨hqS, ts, hX, hm, hts⟩ := hS
      have e1 : P.B0 ∈ [P.B0, GB] := by simp
      have e2 : GB ∈ [P.B0, GB] := by simp
      have hlt := hwb.vwNew
      refine .inr (.inl ⟨rfl, by rw [wr_only_mem e1]; exact hqS, fun p hp => ?_, by rw [wr_only_mem e2]; exact hGB⟩)
      rw [wr_only_mem e1] at hp
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt
        (Nat.le_trans (hm p hp) (Nat.le_trans hts (Nat.min_le_right _ _))) hlt)
    · obtain ⟨-, hM, -⟩ := h2 rfl
      exact .inr (.inr ⟨.inl rfl, prev_of_snap hanc hM _⟩)
    · exact .inr (.inr ⟨.inr rfl, prev_of_snap hanc (h3 rfl) _⟩)
  intro b σ' hs
  have hrel' := rel_store hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨Pc, -, hr⟩, hcl, -⟩ := step_storeFactsTU hs
  have hHq : (σ'.r.wr P.H).q = 1 := by
    rw [hr]; unfold Plan.after
    split <;> rw [Res.addW_q] <;> first | exact hH | (rw [(consPlan P).keep_wr_self hHg hwh]; exact hH)
  have hk : CKeep P (fun x => x = P.H ∨ x ∈ (consPlan P).gives P.H (nv j)) σ σ' := by
    refine ⟨hrel', fun x hx hq => ?_, min_mono hwv.mono.vrNew hwv.mono.vwNew, snapLe_store hs,
      fun K hsp => ?_, fun h => by rw [← hcl]; exact h⟩
    · rw [hr]; exact keepsFull_store (fun e => hx (.inl e)) hwh (fun e => hx (.inr e)) hq
    · refine hsp.store_other hs (Ne.symm hL.h_t) hwh fun hm => ?_
      rcases hj with rfl | rfl | rfl
      · rw [show nv 1 = 1#128 from rfl, cons_gives_H1] at hm
        simp [hL.b0_t.symm, (ne_gb (show (8 : Nat) ≠ 5 by decide))] at hm
      · rw [show nv 2 = 2#128 from rfl, cons_gives_H2] at hm; cases hm
      · rw [show nv 3 = 3#128 from rfl, cons_gives_H3] at hm; cases hm
  have hmsg : ∀ k : Nat, j = k → MsgAt σ' P.H (lo (nv k)) := fun k e => by
    subst e
    exact ⟨tw, nv j, read?_of_writeSnap hws (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hwb.vwNew)),
      rfl⟩
  refine ⟨fun e => ?_, fun e => ?_⟩
  · subst e
    obtain ⟨-, hGA, K, hsp, hkl, hG2, hU2⟩ := h1 rfl
    have hD : ∀ x, x ≠ P.H → x ≠ P.B0 → x ≠ GB → ¬ (x = P.H ∨ x ∈ (consPlan P).gives P.H (nv 1)) := by
      intro x h0 h1 h2 hx
      rw [show nv 1 = 1#128 from rfl, cons_gives_H1] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx | hx
      · exact h0 hx
      · exact h1 hx
      · exact h2 hx
    exact ⟨by rw [hrel']; exact hrel, hHq, fun e => absurd e (by decide),
      fun _ => ⟨q_ckeep hGA hk (hD GA (ne_ga (show (8 : Nat) ≠ 5 by decide)).symm
          (ne_ga (show (4 : Nat) ≠ 5 by decide)).symm (by decide)),
        hmsg 1 rfl, K, hk.spin K hsp, hkl.ckeep hsp hk,
        hG2.imp (fun g => Got2.ckeep g hk (hD _ hL.b1_h (b0_b1 P).symm (ne_gb (by decide))))
          (fun u => u.ckeep hsp hk),
        .inr (hU2.ckeep hsp hk)⟩,
      fun e => absurd e (by decide)⟩
  · subst e
    obtain ⟨hGA, hM, K, hsp, hkl, hG3⟩ := h2 rfl
    have hD : ∀ x, x ≠ P.H → ¬ (x = P.H ∨ x ∈ (consPlan P).gives P.H (nv 2)) := by
      intro x h0 hx
      rw [show nv 2 = 2#128 from rfl, cons_gives_H2] at hx
      simp only [List.not_mem_nil, or_false] at hx
      exact h0 hx
    exact ⟨by rw [hrel']; exact hrel, hHq, fun e => absurd e (by decide), fun e => absurd e (by decide),
      fun _ => ⟨q_ckeep hGA hk (hD GA (ne_ga (show (8 : Nat) ≠ 5 by decide)).symm), hM.ckeep hk, K,
        hk.spin K hsp, hkl.ckeep hsp hk,
        hG3.imp (fun g => Got3.ckeep g hk (hD _ hL.b0_h) (hD _ (ne_gb (show (8 : Nat) ≠ 5 by decide)).symm))
          (fun u => u.ckeep hsp hk)⟩⟩

#print axioms vcC_spin
#print axioms vcC_data
#print axioms vcC_storeH

end Kraken.Promising.SLR.EnvG.SpscA
