/-
**`treiber_aba_tagged.kl`, part 8: the final
configuration.**

- `DoneM0`, `DoneM1`: `Done0`, `Done1` over a memory and a resource (the
  rule link's `B` sees the configuration's memory and the thread's resource,
  not its `EStateX`); `Done0.toM`, `Done1.toM` move them to a later memory.
- `BV`: **the shared postcondition** of both threads' rules: thread `0`
  done (`DoneM0`) or thread `1` done (`DoneM1`), with the thread's `r12`,
  `r13`. The fractions tell the two apart (`Fr`: the tokens `tok0`, `tok1`).
- `hB0`, `hB1`: the rule link's `hB` from each thread's postcondition.
- `X_two`: with two threads whose fractions of `x` add up to at least `1`,
  every pair in the total write set of `x` is one of theirs (no slot holds
  any of `x`).
- **`final_never`**: at a final configuration with a clean erasure and two
  threads, the `.kl`'s outcome `0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B` is
  impossible (`aba_never` on the attribution of the final memory's messages
  of `head` and of the 8-byte locations: `Erase.X_iff_of_final`, `X_two`,
  `ExH`, `ExN`).
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABAComb
import Kraken.Promising.SLR.EnvG.X64VecTreiberABANoNT

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (initVal_eq)

namespace Kraken.Promising.X64.EnvG.VecABA

/-! ## The final facts over a memory -/

section DoneM

variable {P : Params} {S : BitVec 64 → Prop}

theorem IV.mono {m m' : Memory} (h : m.Prefix m') (hiv : IV P m) : IV P m' := by
  unfold IV
  rw [initVal_eq h.1, initVal_eq h.1, initVal_eq h.1]
  exact hiv

/-- Thread `0` done, over a memory `m` and a resource `r`. -/
def DoneM0 (P : Params) (S : BitVec 64 → Prop) (m : Memory) (r : Res) (r12 r13 : BitVec 64) : Prop :=
  Fr P 0 r ∧ IV P m ∧ ∃ v K tm tr W, r12 = lo v ∧ PopR P S 0 m K v r13 tm tr W ∧
    ExH P r (· = ((hi v + 1) ++ r13, W))

/-- Thread `1` done, over a memory `m` and a resource `r`. -/
def DoneM1 (P : Params) (S : BitVec 64 → Prop) (m : Memory) (r : Res) (r12 r13 : BitVec 64) : Prop :=
  Fr P 1 r ∧ IV P m ∧ ∃ (T1 : Time) (n1 : Val) (W2 : Time) (n2 : Val) (K : Loc → Time),
    R1 P S m K r12 T1 n1 ∧ R2 P S m K r13 T1 W2 n2 ∧
    ((r12 = 0 ∧ ExH P r (H1 r12 T1 n1 W2 n2 0 0)) ∨
      (r12 ≠ 0 ∧ ∃ W3 n3 Tn, R3 P S m r12 W2 W3 n3 Tn ∧ ExH P r (H1 r12 T1 n1 W2 n2 W3 n3) ∧
        ExN r (fun x t => K x < t ∧ x = nd r12 ∧ t ≤ Tn)))

theorem Done0.toM {σ : EStateX} {m : Memory} {r12 r13 : BitVec 64} (h : Done0 P S σ r12 r13)
    (hpre : σ.snap.mem.Prefix m) : DoneM0 P S m σ.r r12 r13 := by
  obtain ⟨⟨-, hfr, hiv, -⟩, v, K, tm, tr, W, h1, h2, h3⟩ := h
  exact ⟨hfr, hiv.mono hpre, v, K, tm, tr, W, h1, h2.mono hpre (Nat.le_refl _), h3⟩

theorem Done1.toM {σ : EStateX} {m : Memory} {r12 r13 : BitVec 64} (h : Done1 P S σ r12 r13)
    (hpre : σ.snap.mem.Prefix m) : DoneM1 P S m σ.r r12 r13 := by
  obtain ⟨⟨-, hfr, hiv, -⟩, T1, n1, W2, n2, K, h1, h2, h3⟩ := h
  refine ⟨hfr, hiv.mono hpre, T1, n1, W2, n2, K, h1.mono hpre (fun _ => Nat.le_refl _),
    h2.mono hpre (fun _ => Nat.le_refl _), ?_⟩
  rcases h3 with ⟨h0, hH, -⟩ | ⟨h0, W3, n3, Tn, hr3, hH, hN⟩
  · exact .inl ⟨h0, hH⟩
  · exact .inr ⟨h0, W3, n3, Tn, hr3.mono hpre, hH, hN⟩

end DoneM

/-! ## The shared postcondition -/

/-- **The shared postcondition**: thread `0` or thread `1` done on the
resource `r`, with its `r12`, `r13`. -/
def BV (P : Params) (S0 S1 : BitVec 64 → Prop) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ t, c.threads[0]? = some t ∧ DoneM0 P S0 c.mem r (t.st.st.1.regs.get64 .r12) (t.st.st.1.regs.get64 .r13)) ∨
    (∃ t, c.threads[1]? = some t ∧ DoneM1 P S1 c.mem r (t.st.st.1.regs.get64 .r12) (t.st.st.1.regs.get64 .r13))

section HB

variable {P : Params} {S0 S1 : BitVec 64 → Prop} {post : MachineState × EStateX → Prop}

/-- **`hB` for thread `0`.** -/
theorem hB0 (hp : ∀ y, post y → Done0 P S0 y.2 (y.1.1.regs.get64 .r12) (y.1.1.regs.get64 .r13)) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel 0 plan0 σ c t r g cl → cl → BV P S0 S1 c r g := by
  rintro c t r g cl σ hpost hp' hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, (hp _ hpost).toM hpre⟩
  · rw [hp'] at hts; cases hts

/-- **`hB` for thread `1`.** -/
theorem hB1 (hp : ∀ y, post y → Done1 P S1 y.2 (y.1.1.regs.get64 .r12) (y.1.1.regs.get64 .r13)) :
    ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX), post (t.st.st, σ) → t.prom = [] →
      EnvRel 1 plan0 σ c t r g cl → cl → BV P S0 S1 c r g := by
  rintro c t r g cl σ hpost hp' hrel -
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr ⟨t, hrel.ht, (hp _ hpost).toM hpre⟩
  · rw [hp'] at hts; cases hts

end HB

/-! ## The final configuration -/

section Final

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- **Two threads covering `x`**: when the threads' fractions of `x` add up
to at least `1`, the total write set of `x` is theirs. -/
theorem X_two (E : Erase rF g T c) (hsize : c.threads.size = 2) {x : Loc}
    (hge : 1 ≤ ((rF 0).wr x).q + ((rF 1).wr x).q) {p : Val × Time} (hp : ((total rF g c).wr x).X p) :
    ((rF 0).wr x).X p ∨ ((rF 1).wr x).X p := by
  rcases X_total_cases hp with ⟨k, hk, hX⟩ | ⟨s, hs, hX⟩
  · rw [hsize] at hk
    rcases k with _ | _ | k
    · exact .inl hX
    · exact .inr hX
    · omega
  · exfalso
    have h1 := E.q_le_one x
    rw [q_total, hsize, q_threadsRes] at h1
    simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at h1
    have h2 := Res.Sub.q_le (slotsRes_sub hs) x
    have h3 : (s.res.wr x).q = 0 := by
      have := (s.res.wr x).nonneg; have := (g.slotsRes.wr x).nonneg; grind
    exact (s.res.wr x).zero h3 p hX

end Final

section Never

variable {P : Params} {S0 S1 : BitVec 64 → Prop} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop}
  {c : Config isa}

theorem fr_tok0 {r : Res} (h : Fr P 0 r) : 1 ≤ (r.wr P.tok0).q := by
  have := h.2; simpa using this

theorem fr_tok1 {r : Res} (h : Fr P 1 r) : 1 ≤ (r.wr P.tok1).q := by
  have := h.2; simp only [Nat.one_ne_zero, ↓reduceIte] at this; exact this.1

/-- **The core of the final argument**: thread `0` done on `rF i`, thread
`1` done on `rF j`, `i ≠ j`, with the ABA outcome's registers, is
contradictory. -/
theorem core (E : Erase rF g T c) (hf : c.final = true) (hsize : c.threads.size = 2) {i j : Nat}
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) (hA : P.a ≠ 0) (hB : P.b ≠ 0) (hAB : P.a ≠ P.b)
    (hS0 : ¬ S0 P.a) (hS1A : ¬ S1 P.a) (hS1B : ¬ S1 P.b) {a12 b12 : BitVec 64}
    (h0 : DoneM0 P S0 c.mem (rF i) a12 P.b) (h1 : DoneM1 P S1 c.mem (rF j) b12 P.b) (ha : a12 = P.a) : False := by
  obtain ⟨hfr0, hIV, v0, K0, tm0, tr0, W0, e12, hp0, hX0⟩ := h0
  obtain ⟨hfr1, -, T1, n1, W2, n2, K, hr1, hr2, hrest⟩ := h1
  have hv0 : lo v0 = P.a := by rw [← e12, ha]
  have hi' : i < c.threads.size := by rw [hsize]; exact hi
  have hj' : j < c.threads.size := by rw [hsize]; exact hj
  -- the threads' fractions of a location, as thread `0`'s and thread `1`'s
  have hsum : ∀ x, ((rF 0).wr x).q + ((rF 1).wr x).q = ((rF i).wr x).q + ((rF j).wr x).q := by
    intro x
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> first | omega | grind
  have hXij : ∀ {x p}, (((rF 0).wr x).X p ∨ ((rF 1).wr x).X p) → ((rF i).wr x).X p ∨ ((rF j).wr x).X p := by
    intro x p h
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> first | omega | exact h | exact h.symm
  -- `head`: both threads hold exactly half
  have hq := E.q_add_le_one hi' hj' hij P.hd
  have hqi : ((rF i).wr P.hd).q = 1 / 2 := by have := hfr0.1; have := hfr1.1; grind
  have hqj : ((rF j).wr P.hd).q = 1 / 2 := by have := hfr0.1; have := hfr1.1; grind
  have hposH : 0 < ((total rF g c).wr P.hd).q := by
    have := Res.Sub.q_le (sub_total_thread (rF := rF) (g := g) hi') P.hd; grind
  have attrH : ∀ t v, c.mem.read? P.hd t = some v → ((rF i).wr P.hd).X (v, t) ∨ ((rF j).wr P.hd).X (v, t) := by
    intro t v hv
    exact hXij (X_two E hsize (by rw [hsum]; grind) ((E.X_iff_of_final hf hposH (v, t)).mpr hv))
  -- the 8-byte locations: thread `1` holds them whole
  have attrN : ∀ x t v, x.bytes = 8 → c.mem.read? x t = some v →
      ((rF j).wr x).q = 1 ∧ ((rF j).wr x).X (v, t) := by
    intro x t v hx hv
    have hq1 := hfr1.nd_ge hx
    have hqx := E.q_add_le_one hi' hj' hij x
    have hn := ((rF i).wr x).nonneg
    have hqj1 : ((rF j).wr x).q = 1 := by grind
    have hqi0 : ((rF i).wr x).q = 0 := by grind
    have hpos : 0 < ((total rF g c).wr x).q := by
      have := Res.Sub.q_le (sub_total_thread (rF := rF) (g := g) hj') x; grind
    rcases hXij (X_two E hsize (by rw [hsum]; grind) ((E.X_iff_of_final hf hpos (v, t)).mpr hv)) with h | h
    · exact absurd h (((rF i).wr x).zero hqi0 _)
    · exact ⟨hqj1, h⟩
  refine aba_never hIV hA hB hAB hS0 hS1A hS1B hp0 hv0 hr1 hr2 ?_
  rcases hrest with ⟨h12, hH⟩ | ⟨h12, W3, n3, Tn, hr3, hH, hN⟩
  · refine .inl ⟨h12, fun t v hv => ?_⟩
    rcases attrH t v hv with h | h
    · exact (hX0 hqi _ h).imp_right .inl
    · exact (hH hqj _ h).imp_right .inr
  · refine .inr ⟨h12, W3, n3, Tn, hr3, fun t v hv => ?_, fun x t v hx hv => ?_⟩
    · rcases attrH t v hv with h | h
      · exact (hX0 hqi _ h).imp_right .inl
      · exact (hH hqj _ h).imp_right .inr
    · obtain ⟨hq1, h⟩ := attrN x t v hx hv
      exact hN x hx hq1 _ h

/-- **The ABA outcome is never final**: at a final configuration with two
threads, a clean erasure and both threads' `BV`, not
`0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B`. -/
theorem final_never (E : Erase rF g T c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hBV : ∀ tid, c.Done tid → BV P S0 S1 c (rF tid) g) (hA : P.a ≠ 0) (hB : P.b ≠ 0) (hAB : P.a ≠ P.b)
    (hS0 : ¬ S0 P.a) (hS1A : ¬ S1 P.a) (hS1B : ¬ S1 P.b) :
    ¬ ∃ t0 t1, c.threads[0]? = some t0 ∧ c.threads[1]? = some t1 ∧
      t0.st.st.1.regs.get64 .r12 = P.a ∧ t0.st.st.1.regs.get64 .r13 = P.b ∧
      t1.st.st.1.regs.get64 .r13 = P.b := by
  rintro ⟨t0, t1, ht0, ht1, h12, h13, h13'⟩
  have hi0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have hi1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have tok0 := fun {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (h : Fr P 0 (rF i)) (h' : Fr P 0 (rF j)) =>
    (show False by have := E.q_add_le_one hi hj hij P.tok0; have := fr_tok0 h; have := fr_tok0 h'; grind)
  have tok1 := fun {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (h : Fr P 1 (rF i)) (h' : Fr P 1 (rF j)) =>
    (show False by have := E.q_add_le_one hi hj hij P.tok1; have := fr_tok1 h; have := fr_tok1 h'; grind)
  rcases hBV 0 (Config.final_done hf hi0) with ⟨t, ht, hd0⟩ | ⟨t, ht, hd0⟩ <;>
    rcases hBV 1 (Config.final_done hf hi1) with ⟨t', ht', hd1⟩ | ⟨t', ht', hd1⟩
  · exact tok0 hi0 hi1 (by decide) hd0.1 hd1.1
  · rw [ht0] at ht; cases ht; rw [ht1] at ht'; cases ht'
    rw [h13] at hd0; rw [h13'] at hd1
    exact core E hf hsize (by decide) (by decide) (by decide) hA hB hAB hS0 hS1A hS1B hd0 hd1 h12
  · rw [ht1] at ht; cases ht; rw [ht0] at ht'; cases ht'
    rw [h13] at hd1; rw [h13'] at hd0
    exact core E hf hsize (by decide) (by decide) (by decide) hA hB hAB hS0 hS1A hS1B hd1 hd0 h12
  · exact tok1 hi0 hi1 (by decide) hd0.1 hd1.1

end Never

end Kraken.Promising.X64.EnvG.VecABA
