/-
**`treiber_aba_tagged.kl`, part 6: the final
combinatorics** over a memory `m`. ISA-neutral.

`aba_never`: thread `0`'s pop record (`PopR`, node `A`, value `B`), thread
`1`'s records (`R1`, `R2` with `r13 = B`, and `R3` if it pushed) and the
attribution of `m`'s messages (every message of `head` is the initial one,
thread `0`'s write `W0`, or one of thread `1`'s `H1` writes; every message of
an 8-byte location is thread `1`'s node store, above the node bounds `K`,
at or below `Tn`) are contradictory. The ABA outcome
`0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B` cannot be final.

The argument: every `cmpxchg16b` read `tr` is the last message of `head`
below its write `W` (no message of `head` lies in `(tr, W)`: `AtomicT` and the
attribution, `gap`), the thread-`1` writes are ordered `T1 ≤ tr2 < W2 ≤ tr3 <
W3`, and the case of `W0`'s position decides every read:

- `r12 = 0`: the first pop's `head` read at `T1` (null) is the initial
  `head` (`A`), `W0` (`B`) or `W2 > T1`;
- `W0 < T1`: thread `1` popped `B` (node `0`) and then read `0`, not `B`;
- `T1 < W0 < W2`: thread `0` read `T1`, whose node is `A.next = B`, not `A`;
- `W2 < W0 < W3`: thread `0` read `W2`, whose node is `B.next = 0`, not `A`;
- `W3 < W0`: thread `0` read the push `W3 = {A, 3}` (the tags make `W3` the
  only message with that value, so its `head` load read `W3` too), and its
  node load then saw thread `1`'s store `A.next := 0` (`Tn < W3`), not `B`.
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABARec

namespace Kraken.Promising.X64.EnvG.VecABA

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get?)

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## Values -/

theorem hi_app (a b : BitVec 64) : hi (a ++ b) = a := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [show ¬ (64 + i < 64) by omega, BitVec.getLsbD_eq_getElem hi]

theorem lo_app (a b : BitVec 64) : lo (a ++ b) = b := by
  ext i hi
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
  simp [BitVec.getLsbD_eq_getElem hi]
  omega

theorem hi_sw (a : BitVec 64) : hi (BitVec.setWidth 128 a) = 0 := by
  ext i hi
  simp

theorem lo_sw (a : BitVec 64) : lo (BitVec.setWidth 128 a) = a := by
  ext i hi
  simp [BitVec.getLsbD_eq_getElem hi]
  omega

theorem sw_sw (a : BitVec 64) : BitVec.setWidth 64 (BitVec.setWidth 128 a) = a := by
  ext i hi; simp

/-! ## Reads -/

section Reads

variable {m : Memory}

theorem rd_val {l : Loc} {t : Time} {v v' : Val} (h : m.read? l t = some v) (h' : m.read? l t = some v') :
    v = v' := by
  rw [h] at h'; exact Option.some.inj h'

theorem rd0 {l : Loc} {v : Val} (h : m.read? l 0 = some v) : v = m.initVal l := by
  simp [Memory.read?] at h; exact h.symm

theorem get?_ne0 {t : Time} {wm : Msg} (h : m.get? t = some wm) : t ≠ 0 := by
  rintro rfl; rw [m.get?_zero] at h; cases h

/-- A node load that reads below every node store gave the initial value. -/
theorem nodeRd_init {S : BitVec 64 → Prop} {K tm : Time} {p x : BitVec 64} (hS : ¬ S p)
    (hn : NodeRd S m K p tm x) (hatt : ∀ t v, m.read? (nd p) t = some v → t = 0 ∨ K < t) :
    x = BitVec.setWidth 64 (m.initVal (nd p)) := by
  rcases hn with h | ⟨tl, u, hrd, rfl, hle, -⟩
  · exact absurd h hS
  · rcases hatt tl u hrd with rfl | h
    · rw [rd0 hrd]
    · omega_t

end Reads

/-! ## The contradiction -/


section Never

variable {P : Params} {m : Memory} {S0 S1 : BitVec 64 → Prop}

/-- **The ABA outcome is impossible.** -/
theorem aba_never (hIV : IV P m) (hA : P.a ≠ 0) (hB : P.b ≠ 0) (hAB : P.a ≠ P.b)
    (hS0 : ¬ S0 P.a) (hS1A : ¬ S1 P.a) (hS1B : ¬ S1 P.b)
    {v0 : Val} {K0 tm0 tr0 W0 : Time} (hp0 : PopR P S0 0 m K0 v0 P.b tm0 tr0 W0) (hv0 : lo v0 = P.a)
    {T1 W2 : Time} {n1 n2 : Val} {K : Loc → Time} {r12 : BitVec 64}
    (hr1 : R1 P S1 m K r12 T1 n1) (hr2 : R2 P S1 m K P.b T1 W2 n2)
    (h1 : (r12 = 0 ∧ ∀ t v, m.read? P.hd t = some v →
        t = 0 ∨ (v, t) = ((hi v0 + 1) ++ P.b, W0) ∨ H1 r12 T1 n1 W2 n2 0 0 (v, t)) ∨
      (r12 ≠ 0 ∧ ∃ W3 n3 Tn, R3 P S1 m r12 W2 W3 n3 Tn ∧
        (∀ t v, m.read? P.hd t = some v →
          t = 0 ∨ (v, t) = ((hi v0 + 1) ++ P.b, W0) ∨ H1 r12 T1 n1 W2 n2 W3 n3 (v, t)) ∧
        (∀ x t v, x.bytes = 8 → m.read? x t = some v → t = 0 ∨ (K x < t ∧ x = nd r12 ∧ t ≤ Tn)))) :
    False := by
  obtain ⟨hIh, hIa, hIb⟩ := hIV
  have hW0r : m.read? P.hd W0 = some ((hi v0 + 1) ++ P.b) := read?_of_get? hp0.wr
  have hW0z : W0 ≠ 0 := get?_ne0 hp0.wr
  -- the second pop of thread `1` popped `B`
  rcases hr2 with ⟨hb0, -⟩ | ⟨-, v2, tm2, tr2, x2, ev2, en2, hp2, hT1⟩
  · exact hB hb0
  have hW2r : m.read? P.hd W2 = some ((hi v2 + 1) ++ x2) := read?_of_get? hp2.wr
  rcases h1 with ⟨h12, hH⟩ | ⟨h12, W3, n3, Tn, hr3, hH, hN⟩
  · -- `r12 = 0`: the first pop read a null `head` at `T1`
    rcases hr1 with ⟨-, v, hv, hl⟩ | ⟨hne, -⟩
    · rcases read?_msg hv with h0 | ⟨wm, hg, hloc⟩
      · subst h0
        rw [rd0 hv, hIh, lo_sw] at hl
        exact hA hl
      · rcases hH T1 v hv with h0 | h0 | (⟨hne, -⟩ | h0 | h0)
        · exact get?_ne0 hg h0
        · simp only [Prod.mk.injEq] at h0
          rw [h0.1, lo_app] at hl
          exact hB hl
        · exact hne h12
        · simp only [Prod.mk.injEq] at h0
          have := hp2.lt
          omega_t
        · simp only [Prod.mk.injEq] at h0
          exact get?_ne0 hg h0.2
    · exact hne h12
  -- `r12 ≠ 0`: the first pop and the push
  rcases hr1 with ⟨h0, -⟩ | ⟨-, v1, tm1, tr1, x1, e12, en1, hp1⟩
  · exact h12 h0
  obtain ⟨v3, tr3, en3, hrd3, hlt3, hg3, hat3, hW2, hn3⟩ := hr3
  have hT1r : m.read? P.hd T1 = some ((hi v1 + 1) ++ x1) := read?_of_get? hp1.wr
  have hW3r : m.read? P.hd W3 = some n3 := read?_of_get? hg3
  have hT1z : T1 ≠ 0 := get?_ne0 hp1.wr
  -- the messages of `head`
  have cls : ∀ t v, m.read? P.hd t = some v → t = 0 ∨ t = W0 ∨ t = T1 ∨ t = W2 ∨ t = W3 := by
    intro t v hv
    rcases hH t v hv with h | h | (⟨-, h⟩ | h | h) <;> (try simp only [Prod.mk.injEq] at h) <;> omega_t
  -- thread `0`'s write is not thread `1`'s
  have tid_ne : ∀ {t : Time} {v : Val}, m.get? t = some ⟨P.hd, v, 1⟩ → W0 ≠ t := by
    intro t v hg he
    subst he
    rw [hp0.wr] at hg
    cases hg
  have hne1 := tid_ne hp1.wr
  have hne2 := tid_ne hp2.wr
  have hne3 := tid_ne hg3
  -- no message of `head` strictly inside a `cmpxchg16b` window but its own thread's
  have g0 : ∀ {t : Time} {v : Val}, m.get? t = some ⟨P.hd, v, 1⟩ → ¬ (tr0 < t ∧ t < W0) := by
    intro t v hg ⟨h1, h2⟩
    have := hp0.atm t _ h1 h2 hg rfl
    cases this
  have g01 := g0 hp1.wr
  have g02 := g0 hp2.wr
  have g03 := g0 hg3
  have g1 : ¬ (tr1 < W0 ∧ W0 < T1) := fun ⟨h1, h2⟩ => by have := hp1.atm W0 _ h1 h2 hp0.wr rfl; cases this
  have g2 : ¬ (tr2 < W0 ∧ W0 < W2) := fun ⟨h1, h2⟩ => by have := hp2.atm W0 _ h1 h2 hp0.wr rfl; cases this
  have g3 : ¬ (tr3 < W0 ∧ W0 < W3) := fun ⟨h1, h2⟩ => by have := hat3 W0 _ h1 h2 hp0.wr rfl; cases this
  have c0 := cls _ _ hp0.rd
  have c1 := cls _ _ hp1.rd
  have c2 := cls _ _ hp2.rd
  have c3 := cls _ _ hrd3
  have hl0 := hp0.lt
  have hl1 := hp1.lt
  have hl2 := hp2.lt
  -- the node loads that read below every node store
  have hatt : ∀ p : BitVec 64, ∀ t v, m.read? (nd p) t = some v → t = 0 ∨ K (nd p) < t := fun p t v hv =>
    (hN (nd p) t v rfl hv).imp_right fun h => h.1
  have hnd : ∀ {v : Val} {tm tr W : Time} {x : BitVec 64}, PopR P S1 1 m (K (nd (lo v))) v x tm tr W →
      ¬ S1 (lo v) → x = BitVec.setWidth 64 (m.initVal (nd (lo v))) :=
    fun hp hS => nodeRd_init hS hp.node (hatt _)
  -- the case of `W0`'s position
  rcases (show W0 < T1 ∨ (T1 < W0 ∧ W0 < W2) ∨ (W2 < W0 ∧ W0 < W3) ∨ W3 < W0 by omega_t) with
    ha | ⟨hb1, hb2⟩ | ⟨hc1, hc2⟩ | hd
  · -- thread `1` popped `B` (node `0`) and then read `0`
    have e1 : tr1 = W0 := by omega_t
    have e2 : tr2 = T1 := by omega_t
    have hv1 := rd_val (e1 ▸ hp1.rd) hW0r
    have hv2 := rd_val (e2 ▸ hp2.rd) hT1r
    have hlo1 : lo v1 = P.b := by rw [hv1, lo_app]
    have hx1 := hnd hp1 (by rw [hlo1]; exact hS1B)
    rw [hlo1, hIb] at hx1
    rw [hv2, lo_app, hx1] at ev2
    exact hB (by rw [ev2]; rfl)
  · -- thread `0` read `T1`, whose node is `A.next = B`
    have e0 : tr0 = T1 := by omega_t
    have e1 : tr1 = 0 := by omega_t
    have hv0' := rd_val (e0 ▸ hp0.rd) hT1r
    have hv1 := rd0 (e1 ▸ hp1.rd)
    rw [hIh] at hv1
    have hlo1 : lo v1 = P.a := by rw [hv1, lo_sw]
    have hx1 := hnd hp1 (by rw [hlo1]; exact hS1A)
    rw [hlo1, hIa, sw_sw] at hx1
    rw [hv0', lo_app, hx1] at hv0
    exact hAB hv0.symm
  · -- thread `0` read `W2`, whose node is `B.next = 0`
    have e0 : tr0 = W2 := by omega_t
    have hv0' := rd_val (e0 ▸ hp0.rd) hW2r
    have hx2 := hnd hp2 (by rw [← ev2]; exact hS1B)
    rw [← ev2, hIb] at hx2
    rw [hv0', lo_app, hx2] at hv0
    exact hA (by rw [← hv0]; rfl)
  · -- thread `0` read the push `W3 = {A, 3}`, then the node store `A.next := 0`
    have e0 : tr0 = W3 := by omega_t
    have e3 : tr3 = W2 := by omega_t
    have e2 : tr2 = T1 := by omega_t
    have e1 : tr1 = 0 := by omega_t
    have hv0' := rd_val (e0 ▸ hp0.rd) hW3r
    have hv3 := rd_val (e3 ▸ hrd3) hW2r
    have hv2 := rd_val (e2 ▸ hp2.rd) hT1r
    have hv1 := rd0 (e1 ▸ hp1.rd)
    rw [hIh] at hv1
    have hx2 := hnd hp2 (by rw [← ev2]; exact hS1B)
    rw [← ev2, hIb] at hx2
    -- the tags
    have hh1 : hi v1 = 0 := by rw [hv1, hi_sw]
    have hh2 : hi v2 = 0 + 1 := by rw [hv2, hi_app, hh1]
    have hh3 : hi v3 = 0 + 1 + 1 := by rw [hv3, hi_app, hh2]
    have hh0 : hi v0 = 0 + 1 + 1 + 1 := by rw [hv0', en3, hi_app, hh3]
    have hr12 : r12 = P.a := by rw [← hv0, hv0', en3, lo_app]
    have hlo3 : lo v3 = 0 := by rw [hv3, lo_app, hx2]; rfl
    -- thread `0`'s `head` load read `W3` too
    have htm : tm0 = W3 := by
      have hm := hp0.tmr
      rcases cls _ _ hp0.rdm with h | h | h | h | h
      · subst h
        have := rd0 hp0.rdm
        rw [hIh] at this
        rw [this, hi_sw] at hh0
        exact absurd hh0 (by decide)
      · omega_t
      · subst h
        have := rd_val hp0.rdm hT1r
        rw [this, hi_app, hh1] at hh0
        exact absurd hh0 (by decide)
      · subst h
        have := rd_val hp0.rdm hW2r
        rw [this, hi_app, hh2] at hh0
        exact absurd hh0 (by decide)
      · exact h
    -- the node store before the push
    rcases hn3 with hS | ⟨hgn, hTn⟩
    · rw [hr12] at hS; exact hS1A hS
    rcases hp0.node with hS | ⟨tl0, u0, hrd0, hx0, -, hnw⟩
    · rw [hv0] at hS; exact hS0 hS
    rw [hv0] at hrd0 hnw
    rw [hr12] at hgn
    have hTnz : Tn ≠ 0 := get?_ne0 hgn
    have hle : Tn ≤ tl0 := Nat.le_of_not_lt fun hlt => hnw Tn _ hlt (by rw [htm] at *; omega_t) hgn rfl
    rcases hN _ tl0 u0 rfl hrd0 with h0 | ⟨-, -, hle'⟩
    · omega_t
    have e : tl0 = Tn := by omega_t
    subst e
    have hu := rd_val hrd0 (read?_of_get? hgn)
    rw [hu, hlo3] at hx0
    exact hB (by rw [hx0]; rfl)

end Never

end Kraken.Promising.X64.EnvG.VecABA
