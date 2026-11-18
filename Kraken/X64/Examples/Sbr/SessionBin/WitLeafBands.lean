import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# The witness's `powf`/`log2f`: the floating-point facts

With `lg = fun _ => 1.0f` and `pw = fun _ _ => 1.0f` (the stand-ins of `WitEnvDefs`) the band
counts are `2 * lrint(h)` for `h = 7 - bs_freq_scale` (times `invwarp` in the second region),
every `make_bands` base is `1.0f`, so `chain` is constant and the borders are `k[0]`,
`k[1] ≤ 64`. The float facts are closed `decide`s: the float operations reduce in the kernel
through the core float model.
-/

namespace Kraken.Examples.Sbr.WitEnv
open Kraken.Examples.Sbr.Reset

/-- `1.0f * n = n` and `lrint n = n` for small `n`. -/
theorem f1_small : ∀ n, n < 65 →
    BitVec.f32mul f1 (BitVec.sitof32 (BitVec.ofNat 32 n)) = BitVec.sitof32 (BitVec.ofNat 32 n)
    ∧ (BitVec.f32toi64 (BitVec.sitof32 (BitVec.ofNat 32 n))).toInt = n := by
  decide

/-- The `NqOK` body for `lg = 1.0f`, on 64 consecutive values from `64 * k`. -/
abbrev NqRow (k : Nat) : Prop := ∀ n, n < 64 →
    (BitVec.f32toi64 (BitVec.f32mul f1 (BitVec.sitof32 (BitVec.ofNat 32 (64 * k + n))))).toInt
      < 2 ^ 32

/-- `NqOK` body for `lg = 1.0f`. -/
theorem nq_const (nb : Nat) (h : nb < 256) :
    (BitVec.f32toi64 (BitVec.f32mul f1 (BitVec.sitof32 (BitVec.ofNat 32 nb)))).toInt < 2 ^ 32 := by
  have r0 : NqRow 0 := by decide
  have r1 : NqRow 1 := by decide
  have r2 : NqRow 2 := by decide
  have r3 : NqRow 3 := by decide
  have e : nb = 64 * (nb / 64) + nb % 64 := (Nat.div_add_mod nb 64).symm
  have hm : nb % 64 < 64 := Nat.mod_lt _ (by omega)
  obtain h0 | h1 | h2 | h3 : nb / 64 = 0 ∨ nb / 64 = 1 ∨ nb / 64 = 2 ∨ nb / 64 = 3 := by omega
  · have := r0 _ hm; rwa [← h0, ← e] at this
  · have := r1 _ hm; rwa [← h1, ← e] at this
  · have := r2 _ hm; rwa [← h2, ← e] at this
  · have := r3 _ hm; rwa [← h3, ← e] at this

/-- A fixed point of `x ↦ b * x` is fixed by `chain`. -/
theorem chain_fix {b p : BitVec 32} (h : BitVec.f32mul b p = p) : ∀ j, chain b p j = p
  | 0 => rfl
  | j + 1 => by rw [chain, chain_fix h j, h]

/-- `BandsAt` for `pw = 1.0f` and a start border `≤ 64`. -/
theorem bandsAt_const {start : Nat} (h : start ≤ 64) (stop nb : Nat) :
    BandsAt (fun _ _ => f1) start stop nb := by
  intro j _ _
  have := f1_small start (by omega)
  simp only [chain_fix this.1, this.2]
  omega

/-- The band counts for `lg = 1.0f`. -/
theorem nb_const (fs : Nat) (h1 : 1 ≤ fs) (h3 : fs ≤ 3) (alter : Nat) (ha : alter ≤ 1) (a b : Nat) :
    nbOf (fun _ => f1) a b (BitVec.sitof32 (BitVec.ofNat 32 (7 - fs))) = 2 * (7 - fs : Nat)
    ∧ 2 * 3 ≤ nbOf (fun _ => f1) a b
        (BitVec.f32mul (BitVec.sitof32 (BitVec.ofNat 32 (7 - fs))) (invwarp alter))
    ∧ nbOf (fun _ => f1) a b
        (BitVec.f32mul (BitVec.sitof32 (BitVec.ofNat 32 (7 - fs))) (invwarp alter)) ≤ 12 := by
  simp only [nbOf]
  obtain rfl | rfl | rfl : fs = 1 ∨ fs = 2 ∨ fs = 3 := by omega
  all_goals obtain rfl | rfl : alter = 0 ∨ alter = 1 := by omega
  all_goals decide

/-- The floating-point hypothesis holds for the constant stand-ins. -/
theorem bandsOK_const : BandsOK (fun _ => f1) (fun _ _ => f1) := by
  refine ⟨?_, fun _ _ _ _ nb hnb => nq_const nb hnb⟩
  intro sr _ start _ k2 hk2 fs h1 h3 alter ha
  split
  · trivial
  · intro k0 hk0 _
    have hn := nb_const fs h1 h3 alter ha
    refine ⟨fun _ => ⟨?_, bandsAt_const ?_ _ _⟩, fun hlt => ⟨?_, ?_, bandsAt_const ?_ _ _⟩⟩
    · rw [(hn _ _).1]; omega
    · omega
    · exact Int.le_trans (by decide) (hn _ _).2.1
    · exact Int.le_trans (hn _ _).2.2 (by decide)
    · split <;> omega

end Kraken.Examples.Sbr.WitEnv
