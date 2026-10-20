import WeakCore.TermSys
/-!
# TermKidLabel — the kids' labels after the M0 barrier spawn (M0)

After `spawnS` (M0: `lbase := cs.lbase + cs.n * th.nalloc`, kid stripe `L := kids.length`), kid `q`'s
label `j` is `freshLabel (b + N*na) L q j`.  With `m := q + L*j` it equals
`freshLabel b N (m % N) (na + m / N)`: thread `0`'s label at an index `≥ na` when `m % N = 0`, else a
label of the unborn stripe `m % N ∈ (0, N)`.
-/
namespace TermSys
open CoreLang CoreTerm TermRun TermMem TermCut
open WeakMem (AllocLabel)

/-- The kid label in the old striping: stripe `m % N`, index `na + m / N` (`m := q + L*j`). -/
theorem kidLabel_eq (b N na L q j : Nat) :
    freshLabel (b + N * na) L q j = freshLabel b N ((q + L * j) % N) (na + (q + L * j) / N) := by
  show b + N * na + q + L * j = b + (q + L * j) % N + N * (na + (q + L * j) / N)
  have h := Nat.mod_add_div (q + L * j) N
  generalize (q + L * j) % N = r at h ⊢
  generalize (q + L * j) / N = s at h ⊢
  rw [Nat.mul_add]
  omega

/-- **Kid label cases**: a thread-`0` label at index `≥ na`, or an unborn-stripe label. -/
theorem kidLabel_cases (b N na L q j : Nat) (hN : 0 < N) :
    (∃ s, freshLabel (b + N * na) L q j = freshLabel b N 0 (na + s)) ∨
      (∃ r s, 0 < r ∧ r < N ∧ freshLabel (b + N * na) L q j = freshLabel b N r s) := by
  rw [kidLabel_eq]
  cases h : (q + L * j) % N with
  | zero => exact Or.inl ⟨_, rfl⟩
  | succ r =>
    refine Or.inr ⟨r + 1, _, Nat.succ_pos r, ?_, rfl⟩
    rw [← h]; exact Nat.mod_lt _ hN

/-- **Generic kid-label transfer**: any label property holding on thread `0`'s labels from `na` on
and on every unborn stripe holds on every kid label. -/
theorem kidLabel_of {P : AllocLabel → Prop} {b N na : Nat} (hN : 0 < N)
    (h0 : ∀ k, na ≤ k → P (freshLabel b N 0 k))
    (hU : ∀ r s, 0 < r → r < N → P (freshLabel b N r s)) (L q j : Nat) :
    P (freshLabel (b + N * na) L q j) := by
  rcases kidLabel_cases b N na L q j hN with ⟨s, e⟩ | ⟨r, s, h1, h2, e⟩
  · rw [e]; exact h0 _ (Nat.le_add_right _ _)
  · rw [e]; exact hU r s h1 h2

/-- **Kid freshness**: every kid label is globally fresh (thread `0`'s `fresh` + the unborn stripes). -/
theorem kidFresh {Eg : GEnv} {cs : Cfg} {th : TTh} (hpos : 0 < cs.n) (_hnp : th.promises = [])
    (h0 : ∀ k, th.nalloc ≤ k → GFreshL Eg cs th (freshLabel cs.lbase cs.n 0 k))
    (hU : ∀ r s, 0 < r → r < cs.n → Eg.sto (freshLabel cs.lbase cs.n r s) = none ∧
      Eg.box (freshLabel cs.lbase cs.n r s) = none ∧ Eg.ini (freshLabel cs.lbase cs.n r s) = 0 ∧
      Eg.pfr (freshLabel cs.lbase cs.n r s) = none ∧
      ∀ (t : Nat) (m : WeakMem.Msg), cs.mem[t]? = some m → m.loc.label ≠ freshLabel cs.lbase cs.n r s)
    (L q j : Nat) :
    GFreshL Eg cs th (freshLabel (cs.lbase + cs.n * th.nalloc) L q j) :=
  kidLabel_of (P := GFreshL Eg cs th) hpos h0
    (fun r s h1 h2 =>
      have ⟨a1, a2, a3, a4, a5⟩ := hU r s h1 h2
      ⟨a1, a2, a3, a4, fun t m hm hl => absurd hl (a5 t m hm)⟩) L q j

end TermSys

#print axioms TermSys.kidLabel_eq
#print axioms TermSys.kidLabel_cases
#print axioms TermSys.kidLabel_of
#print axioms TermSys.kidFresh
