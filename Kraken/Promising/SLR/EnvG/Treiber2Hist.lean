/-
Part 2: **the history layer of the two-thread
Treiber stack**, pure.

At the final clean erasure (`EnvG/Treiber2Final.lean`) the messages of `top`
are exactly the initial one (`0`), the two pushes `A.p`, `B.p` and the pops
`A.q`, `B.q` of the threads that popped (`T`). Each side `X` (a thread)
contributes what its program and the push form of `top`'s release predicate
(`PushF`) give:

- its push message has the node's value `X.n`, and the message it overwrote
  (adjacent below it) has the value `X.y` its link word holds;
- if it popped (`PopOK`): its `ldar` read `X.tr0 ≥ X.p` and its `casal` read
  `X.tr ≥ X.tr0` with the same value `X.v ≠ 0`; the `casal`'s write `X.q` is
  adjacent above `X.tr` with the value `X.x4` its `ldr` read, which is the
  link `Y.y` when `X.v` is node `Y.n` pushed at or before `X.tr0`;
- if it did not (`cbz`), its `ldar` read a `0` at or after its push.

`hist_ok` (the **law**): both threads popped, and they popped the two
distinct nodes. The proof is the case analysis of the first pusher's
successor in `top`'s order (`hist_core`).

Contents: `Side`, `T`, `PopOK`, `SideOK`, `HistOK` (+ `swap`), `hist_core`,
`hist_ok`.

No imports: the layer is pure, and `EnvG/X64Treiber2Hist.lean`
aliases it.
-/

namespace Kraken.Promising.SLR.EnvG.Treiber2

/-- One thread's history data: push time, node and link value; whether it
popped, and the pop's write, reads, value and written value. -/
structure Side where
  p : Nat
  n : BitVec 64
  y : BitVec 64
  popped : Prop
  q : Nat
  tr0 : Nat
  tr : Nat
  v : BitVec 64
  x4 : BitVec 64

/-- The timestamps of `top`'s messages. -/
def T (A B : Side) (u : Nat) : Prop :=
  u = 0 ∨ u = A.p ∨ u = B.p ∨ (A.popped ∧ u = A.q) ∨ (B.popped ∧ u = B.q)

theorem T.swap {A B : Side} {u : Nat} (h : T A B u) : T B A u := by
  unfold T at *; rcases h with h | h | h | h | h <;> simp [h]

/-- A successful pop of side `X`. -/
structure PopOK (val : Nat → BitVec 64) (A B X : Side) : Prop where
  le0 : X.p ≤ X.tr0
  le1 : X.tr0 ≤ X.tr
  lt : X.tr < X.q
  t0 : T A B X.tr0
  t1 : T A B X.tr
  v0 : val X.tr0 = X.v
  v1 : val X.tr = X.v
  nz : X.v ≠ 0
  adj : ∀ u, T A B u → X.tr < u → u < X.q → False
  vq : val X.q = X.x4
  nodeA : X.v = A.n → A.p ≤ X.tr0 → X.x4 = A.y
  nodeB : X.v = B.n → B.p ≤ X.tr0 → X.x4 = B.y

/-- Side `X`'s facts. -/
structure SideOK (val : Nat → BitVec 64) (A B X : Side) : Prop where
  ppos : 0 < X.p
  pval : val X.p = X.n
  push : ∃ s, s < X.p ∧ T A B s ∧ val s = X.y ∧ ∀ u, T A B u → s < u → u < X.p → False
  pop : X.popped → PopOK val A B X
  cbz : ¬ X.popped → ∃ r, T A B r ∧ X.p ≤ r ∧ val r = 0

/-- **The final history of `top`.** -/
structure HistOK (val : Nat → BitVec 64) (A B : Side) : Prop where
  val0 : val 0 = 0
  nne : A.n ≠ B.n
  anz : A.n ≠ 0
  bnz : B.n ≠ 0
  pne : A.p ≠ B.p
  qne : A.popped → B.popped → A.q ≠ B.q
  qa : A.popped → A.q ≠ B.p
  qb : B.popped → B.q ≠ A.p
  sa : SideOK val A B A
  sb : SideOK val A B B

theorem PopOK.swap {val : Nat → BitVec 64} {A B X : Side} (h : PopOK val A B X) : PopOK val B A X :=
  ⟨h.le0, h.le1, h.lt, h.t0.swap, h.t1.swap, h.v0, h.v1, h.nz, fun u hu => h.adj u hu.swap, h.vq, h.nodeB,
    h.nodeA⟩

theorem SideOK.swap {val : Nat → BitVec 64} {A B X : Side} (h : SideOK val A B X) : SideOK val B A X := by
  obtain ⟨s, h1, h2, h3, h4⟩ := h.push
  refine ⟨h.ppos, h.pval, ⟨s, h1, h2.swap, h3, fun u hu => h4 u hu.swap⟩, fun hp => (h.pop hp).swap,
    fun hp => ?_⟩
  obtain ⟨r, h1, h2, h3⟩ := h.cbz hp
  exact ⟨r, h1.swap, h2, h3⟩

theorem HistOK.swap {val : Nat → BitVec 64} {A B : Side} (h : HistOK val A B) : HistOK val B A :=
  ⟨h.val0, Ne.symm h.nne, h.bnz, h.anz, Ne.symm h.pne, fun hb ha => Ne.symm (h.qne ha hb), h.qb, h.qa,
    h.sb.swap, h.sa.swap⟩

section Core

variable {val : Nat → BitVec 64} {A B : Side}

/-- A pop write is above its push. -/
theorem PopOK.p_lt_q {X : Side} (h : PopOK val A B X) : X.p < X.q := by
  have := h.le0; have := h.le1; have := h.lt; omega

/-- **The law, first pusher `A`.** -/
theorem hist_core (H : HistOK val A B) (hlt : A.p < B.p) :
    A.popped ∧ B.popped ∧ ((A.v = A.n ∧ B.v = B.n) ∨ (A.v = B.n ∧ B.v = A.n)) := by
  have hA := H.sa; have hB := H.sb
  have hpa := hA.ppos
  have hqA : A.popped → A.p < A.q := fun hp => (hA.pop hp).p_lt_q
  have hqB : B.popped → B.p < B.q := fun hp => (hB.pop hp).p_lt_q
  -- the message the second push `B.p` overwrote
  obtain ⟨sb, hsb, hTsb, hvsb, hadjb⟩ := hB.push
  rcases hTsb with h | h | h | ⟨hpA, h⟩ | ⟨hpB, h⟩
  · -- `0`: but `A.p` lies between
    exact (hadjb A.p (Or.inr (Or.inl rfl)) (by omega) hlt).elim
  · -- **case A**: `B` pushed right after `A`; `B.y = A.n`
    have hyb : B.y = A.n := by rw [← hvsb, h, hA.pval]
    have hgtA : A.popped → B.p < A.q := fun hp => by
      have h1 := hqA hp; have h2 := H.qa hp
      rcases Nat.lt_or_ge A.q B.p with h3 | h3
      · exact (hadjb A.q (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, rfl⟩)))) (by omega) h3).elim
      · omega
    -- a pop that read `B.p`: value `B.n`, writes `A.n`
    have first : ∀ X, PopOK val A B X → X.tr = B.p → X.v = B.n ∧ X.x4 = A.n := by
      intro X hX htr
      have hv : X.v = B.n := by rw [← hX.v1, htr, hB.pval]
      refine ⟨hv, ?_⟩
      have h0 : X.tr0 = B.p := by
        have := hX.le0; have := hX.le1
        rcases hX.t0 with h1 | h1 | h1 | ⟨hp, h1⟩ | ⟨hp, h1⟩
        · exfalso
          have h2 := hX.v0; rw [h1, H.val0] at h2
          exact hX.nz h2.symm
        · exfalso
          have h2 := hX.v0; rw [h1, hA.pval, hv] at h2
          exact H.nne h2
        · exact h1
        · have := hgtA hp; omega
        · have := hqB hp; omega
      rw [← hyb]; exact hX.nodeB hv (by omega)
    -- a pop's read: `B.p`, or the other's pop write
    have hclassA : ∀ hp : A.popped, A.tr = B.p ∨ (B.popped ∧ A.tr = B.q) := by
      intro hp
      have hX := hA.pop hp
      have := hX.le0; have := hX.le1; have := hX.lt
      rcases hX.t1 with h1 | h1 | h1 | ⟨_, h1⟩ | ⟨hpB, h1⟩
      · omega
      · exact (hX.adj B.p (Or.inr (Or.inr (Or.inl rfl))) (by omega) (hgtA hp)).elim
      · exact .inl h1
      · omega
      · exact .inr ⟨hpB, h1⟩
    have hclassB : ∀ hp : B.popped, B.tr = B.p ∨ (A.popped ∧ B.tr = A.q) := by
      intro hp
      have hX := hB.pop hp
      have := hX.le0; have := hX.le1; have := hX.lt
      rcases hX.t1 with h1 | h1 | h1 | ⟨hpA, h1⟩ | ⟨_, h1⟩
      · omega
      · omega
      · exact .inl h1
      · exact .inr ⟨hpA, h1⟩
      · omega
    by_cases hpA : A.popped <;> by_cases hpB : B.popped
    · refine ⟨hpA, hpB, ?_⟩
      have hXA := hA.pop hpA; have hXB := hB.pop hpB
      rcases hclassA hpA with h1 | ⟨-, h1⟩ <;> rcases hclassB hpB with h2 | ⟨-, h2⟩
      · -- both read `B.p`: one pop write lies between the other's read and write
        exfalso
        have := hXA.lt; have := hXB.lt; have := H.qne hpA hpB
        rcases Nat.lt_or_ge A.q B.q with h3 | h3
        · exact hXB.adj A.q (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpA, rfl⟩)))) (by omega) h3
        · exact hXA.adj B.q (Or.inr (Or.inr (Or.inr (Or.inr ⟨hpB, rfl⟩)))) (by omega) (by omega)
      · -- `A` first, `B` read `A`'s pop write
        obtain ⟨hv, hx⟩ := first A hXA h1
        have hvB : B.v = A.n := by rw [← hXB.v1, h2, hXA.vq, hx]
        exact .inr ⟨hv, hvB⟩
      · obtain ⟨hv, hx⟩ := first B hXB h2
        have hvA : A.v = A.n := by rw [← hXA.v1, h1, hXB.vq, hx]
        exact .inl ⟨hvA, hv⟩
      · exfalso; have := hXA.lt; have := hXB.lt; omega
    · -- only `A` popped: `B` read a `0` at or after its push
      exfalso
      have hXA := hA.pop hpA
      obtain ⟨r, hTr, hr, hv⟩ := hB.cbz hpB
      rcases hclassA hpA with h1 | ⟨h1, -⟩
      · obtain ⟨-, hx⟩ := first A hXA h1
        rcases hTr with h2 | h2 | h2 | ⟨_, h2⟩ | ⟨h3, -⟩
        · omega
        · omega
        · rw [h2, hB.pval] at hv; exact H.bnz hv
        · rw [h2, hXA.vq, hx] at hv; exact H.anz hv
        · exact hpB h3
      · exact hpB h1
    · -- only `B` popped
      exfalso
      have hXB := hB.pop hpB
      obtain ⟨r, hTr, hr, hv⟩ := hA.cbz hpA
      rcases hclassB hpB with h1 | ⟨h1, -⟩
      · obtain ⟨-, hx⟩ := first B hXB h1
        rcases hTr with h2 | h2 | h2 | ⟨h3, -⟩ | ⟨_, h2⟩
        · omega
        · rw [h2, hA.pval] at hv; exact H.anz hv
        · rw [h2, hB.pval] at hv; exact H.bnz hv
        · exact hpA h3
        · rw [h2, hXB.vq, hx] at hv; exact H.anz hv
      · exact hpA h1
    · -- neither popped
      exfalso
      obtain ⟨r, hTr, hr, hv⟩ := hA.cbz hpA
      rcases hTr with h2 | h2 | h2 | ⟨h3, -⟩ | ⟨h3, -⟩
      · omega
      · rw [h2, hA.pval] at hv; exact H.anz hv
      · rw [h2, hB.pval] at hv; exact H.bnz hv
      · exact hpA h3
      · exact hpB h3
  · omega
  · -- **case B**: `A` popped its own node before `B` pushed
    have hXA := hA.pop hpA
    have hgap : ∀ u, T A B u → A.q < u → u < B.p → False := fun u hu h1 h2 => hadjb u hu (by omega) h2
    have htrA : A.tr = A.p := by
      have := hXA.le0; have := hXA.le1; have := hXA.lt
      rcases hXA.t1 with h1 | h1 | h1 | ⟨_, h1⟩ | ⟨hpB, h1⟩
      · omega
      · exact h1
      · omega
      · omega
      · have := hqB hpB; omega
    have hvA : A.v = A.n := by rw [← hXA.v1, htrA, hA.pval]
    refine ⟨hpA, ?_⟩
    by_cases hpB : B.popped
    · have hXB := hB.pop hpB
      have htrB : B.tr = B.p := by
        have := hXB.le0; have := hXB.le1; have := hXB.lt
        rcases hXB.t1 with h1 | h1 | h1 | ⟨_, h1⟩ | ⟨_, h1⟩
        · omega
        · omega
        · exact h1
        · omega
        · omega
      exact ⟨hpB, .inl ⟨hvA, by rw [← hXB.v1, htrB, hB.pval]⟩⟩
    · exfalso
      obtain ⟨r, hTr, hr, hv⟩ := hB.cbz hpB
      rcases hTr with h2 | h2 | h2 | ⟨_, h2⟩ | ⟨h3, -⟩
      · omega
      · omega
      · rw [h2, hB.pval] at hv; exact H.bnz hv
      · omega
      · exact hpB h3
  · have := hqB hpB; omega

end Core

/-- **The law of the two-thread Treiber stack**: both threads popped, and
they popped the two distinct nodes. -/
theorem hist_ok {val : Nat → BitVec 64} {A B : Side} (H : HistOK val A B) :
    A.popped ∧ B.popped ∧ ((A.v = A.n ∧ B.v = B.n) ∨ (A.v = B.n ∧ B.v = A.n)) := by
  rcases Nat.lt_or_ge A.p B.p with h | h
  · exact hist_core H h
  · have h' : B.p < A.p := by have := H.pne; omega
    obtain ⟨h1, h2, h3⟩ := hist_core H.swap h'
    refine ⟨h2, h1, ?_⟩
    rcases h3 with ⟨h4, h5⟩ | ⟨h4, h5⟩
    · exact .inl ⟨h5, h4⟩
    · exact .inr ⟨h5, h4⟩

/-- **A pop of the other side's node reads at or after its push** (`treiber2`'s
data read: the window of the popped node's data word covers its push). -/
theorem hist_time {val : Nat → BitVec 64} {A B : Side} (H : HistOK val A B) (ha : A.popped) (hv : A.v = B.n) :
    B.p ≤ A.tr0 := by
  have hA := H.sa.pop ha
  have h0 := hA.v0
  rcases hA.t0 with h | h | h | ⟨-, h⟩ | ⟨hb, h⟩
  · rw [h, H.val0] at h0; exact absurd (h0.trans hv).symm H.bnz
  · rw [h, H.sa.pval] at h0; exact absurd (h0.trans hv) H.nne
  · omega
  · have := hA.le1; have := hA.lt; omega
  · have := (H.sb.pop hb).p_lt_q; omega

end Kraken.Promising.SLR.EnvG.Treiber2
