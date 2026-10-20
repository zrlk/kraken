/-
**`counter = N` from the threads' final
histories.** ISA-neutral, a statement about one memory.

At a final configuration every thread is in phase `6` with no outstanding
promise, so (`Bk`) every message is one of the recorded writes of its thread:
its RMW write `a'` to `next = x`, its counter write `w` to `c`, its owner
write `o'` to `o`. `FinW` collects what the invariant (`Facts`, `Bk`) gives
about such a memory `M` for `N` threads; nothing else about the machine is
used, so the argument applies to any memory with these histories.

`cnt M l τ` counts the messages to `l` in `[1, τ]`; it is the number of
threads whose `l`-write is at most `τ` (`cnt_eq_countP`), so at most `N`, and
`N` at the end of the memory. By strong induction on timestamps, the low
word read from `l` at `τ` is `cnt M l τ` (mod `2^32`):

- `next` (`valX`): the RMW read `a` precedes the write `a'` with no other
  write to `x` in between (atomicity), so the thread's ticket `t` is
  `k j = cnt x a` and its write is the `k j + 1`-st; tickets are distinct
  and below `N` (`k_inj`, `k_lt`).
- `owner` (`valO`), **with no mutual exclusion assumed**: the owner write
  `o'` of thread `j` is the `k j + 1`-st. Every earlier owner write is that
  of a thread with a different ticket `k m = cnt o o'_m - 1` (induction), so
  the `cnt o (o' - 1)` earlier writes use up the tickets below
  `cnt o (o' - 1)` and `k j ≥ cnt o (o' - 1)`; the spin's read `s` returned
  `t`, so `k j = cnt o s ≤ cnt o q ≤ cnt o (o' - 1)`; hence the release read
  `q` returned `k j` and `o'` writes `k j + 1`.
- `counter` (`valC`): no other counter write lies between a thread's read
  `r` and its write `w`. A thread `m` with a smaller ticket wrote before its
  release `o'_m ≤ s_j`, inside `(r_j, s_j]`, where `j` saw no counter write;
  one with a larger ticket would see `j`'s write inside `(r_m, s_m]`.

**`FinW.finalVal`**: the last counter write is the `N`-th, so
`finalVal c = N`.
-/
import Kraken.Promising.SLR.EnvG.TicketX2Env
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Counting the messages to a location -/

/-- Is the message at `ts` to `l`? -/
def isAt (M : Memory) (l : Loc) (ts : Time) : Bool :=
  match M.get? ts with
  | some m => decide (m.loc = l)
  | none => false

/-- The number of messages to `l` with timestamps in `[1, n]`. -/
def cnt (M : Memory) (l : Loc) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt M l n + if isAt M l (n + 1) then 1 else 0

variable {M : Memory} {l : Loc}

theorem isAt_iff {ts : Time} : isAt M l ts = true ↔ ∃ m, M.get? ts = some m ∧ m.loc = l := by
  unfold isAt; split <;> simp_all

theorem isAt_of_get {ts : Time} {m : Msg} (hg : M.get? ts = some m) (hl : m.loc = l) : isAt M l ts = true :=
  isAt_iff.mpr ⟨m, hg, hl⟩

theorem pos_of_get {ts : Time} {m : Msg} (hg : M.get? ts = some m) : 0 < ts := by
  unfold Memory.get? at hg
  split at hg
  · cases hg
  · omega_t

theorem isAt_pos {ts : Time} (h : isAt M l ts = true) : 0 < ts := by
  obtain ⟨m, hg, -⟩ := isAt_iff.mp h
  exact pos_of_get hg

theorem cnt_le_succ (n : Nat) : cnt M l n ≤ cnt M l (n + 1) := by
  simp only [cnt]; omega

theorem cnt_at {n : Nat} (h : isAt M l (n + 1) = true) : cnt M l (n + 1) = cnt M l n + 1 := by
  simp [cnt, h]

theorem cnt_not {n : Nat} (h : isAt M l (n + 1) = false) : cnt M l (n + 1) = cnt M l n := by
  simp [cnt, h]

theorem cnt_at' {ts : Time} (h : isAt M l ts = true) : cnt M l ts = cnt M l (ts - 1) + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, ts = p + 1 := ⟨ts - 1, by have := isAt_pos h; omega_t⟩
  rw [cnt_at h]; rfl

theorem cnt_mono {a b : Nat} (h : a ≤ b) : cnt M l a ≤ cnt M l b := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · exact Nat.le_trans (ih hab) (cnt_le_succ b)
    · obtain rfl : a = b + 1 := by omega
      exact Nat.le_refl _

theorem cnt_const {a b : Nat} (hab : a ≤ b) (h : ∀ ts, a < ts → ts ≤ b → isAt M l ts = false) :
    cnt M l b = cnt M l a := by
  induction b with
  | zero => obtain rfl : a = 0 := by omega
            rfl
  | succ b ih =>
    by_cases hab' : a ≤ b
    · rw [cnt_not (h _ (by omega) (Nat.le_refl _)), ih hab' (fun ts h1 h2 => h ts h1 (by omega))]
    · obtain rfl : a = b + 1 := by omega
      rfl

theorem cnt_lt {a b : Nat} (hb : isAt M l b = true) (hab : a < b) : cnt M l a < cnt M l b := by
  rw [cnt_at' hb]
  have := cnt_mono (M := M) (l := l) (show a ≤ b - 1 by omega)
  omega

theorem cnt_inj {a b : Nat} (ha : isAt M l a = true) (hb : isAt M l b = true) (h : cnt M l a = cnt M l b) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have := cnt_lt hb hlt; omega
  · exact heq
  · have := cnt_lt ha hgt; omega

/-- An `l`-message at `b` above `cnt a` is after `a`. -/
theorem le_of_cnt_le {a b : Nat} (hb : isAt M l b = true) (h : cnt M l b ≤ cnt M l a) : b ≤ a :=
  Nat.le_of_not_lt fun hlt => absurd (cnt_lt hb hlt) (by omega)

/-- **Intermediate values**: every value from `1` to `cnt b` is the count at
an `l`-message up to `b`. -/
theorem cnt_ivt {n b : Nat} (h1 : 1 ≤ n) (h2 : n ≤ cnt M l b) :
    ∃ ts, ts ≤ b ∧ isAt M l ts = true ∧ cnt M l ts = n := by
  induction b with
  | zero => simp [cnt] at h2; omega
  | succ b ih =>
    by_cases hn : n ≤ cnt M l b
    · obtain ⟨ts, h, h', h''⟩ := ih hn
      exact ⟨ts, by omega, h', h''⟩
    · cases hb : isAt M l (b + 1)
      · rw [cnt_not hb] at h2; omega
      · rw [cnt_at hb] at h2
        exact ⟨b + 1, Nat.le_refl _, hb, by rw [cnt_at hb]; omega⟩

/-! ## The count is a number of threads -/

theorem countP_split (f : Nat → Nat) (b : Nat) (L : List Nat) :
    L.countP (fun j => decide (f j ≤ b + 1)) =
      L.countP (fun j => decide (f j ≤ b)) + L.countP (fun j => decide (f j = b + 1)) := by
  induction L with
  | nil => rfl
  | cons j L ih =>
    simp only [List.countP_cons, ih]
    repeat' split
    all_goals (simp only [decide_eq_true_eq] at *; omega)

theorem countP_eq_le_one (f : Nat → Nat) (n : Nat) :
    ∀ L : List Nat, L.Nodup → (∀ j ∈ L, ∀ j' ∈ L, f j = f j' → j = j') →
      L.countP (fun j => decide (f j = n)) ≤ 1
  | [], _, _ => by simp
  | j :: L, hnd, hinj => by
    rw [List.nodup_cons] at hnd
    rw [List.countP_cons]
    by_cases hj : f j = n
    · have : L.countP (fun j => decide (f j = n)) = 0 := by
        rw [List.countP_eq_zero]
        intro j' hj' hf
        have := hinj j (List.mem_cons_self ..) j' (List.mem_cons_of_mem _ hj') (hj.trans (of_decide_eq_true hf).symm)
        subst this; exact hnd.1 hj'
      simp [this, hj]
    · have := countP_eq_le_one f n L hnd.2 fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b
        (List.mem_cons_of_mem _ hb)
      simp [hj]; omega

/-- **The count of `l`-messages up to `b` is the number of threads whose
`l`-write `f j` is at most `b`**, when each thread `j < N` has exactly one
`l`-message, at `f j`, and every `l`-message is one of them. -/
theorem cnt_eq_countP {N : Nat} (f : Nat → Nat) (hf : ∀ j < N, ∃ v, M.get? (f j) = some ⟨l, v, j⟩)
    (hcov : ∀ ts m, M.get? ts = some m → m.loc = l → ∃ j < N, f j = ts) :
    ∀ b, cnt M l b = (List.range N).countP (fun j => decide (f j ≤ b)) := by
  have hat : ∀ j < N, isAt M l (f j) = true := fun j hj =>
    let ⟨_, hv⟩ := hf j hj; isAt_of_get hv rfl
  have hinj : ∀ j ∈ List.range N, ∀ j' ∈ List.range N, f j = f j' → j = j' := by
    intro j hj j' hj' he
    obtain ⟨v, hv⟩ := hf j (List.mem_range.mp hj)
    obtain ⟨v', hv'⟩ := hf j' (List.mem_range.mp hj')
    rw [he, hv'] at hv
    exact (congrArg Msg.tid (Option.some.inj hv)).symm
  intro b
  induction b with
  | zero =>
    refine (List.countP_eq_zero.mpr fun j hj h => ?_).symm
    have := isAt_pos (hat j (List.mem_range.mp hj))
    simp at h; omega_t
  | succ b ih =>
    rw [countP_split, ← ih]
    cases hb : isAt M l (b + 1)
    · have h0 : (List.range N).countP (fun j => decide (f j = b + 1)) = 0 :=
        List.countP_eq_zero.mpr fun j hj h => by
          have := hat j (List.mem_range.mp hj)
          rw [of_decide_eq_true h, hb] at this; cases this
      rw [cnt_not hb, h0, Nat.add_zero]
    · rw [cnt_at hb]
      have h1 := countP_eq_le_one f (b + 1) _ List.nodup_range hinj
      obtain ⟨m, hg, hl⟩ := isAt_iff.mp hb
      obtain ⟨j, hj, hfj⟩ := hcov _ m hg hl
      have h2 : 0 < (List.range N).countP (fun j => decide (f j = b + 1)) :=
        List.countP_pos_iff.mpr ⟨j, List.mem_range.mpr hj, by simp [hfj]⟩
      omega

/-! ## Reads -/

theorem read?_cases {τ : Time} {v : Val} (h : M.read? l τ = some v) :
    (τ = 0 ∧ v = M.initVal l) ∨ ∃ m, M.get? τ = some m ∧ m.loc = l ∧ m.val = v := by
  unfold Memory.read? at h
  split at h
  · exact .inl ⟨by assumption, (Option.some.inj h).symm⟩
  · split at h
    · rename_i m hm
      split at h
      · rename_i hl
        exact .inr ⟨m, hm, by simpa using hl, Option.some.inj h⟩
      · cases h
    · cases h

theorem read?_of_get {τ : Time} {m : Msg} (hg : M.get? τ = some m) : M.read? m.loc τ = some m.val := by
  have := pos_of_get hg
  unfold Memory.read?
  split
  · omega_t
  · rw [hg]; simp

theorem lo_inc (u : BitVec 32) : lo (inc u) = u + 1 := by simp

theorem ofNat_succ32 (a : Nat) : BitVec.ofNat 32 a + 1 = BitVec.ofNat 32 (a + 1) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

theorem ofNat32_inj {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-! ## The final histories -/

/-- **The final memory `M` of `N` threads**: three distinct words, initially
`0`; every message is by a thread `j < N`, which is in phase `6` with the
facts of its history `H j` and no outstanding promise. -/
structure FinW (x o c : BitVec 64) (N : Nat) (M : Memory) (G : Nat → TkSt) (H : Nat → Hist) : Prop where
  xo : x ≠ o
  xc : x ≠ c
  oc : o ≠ c
  bound : N < 2 ^ 32
  x0 : M.initVal ⟨x, 4⟩ = 0
  o0 : M.initVal ⟨o, 4⟩ = 0
  c0 : M.initVal ⟨c, 4⟩ = 0
  msg : ∀ ts m, M.get? ts = some m → m.tid < N
  fin : ∀ j < N, (G j).k = 6
  facts : ∀ j < N, ∃ V, Facts x o c j M V (G j) (H j)
  bk : ∀ j < N, Bk j M [] (G j) (H j)

namespace FinW

variable {x o c : BitVec 64} {N : Nat} {G : Nat → TkSt} {H : Nat → Hist} (hW : FinW x o c N M G H)
include hW

theorem lv {j : Nat} (hj : j < N) (n : Nat) (hn : n ≤ 6) : ∃ V, Lv x o c j M V (G j) (H j) n :=
  let ⟨V, hF⟩ := hW.facts j hj
  ⟨V, hF.1 n (by rw [hW.fin j hj]; exact hn)⟩

theorem l1 {j : Nat} (hj : j < N) :
    (∃ v, M.read? ⟨x, 4⟩ (H j).a = some v ∧ lo v = (G j).t) ∧ M.get? (H j).a' = some ⟨⟨x, 4⟩, inc (G j).t, j⟩ ∧
      (H j).a < (H j).a' ∧
      ∀ ts m, (H j).a < ts → ts < (H j).a' → M.get? ts = some m → m.loc = ⟨x, 4⟩ → m.tid = j :=
  let ⟨_, h⟩ := hW.lv hj 1 (by omega); h

theorem l2 {j : Nat} (hj : j < N) : ∃ v, M.read? ⟨o, 4⟩ (H j).s = some v ∧ lo v = (G j).t :=
  let ⟨_, h⟩ := hW.lv hj 2 (by omega); h.1

theorem l3 {j : Nat} (hj : j < N) :
    (∃ v, M.read? ⟨c, 4⟩ (H j).r = some v ∧ lo v = (G j).e) ∧ NoWriteInX M ⟨c, 4⟩ (H j).r (H j).s :=
  let ⟨_, h⟩ := hW.lv hj 3 (by omega); ⟨h.1, h.2.1⟩

theorem l4 {j : Nat} (hj : j < N) :
    M.get? (H j).w = some ⟨⟨c, 4⟩, inc (G j).e, j⟩ ∧ (H j).r < (H j).w ∧ (H j).s < (H j).w :=
  let ⟨_, h⟩ := hW.lv hj 4 (by omega); ⟨h.1, h.2.1, h.2.2.1⟩

theorem l5 {j : Nat} (hj : j < N) :
    (∃ v, M.read? ⟨o, 4⟩ (H j).q = some v ∧ lo v = (G j).u) ∧ (H j).s ≤ (H j).q :=
  let ⟨_, h⟩ := hW.lv hj 5 (by omega); ⟨h.1, h.2.1⟩

theorem l6 {j : Nat} (hj : j < N) :
    M.get? (H j).o' = some ⟨⟨o, 4⟩, inc (G j).u, j⟩ ∧ (H j).q < (H j).o' ∧ (H j).w < (H j).o' :=
  let ⟨_, h⟩ := hW.lv hj 6 (by omega); h

/-- **Every message is a recorded write** of its thread. -/
theorem cover {ts : Time} {m : Msg} (hg : M.get? ts = some m) :
    ∃ j < N, (ts = (H j).a' ∧ m = ⟨⟨x, 4⟩, inc (G j).t, j⟩) ∨ (ts = (H j).w ∧ m = ⟨⟨c, 4⟩, inc (G j).e, j⟩) ∨
      (ts = (H j).o' ∧ m = ⟨⟨o, 4⟩, inc (G j).u, j⟩) := by
  have hj := hW.msg ts m hg
  refine ⟨m.tid, hj, ?_⟩
  rcases (hW.bk _ hj).own ts m hg rfl with hin | hr
  · cases hin
  rcases hr with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact .inl ⟨rfl, Option.some.inj (hg.symm.trans (hW.l1 hj).2.1)⟩
  · exact .inr (.inl ⟨rfl, Option.some.inj (hg.symm.trans (hW.l4 hj).1)⟩)
  · exact .inr (.inr ⟨rfl, Option.some.inj (hg.symm.trans (hW.l6 hj).1)⟩)

theorem coverX {ts : Time} {m : Msg} (hg : M.get? ts = some m) (hl : m.loc = ⟨x, 4⟩) :
    ∃ j < N, ts = (H j).a' ∧ m = ⟨⟨x, 4⟩, inc (G j).t, j⟩ := by
  obtain ⟨j, hj, h | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := hW.cover hg
  · exact ⟨j, hj, h⟩
  · exact absurd hl (loc_ne (Ne.symm hW.xc))
  · exact absurd hl (loc_ne (Ne.symm hW.xo))

theorem coverO {ts : Time} {m : Msg} (hg : M.get? ts = some m) (hl : m.loc = ⟨o, 4⟩) :
    ∃ j < N, ts = (H j).o' ∧ m = ⟨⟨o, 4⟩, inc (G j).u, j⟩ := by
  obtain ⟨j, hj, ⟨-, rfl⟩ | ⟨-, rfl⟩ | h⟩ := hW.cover hg
  · exact absurd hl (loc_ne hW.xo)
  · exact absurd hl (loc_ne (Ne.symm hW.oc))
  · exact ⟨j, hj, h⟩

theorem coverC {ts : Time} {m : Msg} (hg : M.get? ts = some m) (hl : m.loc = ⟨c, 4⟩) :
    ∃ j < N, ts = (H j).w ∧ m = ⟨⟨c, 4⟩, inc (G j).e, j⟩ := by
  obtain ⟨j, hj, ⟨-, rfl⟩ | h | ⟨-, rfl⟩⟩ := hW.cover hg
  · exact absurd hl (loc_ne hW.xc)
  · exact ⟨j, hj, h⟩
  · exact absurd hl (loc_ne hW.oc)

theorem cntX_le (b : Nat) : cnt M ⟨x, 4⟩ b ≤ N := by
  rw [cnt_eq_countP (fun j => (H j).a') (fun j hj => ⟨_, (hW.l1 hj).2.1⟩)
    (fun ts m hg hl => let ⟨j, hj, h, _⟩ := hW.coverX hg hl; ⟨j, hj, h.symm⟩)]
  exact Nat.le_trans List.countP_le_length (by simp)

theorem cntO_le (b : Nat) : cnt M ⟨o, 4⟩ b ≤ N := by
  rw [cnt_eq_countP (fun j => (H j).o') (fun j hj => ⟨_, (hW.l6 hj).1⟩)
    (fun ts m hg hl => let ⟨j, hj, h, _⟩ := hW.coverO hg hl; ⟨j, hj, h.symm⟩)]
  exact Nat.le_trans List.countP_le_length (by simp)

theorem cntC_le (b : Nat) : cnt M ⟨c, 4⟩ b ≤ N := by
  rw [cnt_eq_countP (fun j => (H j).w) (fun j hj => ⟨_, (hW.l4 hj).1⟩)
    (fun ts m hg hl => let ⟨j, hj, h, _⟩ := hW.coverC hg hl; ⟨j, hj, h.symm⟩)]
  exact Nat.le_trans List.countP_le_length (by simp)

/-- At the end of the memory, all `N` counter writes are counted. -/
theorem cntC_last : cnt M ⟨c, 4⟩ M.last = N := by
  rw [cnt_eq_countP (fun j => (H j).w) (fun j hj => ⟨_, (hW.l4 hj).1⟩)
    (fun ts m hg hl => let ⟨j, hj, h, _⟩ := hW.coverC hg hl; ⟨j, hj, h.symm⟩)]
  have : (List.range N).countP (fun j => decide ((H j).w ≤ M.last)) = (List.range N).length :=
    List.countP_eq_length.mpr fun j hj => by
      simpa using Memory.last_le_of_get?_eq_some M (hW.l4 (List.mem_range.mp hj)).1
  simpa using this

/-! ### `next`: the tickets -/

/-- Thread `j`'s ticket, as a count. -/
def k (M : Memory) (x : BitVec 64) (H : Nat → Hist) (j : Nat) : Nat := cnt M ⟨x, 4⟩ (H j).a

omit hW in
theorem k_def (j : Nat) : k M x H j = cnt M ⟨x, 4⟩ (H j).a := rfl

/-- The RMW's write is the next write to `x` after its read. -/
theorem stepX {j : Nat} (hj : j < N) : cnt M ⟨x, 4⟩ (H j).a' = k M x H j + 1 := by
  obtain ⟨-, hga, hlt, hat⟩ := hW.l1 hj
  have hc : cnt M ⟨x, 4⟩ ((H j).a' - 1) = cnt M ⟨x, 4⟩ (H j).a := by
    refine cnt_const (show (H j).a ≤ (H j).a' - 1 by omega_t) fun ts h1 h2 => ?_
    cases hb : isAt M ⟨x, 4⟩ ts
    · rfl
    obtain ⟨m, hg, hl⟩ := isAt_iff.mp hb
    have htid := hat ts m h1 (by omega_t) hg hl
    obtain ⟨j', -, rfl, rfl⟩ := hW.coverX hg hl
    subst htid
    omega_t
  rw [cnt_at' (isAt_of_get hga rfl), k_def, hc]

/-- The low word of `x` at `τ` is the number of writes to `x` up to `τ`. -/
theorem valX : ∀ τ v, M.read? ⟨x, 4⟩ τ = some v → lo v = BitVec.ofNat 32 (cnt M ⟨x, 4⟩ τ) := by
  intro τ
  induction τ using Nat.strongRecOn with
  | _ τ ih =>
  intro v hv
  rcases read?_cases hv with ⟨rfl, rfl⟩ | ⟨m, hg, hl, rfl⟩
  · rw [hW.x0]; rfl
  · obtain ⟨j, hj, rfl, rfl⟩ := hW.coverX hg hl
    obtain ⟨⟨va, hra, hva⟩, -, hlt, -⟩ := hW.l1 hj
    rw [hW.stepX hj, lo_inc, ← hva, ih _ hlt va hra, ofNat_succ32]; rfl

theorem t_eq {j : Nat} (hj : j < N) : (G j).t = BitVec.ofNat 32 (k M x H j) := by
  obtain ⟨⟨va, hra, hva⟩, -⟩ := hW.l1 hj
  rw [← hva, hW.valX _ va hra]; rfl

theorem k_lt {j : Nat} (hj : j < N) : k M x H j < N := by
  have := hW.stepX hj; have := hW.cntX_le (H j).a'; omega

/-- **Tickets are distinct.** -/
theorem k_inj {j j' : Nat} (hj : j < N) (hj' : j' < N) (h : k M x H j = k M x H j') : j = j' := by
  have ha := (hW.l1 hj).2.1
  have ha' := (hW.l1 hj').2.1
  have he := cnt_inj (isAt_of_get ha rfl) (isAt_of_get ha' rfl) (by rw [hW.stepX hj, hW.stepX hj', h])
  rw [he, ha'] at ha
  exact (congrArg Msg.tid (Option.some.inj ha)).symm

/-! ### `owner`: the releases, in ticket order -/

/-- The low word of `o` at `τ` is the number of writes to `o` up to `τ`, and
the owner write at `τ` is that of the thread whose ticket is one below the
count (by strong induction on `τ`; no mutual exclusion is assumed). -/
theorem valO : ∀ τ, (∀ v, M.read? ⟨o, 4⟩ τ = some v → lo v = BitVec.ofNat 32 (cnt M ⟨o, 4⟩ τ)) ∧
    ∀ j < N, (H j).o' = τ → k M x H j + 1 = cnt M ⟨o, 4⟩ τ := by
  intro τ
  induction τ using Nat.strongRecOn with
  | _ τ ih =>
  have core : ∀ j < N, (H j).o' = τ →
      lo (inc (G j).u) = BitVec.ofNat 32 (cnt M ⟨o, 4⟩ τ) ∧ k M x H j + 1 = cnt M ⟨o, 4⟩ τ := by
    intro j hj hτ
    obtain ⟨hgo, hqo, hwo⟩ := hW.l6 hj
    obtain ⟨-, -, hsw⟩ := hW.l4 hj
    obtain ⟨⟨vq, hrq, hvq⟩, hsq⟩ := hW.l5 hj
    obtain ⟨vs, hrs, hvs⟩ := hW.l2 hj
    have hat : isAt M ⟨o, 4⟩ τ = true := hτ ▸ isAt_of_get hgo rfl
    have hks : k M x H j = cnt M ⟨o, 4⟩ (H j).s := by
      have h1 := (ih _ (by omega_t)).1 vs hrs
      rw [hvs, hW.t_eq hj] at h1
      exact ofNat32_inj (by have := hW.k_lt hj; have := hW.bound; omega)
        (by have := hW.cntO_le (H j).s; have := hW.bound; omega) h1
    have hu : (G j).u = BitVec.ofNat 32 (cnt M ⟨o, 4⟩ (H j).q) := by
      rw [← hvq]; exact (ih _ (by omega_t)).1 vq hrq
    have hle1 := cnt_mono (M := M) (l := ⟨o, 4⟩) hsq
    have hle2 := cnt_mono (M := M) (l := ⟨o, 4⟩) (show (H j).q ≤ τ - 1 by omega_t)
    have hge : cnt M ⟨o, 4⟩ (τ - 1) ≤ k M x H j := by
      refine Nat.le_of_not_lt fun hlt => ?_
      obtain ⟨τ', hτ', hat', hc⟩ := cnt_ivt (M := M) (l := ⟨o, 4⟩) (n := k M x H j + 1) (by omega) hlt
      obtain ⟨m', hg', hl'⟩ := isAt_iff.mp hat'
      obtain ⟨jm, hjm, rfl, -⟩ := hW.coverO hg' hl'
      have := (ih _ (by have := isAt_pos hat; omega_t)).2 jm hjm rfl
      obtain rfl := hW.k_inj hjm hj (by omega)
      omega_t
    have hτc := cnt_at' hat
    refine ⟨?_, by omega⟩
    rw [lo_inc, hu, ofNat_succ32, hτc]
    congr 1; omega
  refine ⟨fun v hv => ?_, fun j hj hτ => (core j hj hτ).2⟩
  rcases read?_cases hv with ⟨rfl, rfl⟩ | ⟨m, hg, hl, rfl⟩
  · rw [hW.o0]; rfl
  · obtain ⟨j, hj, hτ, rfl⟩ := hW.coverO hg hl
    exact (core j hj hτ.symm).1

theorem ko {j : Nat} (hj : j < N) : k M x H j + 1 = cnt M ⟨o, 4⟩ (H j).o' := (hW.valO _).2 j hj rfl

theorem ks {j : Nat} (hj : j < N) : k M x H j = cnt M ⟨o, 4⟩ (H j).s := by
  obtain ⟨vs, hrs, hvs⟩ := hW.l2 hj
  have h1 := (hW.valO _).1 vs hrs
  rw [hvs, hW.t_eq hj] at h1
  exact ofNat32_inj (by have := hW.k_lt hj; have := hW.bound; omega)
    (by have := hW.cntO_le (H j).s; have := hW.bound; omega) h1

/-- A thread with a smaller ticket released before a thread's spin read. -/
theorem o'_le_s {j m : Nat} (hj : j < N) (hm : m < N) (hk : k M x H m < k M x H j) : (H m).o' ≤ (H j).s :=
  le_of_cnt_le (isAt_of_get (hW.l6 hm).1 rfl) (by rw [← hW.ko hm, ← hW.ks hj]; omega)

/-! ### `counter` -/

/-- No other counter write lies between a thread's counter read and write. -/
theorem noC {j : Nat} (hj : j < N) {ts : Time} (h1 : (H j).r < ts) (h2 : ts < (H j).w) :
    isAt M ⟨c, 4⟩ ts = false := by
  cases hb : isAt M ⟨c, 4⟩ ts
  · rfl
  obtain ⟨m', hg', hl'⟩ := isAt_iff.mp hb
  obtain ⟨jm, hjm, rfl, -⟩ := hW.coverC hg' hl'
  have hne : jm ≠ j := by rintro rfl; omega_t
  have hkne : k M x H jm ≠ k M x H j := fun h => hne (hW.k_inj hjm hj h)
  rcases Nat.lt_or_gt_of_ne hkne with hlt | hgt
  · -- `jm` released before `j`'s spin read; its counter write is in `(r_j, s_j]`
    have := hW.o'_le_s hj hjm hlt
    have := (hW.l6 hjm).2.2
    exact absurd hl' ((hW.l3 hj).2 _ m' h1 (by omega_t) hg')
  · -- `j` released before `jm`'s spin read; `j`'s counter write is in `(r_jm, s_jm]`
    have := hW.o'_le_s hjm hj hgt
    have := (hW.l6 hj).2.2
    have := (hW.l4 hjm).2.1
    exact absurd rfl ((hW.l3 hjm).2 _ _ (by omega_t) (by omega_t) (hW.l4 hj).1)

/-- The low word of `c` at `τ` is the number of writes to `c` up to `τ`. -/
theorem valC : ∀ τ v, M.read? ⟨c, 4⟩ τ = some v → lo v = BitVec.ofNat 32 (cnt M ⟨c, 4⟩ τ) := by
  intro τ
  induction τ using Nat.strongRecOn with
  | _ τ ih =>
  intro v hv
  rcases read?_cases hv with ⟨rfl, rfl⟩ | ⟨m, hg, hl, rfl⟩
  · rw [hW.c0]; rfl
  · obtain ⟨j, hj, rfl, rfl⟩ := hW.coverC hg hl
    obtain ⟨⟨vr, hrr, hvr⟩, -⟩ := hW.l3 hj
    obtain ⟨hgw, hrw, -⟩ := hW.l4 hj
    rw [cnt_at' (isAt_of_get hgw rfl), cnt_const (show (H j).r ≤ (H j).w - 1 by omega_t)
      fun ts h1 h2 => hW.noC hj h1 (by omega_t)]
    rw [lo_inc, ← hvr, ih _ hrw vr hrr, ofNat_succ32]

/-- **`counter = N` at the end.** -/
theorem finalVal : M.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h0 : M.read? ⟨c, 4⟩ 0 = some (M.initVal ⟨c, 4⟩) := by simp [Memory.read?]
    rw [Memory.finalVal_of_max h0 fun ts' v' h => ?_, hW.c0]; · rfl
    rcases read?_cases h with ⟨rfl, -⟩ | ⟨m, hg, -, -⟩
    · exact Nat.le_refl _
    · exact absurd (hW.msg _ _ hg) (Nat.not_lt_zero _)
  · obtain ⟨τ, -, hat, hc⟩ := cnt_ivt (M := M) (l := ⟨c, 4⟩) (n := N) hN (by rw [hW.cntC_last]; exact Nat.le_refl _)
    obtain ⟨m, hg, hl⟩ := isAt_iff.mp hat
    obtain ⟨j, hj, rfl, rfl⟩ := hW.coverC hg hl
    have hr : M.read? ⟨c, 4⟩ (H j).w = some (inc (G j).e) := read?_of_get hg
    rw [Memory.finalVal_of_max hr fun ts' v' h => ?_]
    · have hv := hW.valC _ _ hr
      rw [hc] at hv
      have : inc (G j).e = (lo (inc (G j).e)).setWidth 128 := by simp
      rw [this, hv]
      apply BitVec.eq_of_toNat_eq
      simp [Nat.mod_eq_of_lt hW.bound]
    · refine Nat.le_of_not_lt fun hlt => ?_
      rcases read?_cases h with ⟨rfl, -⟩ | ⟨m', hg', hl', -⟩
      · omega_t
      · have := cnt_lt (isAt_of_get hg' hl') hlt
        have := hW.cntC_le ts'
        omega

end FinW

end Kraken.Promising.SLR.EnvG.TicketX2

#print axioms Kraken.Promising.SLR.EnvG.TicketX2.FinW.finalVal
