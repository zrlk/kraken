/-
The initial resources of the spinlock counter and the `lockPred` instance of
initial erasure (ISA-neutral). Completes `SLR/SpinInit.lean`
for the resource specification of `SLR/SwpSpec.lean`.

Every initial resource is *initial* (`Res.IsInit`): its write set at each
location is the initial message, if it holds a positive fraction, and it
holds no acquire id. Thread `j` holds `1/N` of the lock `Lk`, `1/2` of its
token `K j` and all of its fresh token `F j` (`threadFrac`); the pool holds
the counter `C` and the other half of every `K j` (`poolFrac`).

## Contents

- `Perm.init`, `Res.initOf`, `Res.IsInit` (closed under `op`, `prod`,
  `threadsRes`).
- `SpinLocs`: the locations are distinct (`Lk`, `C`, the `K j`, the `F j`).
- `threadFrac`, `poolFrac`, `threadRes`, `poolRes`; `valid_init`.
- `Spinlock.erase_init_lockPred`: `Erase` at `Config.init` for
  `spinGhost Lk (lockPred N Lk C K F) poolRes`, threads `threadRes`.
- `Spinlock.counter_init`: `counter_of_theorem1Pure` with all initial-state
  obligations discharged.
-/
import Kraken.Promising.SLR.SpinInit
import Kraken.Promising.SLR.SwpSpec

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- The permission `(q, {(v, 0)})`: fraction `q` with the initial message
(empty write set at `q = 0`). -/
def Perm.init (q : Rat) (hq : 0 ≤ q) (v : Val) : Perm where
  q := q
  X p := 0 < q ∧ p = (v, 0)
  nonneg := hq
  zero h p hp := by have := hp.1; grind

/-- The resource with fraction `f x` of every location `x`, at its initial
message, and no acquire id. -/
def Res.initOf (m : Memory) (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) : Res :=
  ⟨fun x => Perm.init (f x) (hf x) (m.initVal x), fun _ _ => 0⟩

/-- An initial resource: the write set of each location it holds is the
initial message; no acquire id. -/
def Res.IsInit (m : Memory) (r : Res) : Prop :=
  (∀ x p, (r.wr x).X p ↔ 0 < (r.wr x).q ∧ p = (m.initVal x, 0)) ∧ ∀ x ι, r.acq x ι = 0

namespace Res.IsInit

variable {m : Memory}

theorem initOf (f : Loc → Rat) (hf : ∀ x, 0 ≤ f x) : (Res.initOf m f hf).IsInit m :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => rfl⟩

theorem unit : Res.unit.IsInit m :=
  ⟨fun _ p => ⟨fun h => h.elim, fun h => absurd h.1 (by simp [Res.unit, Perm.unit])⟩, fun _ _ => rfl⟩

theorem op {a b : Res} (ha : a.IsInit m) (hb : b.IsInit m) : (a.op b).IsInit m := by
  refine ⟨fun x p => ?_, fun x ι => by show a.acq x ι + b.acq x ι = 0; rw [ha.2, hb.2]⟩
  show (a.wr x).X p ∨ (b.wr x).X p ↔ 0 < (a.wr x).q + (b.wr x).q ∧ _
  rw [ha.1, hb.1]
  have := (a.wr x).nonneg
  have := (b.wr x).nonneg
  constructor
  · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩) <;> exact ⟨by grind, rfl⟩
  · rintro ⟨h, rfl⟩
    by_cases h' : 0 < (a.wr x).q
    · exact .inl ⟨h', rfl⟩
    · exact .inr ⟨by grind, rfl⟩

theorem prod : ∀ {rs : List Res}, (∀ r ∈ rs, r.IsInit m) → (Res.prod rs).IsInit m
  | [], _ => unit
  | r :: rs, h => by
    rw [Res.prod_cons]
    exact op (h r List.mem_cons_self) (prod fun r' hr' => h r' (List.mem_cons_of_mem r hr'))

theorem threadsRes {rF : Nat → Res} {n : Nat} (h : ∀ i < n, (rF i).IsInit m) :
    (SLR.threadsRes rF n).IsInit m :=
  prod fun r hr => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    exact h i (List.mem_range.mp hi)

end Res.IsInit

namespace Spinlock

/-- The locations of the spinlock counter are distinct: the lock, the
counter, and per thread `j < N` the tokens `K j`, `F j`. -/
structure SpinLocs (N : Nat) (Lk C : Loc) (K F : Nat → Loc) : Prop where
  lk_c : Lk ≠ C
  k_lk : ∀ j < N, K j ≠ Lk
  k_c : ∀ j < N, K j ≠ C
  f_lk : ∀ j < N, F j ≠ Lk
  f_c : ∀ j < N, F j ≠ C
  k_f : ∀ i < N, ∀ j < N, K i ≠ F j
  k_inj : ∀ i < N, ∀ j < N, K i = K j → i = j
  f_inj : ∀ i < N, ∀ j < N, F i = F j → i = j

/-- Thread `j`'s initial fractions: `1/N` of the lock, `1/2` of `K j`, all
of `F j`. -/
def threadFrac (N : Nat) (Lk : Loc) (K F : Nat → Loc) (j : Nat) (x : Loc) : Rat :=
  (if x = Lk then (1 : Rat) / (N : Rat) else 0) + (if x = K j then 1 / 2 else 0) + (if x = F j then 1 else 0)

/-- The pool's initial fractions: all of the counter, `1/2` of every `K j`. -/
def poolFrac (N : Nat) (C : Loc) (K : Nat → Loc) (x : Loc) : Rat :=
  (if x = C then 1 else 0) + ((List.range N).map fun i => if x = K i then (1 / 2 : Rat) else 0).sum

private theorem ite_nonneg {p : Prop} [Decidable p] {a : Rat} (ha : 0 ≤ a) : 0 ≤ (if p then a else 0) := by
  split
  · exact ha
  · exact Rat.le_refl

private theorem sum_nonneg {n : Nat} {f : Nat → Rat} (h : ∀ i, 0 ≤ f i) : 0 ≤ ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := h n
    grind

theorem threadFrac_nonneg (N : Nat) (Lk : Loc) (K F : Nat → Loc) (j : Nat) (x : Loc) :
    0 ≤ threadFrac N Lk K F j x := by
  unfold threadFrac
  have h1 : (0 : Rat) ≤ 1 / (N : Rat) := by
    rw [Rat.div_def, Rat.one_mul, Rat.inv_def]
    exact Rat.divInt_nonneg (by omega) (Rat.num_nonneg.mpr Rat.natCast_nonneg)
  have := ite_nonneg (p := x = Lk) h1
  have := ite_nonneg (p := x = K j) (a := 1 / 2) (by grind)
  have := ite_nonneg (p := x = F j) (a := 1) (by grind)
  grind

theorem poolFrac_nonneg (N : Nat) (C : Loc) (K : Nat → Loc) (x : Loc) : 0 ≤ poolFrac N C K x := by
  unfold poolFrac
  have := ite_nonneg (p := x = C) (a := 1) (by grind)
  have := sum_nonneg (n := N) (f := fun i => if x = K i then (1 / 2 : Rat) else 0)
    (fun _ => ite_nonneg (by grind))
  grind

/-- Thread `j`'s initial resource. -/
def threadRes (m : Memory) (N : Nat) (Lk : Loc) (K F : Nat → Loc) (j : Nat) : Res :=
  Res.initOf m (threadFrac N Lk K F j) (threadFrac_nonneg N Lk K F j)

/-- The pool's initial resource. -/
def poolRes (m : Memory) (N : Nat) (C : Loc) (K : Nat → Loc) : Res :=
  Res.initOf m (poolFrac N C K) (poolFrac_nonneg N C K)

/-- A sum of one term `a` at an injective family's preimage of `x` (public;
`EnvG/TicketLockGhost.lean` uses it). -/
theorem sum_ite_inj {N : Nat} {f : Nat → Loc} (hinj : ∀ i < N, ∀ j < N, f i = f j → i = j)
    (x : Loc) (a : Rat) :
    ((List.range N).map fun i => if x = f i then a else 0).sum = if ∃ j < N, x = f j then a else 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append,
      ih fun i hi j hj h => hinj i (by omega) j (by omega) h]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases hn : x = f n
    · have hno : ¬ ∃ j < n, x = f j := fun ⟨j, hj, hx⟩ =>
        absurd (hinj j (by omega) n (by omega) (hx.symm.trans hn)) (by omega)
      have hyes : ∃ j < n + 1, x = f j := ⟨n, by omega, hn⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hn)]
      simp only [hno, hyes, ↓reduceIte]
      grind
    · by_cases he : ∃ j < n, x = f j
      · have hyes : ∃ j < n + 1, x = f j := by obtain ⟨j, hj, hx⟩ := he; exact ⟨j, by omega, hx⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
        simp only [he, hyes, ↓reduceIte]
        grind
      · have hno : ¬ ∃ j < n + 1, x = f j := fun ⟨j, hj, hx⟩ => by
          by_cases hjn : j = n
          · subst hjn; exact hn hx
          · exact he ⟨j, by omega, hx⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
        simp only [he, hno, ↓reduceIte]
        grind

/-- A sum of three families is the sum of the three sums (public). -/
theorem sum_add3 {n : Nat} (f g h : Nat → Rat) :
    ((List.range n).map fun i => f i + g i + h i).sum =
      ((List.range n).map f).sum + ((List.range n).map g).sum + ((List.range n).map h).sum := by
  induction n with
  | zero => simp; grind
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, List.map_append, List.sum_append,
      List.map_append, List.sum_append, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    grind

/-- The threads' total fraction of `x`. -/
theorem q_threads_init (m : Memory) {N : Nat} {Lk : Loc} {K F : Nat → Loc}
    (hK : ∀ i < N, ∀ j < N, K i = K j → i = j) (hF : ∀ i < N, ∀ j < N, F i = F j → i = j) (x : Loc) :
    ((threadsRes (threadRes m N Lk K F) N).wr x).q =
      (if x = Lk then (N : Rat) * (1 / (N : Rat)) else 0) + (if ∃ j < N, x = K j then 1 / 2 else 0) +
        (if ∃ j < N, x = F j then 1 else 0) := by
  rw [q_threadsRes]
  show ((List.range N).map fun j => threadFrac N Lk K F j x).sum = _
  unfold threadFrac
  rw [sum_add3 (fun _ => if x = Lk then 1 / (N : Rat) else 0) (fun i => if x = K i then 1 / 2 else 0)
      (fun i => if x = F i then 1 else 0), sum_ite_inj hK, sum_ite_inj hF, sum_range_const]
  by_cases hx : x = Lk <;> simp [hx]

/-- **The initial resources are valid**: at most the whole of every
location. -/
theorem valid_init (m : Memory) {N : Nat} {Lk C : Loc} {K F : Nat → Loc} (hL : SpinLocs N Lk C K F)
    (hN : 0 < N) : ((threadsRes (threadRes m N Lk K F) N).op (poolRes m N C K)).valid := by
  refine ⟨fun x => ?_, fun x ι => ?_⟩
  · show ((threadsRes (threadRes m N Lk K F) N).wr x).q + poolFrac N C K x ≤ 1
    rw [q_threads_init m hL.k_inj hL.f_inj]
    unfold poolFrac
    rw [sum_ite_inj hL.k_inj]
    have hN' : (N : Rat) ≠ 0 := by have := Nat.pos_iff_ne_zero.mp hN; exact_mod_cast this
    have h1 : (N : Rat) * (1 / N) = 1 := by grind
    by_cases hLk : x = Lk
    · subst hLk
      have hk : ¬ ∃ j < N, x = K j := fun ⟨j, hj, h⟩ => hL.k_lk j hj h.symm
      have hf : ¬ ∃ j < N, x = F j := fun ⟨j, hj, h⟩ => hL.f_lk j hj h.symm
      simp only [hk, hf, hL.lk_c, ↓reduceIte]
      grind
    · by_cases hC : x = C
      · subst hC
        have hk : ¬ ∃ j < N, x = K j := fun ⟨j, hj, h⟩ => hL.k_c j hj h.symm
        have hf : ¬ ∃ j < N, x = F j := fun ⟨j, hj, h⟩ => hL.f_c j hj h.symm
        simp only [hk, hf, hLk, ↓reduceIte]
        grind
      · by_cases hk : ∃ j < N, x = K j
        · have hf : ¬ ∃ j < N, x = F j := fun ⟨j, hj, h⟩ => by
            obtain ⟨i, hi, h'⟩ := hk
            exact hL.k_f i hi j hj (h'.symm.trans h)
          simp only [hk, hf, hLk, hC, ↓reduceIte]
          grind
        · by_cases hf : ∃ j < N, x = F j <;> simp only [hk, hf, hLk, hC, ↓reduceIte] <;> grind
  · show (threadsRes (threadRes m N Lk K F) N).acq x ι + 0 ≤ 1
    have := (Res.IsInit.threadsRes (m := m) (rF := threadRes m N Lk K F) (n := N)
      (fun _ _ => Res.IsInit.initOf _ _)).2 x ι
    omega

/-- The pool satisfies `lockPred` at the initial lock value `0`, view `0`
(`Good` with no thread incremented, the counter at its initial `0`). -/
theorem lockPred_pool (m : Memory) {N : Nat} {Lk C : Loc} {K F : Nat → Loc} (hL : SpinLocs N Lk C K F)
    (hC0 : m.initVal C = 0) :
    (lockPred N Lk C K F).P 0 m 0 (poolRes m N C K) := by
  intro _
  have hpC : poolFrac N C K C = 1 := by
    unfold poolFrac
    rw [sum_ite_inj hL.k_inj]
    have hk : ¬ ∃ j < N, C = K j := fun ⟨j, hj, h⟩ => hL.k_c j hj h.symm
    simp only [hk, ↓reduceIte]
    grind
  refine .inl ⟨0, fun _ => false, 0, ⟨hpC, fun j hj => ⟨fun _ => ?_, fun h => by cases h⟩⟩, ?_, ?_, ?_, ?_⟩
  · show 1 / 2 ≤ poolFrac N C K (K j)
    unfold poolFrac
    rw [sum_ite_inj hL.k_inj]
    have hk : ∃ i < N, K j = K i := ⟨j, hj, rfl⟩
    simp only [hk, hL.k_c j hj, ↓reduceIte]
    grind
  · show 0 < poolFrac N C K C ∧ _ = (m.initVal C, 0)
    rw [hpC, hC0]
    exact ⟨by grind, rfl⟩
  · rintro p ⟨-, rfl⟩
    exact Nat.le_refl 0
  · exact (List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr fun _ _ => by simp)).symm
  · exact Nat.le_refl 0

/-- **Initial erasure of the spinlock counter** with the resource
specification of `SwpSpec.lean`: threads `threadRes`, the pool `poolRes`
under `lockPred` in `spinGhost`. -/
theorem erase_init_lockPred {states : List I.State} {initMem : List (Loc × Val)} {N : Nat}
    {Lk C : Loc} {K F : Nat → Loc} (T : Nat → Prop) (hL : SpinLocs N Lk C K F) (hN : states.length = N)
    (hN0 : 0 < N) (hC0 : (Config.init states initMem).mem.initVal C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal Lk = 0) :
    Erase (threadRes (Config.init states initMem).mem N Lk K F)
      (spinGhost Lk (lockPred N Lk C K F) (poolRes (Config.init states initMem).mem N C K)) T
      (Config.init states initMem) := by
  subst hN
  have hI : ((threadsRes (threadRes (Config.init states initMem).mem states.length Lk K F) states.length).op
      (poolRes (Config.init states initMem).mem states.length C K)).IsInit (Config.init states initMem).mem :=
    (Res.IsInit.threadsRes fun _ _ => Res.IsInit.initOf _ _).op (Res.IsInit.initOf _ _)
  refine erase_init T (valid_init _ hL hN0) hI.2 (fun x hq p => ?_) ?_
  · rw [hI.1]
    exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  · rw [hLk0]
    exact lockPred_pool _ hL hC0

/-- **`counter = N` from Theorem 1′ with the spinlock's initial state**:
`counter_of_theorem1Pure` with initial erasure, the initial ghost's facts and
the pool specification discharged (`erase_init_lockPred`, `pend_init`,
`spinGhost_*`, `poolSpec_lockPred`). What remains: Theorem 1′, its scope,
(O5) and the workers' `NPSafe` from the initial resources `threadRes`. -/
theorem counter_init [I.LawfulState] {A : Arch} {fuel : Nat} (hT : Theorem1IIPure (I := I) A fuel)
    {states : List I.State} {initMem : List (Loc × Val)} {N : Nat} {Lk C : Loc} {K F : Nat → Loc}
    (hL : SpinLocs N Lk C K F) (hN : states.length = N) (hN0 : 0 < N)
    (hC0 : (Config.init states initMem).mem.initVal C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal Lk = 0)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hpure : PromisePure A fuel states initMem
      (spinGhost Lk (lockPred N Lk C K F) (poolRes (Config.init states initMem).mem N C K)).rel)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A (fun _ r _ => Post N Lk K r) tid n m True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N Lk K F tid)
      (spinGhost Lk (lockPred N Lk C K F) (poolRes (Config.init states initMem).mem N C K)))
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal C = BitVec.ofNat 128 N :=
  counter_of_theorem1Pure hT hH (erase_init_lockPred _ hL hN hN0 hC0 hLk0) pend_init hpure hsafe hN hN0
    spinGhost_rel_Lk spinGhost_upd_Lk (by rw [spinGhost_acqTab_length]; exact Nat.zero_lt_one)
    spinGhost_acqPred_zero poolSpec_lockPred hc hf

end Spinlock

end Kraken.Promising.SLR
