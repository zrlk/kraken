/-
**Part 1: the ticket lock's resources, ghost
state and final argument** (`ticketlock2.kl`). ISA-neutral.

The program: `ldadda` a ticket `t` from `next` (`X`), spin with `ldar` on
`owner` (`O`) until its low word is `t`, increment the counter (`C`) with a
plain load/store pair, release with `stlr` of `t + 1` to `owner`.

- **Dispenser** `disp P`: `next`/`owner` with tickets `tk n = n` for
  `n < N + 1` (one spare ticket, `N`, never handed out: its slot carries the
  final critical section) and dispenser update id `N + 1`.
- **Predicates.** `CS P n V R` (the critical-section resource at turn `n`):
  all of `C`, every counter write at or below `V`, and either the counter's
  maximal write has value `n` (`Good`) or a positive share of `O` (`Bad`: what
  an unclean release gives). `owner`'s release predicate `relO`: `CS` at the
  low word of the value. Ticket `n`'s acquire predicate `qPred P n`: `CS n` at
  value `n`, nothing at any other value. The dispenser's predicate `pdPred`:
  anything at the initial message or above the last ticket, nothing else
  (closed under dropping tokens).
- **Initial state.** `tkGhost`: `owner`'s initial message in release mode with
  one slot per ticket id (`0`: all of `C`, the others empty) and the
  dispenser slot (`N + 1`: all the tokens); `thRes`: thread `j` holds `1/N`
  of `next` and of `owner` and all of its ghost location `kLoc j` (never
  accessed; it tells the threads apart in the thread-uniform postcondition).
  `erase_tkInit` (`Erase.init`), `tx_tkInit` (`TX`).
- **Final argument** `ticket_final`: the threads hold all of `owner`; their
  `next` writes have distinct writers, so their ranks are `1..N`
  (`CountInv`); the writer of rank `N` released `owner` with low word `N`; that
  message is in release mode and carries the slot of the spare ticket `N`
  (never handed: no `next` message has rank above `N`), whose resource is
  `CS N`, `Good` since no slot holds a share of `owner`.

`sum_ite_inj`, `sum_add3`: `Spinlock`'s (`SLR/SpinInitRes.lean`; now public; no local copies).
-/
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.DispenserFresh

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

/-! ## Locations -/

/-- The low word of a value (what the 32-bit `ldar`/`cmp` see). -/
def lo (v : Val) : Nat := (BitVec.setWidth 32 v).toNat

theorem lo_lt (v : Val) : lo v < 2 ^ 32 := (BitVec.setWidth 32 v).isLt

/-- The ticket lock's parameters: `N` threads, `next`, `owner`, the counter. -/
structure Sys where
  N : Nat
  X : Loc
  O : Loc
  C : Loc

/-- Thread `j`'s ghost location (never accessed by the program). -/
def kLoc (j : Nat) : Loc := ⟨0, 2 * j + 5⟩

theorem kLoc_inj {i j : Nat} (h : kLoc i = kLoc j) : i = j := by
  simp only [kLoc, Loc.mk.injEq] at h; omega_t

/-- The locations are distinct 4-byte words, `0 < N`, `N + 1 < 2 ^ 32`. -/
structure Locs (P : Sys) : Prop where
  xo : P.X ≠ P.O
  xc : P.X ≠ P.C
  oc : P.O ≠ P.C
  xb : P.X.bytes = 4
  ob : P.O.bytes = 4
  cb : P.C.bytes = 4
  n0 : 0 < P.N
  n32 : P.N + 1 < 2 ^ 32

theorem kLoc_ne {l : Loc} (hl : l.bytes = 4) (j : Nat) : kLoc j ≠ l := by
  intro h; rw [← h] at hl; simp only [kLoc] at hl; omega_t

/-- **The dispenser**: tickets `0..N` of `owner`, update id `N + 1`. -/
def disp (P : Sys) (h : P.X ≠ P.O) : Dispenser where
  x := P.X
  o := P.O
  ιD := P.N + 1
  tk := id
  N := P.N + 1
  xo := h
  tkInj _ _ _ _ h := h
  tkNe _ hn := Nat.ne_of_lt hn

/-! ## Predicates -/

/-- **The critical-section resource at turn `n`**, at view `V`. -/
def CS (P : Sys) (n : Nat) (V : View) (R : Res) : Prop :=
  (R.wr P.C).q = 1 ∧ (∀ p, (R.wr P.C).X p → p.2 ≤ V) ∧
    ((∃ val ts, (R.wr P.C).X (val, ts) ∧ val.toNat = n ∧ ∀ p, (R.wr P.C).X p → p.2 ≤ ts) ∨
      0 < (R.wr P.O).q)

/-- `owner`'s release predicate: `CS` at the low word. -/
def relO (P : Sys) : Pred := ⟨fun v _ V R => CS P (lo v) V R, fun _ _ _ _ _ _ h => h⟩

/-- Ticket `n`'s acquire predicate. -/
def qPred (P : Sys) (n : Nat) : Pred :=
  ⟨fun v _ V R => (lo v = n → CS P n V R) ∧ (lo v ≠ n → R = Res.unit), fun _ _ _ _ _ _ h => h⟩

/-- The dispenser's predicate. -/
def pdPred (P : Sys) : Pred :=
  ⟨fun v _ V R => V = 0 ∨ P.N + 1 ≤ lo v ∨ R = Res.unit, fun _ _ _ _ _ _ h => h⟩

theorem cs_not_unit {P : Sys} {n : Nat} {V : View} : ¬ CS P n V Res.unit := fun h => by
  have := h.1; simp [Res.unit, Perm.unit] at this

theorem relO_impure (P : Sys) (v : Val) : ¬ Pred.Pure (relO P) v := fun h =>
  cs_not_unit (h (default : Memory) 0)

/-! ## Initial resources and ghost -/

private theorem ite_nonneg' {p : Prop} [Decidable p] {a : Rat} (ha : 0 ≤ a) : 0 ≤ (if p then a else 0) := by
  split
  · exact ha
  · exact Rat.le_refl

theorem invN_nonneg (N : Nat) : (0 : Rat) ≤ 1 / (N : Rat) := by
  rw [Rat.div_def, Rat.one_mul, Rat.inv_def]
  exact Rat.divInt_nonneg (by omega_t) (Rat.num_nonneg.mpr Rat.natCast_nonneg)

/-- Thread `j`'s initial fractions: `1/N` of `next` and `owner`, all of
`kLoc j`. -/
def thFrac (P : Sys) (j : Nat) (l : Loc) : Rat :=
  (if l = P.X then 1 / (P.N : Rat) else 0) + (if l = P.O then 1 / (P.N : Rat) else 0) +
    (if l = kLoc j then 1 else 0)

theorem thFrac_nonneg (P : Sys) (j : Nat) (l : Loc) : 0 ≤ thFrac P j l := by
  unfold thFrac
  have := ite_nonneg' (p := l = P.X) (invN_nonneg P.N)
  have := ite_nonneg' (p := l = P.O) (invN_nonneg P.N)
  have := ite_nonneg' (p := l = kLoc j) (a := 1) (by grind)
  grind

/-- Thread `j`'s initial resource. -/
def thRes (m : Memory) (P : Sys) (j : Nat) : Res := Res.initOf m (thFrac P j) (thFrac_nonneg P j)

/-- The resource of ticket `0`'s initial slot: all of the counter. -/
def cs0 (m : Memory) (P : Sys) : Res :=
  Res.initOf m (fun l => if l = P.C then 1 else 0) fun _ => ite_nonneg' (by grind)

/-- The dispenser's initial resource: every ticket. -/
def toks (P : Sys) : Res := ⟨fun _ => Perm.unit, fun l j => if l = P.O ∧ j < P.N + 1 then 1 else 0⟩

/-- **The initial ghost state.** -/
def tkGhost (m : Memory) (P : Sys) : Ghost where
  rel l := if l = P.O then relO P else Pred.emp
  acqTab := (List.range (P.N + 1)).map (qPred P) ++ [pdPred P]
  u := ⟨(P.O, 0), 0, cs0 m P⟩ :: ⟨(P.O, 0), P.N + 1, toks P⟩ ::
    (List.range P.N).map fun j => ⟨(P.O, 0), j + 1, Res.unit⟩
  relMsgs := [(P.O, 0)]
  pend := []
  upd l := if l = P.O then [P.N + 1] else []
  claims := []

variable {m : Memory} {P : Sys}

theorem tkGhost_rel_O : (tkGhost m P).rel P.O = relO P := by simp [tkGhost]

theorem tkGhost_rel_ne {l : Loc} (h : l ≠ P.O) : (tkGhost m P).rel l = Pred.emp := by simp [tkGhost, h]

theorem tkGhost_acqTab_length : (tkGhost m P).acqTab.length = P.N + 2 := by simp [tkGhost]

theorem tkGhost_acqPred_q {n : Nat} (hn : n < P.N + 1) : (tkGhost m P).acqPred n = qPred P n := by
  simp only [tkGhost, Ghost.acqPred, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega_t)]
  simp [hn]

theorem tkGhost_acqPred_pd : (tkGhost m P).acqPred (P.N + 1) = pdPred P := by
  simp only [tkGhost, Ghost.acqPred, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem tkGhost_upd_O : (tkGhost m P).upd P.O = [P.N + 1] := by simp [tkGhost]

theorem tkGhost_upd_ne {l : Loc} (h : l ≠ P.O) : (tkGhost m P).upd l = [] := by simp [tkGhost, h]

theorem tkGhost_pend : ∀ ts, ts ∉ (tkGhost m P).pend := fun _ h => by cases h

private theorem prod_units (n : Nat) : Res.prod ((List.range n).map fun _ => Res.unit) = Res.unit := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, Res.prod_append, ih]; simp [Res.op_unit]

theorem tkGhost_slotsRes : (tkGhost m P).slotsRes = (cs0 m P).op (toks P) := by
  have : (tkGhost m P).slotsRes = (cs0 m P).op ((toks P).op (Res.prod ((List.range P.N).map fun _ => Res.unit))) := by
    simp only [Ghost.slotsRes, tkGhost, List.map_cons, List.map_map, Res.prod_cons]; rfl
  rw [this, prod_units, Res.op_unit]

/-- The threads' total initial fraction of `l`. -/
theorem q_threads_tk (l : Loc) :
    ((threadsRes (thRes m P) P.N).wr l).q =
      (P.N : Rat) * (if l = P.X then 1 / (P.N : Rat) else 0) +
        (P.N : Rat) * (if l = P.O then 1 / (P.N : Rat) else 0) + (if ∃ j < P.N, l = kLoc j then 1 else 0) := by
  rw [q_threadsRes]
  show ((List.range P.N).map fun j => thFrac P j l).sum = _
  unfold thFrac
  rw [Spinlock.sum_add3 (fun _ => if l = P.X then 1 / (P.N : Rat) else 0) (fun _ => if l = P.O then 1 / (P.N : Rat) else 0)
      (fun i => if l = kLoc i then 1 else 0), Spinlock.sum_ite_inj (fun i _ j _ h => kLoc_inj h), sum_range_const,
    sum_range_const]

section Init

variable {states : List I.State} {initMem : List (Loc × Val)}

theorem total_tk (rF : Nat → Res) :
    total rF (tkGhost m P) (Config.init states initMem) =
      (threadsRes rF states.length).op ((cs0 m P).op (toks P)) := by
  rw [total, tkGhost_slotsRes, Config.init_size]

theorem total_tk_acq {m' : Memory} (hN : states.length = P.N) (l : Loc) (ι : PredId) :
    (total (thRes m' P) (tkGhost m P) (Config.init states initMem)).acq l ι = (toks P).acq l ι := by
  rw [total_tk, hN]
  have h1 := (Res.IsInit.threadsRes (m := m') (rF := thRes _ P) (n := P.N)
    (fun _ _ => Res.IsInit.initOf _ _)).2 l ι
  show (threadsRes _ P.N).acq l ι + ((cs0 m P).acq l ι + (toks P).acq l ι) = _
  rw [h1]; simp [cs0, Res.initOf]

theorem total_tk_wr {m' : Memory} (hN : states.length = P.N) (l : Loc) :
    (total (thRes m' P) (tkGhost m P) (Config.init states initMem)).wr l =
      ((threadsRes (thRes m' P) P.N).op (cs0 m P)).wr l := by
  rw [total_tk, hN]
  show ((threadsRes _ P.N).wr l).op ((cs0 m P).wr l |>.op Perm.unit) = _
  rw [Perm.op_unit]; rfl

/-- One predicate of the list takes `R`, the others the empty resource. -/
theorem sepList_one {v : Val} {mm : Memory} {V : View} {R : Res} :
    ∀ (Ps : List Pred) (i : Nat) (hi : i < Ps.length), (Ps[i]'hi).P v mm V R →
      (∀ j (hj : j < Ps.length), j ≠ i → (Ps[j]'hj).P v mm V Res.unit) → Pred.SepList Ps v mm V R
  | [], _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | φ :: Ps, 0, _, hR, hu =>
    ⟨R, Res.unit, (Res.op_unit R).symm, hR, sepList_unit Ps fun j hj => hu (j + 1) (by simp; omega_t) (by omega_t)⟩
  | φ :: Ps, i + 1, hi, hR, hu =>
    ⟨Res.unit, R, (Res.unit_op R).symm, hu 0 (by simp) (by omega_t),
      sepList_one Ps i (by simp at hi; omega_t) hR fun j hj hne => hu (j + 1) (by simp; omega_t) (by omega_t)⟩
where
  sepList_unit : ∀ (Ps : List Pred), (∀ j (hj : j < Ps.length), (Ps[j]'hj).P v mm V Res.unit) →
      Pred.SepList Ps v mm V Res.unit
    | [], _ => rfl
    | φ :: Ps, h => ⟨Res.unit, Res.unit, (Res.op_unit _).symm, h 0 (by simp),
        sepList_unit Ps fun j hj => h (j + 1) (by simp; omega_t)⟩

/-- **Initial erasure** of the ticket lock. -/
theorem erase_tkInit (T : Nat → Prop) (hL : Locs P) (hN : states.length = P.N)
    (hm : (Config.init states initMem).mem = m) (hC0 : m.initVal P.C = 0) (hO0 : m.initVal P.O = 0) :
    Erase (thRes m P) (tkGhost m P) T (Config.init states initMem) := by
  have hacq := total_tk_acq (m := m) (m' := m) (P := P) (states := states) (initMem := initMem) hN
  have hwr := total_tk_wr (m := m) (m' := m) (P := P) (states := states) (initMem := initMem) hN
  have hI : ((threadsRes (thRes m P) P.N).op (cs0 m P)).IsInit m :=
    (Res.IsInit.threadsRes fun _ _ => Res.IsInit.initOf _ _).op (Res.IsInit.initOf _ _)
  have hN' : (P.N : Rat) ≠ 0 := by have := Nat.pos_iff_ne_zero.mp hL.n0; exact_mod_cast this
  have h1 : (P.N : Rat) * (1 / P.N) = 1 := by grind
  have hkx : ¬ ∃ j < P.N, P.X = kLoc j := fun ⟨j, _, h⟩ => kLoc_ne hL.xb j h.symm
  have hko : ¬ ∃ j < P.N, P.O = kLoc j := fun ⟨j, _, h⟩ => kLoc_ne hL.ob j h.symm
  have hkc : ¬ ∃ j < P.N, P.C = kLoc j := fun ⟨j, _, h⟩ => kLoc_ne hL.cb j h.symm
  -- the acquire ids held at `owner`
  have hids : ∀ l, (tkGhost m P).acqIds (total (thRes m P) (tkGhost m P) (Config.init states initMem)).acq l =
      if l = P.O then List.range (P.N + 1) else [] := by
    intro l
    simp only [Ghost.acqIds, tkGhost_acqTab_length, hacq, toks]
    by_cases hl : l = P.O
    · subst hl
      simp only [true_and, ↓reduceIte, List.range_succ (n := P.N + 1), List.filter_append]
      rw [List.filter_eq_self.mpr (fun a ha => by simp at ha; simp [ha])]
      simp
    · simp [hl]
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- validity
    refine ⟨fun l => ?_, fun l ι => ?_⟩
    · rw [hwr]
      show ((threadsRes (thRes m P) P.N).wr l).q + (if l = P.C then 1 else 0) ≤ 1
      rw [q_threads_tk]
      by_cases hx : l = P.X
      · subst hx; simp [hkx, hL.xo, hL.xc]; grind
      · by_cases ho : l = P.O
        · subst ho; simp [hko, hL.oc, hx]; grind
        · by_cases hc : l = P.C
          · subst hc; simp [hkc, hx, ho]; grind
          · by_cases hk : ∃ j < P.N, l = kLoc j <;> simp [hk, hx, ho, hc] <;> grind
    · rw [hacq]; simp only [toks]
      by_cases hh : l = P.O ∧ ι < P.N + 1 <;> simp [hh]
  · -- slot ids
    intro s hs
    simp only [tkGhost, List.mem_cons, List.mem_map, List.mem_range] at hs
    rw [tkGhost_acqTab_length]
    rcases hs with rfl | rfl | ⟨j, hj, rfl⟩ <;> simp <;> omega_t
  · -- held ids
    intro l ι h
    rw [hacq] at h
    simp only [toks] at h
    rw [tkGhost_acqTab_length]
    by_cases hh : l = P.O ∧ ι < P.N + 1
    · have := hh.2; omega_t
    · simp [hh] at h
  · -- `relAcq`
    intro l v mm V r hr
    rw [Ghost.acqPreds, hids]
    by_cases hl : l = P.O
    · subst hl
      rw [tkGhost_rel_O] at hr
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), Ghost.updPreds, tkGhost_upd_O, List.map_singleton, tkGhost_acqPred_pd,
        List.map_congr_left fun n hn => tkGhost_acqPred_q (m := m) (P := P) (List.mem_range.mp hn)]
      refine sepList_one _ (min (lo v) (P.N + 1)) (by simp; omega_t) ?_ ?_
      · by_cases hlt : lo v < P.N + 1
        · rw [List.getElem_append_left (by simp; omega_t)]
          simp only [List.getElem_map, List.getElem_range, Nat.min_eq_left (Nat.le_of_lt hlt)]
          exact ⟨fun _ => hr, fun h => absurd rfl h⟩
        · rw [List.getElem_append_right (by simp; omega_t)]
          simp only [List.length_map, List.length_range, Nat.min_eq_right (Nat.le_of_not_lt hlt),
            Nat.sub_self, List.getElem_cons_zero]
          exact .inr (.inl (by omega_t))
      · intro j hj hne
        by_cases hjl : j < P.N + 1
        · rw [List.getElem_append_left (by simp; omega_t)]
          simp only [List.getElem_map, List.getElem_range]
          refine ⟨fun h => ?_, fun _ => rfl⟩
          exfalso; apply hne; omega_t
        · rw [List.getElem_append_right (by simp; omega_t)]
          simp only [List.length_map, List.length_range]
          have : j - (P.N + 1) = 0 := by simp at hj; omega_t
          simp only [this, List.getElem_cons_zero]
          exact .inr (.inr rfl)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hl)]
      rw [tkGhost_rel_ne hl] at hr
      rw [Ghost.updPreds, tkGhost_upd_ne hl]
      exact hr
  · -- write sets
    intro l hq p
    rw [hwr] at hq ⊢
    rw [hI.1, hm]
    exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  · -- pure relaxed initial messages
    intro l hl
    have hne : l ≠ P.O := fun h => hl (by subst h; simp [tkGhost])
    rw [tkGhost_rel_ne hne]; exact Pred.emp_pure _
  · intro k hk; simp [tkGhost] at hk; rw [hk]
  · -- slots distinct
    simp only [tkGhost, List.map_cons, List.map_map]
    refine List.nodup_cons.mpr ⟨by simp, List.nodup_cons.mpr ⟨by simp,
      Dispenser.nodup_map_of_inj _ List.nodup_range fun a _ b _ h => by simp at h; omega_t⟩⟩
  · -- slot domain
    intro k ι
    rw [hacq]
    simp only [tkGhost, toks, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      rcases hs with rfl | rfl | ⟨j, hj, rfl⟩ <;> simp <;> omega_t
    · rintro ⟨rfl, h⟩
      have hι : ι ≤ P.N + 1 := by
        rcases h with h | h
        · by_cases hh : ι < P.N + 1
          · omega_t
          · simp [hh] at h
        · simp at h; omega_t
      by_cases h0 : ι = 0
      · exact ⟨_, .inl rfl, rfl, h0.symm⟩
      · by_cases hN1 : ι = P.N + 1
        · exact ⟨_, .inr (.inl rfl), rfl, hN1.symm⟩
        · exact ⟨⟨(P.O, 0), ι, Res.unit⟩, .inr (.inr ⟨ι - 1, by omega_t, by simp; omega_t⟩), rfl, rfl⟩
  · -- slot predicates at the initial value
    intro s hs
    simp only [tkGhost, List.mem_cons, List.mem_map, List.mem_range] at hs
    rw [hm]
    have hlo : lo (m.initVal P.O) = 0 := by rw [hO0]; rfl
    rcases hs with rfl | rfl | ⟨j, hj, rfl⟩
    · rw [tkGhost_acqPred_q (by omega_t)]
      refine ⟨fun _ => ⟨?_, ?_, .inl ⟨0, 0, ?_, rfl, ?_⟩⟩, fun h => absurd hlo h⟩
      · simp [cs0, Res.initOf, Perm.init]
      · rintro p ⟨-, rfl⟩; exact Nat.le_refl 0
      · exact ⟨by simp <;> grind, by rw [hC0]⟩
      · rintro p ⟨-, rfl⟩; exact Nat.le_refl 0
    · rw [tkGhost_acqPred_pd]; exact .inl rfl
    · rw [tkGhost_acqPred_q (by omega_t)]
      exact ⟨fun h => absurd (hlo.symm.trans h) (by omega_t), fun _ => rfl⟩
  · -- update ids
    intro l
    by_cases hl : l = P.O
    · subst hl
      rw [tkGhost_upd_O]
      refine ⟨by simp, fun ι hι => ?_⟩
      simp only [List.mem_singleton] at hι
      subst hι
      exact ⟨by rw [tkGhost_acqTab_length]; omega_t, by rw [hacq]; simp [toks]⟩
    · rw [tkGhost_upd_ne hl]; simp

/-- **The extension `TX` at the start.** -/
theorem tx_tkInit (hL : Locs P) (hN : states.length = P.N)
    (hX0 : (Config.init states initMem).mem.initVal P.X = 0) :
    (disp P hL.xo).TX (tkGhost m P) (Config.init states initMem) := by
  have hC : (disp P hL.xo).CountInv (Config.init states initMem : Config I) :=
    SingleRmw.countInv_init hX0 (by simp only [disp]; omega_t)
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, hC.monoX⟩, hC⟩
  · refine ⟨⟨(P.O, 0), P.N + 1, toks P⟩, by simp [tkGhost], ⟨rfl, rfl⟩, fun n hn => ⟨?_, fun _ => ?_⟩⟩
    · rintro ⟨⟨tr, tw, v, h, -⟩, -⟩; cases h
    · simp only [disp] at hn ⊢; simp [toks, hn]
  · simp [tkGhost, disp]
  · simp [Ghost.Claimed, tkGhost]
  · intro v mm V r ι h
    simp only [disp] at h ⊢
    rw [tkGhost_acqPred_pd] at h ⊢
    rcases h with h | h | rfl
    · exact .inl h
    · exact .inr (.inl h)
    · refine .inr (.inr ?_)
      apply Res.ext
      · rfl
      · funext y j; simp [dropTk, Res.unit]

end Init

/-! ## The final argument -/

/-- **The workers' postcondition** (thread-uniform): at least `1/N` of
`owner`, and the whole ghost location of some `j` such that `j` wrote a
message to `next` whose value is the low word of some `owner` message. -/
def TPost (P : Sys) (c : Config I) (r : Res) : Prop :=
  1 / (P.N : Rat) ≤ (r.wr P.O).q ∧ ∃ j, 1 ≤ (r.wr (kLoc j)).q ∧ ∃ tw w, c.mem.get? tw = some w ∧
    w.loc = P.X ∧ w.tid = j ∧ ∃ ts v, c.mem.read? P.O ts = some v ∧ lo v = w.val.toNat

section Count

variable {D : Dispenser} {c : Config I}

/-- Every count of `x` is at most the number of threads. -/
theorem _root_.Kraken.Promising.SLR.Dispenser.CountInv.count_le (h : D.CountInv c) (n : Nat) : D.xCount c.mem n ≤ c.threads.size := by
  have := Dispenser.xCount_le_of_writers (D := D) (mem := c.mem) (n := n) (S := c.threads.size + 1)
    (j₀ := c.threads.size) (by omega_t)
    (fun ts w _ _ hw hl => by have := h.wlt ts w hw hl; exact ⟨by omega_t, by omega_t⟩) h.wdist
  omega_t

/-- **The top rank**: messages to `x` at `tw i` (`i < size`) with pairwise
distinct writers include one of rank `size`. -/
theorem _root_.Kraken.Promising.SLR.Dispenser.CountInv.top_rank (h : D.CountInv c) {n : Nat}
    (hn : c.threads.size = n) (hn0 : 0 < n) (tw : Nat → Time) (w : Nat → Msg)
    (hw : ∀ i < n, c.mem.get? (tw i) = some (w i) ∧ (w i).loc = D.x)
    (hinj : ∀ i < n, ∀ j < n, (w i).tid = (w j).tid → i = j) :
    ∃ i < n, D.xCount c.mem (tw i) = n := by
  have hpos : ∀ i < n, 1 ≤ D.xCount c.mem (tw i) := fun i hi => by
    obtain ⟨hg, hl⟩ := hw i hi
    have h0 : 0 < tw i := Nat.pos_of_ne_zero fun e => by rw [e, Memory.get?_zero] at hg; cases hg
    have := Dispenser.xCount_lt_of_xAt (D := D) c.mem h0 (Dispenser.xAt_iff.mpr ⟨_, hg, hl⟩)
    omega_t
  let f := fun i => D.xCount c.mem (tw i) - 1
  have hnd : ((List.range n).map f).Nodup := by
    refine Dispenser.nodup_map_of_inj f List.nodup_range fun a ha b hb he => ?_
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    have he' : D.xCount c.mem (tw a) = D.xCount c.mem (tw b) := by
      have := hpos a ha'; have := hpos b hb'; simp only [f] at he; omega_t
    have hts : tw a = tw b := by
      rcases Nat.lt_trichotomy (tw a) (tw b) with hlt | heq | hgt
      · have := Dispenser.xCount_lt_of_xAt (D := D) c.mem hlt
          (Dispenser.xAt_iff.mpr ⟨_, (hw b hb').1, (hw b hb').2⟩)
        omega_t
      · exact heq
      · have := Dispenser.xCount_lt_of_xAt (D := D) c.mem hgt
          (Dispenser.xAt_iff.mpr ⟨_, (hw a ha').1, (hw a ha').2⟩)
        omega_t
    have hwe : w a = w b := by
      have h1 := (hw a ha').1; have h2 := (hw b hb').1
      rw [hts, h2] at h1; exact (Option.some.inj h1).symm
    exact hinj a ha' b hb' (by rw [hwe])
  have hlt : ∀ j ∈ (List.range n).map f, j < n := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have := h.count_le (tw i)
    have := hpos i (List.mem_range.mp hi)
    simp only [f]; omega_t
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (pigeonhole hnd hlt (by simp) (n - 1) (by omega_t))
  have := hpos i (List.mem_range.mp hi)
  simp only [f] at he
  exact ⟨i, List.mem_range.mp hi, by have := h.count_le (tw i); omega_t⟩

end Count

/-- **Adequacy of the ticket lock**: at a final configuration with full
erasure, a world above `tkGhost`, the extension `TX` and every thread's
`TPost`, the counter's final value is the number of threads. -/
theorem ticket_final {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (hL : Locs P) {m₀ : Memory}
    (E : Erase rF g T c) (hf : c.final = true) (hN : c.threads.size = P.N) (hle : (tkGhost m₀ P).Le g)
    (hTX : (disp P hL.xo).TX g c) (hpost : ∀ i < P.N, TPost P c (rF i)) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N := by
  have hN0 := hL.n0
  -- the threads hold the whole of `owner`, the slots none of it
  have hsumO : 1 ≤ ((threadsRes rF c.threads.size).wr P.O).q := by
    rw [q_threadsRes, hN]
    have h := sum_range_ge P.N (1 / P.N) _ fun j hj => (hpost j hj).1
    have : (P.N : Rat) ≠ 0 := by have := Nat.pos_iff_ne_zero.mp hN0; exact_mod_cast this
    grind
  have hslotO : (g.slotsRes.wr P.O).q = 0 := by
    have h1 := E.q_le_one P.O
    rw [q_total] at h1
    have := (g.slotsRes.wr P.O).nonneg
    grind
  have hsO : ∀ s ∈ g.u, ¬ 0 < (s.res.wr P.O).q := fun s hs h => by
    have := (slotsRes_sub hs).q_le P.O; grind
  -- every thread's message to `next`, with distinct writers
  have hex : ∀ i, ∃ p : Nat × Time × Msg, i < P.N → 1 ≤ ((rF i).wr (kLoc p.1)).q ∧
      c.mem.get? p.2.1 = some p.2.2 ∧ p.2.2.loc = P.X ∧ p.2.2.tid = p.1 ∧
      ∃ ts v, c.mem.read? P.O ts = some v ∧ lo v = p.2.2.val.toNat := fun i =>
    if hi : i < P.N then
      match hpost i hi with
      | ⟨_, j, hk, tw, w, hg, hl, ht, ho⟩ => ⟨(j, tw, w), fun _ => ⟨hk, hg, hl, ht, ho⟩⟩
    else ⟨(0, 0, default), fun h => absurd h hi⟩
  let F := fun i => Classical.choose (hex i)
  have hF : ∀ i < P.N, _ := fun i hi => Classical.choose_spec (hex i) hi
  have hinj : ∀ i < P.N, ∀ j < P.N, (F i).2.2.tid = (F j).2.2.tid → i = j := by
    intro i hi j hj he
    refine Classical.byContradiction fun hne => ?_
    have := E.q_add_le_one (hN ▸ hi) (hN ▸ hj) hne (kLoc (F i).1)
    have h1 := (hF i hi).1
    have h2 := (hF j hj).1
    rw [← (hF j hj).2.2.2.1, ← he, (hF i hi).2.2.2.1] at h2
    grind
  obtain ⟨i, hi, hrank⟩ := hTX.2.top_rank hN hN0 (fun i => (F i).2.1) (fun i => (F i).2.2)
    (fun i hi => ⟨(hF i hi).2.1, (hF i hi).2.2.1⟩) hinj
  obtain ⟨-, hg, hl, -, ts, v, hv, hlo⟩ := hF i hi
  rw [hTX.2.rank _ _ hg hl, hrank] at hlo
  -- the `owner` message of low word `N` is in release mode
  have hrelO : g.rel P.O = relO P := by rw [hle.rel]; exact tkGhost_rel_O
  have hmsg : (P.O, ts) ∈ g.relMsgs := Classical.byContradiction fun hn => by
    have hp := E.pure P.O ts v hv hn
    rw [hrelO] at hp
    exact relO_impure P v hp
  -- the spare ticket `N` is still in the dispenser
  have hcnt := hTX.2.count_le (c := c)
  obtain ⟨s, hs, -, htk⟩ := hTX.1.disp.slot
  have hnh : ¬ (disp P hL.xo).Handed g c.mem P.N := by
    rintro ⟨tr, tw, v', hcl, hrd, hv'⟩
    obtain ⟨hlt, w', hw', hl', -, -⟩ := E.claimsAt _ tw hcl
    have h1 := hTX.2.read_rank hrd
    have h2 := Dispenser.xCount_lt_of_xAt (D := disp P hL.xo) c.mem hlt (Dispenser.xAt_iff.mpr ⟨w', hw', hl'⟩)
    have h3 := hcnt tw
    omega_t
  have hs1 : s.res.acq P.O P.N = 1 := (htk P.N (by simp only [disp]; omega_t)).2 fun h => hnh h.1
  have hacqT : (total rF g c).acq P.O P.N = 1 := by
    refine Nat.le_antisymm (E.valid.2 _ _) ?_
    obtain ⟨d, hd⟩ := sub_total_slot (rF := rF) (c := c) hs
    rw [hd]
    show 1 ≤ s.res.acq P.O P.N + d.acq P.O P.N
    omega_t
  obtain ⟨s', hs', hk', hid'⟩ := (E.slotsDom (P.O, ts) P.N).mpr ⟨hmsg, .inl hacqT⟩
  have hP := E.slotsPred s' hs' v (by rw [hk']; exact hv)
  rw [hid', Ghost.acqPred_of_prefix hle.acqTab (by rw [tkGhost_acqTab_length]; omega_t),
    tkGhost_acqPred_q (by omega_t)] at hP
  obtain ⟨hq1, -, hgood⟩ := hP.1 hlo
  obtain ⟨val, ts', hX, hval, hmax⟩ := hgood.resolve_right (hsO s' hs')
  -- confrontation: the slot's maximal counter element is the final value
  have hqC : 0 < ((total rF g c).wr P.C).q := by
    have := (sub_total_slot (rF := rF) (c := c) hs').q_le P.C
    rw [hq1] at this
    grind
  have hthC := E.unique_holder_slot hs' hq1
  have hfin : c.mem.finalVal P.C = val := by
    refine E.finalVal_of_max hf hqC ((sub_total_slot hs').X hX) fun p hp => ?_
    rcases X_total_cases hp with ⟨j, hj, hXj⟩ | ⟨s'', hs'', hXs⟩
    · exact absurd hXj (((rF j).wr P.C).zero (hthC j hj) p)
    · by_cases he : s'' = s'
      · subst he; exact hmax p hXs
      · have h2 := E.q_add_le_one_slots hs' hs'' he P.C
        rw [hq1] at h2
        exact absurd hXs ((s''.res.wr P.C).zero (by have := (s''.res.wr P.C).nonneg; grind) p)
  rw [hfin]
  apply BitVec.eq_of_toNat_eq
  rw [hval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hL.n32; omega_t)]

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.erase_tkInit
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tx_tkInit
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.ticket_final
