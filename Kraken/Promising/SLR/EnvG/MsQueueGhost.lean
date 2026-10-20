/-
Part 1: **the ownership plan of the Michael–Scott
queue** `msqueue1.kl` (one enqueuer of node `n1` with data `1`, one
dequeuer) on the adjacency link `EnvGCAdj` (`EnvG/AdjCore.lean`).
ISA-neutral.

## No value knowledge at write time

The enqueuer's `casal x5, x2, [x8]` writes `[x3 + 8]`, where `x3` was loaded
from `tail`; outside `cl` the environment gives no value knowledge, and an
RMW's permission (`RmwOkCAdj`) needs a positive fraction of the written
location without hypotheses. So the enqueuer holds a positive fraction of
**every** location (half of `head` and `tail`, all of the others); the
dequeuer holds the other halves of `head` and `tail`. As in the Treiber node proof, all
history reasoning happens at the final clean erasure
(`EnvG/MsQueueFinal.lean`): the release predicates record only **memory
facts** the writer has (its own reads), never loaded values. No `cl`, no
claim and no forwarding is used.

## The protocol: one predicate `form` at the queue words

`head`, `tail` and the two link words `[d + 8]`, `[n1 + 8]` (the *queue
words*) carry `form`; every other location has `Pred.emp`. `form` is impure
at every value (it requires the message to exist, `form_not_pure`), so every
message of a queue word is in release mode, and the dequeuer, holding the
acquire id `0` of each queue word, finds its slot at the final erasure. At a
non-initial message `(x, v)` at `V`:

- at a link word: `v` is the node `n1`, and the slot holds the node's data
  word frozen (`NodeFrozen`: `O ⋅ J` with `O` whole, its maximal write
  `(d, td)`, `td < V`, `D d`; `J` is what a successful `casal`'s claimed
  update slots may add at the environment, which the final validity
  empties);
- at `head` / `tail`: `v` is the node `n1` (the enqueuer's swing, or its link
  `casal` hitting `head`/`tail` at a junk address), or **provenance**
  (`Prov`): `v ≠ 0` (64 bits) is the value of a message of `[y + 8]` below
  `V`, where `y` is the value of a message of `head` or `tail` below `V`
  (both helping `casal`s and the dequeuer's swing of `head`).

## Plans

Both threads release every write to a queue word (`val := none`); the
enqueuer's entries at the link words give the data word (`gives := [dat]`),
all other entries give nothing.

Contents: `Params`, `QLocs`, `form` (`NodeFrozen`, `Prov`), `ghost₀`,
`planE`/`planD` (+ validity), the initial resources (`fracE`, `fracD`,
`tRes`) and `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.Treiber2Final

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-! ## Parameters -/

/-- The queue's parameters: `head` at `h`, `tail` at `t` (8 bytes each), the
dummy node `d` and the enqueued node `n1`; a node's data word is `[n]`
(4 bytes), its link `[n + 8]` (8 bytes). -/
structure Params where
  h : BitVec 64
  t : BitVec 64
  d : BitVec 64
  n1 : BitVec 64

namespace Params

variable (P : Params)

/-- `head`. -/
def head : Loc := ⟨P.h, 8⟩
/-- `tail`. -/
def tail : Loc := ⟨P.t, 8⟩
/-- The dummy node's link. -/
def dn : Loc := ⟨P.d + 8, 8⟩
/-- The enqueued node's link. -/
def nn : Loc := ⟨P.n1 + 8, 8⟩
/-- The enqueued node's data word. -/
def dat : Loc := ⟨P.n1, 4⟩
/-- The enqueuer's identity token (a ghost location: no access of the code
has `1` byte). -/
def tokE : Loc := ⟨P.h, 1⟩

/-- A link word. -/
def IsN (x : Loc) : Prop := x = P.dn ∨ x = P.nn
/-- A queue word. -/
def IsQ (x : Loc) : Prop := x = P.head ∨ x = P.tail ∨ x = P.dn ∨ x = P.nn

instance (x : Loc) : Decidable (P.IsN x) := by unfold IsN; infer_instance
instance (x : Loc) : Decidable (P.IsQ x) := by unfold IsQ; infer_instance

end Params

/-- The layout hypotheses: the four queue words are distinct, and so are
the two nodes. -/
structure QLocs (P : Params) : Prop where
  ht : P.h ≠ P.t
  hd : P.h ≠ P.d + 8
  hn : P.h ≠ P.n1 + 8
  td : P.t ≠ P.d + 8
  tn : P.t ≠ P.n1 + 8
  dn1 : P.d ≠ P.n1

namespace QLocs

variable {P : Params} (hL : QLocs P)
include hL

theorem head_tail : P.head ≠ P.tail := by simp [Params.head, Params.tail, hL.ht]
theorem head_dn : P.head ≠ P.dn := by
  simp only [Params.head, Params.dn, ne_eq, Loc.mk.injEq, and_true]; exact hL.hd
theorem head_nn : P.head ≠ P.nn := by
  simp only [Params.head, Params.nn, ne_eq, Loc.mk.injEq, and_true]; exact hL.hn
theorem tail_dn : P.tail ≠ P.dn := by
  simp only [Params.tail, Params.dn, ne_eq, Loc.mk.injEq, and_true]; exact hL.td
theorem tail_nn : P.tail ≠ P.nn := by
  simp only [Params.tail, Params.nn, ne_eq, Loc.mk.injEq, and_true]; exact hL.tn
theorem dn_nn : P.dn ≠ P.nn := by
  simp only [Params.dn, Params.nn, ne_eq, Loc.mk.injEq, and_true]
  intro h; exact hL.dn1 (by bv_omega)

theorem not_isN_head : ¬ P.IsN P.head := by
  rintro (h | h)
  · exact hL.head_dn h
  · exact hL.head_nn h

theorem not_isN_tail : ¬ P.IsN P.tail := by
  rintro (h | h)
  · exact hL.tail_dn h
  · exact hL.tail_nn h

end QLocs

section Distinct

variable (P : Params)

theorem dat_ne_of_8 {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ P.dat := by simp [Params.dat]
theorem tokE_ne_of_8 {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ P.tokE := by simp [Params.tokE]
theorem dat_tokE : P.dat ≠ P.tokE := by simp [Params.dat, Params.tokE]
theorem head_dat : P.head ≠ P.dat := dat_ne_of_8 P
theorem tail_dat : P.tail ≠ P.dat := dat_ne_of_8 P
theorem dn_dat : P.dn ≠ P.dat := dat_ne_of_8 P
theorem nn_dat : P.nn ≠ P.dat := dat_ne_of_8 P
theorem head_tokE : P.head ≠ P.tokE := tokE_ne_of_8 P
theorem tail_tokE : P.tail ≠ P.tokE := tokE_ne_of_8 P

theorem not_isQ_dat : ¬ P.IsQ P.dat := by
  rintro (h | h | h | h)
  · exact head_dat P h.symm
  · exact tail_dat P h.symm
  · exact dn_dat P h.symm
  · exact nn_dat P h.symm

theorem not_isQ_tokE : ¬ P.IsQ P.tokE := by
  rintro (h | h | h | h) <;> simp [Params.tokE, Params.head, Params.tail, Params.dn, Params.nn] at h

theorem isQ_of_isN {x : Loc} (h : P.IsN x) : P.IsQ x := by
  rcases h with h | h
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

end Distinct

/-! ## The predicates -/

/-- The data word's property: its low 32 bits are `1`. -/
def D (d : Val) : Prop := BitVec.setWidth 32 d = 1

/-- **The node frozen in a slot**: the data word's permission is `O ⋅ J`
with `O` whole, its maximal write `(d, td)` below `V` and `D d`. -/
def NodeFrozen (P : Params) (R : Res) (V : View) : Prop :=
  ∃ O J : Perm, R.wr P.dat = O.op J ∧ O.q = 1 ∧
    ∃ d td, O.X (d, td) ∧ (∀ p, O.X p → p.2 ≤ td) ∧ td < V ∧ D d

/-- **Provenance** of a value `v` written at `V`: its 64 bits are non-zero
and the 64 bits of a message of `[y + 8]` below `V`, where `y` is the value
of a message of `head` or `tail` below `V`. -/
def Prov (P : Params) (m : Memory) (V : View) (v : Val) : Prop :=
  BitVec.setWidth 64 v ≠ 0 ∧ ∃ x a y b y', (x = P.head ∨ x = P.tail) ∧ a < V ∧ m.read? x a = some y ∧ b < V ∧
    m.read? ⟨BitVec.setWidth 64 y + 8, 8⟩ b = some y' ∧ BitVec.setWidth 64 y' = BitVec.setWidth 64 v

theorem Prov.mono {P : Params} {m m' : Memory} (h : m.Prefix m') {V : View} {v : Val} (hp : Prov P m V v) :
    Prov P m' V v := by
  obtain ⟨hnz, x, a, y, b, y', hx, ha, hr, hb, hr', hy⟩ := hp
  exact ⟨hnz, x, a, y, b, y', hx, ha, Treiber2.read?_mono h hr, hb, Treiber2.read?_mono h hr', hy⟩

/-- **The predicate of the queue words** (`head`, `tail`, the links). -/
def form (P : Params) : Pred where
  P v m V R := V ≠ 0 → ∃ x w, m.get? V = some ⟨x, v, w⟩ ∧
    (P.IsN x → BitVec.setWidth 64 v = P.n1 ∧ NodeFrozen P R V) ∧
    (¬ P.IsN x → BitVec.setWidth 64 v = P.n1 ∨ Prov P m V v)
  mono v m m' V R hpre h := by
    intro hV
    obtain ⟨x, w, hg, h1, h2⟩ := h hV
    exact ⟨x, w, Memory.get?_of_prefix hpre.2 hg, h1, fun hx => (h2 hx).imp id (Prov.mono hpre)⟩

/-- `form` is impure at every value: it needs the message. -/
theorem form_not_pure (P : Params) (v : Val) : ¬ Pred.Pure (form P) v := by
  intro h
  obtain ⟨x, w, hg, -⟩ := h { init := [], msgs := #[] } 1 (by decide)
  simp [Memory.get?] at hg

/-! ## The initial ghost -/

/-- The queue words, as a list. -/
def qList (P : Params) : List Loc := [P.head, P.tail, P.dn, P.nn]

theorem mem_qList {P : Params} {x : Loc} : x ∈ qList P ↔ P.IsQ x := by
  simp [qList, Params.IsQ]

/-- **The initial ghost**: `form` at the queue words (`Pred.emp`
elsewhere); acquire table `[form]`; the initial messages of the queue words
in release mode with unit slots for id `0`; no update ids. -/
def ghost₀ (P : Params) : Ghost where
  rel x := if P.IsQ x then form P else Pred.emp
  acqTab := [form P]
  u := (qList P).map fun x => ⟨(x, 0), 0, Res.unit⟩
  relMsgs := (qList P).map fun x => (x, 0)
  pend := []
  upd _ := []
  claims := []

theorem ghost₀_rel_q {P : Params} {x : Loc} (h : P.IsQ x) : (ghost₀ P).rel x = form P := by
  simp [ghost₀, h]

theorem ghost₀_rel_ne {P : Params} {x : Loc} (h : ¬ P.IsQ x) : (ghost₀ P).rel x = Pred.emp := by
  simp [ghost₀, h]

theorem ghost₀_pend (P : Params) : ∀ ts, ts ∉ (ghost₀ P).pend := fun _ h => by cases h

/-! ## The plans -/

/-- **The enqueuer's plan**: every write to a queue word is a release; at
the links it gives the data word. -/
def planE (P : Params) : Plan :=
  ⟨[{ loc := P.head, gives := [] }, { loc := P.tail, gives := [] }, { loc := P.dn, gives := [P.dat] },
    { loc := P.nn, gives := [P.dat] }]⟩

/-- **The dequeuer's plan**: every write to a queue word is a release
giving nothing. -/
def planD (P : Params) : Plan :=
  ⟨[{ loc := P.head, gives := [] }, { loc := P.tail, gives := [] }, { loc := P.dn, gives := [] },
    { loc := P.nn, gives := [] }]⟩

theorem planE_valid (P : Params) : (planE P).Valid := by
  intro e he
  simp only [planE, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp [dn_dat, nn_dat]

theorem planD_valid (P : Params) : (planD P).Valid := by
  intro e he
  simp only [planD, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> simp

theorem planE_rel (P : Params) (l : Loc) (v : Val) : (planE P).rel l v = decide (P.IsQ l) := by
  simp only [planE, Plan.rel, Plan.find?, List.find?, Params.IsQ]
  by_cases h1 : l = P.head <;> by_cases h2 : l = P.tail <;> by_cases h3 : l = P.dn <;>
    by_cases h4 : l = P.nn <;> simp [h1, h2, h3, h4] <;> (repeat' split) <;> first | rfl | (simp only [decide_eq_true_eq] at *; simp_all)

theorem planD_rel (P : Params) (l : Loc) (v : Val) : (planD P).rel l v = decide (P.IsQ l) := by
  simp only [planD, Plan.rel, Plan.find?, List.find?, Params.IsQ]
  by_cases h1 : l = P.head <;> by_cases h2 : l = P.tail <;> by_cases h3 : l = P.dn <;>
    by_cases h4 : l = P.nn <;> simp [h1, h2, h3, h4] <;> (repeat' split) <;> first | rfl | (simp only [decide_eq_true_eq] at *; simp_all)

/-- The enqueuer's entry for a write to a queue word: the data word at the
links, nothing at `head`/`tail`. -/
theorem planE_find {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) :
    (planE P).find? l v = some { loc := l, gives := if P.IsN l then [P.dat] else [] } := by
  have h1 := hL.head_tail; have h2 := hL.head_dn; have h3 := hL.head_nn; have h4 := hL.tail_dn
  have h5 := hL.tail_nn; have h6 := hL.dn_nn
  rcases hl with rfl | rfl | rfl | rfl
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planE, Plan.find?, Params.IsN]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planE, Plan.find?, Params.IsN]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planE, Plan.find?, Params.IsN]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planE, Plan.find?, Params.IsN]

theorem planD_find {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) :
    (planD P).find? l v = some { loc := l, gives := [] } := by
  have h1 := hL.head_tail; have h2 := hL.head_dn; have h3 := hL.head_nn; have h4 := hL.tail_dn
  have h5 := hL.tail_nn; have h6 := hL.dn_nn
  rcases hl with rfl | rfl | rfl | rfl
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planD, Plan.find?]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planD, Plan.find?]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planD, Plan.find?]
  · have := Ne.symm h1; have := Ne.symm h2; have := Ne.symm h3; have := Ne.symm h4; have := Ne.symm h5
    have := Ne.symm h6; simp_all [planD, Plan.find?]

theorem planE_gives {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) :
    (planE P).gives l v = if P.IsN l then [P.dat] else [] := by
  simp [Plan.gives, planE_find hL hl]

theorem planD_gives {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) : (planD P).gives l v = [] := by
  simp [Plan.gives, planD_find hL hl]

theorem planE_give {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) (cl : Prop) (r : Res) :
    (planE P).give l v cl r = Res.only (if P.IsN l then [P.dat] else []) r := by
  simp [Plan.give, planE_find hL hl, Plan.Entry.give]

theorem planD_give {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) (cl : Prop) (r : Res) :
    (planD P).give l v cl r = Res.only [] r := by
  simp [Plan.give, planD_find hL hl, Plan.Entry.give]

theorem planE_keep {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) (cl : Prop) (r : Res) :
    (planE P).keep l v cl r = Res.drop (if P.IsN l then [P.dat] else []) r := by
  simp [Plan.keep, planE_find hL hl, Plan.Entry.keep]

theorem planD_keep {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsQ l) (v : Val) (cl : Prop) (r : Res) :
    (planD P).keep l v cl r = Res.drop [] r := by
  simp [Plan.keep, planD_find hL hl, Plan.Entry.keep]

/-! ## The initial resources -/

/-- The enqueuer's initial fractions: half of `head` and `tail`, all of
every other location. -/
def fracE (P : Params) (x : Loc) : Rat := if x = P.head ∨ x = P.tail then 1 / 2 else 1

/-- The dequeuer's initial fractions: half of `head` and `tail`. -/
def fracD (P : Params) (x : Loc) : Rat := if x = P.head ∨ x = P.tail then 1 / 2 else 0

theorem fracE_nonneg (P : Params) (x : Loc) : 0 ≤ fracE P x := by unfold fracE; split <;> grind
theorem fracD_nonneg (P : Params) (x : Loc) : 0 ≤ fracD P x := by unfold fracD; split <;> grind

/-- The enqueuer's initial resource (no acquire id). -/
def resE (m : Memory) (P : Params) : Res := Res.initOf m (fracE P) (fracE_nonneg P)

/-- The dequeuer's initial resource: its fractions and the acquire id `0` of
every queue word. -/
def resD (m : Memory) (P : Params) : Res :=
  ⟨(Res.initOf m (fracD P) (fracD_nonneg P)).wr, fun x ι => if P.IsQ x ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: the enqueuer is thread `0`, the dequeuer
thread `1`. -/
def tRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then resE m P else if i = 1 then resD m P else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀ (P : Params) : (ghost₀ P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀, qList, Res.prod, Res.op_unit]

theorem total_init (P : Params) (m : Memory) :
    total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem) = (resE m P).op (resD m P) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

theorem frac_add_le (P : Params) (x : Loc) : fracE P x + fracD P x ≤ 1 := by
  unfold fracE fracD; split <;> grind

/-- **Initial erasure of the queue.** -/
theorem erase_init {P : Params} (hL : QLocs P) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) T (Config.init [s0, s1] initMem) := by
  have htot := total_init (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).acq x ι = if P.IsQ x ∧ ι = 0 then 1 else 0 := by
    intro x ι; rw [htot]; show 0 + (if P.IsQ x ∧ ι = 0 then 1 else 0) = _; simp
  have hq : ∀ x, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).wr x).q = fracE P x + fracD P x := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).wr x).X p ↔
        (0 < fracE P x ∨ 0 < fracD P x) ∧ p = ((Config.init [s0, s1] initMem).mem.initVal x, 0) := by
    intro x p; rw [htot]
    show (0 < fracE P x ∧ p = _) ∨ (0 < fracD P x ∧ p = _) ↔ _
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr h, rfl⟩
    · rintro ⟨h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr ⟨h, rfl⟩
  have hids : ∀ x, (ghost₀ P).acqIds
      (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) (Config.init [s0, s1] initMem)).acq x =
        if P.IsQ x then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost₀ P).acqTab.length = 1 from rfl]
    by_cases hx : P.IsQ x <;> simp [hx, ha]
  have hmem : ∀ s ∈ (ghost₀ P).u, ∃ x, P.IsQ x ∧ s = ⟨(x, 0), 0, Res.unit⟩ := by
    intro s hs
    simp only [ghost₀, List.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨x, mem_qList.mp hx, rfl⟩
  refine Erase.init ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
    refine ⟨fun x => by rw [hq]; exact frac_add_le P x, fun x ι => ?_⟩
    rw [ha]; split <;> omega
  · -- slot ids
    intro s hs
    obtain ⟨x, -, rfl⟩ := hmem s hs
    simp [ghost₀]
  · -- held acquire ids
    intro x ι h
    rw [ha] at h
    show ι < 1
    split at h <;> grind
  · -- release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : P.IsQ x
    · rw [ghost₀_rel_q hx] at h
      simp only [hx, ↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · rw [ghost₀_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact h
  · -- write sets
    intro x hpos p
    rw [hX]
    have : 0 < fracE P x ∨ 0 < fracD P x := by
      rw [hq] at hpos
      have := fracE_nonneg P x; have := fracD_nonneg P x
      by_cases h0 : 0 < fracE P x
      · exact .inl h0
      · exact .inr (by grind)
    simp [this]
  · -- relaxed initial messages are pure
    intro x hx
    have hx' : ¬ P.IsQ x := fun h => hx (by simp [ghost₀, List.mem_map, mem_qList, h])
    rw [ghost₀_rel_ne hx']
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [ghost₀, List.mem_map] at hk
    obtain ⟨x, -, rfl⟩ := hk; rfl
  · -- slots are distinct
    simp only [ghost₀, qList, List.map_cons, List.map_nil]
    have h1 := hL.head_tail; have h2 := hL.head_dn; have h3 := hL.head_nn; have h4 := hL.tail_dn
    have h5 := hL.tail_nn; have h6 := hL.dn_nn
    simp [h1, h2, h3, h4, h5, h6]
  · -- slot domain
    intro k ι
    rw [ha]
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hmem s hs
      exact ⟨by simp [ghost₀, List.mem_map, mem_qList, hx], .inl (by simp [hx])⟩
    · rintro ⟨hk, h⟩
      simp only [ghost₀, List.mem_map, mem_qList] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      have hι : ι = 0 := by
        rcases h with h | h
        · simp only [hx, true_and] at h; split at h <;> grind
        · simp [ghost₀] at h
      subst hι
      exact ⟨⟨(x, 0), 0, Res.unit⟩, by simp [ghost₀, List.mem_map, mem_qList, hx], rfl, rfl⟩
  · -- slots satisfy their predicates at the initial message (view `0`)
    intro s hs
    obtain ⟨x, -, rfl⟩ := hmem s hs
    exact fun h => absurd rfl h
  · -- update ids
    intro x
    simp [ghost₀]

end Init

/-- **Two thread resources each holding `x` whole contradict erasure**
(`tokE_pair_false` and `tokD2_pair_false` are its instances). -/
theorem wr_pair_false {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    {x : Loc} (h1 : 1 ≤ ((rF i).wr x).q) (h2 : 1 ≤ ((rF j).wr x).q) : False := by
  have h3 := (sub_total_pair (rF := rF) (g := g) (c := c) hi hj hij).q_le x
  have h4 := E.valid.1 x
  have h5 : (((rF i).op (rF j)).wr x).q = ((rF i).wr x).q + ((rF j).wr x).q := rfl
  have h6 := Rat.le_trans h3 h4
  rw [h5] at h6
  grind

end Kraken.Promising.SLR.EnvG.MsQueue
