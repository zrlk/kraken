/-
Msqueue2 part 1: **the ownership plan of
`msqueue2.kl`** (the Michael–Scott queue, one enqueuer of `n1` then `n2`,
one dequeuer dequeuing twice; on `EnvGCAdj`). Built on the msqueue1 files
(`EnvG/MsQueueGhost.lean`: `Params`, `QLocs`, `Prov`, `D`,
`fracE`/`resE` are reused).

As in msqueue1 the release predicates record only **memory facts** of the
writer, and all reasoning happens at the final clean erasure
(`EnvG/MsQueue2Final.lean`). The queue words are `head`, `tail` and the
three links `[d + 8]`, `[n1 + 8]`, `[n2 + 8]`. At a non-initial message
`(x, v)` at `V`, `form2` records:

- at a link (only the enqueuer's link `casal` writes one): `v` is `n1` with
  `n1`'s data word frozen in the slot (`NodeFrozenAt`, `D`), or `n2` with
  `n2`'s data word frozen (`D2`) and a message of value `n1` below `V` at a
  `TailLoc` address (`LinkMsg`: the enqueuer's own first link); the address
  is `[y + 8]` for a value `y` of `tail` below `V` (`TailLoc`), and the
  `casal` overwrote an adjacent `0` (`AdjZero`, from `AdjAt.lastAt`);
- at `head`: the dequeuer's `casal` (`HeadF`: it overwrote an adjacent
  message of value `z` and writes the non-zero value of a message of
  `[z + 8]` below `V`), or the link `casal` at a junk `TailLoc` address;
- at `tail`: the swing (`v = n1` or `n2` and `LinkMsg` of it), a helping
  `casal` (`Prov`), or the link `casal` at a junk `TailLoc` address.

**Plans**: every write to a queue word is a release. The enqueuer's entries
at the links depend on the value: writing `n1` gives `n1`'s data word,
writing `n2` gives `n2`'s.

Contents: `Params2`, `QLocs2`, `form2`, `ghost2`, `planE2`/`planD2`
(+ validity and their resources), `resD2`, `tRes2`, `erase_init2`.
-/
import Kraken.Promising.SLR.EnvG.MsQueueGhost

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.Treiber (read?_of_get? get?_of_read? initVal_eq)

variable {I : ISA}

/-! ## Parameters -/

/-- The parameters of `msqueue2.kl`: msqueue1's and the second node `n2`. -/
structure Params2 extends Params where
  n2 : BitVec 64

namespace Params2

variable (P : Params2)

/-- The second node's link. -/
def nn2 : Loc := ⟨P.n2 + 8, 8⟩
/-- The second node's data word. -/
def dat2 : Loc := ⟨P.n2, 4⟩

/-- A link word. -/
def IsL (x : Loc) : Prop := x = P.dn ∨ x = P.nn ∨ x = P.nn2
/-- A queue word. -/
def IsW (x : Loc) : Prop := x = P.head ∨ x = P.tail ∨ P.IsL x

instance (x : Loc) : Decidable (P.IsL x) := by unfold IsL; infer_instance
instance (x : Loc) : Decidable (P.IsW x) := by unfold IsW; infer_instance

end Params2

/-- The layout hypotheses of `msqueue2.kl`: msqueue1's, and `n2`'s link
distinct from `head`/`tail`, the nodes distinct and non-zero. -/
structure QLocs2 (P : Params2) : Prop where
  q1 : QLocs P.toParams
  hn2 : P.h ≠ P.n2 + 8
  tn2 : P.t ≠ P.n2 + 8
  dn2 : P.d ≠ P.n2
  n12 : P.n1 ≠ P.n2
  n1z : P.n1 ≠ 0
  n2z : P.n2 ≠ 0

namespace QLocs2

variable {P : Params2} (hL : QLocs2 P)
include hL

theorem head_nn2 : P.head ≠ P.nn2 := by
  simp only [Params.head, Params2.nn2, ne_eq, Loc.mk.injEq, and_true]; exact hL.hn2
theorem tail_nn2 : P.tail ≠ P.nn2 := by
  simp only [Params.tail, Params2.nn2, ne_eq, Loc.mk.injEq, and_true]; exact hL.tn2
theorem dn_nn2 : P.dn ≠ P.nn2 := by
  simp only [Params.dn, Params2.nn2, ne_eq, Loc.mk.injEq, and_true]
  intro h; exact hL.dn2 (by bv_omega)
theorem nn_nn2 : P.nn ≠ P.nn2 := by
  simp only [Params.nn, Params2.nn2, ne_eq, Loc.mk.injEq, and_true]
  intro h; exact hL.n12 (by bv_omega)

theorem not_isL_head : ¬ P.IsL P.head := by
  rintro (h | h | h)
  · exact hL.q1.head_dn h
  · exact hL.q1.head_nn h
  · exact hL.head_nn2 h

theorem not_isL_tail : ¬ P.IsL P.tail := by
  rintro (h | h | h)
  · exact hL.q1.tail_dn h
  · exact hL.q1.tail_nn h
  · exact hL.tail_nn2 h

theorem n1v_ne_n2v : BitVec.setWidth 128 P.n1 ≠ BitVec.setWidth 128 P.n2 := by
  intro h; apply hL.n12; have := congrArg (BitVec.setWidth 64) h; simpa using this

end QLocs2

section Distinct2

variable (P : Params2)

theorem dat2_ne_of_8 {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ P.dat2 := by simp [Params2.dat2]
theorem dat2_tokE : P.dat2 ≠ P.tokE := by simp [Params2.dat2, Params.tokE]

theorem not_isW_dat : ¬ P.IsW P.dat := by
  rintro (h | h | h | h | h) <;> simp [Params.dat, Params.head, Params.tail, Params.dn, Params.nn, Params2.nn2] at h

theorem not_isW_dat2 : ¬ P.IsW P.dat2 := by
  rintro (h | h | h | h | h) <;>
    simp [Params2.dat2, Params.head, Params.tail, Params.dn, Params.nn, Params2.nn2] at h

theorem not_isW_tokE : ¬ P.IsW P.tokE := by
  rintro (h | h | h | h | h) <;>
    simp [Params.tokE, Params.head, Params.tail, Params.dn, Params.nn, Params2.nn2] at h

theorem isW_of_isL {x : Loc} (h : P.IsL x) : P.IsW x := .inr (.inr h)

end Distinct2

/-! ## Memory facts -/

/-- The data word's property for `n2`: its low 32 bits are `2`. -/
def D2 (d : Val) : Prop := BitVec.setWidth 32 d = 2

/-- **A node's data word `δ` frozen in a slot**: `O ⋅ J` with `O` whole, its
maximal write `(d, td)` below `V`, `Dp d` (`NodeFrozen` at any data word). -/
def NodeFrozenAt (δ : Loc) (Dp : Val → Prop) (R : Res) (V : View) : Prop :=
  ∃ O J : Perm, R.wr δ = O.op J ∧ O.q = 1 ∧
    ∃ d td, O.X (d, td) ∧ (∀ p, O.X p → p.2 ≤ td) ∧ td < V ∧ Dp d

/-- **`x` is `[y + 8]` for a value `y` of `tail` below `V`.** -/
def TailLoc (P : Params2) (m : Memory) (V : View) (x : Loc) : Prop :=
  ∃ a y, a < V ∧ m.read? P.tail a = some y ∧ x = ⟨BitVec.setWidth 64 y + 8, 8⟩

/-- **A message of value `n` below `V` at a `TailLoc` address.** -/
def LinkMsg (P : Params2) (m : Memory) (V : View) (n : BitVec 64) : Prop :=
  ∃ V' x' v' w', V' < V ∧ m.get? V' = some ⟨x', v', w'⟩ ∧ BitVec.setWidth 64 v' = n ∧ TailLoc P m V' x'

/-- **No message of `x` strictly between `a` and `b`.** -/
def NoMsgIn (m : Memory) (x : Loc) (a b : Time) : Prop :=
  ∀ p wm, a < p → p < b → m.get? p = some wm → wm.loc ≠ x

/-- **The message overwritten at `V` is an adjacent `0`.** -/
def AdjZero (m : Memory) (x : Loc) (V : View) : Prop :=
  ∃ tr z, tr < V ∧ m.read? x tr = some z ∧ BitVec.setWidth 64 z = 0 ∧ NoMsgIn m x tr V

/-- **The dequeuer's swing of `head`** at `V`: it overwrote the adjacent
message `z` and writes `v ≠ 0`, the value of a message of `[z + 8]` below
`V`. -/
def HeadF (P : Params2) (m : Memory) (V : View) (v : Val) : Prop :=
  BitVec.setWidth 64 v ≠ 0 ∧ ∃ tr z b y5, tr < V ∧ m.read? P.head tr = some z ∧ NoMsgIn m P.head tr V ∧
    b < V ∧ m.read? ⟨BitVec.setWidth 64 z + 8, 8⟩ b = some y5 ∧ BitVec.setWidth 64 y5 = BitVec.setWidth 64 v

section Mono

variable {P : Params2} {m m' : Memory} (h : m.Prefix m')
include h

theorem TailLoc.mono {V : View} {x : Loc} (ht : TailLoc P m V x) : TailLoc P m' V x :=
  let ⟨a, y, ha, hr, hx⟩ := ht
  ⟨a, y, ha, Treiber2.read?_mono h hr, hx⟩

theorem LinkMsg.mono {V : View} {n : BitVec 64} (hl : LinkMsg P m V n) : LinkMsg P m' V n :=
  let ⟨V', x', v', w', hV, hg, hv, ht⟩ := hl
  ⟨V', x', v', w', hV, Memory.get?_of_prefix h.2 hg, hv, ht.mono h⟩

theorem NoMsgIn.mono {x : Loc} {a b : Time} (hb : b ≤ m.last + 1) (hn : NoMsgIn m x a b) : NoMsgIn m' x a b :=
  fun p wm h1 h2 hw => hn p wm h1 h2 (Memory.get?_of_prefix_le h.2 (by simp only [Time] at *; omega) hw)

theorem AdjZero.mono {x : Loc} {V : View} (hV : V ≤ m.last + 1) (ha : AdjZero m x V) : AdjZero m' x V :=
  let ⟨tr, z, h1, h2, h3, h4⟩ := ha
  ⟨tr, z, h1, Treiber2.read?_mono h h2, h3, h4.mono h hV⟩

theorem HeadF.mono {V : View} {v : Val} (hV : V ≤ m.last + 1) (hh : HeadF P m V v) : HeadF P m' V v :=
  let ⟨hnz, tr, z, b, y5, h1, h2, h3, h4, h5, h6⟩ := hh
  ⟨hnz, tr, z, b, y5, h1, Treiber2.read?_mono h h2, h3.mono h hV, h4, Treiber2.read?_mono h h5, h6⟩

end Mono

/-! ## The predicate -/

/-- The link facts of a message `(x, v)` at `V` with resource `R`. -/
def LinkF (P : Params2) (m : Memory) (V : View) (R : Res) (x : Loc) (v : Val) : Prop :=
  ((BitVec.setWidth 64 v = P.n1 ∧ NodeFrozenAt P.dat D R V) ∨
    (BitVec.setWidth 64 v = P.n2 ∧ NodeFrozenAt P.dat2 D2 R V ∧ LinkMsg P m V P.n1)) ∧
  TailLoc P m V x ∧ AdjZero m x V

/-- The swing's facts at `tail`: `v` is a node with a link message below. -/
def SwingF (P : Params2) (m : Memory) (V : View) (v : Val) : Prop :=
  ∃ n, (n = P.n1 ∨ n = P.n2) ∧ BitVec.setWidth 64 v = n ∧ LinkMsg P m V n

/-- **The predicate of the queue words of `msqueue2.kl`.** -/
def form2 (P : Params2) : Pred where
  P v m V R := V ≠ 0 → ∃ x w, m.get? V = some ⟨x, v, w⟩ ∧ (P.IsL x → LinkF P m V R x v) ∧
    (x = P.head → HeadF P m V v ∨ TailLoc P m V x) ∧
    (x = P.tail → SwingF P m V v ∨ Prov P.toParams m V v ∨ TailLoc P m V x)
  mono v m m' V R hpre h := by
    intro hV
    obtain ⟨x, w, hg, h1, h2, h3⟩ := h hV
    have hle : V ≤ m.last + 1 := Nat.le_succ_of_le (m.last_le_of_get?_eq_some hg)
    refine ⟨x, w, Memory.get?_of_prefix hpre.2 hg, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨h4, h5, h6⟩ := h1 hx
      exact ⟨h4.imp id fun h7 => ⟨h7.1, h7.2.1, h7.2.2.mono hpre⟩, h5.mono hpre, h6.mono hpre hle⟩
    · exact (h2 hx).imp (HeadF.mono hpre hle) (TailLoc.mono hpre)
    · exact (h3 hx).imp (fun ⟨n, hn, hv, hl⟩ => ⟨n, hn, hv, hl.mono hpre⟩)
        (Or.imp (Prov.mono hpre) (TailLoc.mono hpre))

/-! ## The initial ghost -/

/-- The queue words, as a list. -/
def wList (P : Params2) : List Loc := [P.head, P.tail, P.dn, P.nn, P.nn2]

theorem mem_wList {P : Params2} {x : Loc} : x ∈ wList P ↔ P.IsW x := by
  simp [wList, Params2.IsW, Params2.IsL]

/-- **The initial ghost**: `form2` at the queue words (`Pred.emp`
elsewhere); acquire table `[form2]`; the initial messages of the queue words
in release mode with unit slots for id `0`. -/
def ghost2 (P : Params2) : Ghost where
  rel x := if P.IsW x then form2 P else Pred.emp
  acqTab := [form2 P]
  u := (wList P).map fun x => ⟨(x, 0), 0, Res.unit⟩
  relMsgs := (wList P).map fun x => (x, 0)
  pend := []
  upd _ := []
  claims := []

theorem ghost2_rel_w {P : Params2} {x : Loc} (h : P.IsW x) : (ghost2 P).rel x = form2 P := by
  simp [ghost2, h]

theorem ghost2_rel_ne {P : Params2} {x : Loc} (h : ¬ P.IsW x) : (ghost2 P).rel x = Pred.emp := by
  simp [ghost2, h]

theorem ghost2_pend (P : Params2) : ∀ ts, ts ∉ (ghost2 P).pend := fun _ h => by cases h

/-! ## The plans -/

/-- The enqueuer's entries at a link word: `n1` gives `n1`'s data word, `n2`
`n2`'s, any other value nothing. -/
def linkEntries (P : Params2) (x : Loc) : List Plan.Entry :=
  [{ loc := x, val := some (BitVec.setWidth 128 P.n1), gives := [P.dat] },
    { loc := x, val := some (BitVec.setWidth 128 P.n2), gives := [P.dat2] }, { loc := x, gives := [] }]

/-- **The enqueuer's plan**: every write to a queue word is a release; at
the links, by value, it gives the node's data word. -/
def planE2 (P : Params2) : Plan :=
  ⟨[{ loc := P.head, gives := [] }, { loc := P.tail, gives := [] }] ++ linkEntries P P.dn ++
    linkEntries P P.nn ++ linkEntries P P.nn2⟩

/-- **The dequeuer's plan**: every write to a queue word is a release giving
nothing. -/
def planD2 (P : Params2) : Plan :=
  ⟨(wList P).map fun x => { loc := x, gives := [] }⟩

theorem planE2_valid (P : Params2) : (planE2 P).Valid := by
  intro e he
  simp only [planE2, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [dat_ne_of_8, dat2_ne_of_8, Params.dn, Params.nn, Params2.nn2]

theorem planD2_valid (P : Params2) : (planD2 P).Valid := by
  intro e he
  simp only [planD2, wList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

/-- What the enqueuer's release of `v` to `l` gives. -/
def gE (P : Params2) (l : Loc) (v : Val) : List Loc :=
  if P.IsL l then (if v = BitVec.setWidth 128 P.n1 then [P.dat]
    else if v = BitVec.setWidth 128 P.n2 then [P.dat2] else []) else []

theorem planE2_find_mem {P : Params2} {l : Loc} {v : Val} {e : Plan.Entry} (h : (planE2 P).find? l v = some e) :
    e.loc = l ∧ e.split = none ∧ P.IsW e.loc ∧ (e.gives = [] ∨ e.gives = [P.dat] ∨ e.gives = [P.dat2]) := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨hp.1, ?_⟩
  simp only [planE2, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Params2.IsW, Params2.IsL]

theorem planD2_find_mem {P : Params2} {l : Loc} {v : Val} {e : Plan.Entry} (h : (planD2 P).find? l v = some e) :
    e.loc = l ∧ e.split = none ∧ e.gives = [] := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨hp.1, ?_⟩
  simp only [planD2, wList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp

theorem planE2_rel (P : Params2) (l : Loc) (v : Val) : (planE2 P).rel l v = decide (P.IsW l) := by
  unfold Plan.rel
  cases h : (planE2 P).find? l v with
  | some e => obtain ⟨rfl, -, hw, -⟩ := planE2_find_mem h; simp [hw]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro hw
    rw [Plan.find?, List.find?_eq_none] at h
    simp only [planE2, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, Bool.and_eq_true, decide_eq_true_eq, not_and, forall_eq_or_imp, forall_eq] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact h.1 rfl trivial
    · exact h.2.1 rfl trivial
    · exact h.2.2.2.2.1 rfl trivial
    · exact h.2.2.2.2.2.2.2.1 rfl trivial
    · exact h.2.2.2.2.2.2.2.2.2.2 rfl trivial

theorem planD2_rel (P : Params2) (l : Loc) (v : Val) : (planD2 P).rel l v = decide (P.IsW l) := by
  unfold Plan.rel
  cases h : (planD2 P).find? l v with
  | some e =>
    obtain ⟨rfl, -, -⟩ := planD2_find_mem h
    have hm := List.mem_of_find?_eq_some h
    simp only [planD2, List.mem_map, mem_wList] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    simp [hx]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro hw
    rw [Plan.find?, List.find?_eq_none] at h
    have := h { loc := l, gives := [] } (by simp only [planD2, List.mem_map]; exact ⟨l, mem_wList.mpr hw, rfl⟩)
    simp at this

theorem planE2_gives {P : Params2} (hL : QLocs2 P) {l : Loc} (hl : P.IsW l) (v : Val) : (planE2 P).gives l v = gE P l v := by
  have h1 := hL.q1.head_tail; have h2 := hL.q1.head_dn; have h3 := hL.q1.head_nn; have h4 := hL.q1.tail_dn
  have h5 := hL.q1.tail_nn; have h6 := hL.q1.dn_nn; have h7 := hL.head_nn2; have h8 := hL.tail_nn2
  have h9 := hL.dn_nn2; have h10 := hL.nn_nn2
  have hv := hL.n1v_ne_n2v
  unfold Plan.gives gE Plan.find?
  rcases hl with rfl | rfl | rfl | rfl | rfl <;>
    by_cases ha : v = BitVec.setWidth 128 P.n1 <;> by_cases hb : v = BitVec.setWidth 128 P.n2 <;>
    simp_all [planE2, linkEntries, Params2.IsL, Ne.symm h2, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h9,
      Ne.symm h10, eq_comm]

theorem planE2_keep (P : Params2) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planE2 P).keep l v cl r = Res.drop ((planE2 P).gives l v) r := by
  unfold Plan.keep Plan.gives
  cases h : (planE2 P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.keep, (planE2_find_mem h).2.1]

theorem planE2_give (P : Params2) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planE2 P).give l v cl r = Res.only ((planE2 P).gives l v) r := by
  unfold Plan.give Plan.gives
  cases h : (planE2 P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.give, (planE2_find_mem h).2.1]

theorem planE2_gives_sub (P : Params2) (l : Loc) (v : Val) {x : Loc} (h1 : x ≠ P.dat) (h2 : x ≠ P.dat2) :
    x ∉ (planE2 P).gives l v := by
  unfold Plan.gives
  cases h : (planE2 P).find? l v with
  | none => simp
  | some e => rcases (planE2_find_mem h).2.2.2 with h' | h' | h' <;> simp [h', h1, h2]

theorem planD2_gives (P : Params2) (l : Loc) (v : Val) : (planD2 P).gives l v = [] := by
  unfold Plan.gives
  cases h : (planD2 P).find? l v with
  | none => rfl
  | some e => simp [(planD2_find_mem h).2.2]

theorem planD2_keep (P : Params2) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD2 P).keep l v cl r = Res.drop [] r := by
  unfold Plan.keep
  cases h : (planD2 P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.keep, (planD2_find_mem h).2.1, (planD2_find_mem h).2.2]

theorem planD2_give (P : Params2) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD2 P).give l v cl r = Res.only [] r := by
  unfold Plan.give
  cases h : (planD2 P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.give, (planD2_find_mem h).2.1, (planD2_find_mem h).2.2]

/-! ## The initial resources -/

/-- The dequeuer's initial resource: half of `head`/`tail` and the acquire
id `0` of every queue word. -/
def resD2 (m : Memory) (P : Params2) : Res :=
  ⟨(Res.initOf m (fracD P.toParams) (fracD_nonneg P.toParams)).wr, fun x ι => if P.IsW x ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: the enqueuer (`resE`, msqueue1's) is
thread `0`, the dequeuer thread `1`. -/
def tRes2 (m : Memory) (P : Params2) (i : Nat) : Res :=
  if i = 0 then resE m P.toParams else if i = 1 then resD2 m P else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost2 (P : Params2) : (ghost2 P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost2, wList, Res.prod, Res.op_unit]

theorem total_init2 (P : Params2) (m : Memory) :
    total (tRes2 m P) (ghost2 P) (Config.init [s0, s1] initMem) = (resE m P.toParams).op (resD2 m P) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost2, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes2 m P 0, tRes2 m P 1] = _
  simp [tRes2, Res.op_unit]

/-- **Initial erasure of `ghost2`, for any thread resources** whose total
holds the acquire id `0` of every queue word (`ha`), is valid (`hq`) and has
the initial message as its write set wherever it has a permission (`hX`).
`erase_init2` (msqueue2) and `erase_init3` (msqueue3) are its instances. -/
theorem erase_init_ghost2 {P : Params2} (hL : QLocs2 P) (T : Nat → Prop) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res}
    (ha : ∀ x ι, (total rF (ghost2 P) (Config.init states initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0)
    (hq : ∀ x, ((total rF (ghost2 P) (Config.init states initMem)).wr x).q ≤ 1)
    (hX : ∀ x, 0 < ((total rF (ghost2 P) (Config.init states initMem)).wr x).q → ∀ p,
      ((total rF (ghost2 P) (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0)) :
    Erase rF (ghost2 P) T (Config.init states initMem) := by
  have hids : ∀ x, (ghost2 P).acqIds
      (total rF (ghost2 P) (Config.init states initMem)).acq x =
        if P.IsW x then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost2 P).acqTab.length = 1 from rfl]
    by_cases hx : P.IsW x <;> simp [hx, ha]
  have hmem : ∀ s ∈ (ghost2 P).u, ∃ x, P.IsW x ∧ s = ⟨(x, 0), 0, Res.unit⟩ := by
    intro s hs
    simp only [ghost2, List.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨x, mem_wList.mp hx, rfl⟩
  refine Erase.init ⟨hq, fun x ι => ?_⟩ ?_ ?_ ?_ hX ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
    rw [ha]; split <;> omega
  · -- slot ids
    intro s hs
    obtain ⟨x, -, rfl⟩ := hmem s hs
    simp [ghost2]
  · -- held acquire ids
    intro x ι h
    rw [ha] at h
    show ι < 1
    split at h <;> grind
  · -- release predicates split
    intro x v m V r h
    rw [Ghost.acqPreds, hids]
    by_cases hx : P.IsW x
    · rw [ghost2_rel_w hx] at h
      simp only [hx, ↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost2, List.append_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · rw [ghost2_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost2, List.append_nil]
      exact h
  · -- relaxed initial messages are pure
    intro x hx
    have hx' : ¬ P.IsW x := fun h => hx (by simp [ghost2, List.mem_map, mem_wList, h])
    rw [ghost2_rel_ne hx']
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [ghost2, List.mem_map] at hk
    obtain ⟨x, -, rfl⟩ := hk; rfl
  · -- slots are distinct
    simp only [ghost2, wList, List.map_cons, List.map_nil]
    have h1 := hL.q1.head_tail; have h2 := hL.q1.head_dn; have h3 := hL.q1.head_nn; have h4 := hL.q1.tail_dn
    have h5 := hL.q1.tail_nn; have h6 := hL.q1.dn_nn; have h7 := hL.head_nn2; have h8 := hL.tail_nn2
    have h9 := hL.dn_nn2; have h10 := hL.nn_nn2
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · -- slot domain
    intro k ι
    rw [ha]
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hmem s hs
      exact ⟨by simp [ghost2, List.mem_map, mem_wList, hx], .inl (by simp [hx])⟩
    · rintro ⟨hk, h⟩
      simp only [ghost2, List.mem_map, mem_wList] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      have hι : ι = 0 := by
        rcases h with h | h
        · simp only [hx, true_and] at h; split at h <;> grind
        · simp [ghost2] at h
      subst hι
      exact ⟨⟨(x, 0), 0, Res.unit⟩, by simp [ghost2, List.mem_map, mem_wList, hx], rfl, rfl⟩
  · -- slots satisfy their predicates at the initial message (view `0`)
    intro s hs
    obtain ⟨x, -, rfl⟩ := hmem s hs
    exact fun h => absurd rfl h
  · -- update ids
    intro x
    simp [ghost2]


/-- **Initial erasure of the queue of `msqueue2.kl`.** -/
theorem erase_init2 {P : Params2} (hL : QLocs2 P) (T : Nat → Prop) :
    Erase (tRes2 (Config.init [s0, s1] initMem).mem P) (ghost2 P) T (Config.init [s0, s1] initMem) := by
  have htot := total_init2 (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes2 (Config.init [s0, s1] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1] initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0 := by
    intro x ι; rw [htot]; show 0 + (if P.IsW x ∧ ι = 0 then 1 else 0) = _; simp
  have hq : ∀ x, ((total (tRes2 (Config.init [s0, s1] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1] initMem)).wr x).q = fracE P.toParams x + fracD P.toParams x := by
    intro x; rw [htot]; rfl
  have hX : ∀ x p, ((total (tRes2 (Config.init [s0, s1] initMem).mem P) (ghost2 P)
      (Config.init [s0, s1] initMem)).wr x).X p ↔
        (0 < fracE P.toParams x ∨ 0 < fracD P.toParams x) ∧
          p = ((Config.init [s0, s1] initMem).mem.initVal x, 0) := by
    intro x p; rw [htot]
    show (0 < fracE P.toParams x ∧ p = _) ∨ (0 < fracD P.toParams x ∧ p = _) ↔ _
    constructor
    · rintro (⟨h, rfl⟩ | ⟨h, rfl⟩)
      · exact ⟨.inl h, rfl⟩
      · exact ⟨.inr h, rfl⟩
    · rintro ⟨h | h, rfl⟩
      · exact .inl ⟨h, rfl⟩
      · exact .inr ⟨h, rfl⟩
  refine erase_init_ghost2 hL T ha (fun x => by rw [hq]; exact frac_add_le P.toParams x) ?_
  -- write sets
  intro x hpos p
  rw [hX]
  have : 0 < fracE P.toParams x ∨ 0 < fracD P.toParams x := by
    rw [hq] at hpos
    have := fracE_nonneg P.toParams x; have := fracD_nonneg P.toParams x
    by_cases h0 : 0 < fracE P.toParams x
    · exact .inl h0
    · exact .inr (by grind)
  simp [this]

end Init

end Kraken.Promising.SLR.EnvG.MsQueue
