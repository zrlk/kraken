/-
**Part 1: the ownership plan of the x64
Michael–Scott queue** `Kraken/Examples/LockFree/X64/msqueue2.kl` (one
enqueuer of `n1` then `n2`, one dequeuer dequeuing twice) on the x64 adjacency
link `EnvGCAdjX`. ISA-neutral.

A copy of the MS queue proof's `EnvG/MsQueue2Ghost.lean` (same idea, same shape) for the
x64 node layout: a node is its single 8-byte link word `[n]` **at offset `0`**
with no data word, and the dequeuer returns the node pointer. The AArch64
files fix the link at `[n + 8]`, freeze a data word `[n]` and import AArch64
files (`MsQueueGhost → Treiber2Final → TreiberVC`), so they cannot be reused.

## No value knowledge at write time

As in the MS queue proof, the release predicates record only **memory facts** of the
writer (its own reads), and all reasoning happens at the final clean erasure
(`EnvG/X64MsQueue2Final.lean`). The enqueuer holds a positive share of every
8-byte location (its link `lock cmpxchgq` writes an address it loaded), half
of `head`/`tail`; the dequeuer the other halves and the acquire id `0` of
every queue word.

## The predicate `form` at the queue words

The queue words are `head`, `tail` and the links `[s]`, `[n1]`, `[n2]`. At a
non-initial message `(x, v)` at `V`:

- at a link (the enqueuer's link `lock cmpxchgq`, `LinkF`): `v` is `n1` with
  `n1`'s **token** `⟨n1, 1⟩` whole in the slot (`TokFrozen`), or `n2` with
  `n2`'s token and the enqueuer's own `n1` link message below (`LinkMsg`); the
  address is `[y]` for a value `y` of `tail` below `V` (`TailLoc`) and the
  overwritten message is an adjacent `0` (`AdjZero`). The tokens replace the
  AArch64 data words: no access of the code has `1` byte, so the token is
  given exactly once (the link messages of each node are unique).
- at `tail` (`TailF`, uniform for the three writers: the enqueuer's helping
  and own swing and the dequeuer's helping swing): the overwritten message
  `z` is adjacent and `v ≠ 0` is the value of a message of `[z]` below `V`;
  or the link `lock cmpxchgq` at a junk `TailLoc` address.
- at `head` (`HeadF`, the dequeuer's swing): the overwritten message `z` is
  adjacent, and the dequeuer's three reads: `head` read `z` at `tA`, `tail`
  read `t ≠ z` at `tB` with no `tail` message in `(tB, tA]`, `[z]` read `v`
  at `tl` with no `[z]` message in `(tl, tB]`; or the link `lock cmpxchgq` at
  a junk `TailLoc` address. x64's dequeuer has no `next ≠ 0` test (AArch64's
  `cbz`), so `v ≠ 0` is a global fact (`X64MsQueue2Final.hist`).
- at `head`, if the parameters track the swings (`P.trk`; not in
  `msqueue2.kl`, in `msqueue3.kl`): the writer `w` is a dequeuer and the slot
  holds its pop token `P.popTok w` whole (`HW`), or the junk `TailLoc`
  address.

**Plans**: every write to a queue word is a release. The enqueuer's entries
at the links depend on the value: writing `n1` gives `n1`'s token, writing
`n2` gives `n2`'s.

Contents: `Params`, `QLocs`, `TailLoc`, `LinkMsg`, `NoMsgIn`, `AdjZero`,
`TailF`, `HeadF`, `LinkF`, `form`, `ghost₀`, `planE`/`planD` (+ validity and
their resources), `fracE`/`fracD`, `tRes`, `erase_init`.
-/
import Kraken.Promising.SLR.EnvG.TreiberVCCommon

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono)

variable {I : ISA}

/-! ## Parameters -/

/-- The queue's parameters: `head` at `h`, `tail` at `t` (8 bytes each), the
sentinel `s` and the nodes `n1`, `n2`; a node's link is `[n]` (8 bytes,
offset `0`). -/
structure Params where
  h : BitVec 64
  t : BitVec 64
  s : BitVec 64
  n1 : BitVec 64
  n2 : BitVec 64
  /-- Whether the `head` swings are tracked by pop tokens (`popTok`, `HW`;
  the x64 MS queue proof's `msqueue3.kl`, two try-once dequeuers `1`, `2`). `msqueue2.kl`
  does not track them. -/
  trk : Bool

namespace Params

variable (P : Params)

/-- `head`. -/
def head : Loc := ⟨P.h, 8⟩
/-- `tail`. -/
def tail : Loc := ⟨P.t, 8⟩
/-- The sentinel's link. -/
def ls : Loc := ⟨P.s, 8⟩
/-- `n1`'s link. -/
def l1 : Loc := ⟨P.n1, 8⟩
/-- `n2`'s link. -/
def l2 : Loc := ⟨P.n2, 8⟩
/-- `n1`'s token (a ghost location: no access of the code has `1` byte). -/
def tok1 : Loc := ⟨P.n1, 1⟩
/-- `n2`'s token. -/
def tok2 : Loc := ⟨P.n2, 1⟩

/-- Thread `w`'s pop token (a ghost location of `10 + w` bytes: no access
of the code has that width). -/
def popTok (w : Nat) : Loc := ⟨P.h, 10 + w⟩

/-- **The tracking condition of a `head` message** of thread `w` with slot
resource `R`: untracked, or `w` is a dequeuer (`1`, `2`) and the slot holds
its pop token whole. -/
def HW (w : Nat) (R : Res) : Prop := P.trk = false ∨ ((w = 1 ∨ w = 2) ∧ 1 ≤ (R.wr (P.popTok w)).q)

/-- A link word. -/
def IsL (x : Loc) : Prop := x = P.ls ∨ x = P.l1 ∨ x = P.l2
/-- A queue word. -/
def IsW (x : Loc) : Prop := x = P.head ∨ x = P.tail ∨ P.IsL x

instance (x : Loc) : Decidable (P.IsL x) := by unfold IsL; infer_instance
instance (x : Loc) : Decidable (P.IsW x) := by unfold IsW; infer_instance

end Params

/-- The layout hypotheses: `head`, `tail` and the three links are distinct,
the nodes are non-null. -/
structure QLocs (P : Params) : Prop where
  ht : P.h ≠ P.t
  hs : P.h ≠ P.s
  h1 : P.h ≠ P.n1
  h2 : P.h ≠ P.n2
  ts : P.t ≠ P.s
  t1 : P.t ≠ P.n1
  t2 : P.t ≠ P.n2
  s1 : P.s ≠ P.n1
  s2 : P.s ≠ P.n2
  n12 : P.n1 ≠ P.n2
  n1z : P.n1 ≠ 0
  n2z : P.n2 ≠ 0

namespace QLocs

variable {P : Params} (hL : QLocs P)
include hL

theorem head_tail : P.head ≠ P.tail := by simp [Params.head, Params.tail, hL.ht]
theorem head_ls : P.head ≠ P.ls := by simp [Params.head, Params.ls, hL.hs]
theorem head_l1 : P.head ≠ P.l1 := by simp [Params.head, Params.l1, hL.h1]
theorem head_l2 : P.head ≠ P.l2 := by simp [Params.head, Params.l2, hL.h2]
theorem tail_ls : P.tail ≠ P.ls := by simp [Params.tail, Params.ls, hL.ts]
theorem tail_l1 : P.tail ≠ P.l1 := by simp [Params.tail, Params.l1, hL.t1]
theorem tail_l2 : P.tail ≠ P.l2 := by simp [Params.tail, Params.l2, hL.t2]
theorem ls_l1 : P.ls ≠ P.l1 := by simp [Params.ls, Params.l1, hL.s1]
theorem ls_l2 : P.ls ≠ P.l2 := by simp [Params.ls, Params.l2, hL.s2]
theorem l1_l2 : P.l1 ≠ P.l2 := by simp [Params.l1, Params.l2, hL.n12]
theorem tok1_tok2 : P.tok1 ≠ P.tok2 := by simp [Params.tok1, Params.tok2, hL.n12]

theorem not_isL_head : ¬ P.IsL P.head := by
  rintro (h | h | h)
  · exact hL.head_ls h
  · exact hL.head_l1 h
  · exact hL.head_l2 h

theorem not_isL_tail : ¬ P.IsL P.tail := by
  rintro (h | h | h)
  · exact hL.tail_ls h
  · exact hL.tail_l1 h
  · exact hL.tail_l2 h

theorem n1v_ne_n2v : BitVec.setWidth 128 P.n1 ≠ BitVec.setWidth 128 P.n2 := by
  intro h; apply hL.n12; have := congrArg (BitVec.setWidth 64) h; simpa using this

end QLocs

section Distinct

variable (P : Params)

theorem tok1_ne_of_8 {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ P.tok1 := by simp [Params.tok1]
theorem tok2_ne_of_8 {a : BitVec 64} : (⟨a, 8⟩ : Loc) ≠ P.tok2 := by simp [Params.tok2]

theorem not_isW_tok1 : ¬ P.IsW P.tok1 := by
  rintro (h | h | h | h | h) <;> simp [Params.tok1, Params.head, Params.tail, Params.ls, Params.l1, Params.l2] at h

theorem not_isW_tok2 : ¬ P.IsW P.tok2 := by
  rintro (h | h | h | h | h) <;> simp [Params.tok2, Params.head, Params.tail, Params.ls, Params.l1, Params.l2] at h

theorem isW_of_isL {x : Loc} (h : P.IsL x) : P.IsW x := .inr (.inr h)

theorem isW_bytes {x : Loc} (h : P.IsW x) : x.bytes = 8 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

end Distinct

/-! ## Memory facts -/

/-- **`x` is `[y]` for a value `y` of `tail` below `V`.** -/
def TailLoc (P : Params) (m : Memory) (V : View) (x : Loc) : Prop :=
  ∃ a y, a < V ∧ m.read? P.tail a = some y ∧ x = ⟨BitVec.setWidth 64 y, 8⟩

/-- **A message of value `n` below `V` at a `TailLoc` address** (the
address's `tail` read is below `V`). -/
def LinkMsg (P : Params) (m : Memory) (V : View) (n : BitVec 64) : Prop :=
  ∃ V' x' v' w', V' < V ∧ m.get? V' = some ⟨x', v', w'⟩ ∧ BitVec.setWidth 64 v' = n ∧ TailLoc P m V x'

/-- **No message of `x` strictly between `a` and `b`.** -/
def NoMsgIn (m : Memory) (x : Loc) (a b : Time) : Prop :=
  ∀ p wm, a < p → p < b → m.get? p = some wm → wm.loc ≠ x

/-- **The message overwritten at `V` is an adjacent `0`.** -/
def AdjZero (m : Memory) (x : Loc) (V : View) : Prop :=
  ∃ tr z, tr < V ∧ m.read? x tr = some z ∧ BitVec.setWidth 64 z = 0 ∧ NoMsgIn m x tr V

/-- **A swing of `tail`** at `V`: it overwrote the adjacent message `z` and
writes `v ≠ 0`, the value of a message of `[z]` below `V`. -/
def TailF (P : Params) (m : Memory) (V : View) (v : Val) : Prop :=
  BitVec.setWidth 64 v ≠ 0 ∧ ∃ tr z b y', tr < V ∧ m.read? P.tail tr = some z ∧ NoMsgIn m P.tail tr V ∧
    b < V ∧ m.read? ⟨BitVec.setWidth 64 z, 8⟩ b = some y' ∧ BitVec.setWidth 64 y' = BitVec.setWidth 64 v

/-- **The dequeuer's swing of `head`** at `V`: it overwrote the adjacent
message `z`; it read `head` (`y3`, of `z`'s 64 bits) at `tA`, then `tail`
(`yt`, other 64 bits) at `tB` with no `tail` message in `(tB, tA]`, then `[z]`
(`u`, of `v`'s 64 bits) at `tl` with no `[z]` message in `(tl, tB]`. -/
def HeadF (P : Params) (m : Memory) (V : View) (v : Val) : Prop :=
  ∃ tr z, tr < V ∧ m.read? P.head tr = some z ∧ NoMsgIn m P.head tr V ∧
    ∃ tA y3 tB yt tl u, tA < V ∧ m.read? P.head tA = some y3 ∧ BitVec.setWidth 64 y3 = BitVec.setWidth 64 z ∧
      tB < V ∧ m.read? P.tail tB = some yt ∧ BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 z ∧
      (tB < tA → NoMsgIn m P.tail tB (tA + 1)) ∧
      tl < V ∧ m.read? ⟨BitVec.setWidth 64 z, 8⟩ tl = some u ∧ BitVec.setWidth 64 u = BitVec.setWidth 64 v ∧
      NoMsgIn m ⟨BitVec.setWidth 64 z, 8⟩ tl (tB + 1)

/-- **A token whole in a resource.** -/
def TokFrozen (tok : Loc) (R : Res) : Prop := 1 ≤ (R.wr tok).q

section Mono

variable {P : Params} {m m' : Memory} (h : m.Prefix m')
include h

theorem TailLoc.mono {V : View} {x : Loc} (ht : TailLoc P m V x) : TailLoc P m' V x :=
  let ⟨a, y, ha, hr, hx⟩ := ht
  ⟨a, y, ha, read?_mono h hr, hx⟩

theorem LinkMsg.mono {V : View} {n : BitVec 64} (hl : LinkMsg P m V n) : LinkMsg P m' V n :=
  let ⟨V', x', v', w', hV, hg, hv, ht⟩ := hl
  ⟨V', x', v', w', hV, Memory.get?_of_prefix h.2 hg, hv, ht.mono h⟩

theorem NoMsgIn.mono {x : Loc} {a b : Time} (hb : b ≤ m.last + 1) (hn : NoMsgIn m x a b) : NoMsgIn m' x a b :=
  fun p wm h1 h2 hw => hn p wm h1 h2 (Memory.get?_of_prefix_le h.2 (by simp only [Time] at *; omega) hw)

theorem AdjZero.mono {x : Loc} {V : View} (hV : V ≤ m.last + 1) (ha : AdjZero m x V) : AdjZero m' x V :=
  let ⟨tr, z, h1, h2, h3, h4⟩ := ha
  ⟨tr, z, h1, read?_mono h h2, h3, h4.mono h hV⟩

theorem TailF.mono {V : View} {v : Val} (hV : V ≤ m.last + 1) (ht : TailF P m V v) : TailF P m' V v :=
  let ⟨hnz, tr, z, b, y', h1, h2, h3, h4, h5, h6⟩ := ht
  ⟨hnz, tr, z, b, y', h1, read?_mono h h2, h3.mono h hV, h4, read?_mono h h5, h6⟩

theorem HeadF.mono {V : View} {v : Val} (hV : V ≤ m.last + 1) (hh : HeadF P m V v) : HeadF P m' V v := by
  obtain ⟨tr, z, h1, h2, h3, tA, y3, tB, yt, tl, u, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hh
  refine ⟨tr, z, h1, read?_mono h h2, h3.mono h hV, tA, y3, tB, yt, tl, u, h4, read?_mono h h5, h6, h7,
    read?_mono h h8, h9, fun hlt => (h10 hlt).mono h (by simp only [Time, View] at *; omega), h11,
    read?_mono h h12, h13, h14.mono h (by simp only [Time, View] at *; omega)⟩

end Mono

/-! ## The predicate -/

/-- The link facts of a message `(x, v)` at `V` with resource `R`. -/
def LinkF (P : Params) (m : Memory) (V : View) (R : Res) (x : Loc) (v : Val) : Prop :=
  ((BitVec.setWidth 64 v = P.n1 ∧ TokFrozen P.tok1 R) ∨
    (BitVec.setWidth 64 v = P.n2 ∧ TokFrozen P.tok2 R ∧ LinkMsg P m V P.n1)) ∧
  TailLoc P m V x ∧ AdjZero m x V

/-- **The predicate of the queue words.** -/
def form (P : Params) : Pred where
  P v m V R := V ≠ 0 → ∃ x w, m.get? V = some ⟨x, v, w⟩ ∧ (P.IsL x → LinkF P m V R x v) ∧
    (x = P.head → HeadF P m V v ∨ TailLoc P m V x) ∧
    (x = P.tail → TailF P m V v ∨ TailLoc P m V x) ∧
    (x = P.head → TailLoc P m V x ∨ P.HW w R)
  mono v m m' V R hpre h := by
    intro hV
    obtain ⟨x, w, hg, h1, h2, h3, h4⟩ := h hV
    have hle : V ≤ m.last + 1 := Nat.le_succ_of_le (m.last_le_of_get?_eq_some hg)
    refine ⟨x, w, Memory.get?_of_prefix hpre.2 hg, fun hx => ?_, fun hx => ?_, fun hx => ?_,
      fun hx => (h4 hx).imp (TailLoc.mono hpre) id⟩
    · obtain ⟨h4, h5, h6⟩ := h1 hx
      exact ⟨h4.imp id fun h7 => ⟨h7.1, h7.2.1, h7.2.2.mono hpre⟩, h5.mono hpre, h6.mono hpre hle⟩
    · exact (h2 hx).imp (HeadF.mono hpre hle) (TailLoc.mono hpre)
    · exact (h3 hx).imp (TailF.mono hpre hle) (TailLoc.mono hpre)

/-- `form` is impure at every value: it needs the message. -/
theorem form_not_pure (P : Params) (v : Val) : ¬ Pred.Pure (form P) v := by
  intro h
  obtain ⟨x, w, hg, -⟩ := h { init := [], msgs := #[] } 1 (by decide)
  simp [Memory.get?] at hg

/-! ## The initial ghost -/

/-- The queue words, as a list. -/
def wList (P : Params) : List Loc := [P.head, P.tail, P.ls, P.l1, P.l2]

theorem mem_wList {P : Params} {x : Loc} : x ∈ wList P ↔ P.IsW x := by
  simp [wList, Params.IsW, Params.IsL]

/-- **The initial ghost**: `form` at the queue words (`Pred.emp` elsewhere);
acquire table `[form]`; the initial messages of the queue words in release
mode with unit slots for id `0`. -/
def ghost₀ (P : Params) : Ghost where
  rel x := if P.IsW x then form P else Pred.emp
  acqTab := [form P]
  u := (wList P).map fun x => ⟨(x, 0), 0, Res.unit⟩
  relMsgs := (wList P).map fun x => (x, 0)
  pend := []
  upd _ := []
  claims := []

theorem ghost₀_rel_w {P : Params} {x : Loc} (h : P.IsW x) : (ghost₀ P).rel x = form P := by
  simp [ghost₀, h]

theorem ghost₀_rel_ne {P : Params} {x : Loc} (h : ¬ P.IsW x) : (ghost₀ P).rel x = Pred.emp := by
  simp [ghost₀, h]

theorem ghost₀_pend (P : Params) : ∀ ts, ts ∉ (ghost₀ P).pend := fun _ h => by cases h

/-! ## The plans -/

/-- The enqueuer's entries at a link word: `n1` gives `n1`'s token, `n2`
`n2`'s, any other value nothing. -/
def linkEntries (P : Params) (x : Loc) : List Plan.Entry :=
  [{ loc := x, val := some (BitVec.setWidth 128 P.n1), gives := [P.tok1] },
    { loc := x, val := some (BitVec.setWidth 128 P.n2), gives := [P.tok2] }, { loc := x, gives := [] }]

/-- **The enqueuer's plan**: every write to a queue word is a release; at the
links, by value, it gives the node's token. -/
def planE (P : Params) : Plan :=
  ⟨[{ loc := P.head, gives := [] }, { loc := P.tail, gives := [] }] ++ linkEntries P P.ls ++
    linkEntries P P.l1 ++ linkEntries P P.l2⟩

/-- **The dequeuer's plan**: every write to a queue word is a release giving
nothing. -/
def planD (P : Params) : Plan :=
  ⟨(wList P).map fun x => { loc := x, gives := [] }⟩

theorem planE_valid (P : Params) : (planE P).Valid := by
  intro e he
  simp only [planE, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [tok1_ne_of_8, tok2_ne_of_8, Params.ls, Params.l1, Params.l2]

theorem planD_valid (P : Params) : (planD P).Valid := by
  intro e he
  simp only [planD, wList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

/-- What the enqueuer's release of `v` to `l` gives. -/
def gE (P : Params) (l : Loc) (v : Val) : List Loc :=
  if P.IsL l then (if v = BitVec.setWidth 128 P.n1 then [P.tok1]
    else if v = BitVec.setWidth 128 P.n2 then [P.tok2] else []) else []

theorem planE_find_mem {P : Params} {l : Loc} {v : Val} {e : Plan.Entry} (h : (planE P).find? l v = some e) :
    e.loc = l ∧ e.split = none ∧ P.IsW e.loc ∧ (e.gives = [] ∨ e.gives = [P.tok1] ∨ e.gives = [P.tok2]) := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨hp.1, ?_⟩
  simp only [planE, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Params.IsW, Params.IsL]

theorem planD_find_mem {P : Params} {l : Loc} {v : Val} {e : Plan.Entry} (h : (planD P).find? l v = some e) :
    e.loc = l ∧ e.split = none ∧ e.gives = [] := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  refine ⟨hp.1, ?_⟩
  simp only [planD, wList, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> simp

theorem planE_rel (P : Params) (l : Loc) (v : Val) : (planE P).rel l v = decide (P.IsW l) := by
  unfold Plan.rel
  cases h : (planE P).find? l v with
  | some e => obtain ⟨rfl, -, hw, -⟩ := planE_find_mem h; simp [hw]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro hw
    rw [Plan.find?, List.find?_eq_none] at h
    simp only [planE, linkEntries, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false, Bool.and_eq_true, decide_eq_true_eq, not_and, forall_eq_or_imp, forall_eq] at h
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact h.1 rfl trivial
    · exact h.2.1 rfl trivial
    · exact h.2.2.2.2.1 rfl trivial
    · exact h.2.2.2.2.2.2.2.1 rfl trivial
    · exact h.2.2.2.2.2.2.2.2.2.2 rfl trivial

theorem planD_rel (P : Params) (l : Loc) (v : Val) : (planD P).rel l v = decide (P.IsW l) := by
  unfold Plan.rel
  cases h : (planD P).find? l v with
  | some e =>
    obtain ⟨rfl, -, -⟩ := planD_find_mem h
    have hm := List.mem_of_find?_eq_some h
    simp only [planD, List.mem_map, mem_wList] at hm
    obtain ⟨x, hx, rfl⟩ := hm
    simp [hx]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq, decide_eq_false_iff_not]
    intro hw
    rw [Plan.find?, List.find?_eq_none] at h
    have := h { loc := l, gives := [] } (by simp only [planD, List.mem_map]; exact ⟨l, mem_wList.mpr hw, rfl⟩)
    simp at this

theorem planE_gives {P : Params} (hL : QLocs P) {l : Loc} (hl : P.IsW l) (v : Val) :
    (planE P).gives l v = gE P l v := by
  have h1 := hL.head_tail; have h2 := hL.head_ls; have h3 := hL.head_l1; have h4 := hL.tail_ls
  have h5 := hL.tail_l1; have h6 := hL.ls_l1; have h7 := hL.head_l2; have h8 := hL.tail_l2
  have h9 := hL.ls_l2; have h10 := hL.l1_l2
  have hv := hL.n1v_ne_n2v
  unfold Plan.gives gE Plan.find?
  rcases hl with rfl | rfl | rfl | rfl | rfl <;>
    by_cases ha : v = BitVec.setWidth 128 P.n1 <;> by_cases hb : v = BitVec.setWidth 128 P.n2 <;>
    simp_all [planE, linkEntries, Params.IsL, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h9,
      Ne.symm h10, eq_comm]

theorem planE_keep (P : Params) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planE P).keep l v cl r = Res.drop ((planE P).gives l v) r := by
  unfold Plan.keep Plan.gives
  cases h : (planE P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.keep, (planE_find_mem h).2.1]

theorem planE_give (P : Params) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planE P).give l v cl r = Res.only ((planE P).gives l v) r := by
  unfold Plan.give Plan.gives
  cases h : (planE P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.give, (planE_find_mem h).2.1]

theorem planE_gives_sub (P : Params) (l : Loc) (v : Val) {x : Loc} (h1 : x ≠ P.tok1) (h2 : x ≠ P.tok2) :
    x ∉ (planE P).gives l v := by
  unfold Plan.gives
  cases h : (planE P).find? l v with
  | none => simp
  | some e => rcases (planE_find_mem h).2.2.2 with h' | h' | h' <;> simp [h', h1, h2]

theorem planD_gives (P : Params) (l : Loc) (v : Val) : (planD P).gives l v = [] := by
  unfold Plan.gives
  cases h : (planD P).find? l v with
  | none => rfl
  | some e => simp [(planD_find_mem h).2.2]

theorem planD_keep (P : Params) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD P).keep l v cl r = Res.drop [] r := by
  unfold Plan.keep
  cases h : (planD P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.keep, (planD_find_mem h).2.1, (planD_find_mem h).2.2]

theorem planD_give (P : Params) (l : Loc) (v : Val) (cl : Prop) (r : Res) :
    (planD P).give l v cl r = Res.only [] r := by
  unfold Plan.give
  cases h : (planD P).find? l v with
  | none => rfl
  | some e => simp [Plan.Entry.give, (planD_find_mem h).2.1, (planD_find_mem h).2.2]

/-! ## The initial resources -/

/-- The enqueuer's initial fractions: half of `head` and `tail`, all of every
other location. -/
def fracE (P : Params) (x : Loc) : Rat := if x = P.head ∨ x = P.tail then 1 / 2 else 1

/-- The dequeuer's initial fractions: half of `head` and `tail`. -/
def fracD (P : Params) (x : Loc) : Rat := if x = P.head ∨ x = P.tail then 1 / 2 else 0

theorem fracE_nonneg (P : Params) (x : Loc) : 0 ≤ fracE P x := by unfold fracE; split <;> grind
theorem fracD_nonneg (P : Params) (x : Loc) : 0 ≤ fracD P x := by unfold fracD; split <;> grind

theorem frac_add_le (P : Params) (x : Loc) : fracE P x + fracD P x ≤ 1 := by
  unfold fracE fracD; split <;> grind

/-- The enqueuer's initial resource (no acquire id). -/
def resE (m : Memory) (P : Params) : Res := Res.initOf m (fracE P) (fracE_nonneg P)

/-- The dequeuer's initial resource: half of `head`/`tail` and the acquire id
`0` of every queue word. -/
def resD (m : Memory) (P : Params) : Res :=
  ⟨(Res.initOf m (fracD P) (fracD_nonneg P)).wr, fun x ι => if P.IsW x ∧ ι = 0 then 1 else 0⟩

/-- The initial thread resources: the enqueuer is thread `0`, the dequeuer
thread `1`. -/
def tRes (m : Memory) (P : Params) (i : Nat) : Res :=
  if i = 0 then resE m P else if i = 1 then resD m P else Res.unit

/-! ## Initial erasure -/

section Init

variable {s0 s1 : I.State} {initMem : List (Loc × Val)}

theorem slotsRes_ghost₀ (P : Params) : (ghost₀ P).slotsRes = Res.unit := by
  simp [Ghost.slotsRes, ghost₀, wList, Res.prod, Res.op_unit]

theorem total_init (P : Params) (m : Memory) :
    total (tRes m P) (ghost₀ P) (Config.init [s0, s1] initMem) = (resE m P).op (resD m P) := by
  simp only [total, Config.init_size, threadsRes, slotsRes_ghost₀, Res.op_unit, List.length_cons,
    List.length_nil]
  show Res.prod [tRes m P 0, tRes m P 1] = _
  simp [tRes, Res.op_unit]

/-- **Initial erasure of the queue, for any thread resources** whose total
holds the acquire id `0` of every queue word once, at most a whole write
fraction of every location, and only the initial message in its write sets
(as `MsQueue.erase_init_ghost2`: `erase_init` and
`MsQueue3X.erase_init3` are its instances). -/
theorem erase_init_ghostX {P : Params} (hL : QLocs P) (T : Nat → Prop) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res}
    (ha : ∀ x ι, (total rF (ghost₀ P) (Config.init states initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0)
    (hq : ∀ x, ((total rF (ghost₀ P) (Config.init states initMem)).wr x).q ≤ 1)
    (hX : ∀ x, 0 < ((total rF (ghost₀ P) (Config.init states initMem)).wr x).q → ∀ p,
      ((total rF (ghost₀ P) (Config.init states initMem)).wr x).X p ↔
        p = ((Config.init states initMem).mem.initVal x, 0)) :
    Erase rF (ghost₀ P) T (Config.init states initMem) := by
  have hids : ∀ x, (ghost₀ P).acqIds
      (total rF (ghost₀ P) (Config.init states initMem)).acq x =
        if P.IsW x then [0] else [] := by
    intro x
    simp only [Ghost.acqIds]
    rw [show (ghost₀ P).acqTab.length = 1 from rfl]
    by_cases hx : P.IsW x <;> simp [hx, ha]
  have hmem : ∀ s ∈ (ghost₀ P).u, ∃ x, P.IsW x ∧ s = ⟨(x, 0), 0, Res.unit⟩ := by
    intro s hs
    simp only [ghost₀, List.mem_map] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨x, mem_wList.mp hx, rfl⟩
  refine Erase.init ⟨hq, fun x ι => ?_⟩ ?_ ?_ ?_ hX ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl
  · -- valid
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
    by_cases hx : P.IsW x
    · rw [ghost₀_rel_w hx] at h
      simp only [hx, ↓reduceIte, List.map_cons, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact ⟨r, Res.unit, (Res.op_unit r).symm, h, rfl⟩
    · rw [ghost₀_rel_ne hx] at h
      simp only [hx, ↓reduceIte, List.map_nil, Ghost.updPreds, ghost₀, List.append_nil]
      exact h
  · -- relaxed initial messages are pure
    intro x hx
    have hx' : ¬ P.IsW x := fun h => hx (by simp [ghost₀, List.mem_map, mem_wList, h])
    rw [ghost₀_rel_ne hx']
    exact Pred.emp_pure _
  · -- release messages are initial
    intro k hk
    simp only [ghost₀, List.mem_map] at hk
    obtain ⟨x, -, rfl⟩ := hk; rfl
  · -- slots are distinct
    simp only [ghost₀, wList, List.map_cons, List.map_nil]
    have h1 := hL.head_tail; have h2 := hL.head_ls; have h3 := hL.head_l1; have h4 := hL.tail_ls
    have h5 := hL.tail_l1; have h6 := hL.ls_l1; have h7 := hL.head_l2; have h8 := hL.tail_l2
    have h9 := hL.ls_l2; have h10 := hL.l1_l2
    simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  · -- slot domain
    intro k ι
    rw [ha]
    constructor
    · rintro ⟨s, hs, rfl, rfl⟩
      obtain ⟨x, hx, rfl⟩ := hmem s hs
      exact ⟨by simp [ghost₀, List.mem_map, mem_wList, hx], .inl (by simp [hx])⟩
    · rintro ⟨hk, h⟩
      simp only [ghost₀, List.mem_map, mem_wList] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      have hι : ι = 0 := by
        rcases h with h | h
        · simp only [hx, true_and] at h; split at h <;> grind
        · simp [ghost₀] at h
      subst hι
      exact ⟨⟨(x, 0), 0, Res.unit⟩, by simp [ghost₀, List.mem_map, mem_wList, hx], rfl, rfl⟩
  · -- slots satisfy their predicates at the initial message (view `0`)
    intro s hs
    obtain ⟨x, -, rfl⟩ := hmem s hs
    exact fun h => absurd rfl h
  · -- update ids
    intro x
    simp [ghost₀]


/-- **Initial erasure of the queue.** -/
theorem erase_init {P : Params} (hL : QLocs P) (T : Nat → Prop) :
    Erase (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P) T (Config.init [s0, s1] initMem) := by
  have htot := total_init (s0 := s0) (s1 := s1) (initMem := initMem) P (Config.init [s0, s1] initMem).mem
  have ha : ∀ x ι, (total (tRes (Config.init [s0, s1] initMem).mem P) (ghost₀ P)
      (Config.init [s0, s1] initMem)).acq x ι = if P.IsW x ∧ ι = 0 then 1 else 0 := by
    intro x ι; rw [htot]; show 0 + (if P.IsW x ∧ ι = 0 then 1 else 0) = _; simp
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
  refine erase_init_ghostX hL T ha (fun x => by rw [hq]; exact frac_add_le P x) ?_
  -- write sets
  intro x hpos p
  rw [hX]
  have : 0 < fracE P x ∨ 0 < fracD P x := by
    rw [hq] at hpos
    have := fracE_nonneg P x; have := fracD_nonneg P x
    by_cases h0 : 0 < fracE P x
    · exact .inl h0
    · exact .inr (by grind)
  simp [this]

end Init

end Kraken.Promising.X64.EnvG.MsQueueX
