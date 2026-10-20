/-
**The (c′) linearizability spec of a single-word
concurrent stack** (ISA-neutral, program-independent).

Design (c′): a procedure-level, logically atomic specification whose
abstract state is the message history of `top` with per-thread views. This
is the earlier `LinSpec` with the corrections from the `treiber2` prototype applied:

- a history entry (`PEnt`) carries its **pinned** operation and a `pend`
  flag (outstanding promise of its writer); the pinned operation is a
  function of the prefix (`pinOf`), not "some completion exists";
- the empty-pop bracket is "no `top` write in `(r, k0]`" (`LinStep`, read
  disjunct), not `k0 ≤ r`;
- a promise appends a history entry only for a `top` message (`pAppend`);
- no `LiveK` anywhere (the lifting, `Lin/Lift.lean`, needs none);
- the commit (the instruction step that writes or fulfils the `top`
  message) is the linearization point of a writing operation, with the view
  bracket `k0 < q ≤ coh′` (`LinStep`, commit disjunct).

Contents:

1. the abstract object: `Op`, `Call`, `seqStep`, `seqStack`, `headOr0`;
2. the history: `Pos`, `PEnt`, `wrUpTo` (write entries up to a timestamp),
   `stkL` (the stack after them), `Pushed`, `pinOf`;
3. the node layout `StackLayout` (`top`, the link word, the node words, the
   per-thread arenas: ownership before publication) and the lawfulness of a
   message `PhiH` (prefix-local: on the memory cut at the message, `cut`);
4. the **structure part** of the invariant, `Struct`: the `top` history
   matches `top`'s messages, pending entries are outstanding promises, the
   history is sorted, every committed message is lawful (this carries the
   per-node "frozen after publication" facts: a message to a node word
   requires the node not to be pushed below it), read-only entries see the
   empty stack;
5. the abstract steps: `LinStep` (instruction steps: stutter, commit, empty
   pop), `PStepL` (promise steps), `Agree`, and their agreement lemmas.

Every statement here is about configurations of any `ISA`; which machine
steps them is said where they are used (`Lin/Frame.lean`: the fuel-free
semantic machine `StepSemInf`).
-/
import Kraken.Promising.LiveSemInf

namespace Kraken.Promising.Lin

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## 1. The abstract object -/

/-- A node (its address as a 64-bit value; `0` is null). -/
abbrev Node := BitVec 64

/-- An operation with its result: push of `n`; pop returning `some n`, or
`none` when it found the stack empty. -/
inductive Op where
  | push (n : Node)
  | pop (r : Option Node)
  deriving DecidableEq, Repr

/-- An invocation (an operation without its result). -/
inductive Call where
  | push (n : Node)
  | pop
  deriving DecidableEq, Repr

/-- The invocation an operation answers. -/
def Op.call : Op → Call
  | .push n => .push n
  | .pop _ => .pop

/-- **The sequential stack**: one step. -/
def seqStep : List Node → Op → Option (List Node)
  | s, .push n => some (n :: s)
  | n' :: s, .pop (some n) => if n = n' then some s else none
  | [], .pop none => some []
  | _, _ => none

/-- **The sequential stack**: a run from the empty stack. -/
def seqStack (ops : List Op) : Option (List Node) := ops.foldlM seqStep []

/-- `top`'s value for an abstract stack: its head, `0` when empty. -/
def headOr0 : List Node → Node
  | [] => 0
  | n :: _ => n

/-! ## 2. The history -/

/-- Where a linearization point sits in `top`'s coherence order: the write of
`top`'s message at `ts`, or a read-only LP (an empty pop) right after the
message at `ts`. -/
inductive Pos where
  | wr (ts : Time)
  | rd (ts : Time)
  deriving DecidableEq, Repr

/-- The timestamp a position refers to. -/
def Pos.ts : Pos → Time
  | .wr t => t
  | .rd t => t

/-- Strictly before: earlier timestamp, or a write before the reads of it. -/
def Pos.lt : Pos → Pos → Prop
  | .wr t, .wr t' => t < t'
  | .wr t, .rd t' => t ≤ t'
  | .rd t, .wr t' => t < t'
  | .rd t, .rd t' => t < t'

/-- **A history entry**: position, thread, its **pinned** operation, and
whether it is still an outstanding promise of `tid` (`pend`). -/
structure PEnt where
  pos : Pos
  tid : Nat
  op : Op
  pend : Bool
  deriving DecidableEq, Repr

/-- **A thread's abstract state**: idle; running an invocation, with its
coherence view `k0` of `top` at invocation; or returned (its LP done at
`pos`), until the next invocation. -/
inductive TAbs where
  | idle
  | run (call : Call) (k0 : Time)
  | ret (op : Op) (k0 : Time) (pos : Pos)

/-- **The abstract state**: the history and every thread's abstract state. -/
structure AS where
  H : List PEnt
  th : Nat → TAbs

/-- The history is in coherence order (read-only entries of one message may
repeat; they commute). -/
def Sorted (H : List PEnt) : Prop :=
  H.Pairwise fun e e' => e.pos.lt e'.pos ∨ (e.pos = e'.pos ∧ ∃ r, e.pos = .rd r)

/-- The write entries at or below `p`: (timestamp, writer, pinned op). -/
def wrUpTo (p : Time) (H : List PEnt) : List (Time × Nat × Op) :=
  H.filterMap fun e => match e.pos with
    | .wr t => if t ≤ p then some (t, e.tid, e.op) else none
    | .rd _ => none

/-- The stack after the write entries of `Lw` at or below `p` (empty pops do
not change the stack). -/
def stkL (Lw : List (Time × Nat × Op)) (p : Time) : Option (List Node) :=
  seqStack ((Lw.filter fun e => decide (e.1 ≤ p)).map (·.2.2))

/-- Node `n` has a push entry strictly below `q`. -/
def Pushed (n : Node) (q : Time) (Lw : List (Time × Nat × Op)) : Prop :=
  ∃ e ∈ Lw, e.1 < q ∧ e.2.2 = .push n

/-- **The pinned operation of a `top` write of value `v` at `q`**, from the
prefix alone: a push of `v` if `v` is a node never pushed below `q`, else a
pop of the head before `q`. (Single-use nodes: a pop writes `0` or a node
already pushed; a push writes a fresh node.) -/
def pinOf (Lw : List (Time × Nat × Op)) (q : Time) (v : Node) : Op :=
  if v ≠ 0 ∧ (Lw.any fun e => decide (e.1 < q) && decide (e.2.2 = .push v)) = false then .push v
  else .pop (some (headOr0 ((stkL Lw (q - 1)).getD [])))

/-- **Payload acquisition** of node `n` by a thread with views `vs`: its
read view covers a push of `n`. A push's `top` write is a release, so what
the pusher wrote before is below it. -/
def AcqOf (H : List PEnt) (vs : Views) (n : Node) : Prop :=
  ∃ e ∈ H, ∃ q, e.pos = .wr q ∧ e.op = .push n ∧ q ≤ vs.vrNew

/-! ## 3. Node layout and lawfulness of a message -/

/-- **The node layout** of a stack instance: the `top` location, each node's
link word and node words, and the per-thread allocation arenas (a node of
`arena w` is owned by `w` until it is published by a push). -/
structure StackLayout where
  top : Loc
  link : Node → Loc
  words : Node → Loc → Prop
  arena : Nat → Node → Prop
  link_word : ∀ n, words n (link n)

/-- No write to `l` strictly between `a` and `b`. -/
def NoWriteIn (m : Memory) (l : Loc) (a b : Time) : Prop :=
  ∀ q wm, a < q → q < b → m.get? q = some wm → wm.loc ≠ l

/-- The memory up to timestamp `q`. -/
def cut (m : Memory) (q : Time) : Memory := { init := m.init, msgs := m.msgs.extract 0 q }

/-- **Lawfulness of message `msg` of writer `w` at `q`** (memory `m`, write
entries `Lw`; used on the cut at `q`):
- a `top` message is the entry `(q, w, pinOf …)`, the history up to it is a
  legal stack run whose head is the message's value, and a push is of a node
  of `w`'s arena whose link word's last write below `q` holds the head
  before `q`;
- any other message, if it is to a node word, is to a node of `w`'s arena
  that is not pushed below `q` (owned and unpublished: hence node words are
  **frozen after publication**). -/
def MsgOK (L : StackLayout) (w : Nat) (q : Time) (msg : Msg) (m : Memory) (Lw : List (Time × Nat × Op)) :
    Prop :=
  msg.tid = w ∧
  (msg.loc = L.top →
    (q, w, pinOf Lw q (BitVec.setWidth 64 msg.val)) ∈ Lw ∧
    (∃ st, stkL Lw q = some st ∧ BitVec.setWidth 64 msg.val = headOr0 st) ∧
    ∀ n, pinOf Lw q (BitVec.setWidth 64 msg.val) = .push n → L.arena w n ∧
      ∃ s lv st0, s < q ∧ m.read? (L.link n) s = some lv ∧ NoWriteIn m (L.link n) s q ∧
        stkL Lw (q - 1) = some st0 ∧ BitVec.setWidth 64 lv = headOr0 st0) ∧
  (msg.loc ≠ L.top → ∀ n, L.words n msg.loc → L.arena w n ∧ ¬ Pushed n q Lw)

/-- **`Φ`: lawfulness of the message at `q`** of writer `w`, on the memory
cut at `q` and the write entries up to `q` (prefix-local by construction). -/
def PhiH (L : StackLayout) (w : Nat) (q : Time) (m : Memory) (H : List PEnt) : Prop :=
  ∃ msg, (cut m q).get? q = some msg ∧ MsgOK L w q msg (cut m q) (wrUpTo q H)

/-! ## 4. The structure part of the invariant -/

/-- `q` is an outstanding promise of thread `w`. -/
def Outst (c : Config I) (w : Nat) (q : Time) : Prop := ∃ t : Thread I, c.threads[w]? = some t ∧ q ∈ t.prom

/-- **The structure part** (client-independent): it mentions `top`, the node
words and the history only.
- `bnd`: every promise is a message (in `(0, |M|]`);
- `topE`/`topM`: the write entries are exactly `top`'s messages (writer
  included);
- `pend`: an entry is pending iff its message is an outstanding promise;
- `sorted`: coherence order;
- `committed`: every committed message is lawful (`PhiH`);
- `rd`: read-only entries are committed empty pops of the empty stack. -/
structure Struct (L : StackLayout) (c : Config I) (H : List PEnt) : Prop where
  bnd : ∀ (w : Nat) (t : Thread I), c.threads[w]? = some t → ∀ p ∈ t.prom, 0 < p ∧ p ≤ c.mem.last
  topE : ∀ e ∈ H, ∀ q, e.pos = .wr q → ∃ msg, c.mem.get? q = some msg ∧ msg.loc = L.top ∧ msg.tid = e.tid
  topM : ∀ q msg, c.mem.get? q = some msg → msg.loc = L.top → ∃ e ∈ H, e.pos = .wr q ∧ e.tid = msg.tid
  pend : ∀ e ∈ H, ∀ q, e.pos = .wr q → (e.pend = true ↔ Outst c e.tid q)
  sorted : Sorted H
  committed : ∀ q msg, c.mem.get? q = some msg → ¬ Outst c msg.tid q → PhiH L msg.tid q c.mem H
  rd : ∀ e ∈ H, ∀ r, e.pos = .rd r →
    e.op = .pop none ∧ e.pend = false ∧ r ≤ c.mem.last ∧ stkL (wrUpTo r H) r = some []

/-! ## 5. Abstract steps -/

/-- Not in the middle of an operation (idle, or returned). -/
def Idle (a : AS) (w : Nat) : Prop := a.th w = .idle ∨ ∃ op k0 p, a.th w = .ret op k0 p

/-- Only thread `w`'s abstract state may change. -/
def OK (w : Nat) (a a' : AS) : Prop := ∀ i, i ≠ w → a'.th i = a.th i

/-- Insert a read-only entry after the entries at or before its position. -/
def insertRdP (H : List PEnt) (e : PEnt) : List PEnt :=
  H.takeWhile (fun e' => decide (e'.pos.ts ≤ e.pos.ts)) ++ e ::
    H.dropWhile (fun e' => decide (e'.pos.ts ≤ e.pos.ts))

/-- **The abstract step of an instruction step of `w`** inside a fragment
(the logically atomic step relation):
- a stutter;
- **the commit** of a writing operation (push, non-empty pop): `top`'s
  message at `q` written fresh above `|M|` (appended) or by fulfilling `w`'s
  own pending entry with the same pinned operation (tagged committed); view
  bracket `k0 < q ≤ coh′(top)`;
- **an empty pop**: a read-only entry after message `r`, bracket "no `top`
  write in `(r, k0]`".
Invocations are not fragment steps; they are added at the call site
(`Lin/Frame.lean`, `InvokeAt`). -/
def LinStep (L : StackLayout) (w : Nat) (c c' : Config I) (a a' : AS) : Prop :=
  a' = a ∨
  (OK w a a' ∧ ∃ op k0 q, op ≠ .pop none ∧ a.th w = .run op.call k0 ∧ a'.th w = .ret op k0 (.wr q) ∧
    k0 < q ∧ (∃ t', c'.threads[w]? = some t' ∧ q ≤ t'.views.getCoh L.top) ∧
    ((c.mem.last < q ∧ a'.H = a.H ++ [⟨.wr q, w, op, false⟩]) ∨
      ∃ H1 H2, a.H = H1 ++ ⟨.wr q, w, op, true⟩ :: H2 ∧ a'.H = H1 ++ ⟨.wr q, w, op, false⟩ :: H2)) ∨
  (OK w a a' ∧ ∃ k0 r, a.th w = .run .pop k0 ∧ a'.th w = .ret (.pop none) k0 (.rd r) ∧
    NoWriteIn c.mem L.top r (k0 + 1) ∧ a'.H = insertRdP a.H ⟨.rd r, w, .pop none, false⟩)

/-- The history after a promise of `msg` by `w` at `q`: a pending entry with
its pinned operation for a `top` message, nothing otherwise. -/
def pAppend (L : StackLayout) (w : Nat) (q : Time) (msg : Msg) (H : List PEnt) : List PEnt :=
  if msg.loc = L.top then H ++ [⟨.wr q, w, pinOf (wrUpTo q H) q (BitVec.setWidth 64 msg.val), true⟩] else H

/-- **The abstract step of a promise step of `w`** (any thread, any
position: the machine's promise rule, not the program). -/
def PStepL (L : StackLayout) (w : Nat) (c c' : Config I) (a a' : AS) : Prop :=
  a'.th = a.th ∧ ∃ msg, c'.mem.get? (c.mem.last + 1) = some msg ∧ a'.H = pAppend L w (c.mem.last + 1) msg a.H

/-- Two abstract states agree up to `p`: the same write entries and pinned
operations at or below `p`. -/
def Agree (p : Time) (a a' : AS) : Prop := wrUpTo p a.H = wrUpTo p a'.H

/-! ## Prefix-locality and agreement -/

theorem cut_eq_of_prefix {m m' : Memory} (h : m.Prefix m') {q : Time} (hq : q ≤ m.last) :
    cut m q = cut m' q := by
  obtain ⟨hi, ⟨l, hl⟩⟩ := h
  have hsz : m.msgs.size ≤ m'.msgs.size := by
    have := congrArg List.length hl
    simp only [List.length_append, Array.length_toList] at this
    omega
  have hq' : q ≤ m.msgs.size := hq
  unfold cut
  rw [hi]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_extract, Nat.min_eq_left hq', Nat.min_eq_left (Nat.le_trans hq' hsz),
    Nat.sub_zero, Nat.zero_add]
  split
  · rename_i hlt
    have hi1 : i < m.msgs.size := Nat.lt_of_lt_of_le hlt hq'
    rw [← Array.getElem?_toList, ← Array.getElem?_toList (xs := m'.msgs), ← hl,
      List.getElem?_append_left (by simpa only [Array.length_toList] using hi1)]
  · rfl

/-- The cut agrees with the memory at or below the cut. -/
theorem cut_get? {m : Memory} {q q' : Time} (hq' : q' ≤ q) (hq : q ≤ m.last) : (cut m q).get? q' = m.get? q' := by
  unfold cut Memory.get?
  split
  · rfl
  · rename_i hne
    have hq2 : q ≤ m.msgs.size := hq
    have hlt : q' - 1 < q := Nat.lt_of_lt_of_le (Nat.sub_one_lt hne) hq'
    simp only [Array.getElem?_extract, Nat.min_eq_left hq2, Nat.sub_zero, Nat.zero_add, hlt, ↓reduceIte]

theorem phiH_prefix (L : StackLayout) (w : Nat) (q : Time) {m m' : Memory} {H H' : List PEnt} (hq : q ≤ m.last)
    (hm : m.Prefix m') (ha : wrUpTo q H = wrUpTo q H') : PhiH L w q m H ↔ PhiH L w q m' H' := by
  unfold PhiH; rw [cut_eq_of_prefix hm hq, ha]

theorem wrUpTo_append_above {p q : Time} (H : List PEnt) (w : Nat) (op : Op) (b : Bool) (hq : p < q) :
    wrUpTo p (H ++ [⟨.wr q, w, op, b⟩]) = wrUpTo p H := by
  unfold wrUpTo
  rw [List.filterMap_append]
  simp [Nat.not_le_of_lt hq]

theorem wrUpTo_tag {p t : Time} (H1 H2 : List PEnt) (w : Nat) (op : Op) (b b' : Bool) :
    wrUpTo p (H1 ++ ⟨.wr t, w, op, b⟩ :: H2) = wrUpTo p (H1 ++ ⟨.wr t, w, op, b'⟩ :: H2) := by
  unfold wrUpTo
  simp only [List.filterMap_append, List.filterMap_cons]

theorem wrUpTo_insertRd {p : Time} (H : List PEnt) (r : Time) (w : Nat) (op : Op) (b : Bool) :
    wrUpTo p (insertRdP H ⟨.rd r, w, op, b⟩) = wrUpTo p H := by
  unfold insertRdP wrUpTo
  rw [List.filterMap_append, List.filterMap_cons]
  simp only
  rw [← List.filterMap_append, List.takeWhile_append_dropWhile]

theorem agree_linStep {L : StackLayout} {w : Nat} {c c' : Config I} {a a' : AS} (h : LinStep L w c c' a a')
    (p : Time) (hp : p ≤ c.mem.last) : Agree p a a' := by
  unfold Agree
  rcases h with rfl | ⟨-, op, k0, t, -, -, -, -, -, ⟨hlt, hH⟩ | ⟨H1, H2, h1, h2⟩⟩ | ⟨-, k0, r, -, -, -, hH⟩
  · rfl
  · rw [hH, wrUpTo_append_above _ _ _ _ (Nat.lt_of_le_of_lt hp hlt)]
  · rw [h1, h2, wrUpTo_tag]
  · rw [hH, wrUpTo_insertRd]

theorem agree_pStep {L : StackLayout} {w : Nat} {c c' : Config I} {a a' : AS} (h : PStepL L w c c' a a')
    (p : Time) (hp : p ≤ c.mem.last) : Agree p a a' := by
  unfold Agree
  obtain ⟨-, msg, -, hH⟩ := h
  rw [hH]
  unfold pAppend
  split
  · rw [wrUpTo_append_above _ _ _ _ (Nat.lt_succ_of_le hp)]
  · rfl

end Kraken.Promising.Lin
