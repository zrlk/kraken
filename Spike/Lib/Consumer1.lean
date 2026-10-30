/-
**The ISA-free part of the one-thread consumers** (`Spike/Lib/A64Consumer.lean`;
an x64 twin imports it too): the source side of the memory rows, the
target memory's invariants of the relation, and small lemmas on runs,
ranges and the kernel's `write` return, none of which mentions the ISA.

Contents:

- `OneCellTy`, `SrcMem`, `srcMem`: the source side of the load and store
  rows, as hypotheses named after the lifts of `TermRun.tstep` they stand
  for (`src_store_step_cfg`, `src_load_step_cfg`), and their proof from
  `Spike.Lib.SrcMem`.
- `src_store_step`, `src_load_step`, `src_swap_step`: those lifts (and the
  exchange's, `Spike.Lib.SrcMem.src_swap_step_cfg`) as steps of thread 0 of
  the source instance (`SrcSem.source`) with no event, the thread having no
  promise and its continuation not at `ret`.
- `exists_sLatest`: a source address with a message has a latest one.
- `LocIn`, `OwnMsgs`, `InitIn`, `MemIn`, `MemFits`: the target memory's
  invariants (every message thread 0's; the memory in the layout; every
  value 64-bit), with `ownMsgs_step`, `ownMsgs_append`, `memIn_append`,
  `memIn_msgs`, `inLayout_of_memIn`, `shared_of_wordAddr`.
- `OwnUpd`, `OwnTree`, `ownOk_step`, `ownOk_promise`, `ownOk_nil`,
  `OwnInit`, `ownOk_init`: the runtime words a thread owns across an
  instruction (kept and unwritten, taken by one word store, or an owned
  word stored or updated by an RMW), and `ExtRows.OwnOk` kept by an
  instruction and a promise and holding at load (owned words at their
  initial values); `writeTree_mono`, `writeTree_true`, `allInv_true`.
- `HoldInv`, `holdInv_run`: the hold of an exchange between its load and
  its store; a local run ends with no hold.
- `Refusal`, `TI`, `sysStep_write_ret`: a refused `write`, the abort
  clause's trace invariant, and the kernel's `write` return.
- `reach_run`, `run_one`, `set_one`, `touches_mono`, `sub_contains`,
  `shared_not_pool`, `overlaps_contains`, `word_off_pool`,
  `stepOneWith_eq`: small lemmas.
- `SrcRd`, `SrcRd.of_all`: the source's reads satisfy a read predicate.
-/
import Spike.Lib.ExtRows
import Spike.Lib.SrcRun
import Spike.Lib.SrcMem
import Scc.Sem.ExtSim
import Scc.Sem.Fits

namespace Spike.Lib.Consumer1

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Sem
open Scc.Sem.SrcSem (mainExit)

/-! ## The source side of the memory rows -/

/-- **A single-word cell type**: a cell of one access unit (WeakCore's
`cellOf`, `accs`; the M1 cells). -/
def OneCellTy (ty : Ty) : Prop := ∃ μ u, cellOf ty = some (μ, u) ∧ TermRun.accs u = some [.one]

/-- **The source side of the load and store rows**: thread 0's release
store and acquire load of a single-word cell at an untagged locative, as
outcomes of its `TermRun.threadSteps` (the thread having no promise). These
are the lifts of `TermRun.tstep` through `storeUnits`/`loadUnits` (to be
proved with the `TermRun` lifts of `Spike/Lib/Seg.lean`'s rows); the load
reads the latest message at the address. -/
structure SrcMem (P : SrcSem.SrcParams) (p : Prog) : Prop where
  src_store_step_cfg : ∀ (c : TermRun.Cfg) (th : TermRun.TTh) (x : String) (a b : At) (e : Expr) (ty tb : Ty)
      (pw wb : TermRun.Word) (sa : WeakMem.Address), c.ths[0]? = some th → th.promises = [] →
    th.term = .let_ x (.store true a b none) e → TermRun.evalAt th.env a = some (ty, [pw]) →
    pw.val = .loc sa 0 → OneCellTy ty → TermRun.evalAt th.env b = some (tb, [wb]) →
    ∃ (th' : TermRun.TTh) (mv : Nat),
      { c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! 0 th' } ∈ TermRun.threadSteps p P.k P.arch c 0 ∧
      th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack
  src_load_step_cfg : ∀ (c : TermRun.Cfg) (th : TermRun.TTh) (x : String) (a : At) (e : Expr) (ty : Ty)
      (pw : TermRun.Word) (sa : WeakMem.Address) (j : Nat) (m : WeakMem.Msg), c.ths[0]? = some th →
    th.promises = [] → th.term = .let_ x (.load true a) e → TermRun.evalAt th.env a = some (ty, [pw]) →
    pw.val = .loc sa 0 → OneCellTy ty → MemRel.SLatest c.mem sa j → c.mem[j]? = some m →
    ∃ th' : TermRun.TTh, { c with ths := c.ths.set! 0 th' } ∈ TermRun.threadSteps p P.k P.arch c 0 ∧
      th'.term = e ∧ th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧
      th'.σs = th.σs ∧ th'.stack = th.stack

/-- **`SrcMem` holds.** -/
theorem srcMem (P : Scc.Sem.SrcSem.SrcParams) (p : Prog) : SrcMem P p where
  src_store_step_cfg c th x a b e ty tb pw wb sa h0 hp ht hea hpw hone heb := by
    obtain ⟨μ, u, hcell, hu⟩ := hone
    exact Spike.Lib.SrcMem.src_store_step_cfg h0 ht hea heb hpw hcell hu hp
  src_load_step_cfg c th x a e ty pw sa j m h0 hp ht hea hpw hone hj hm := by
    obtain ⟨μ, u, hcell, hu⟩ := hone
    obtain ⟨th', h, h1, h2, h3, h4, h5⟩ := Spike.Lib.SrcMem.src_load_step_cfg (p := p) (k := P.k) (arch := P.arch)
      h0 ht hea hpw hcell hu hj hm
    exact ⟨th', h, h1, h2, h3.trans hp, h4, h5⟩

variable {P : SrcSem.SrcParams} {p : Prog}

/-- **A thread step of thread 0 with no promise after it, `main` not
returned before or after it, is a step of the source instance with no
event** (certified by the empty solo run). -/
theorem src_step_of_threadSteps (hP : HookOK P p) {c c' : TermRun.Cfg} {th' : TermRun.TTh}
    (hm : c' ∈ TermRun.threadSteps p P.k P.arch c 0) (h0 : c'.ths[0]? = some th') (hp : th'.promises = [])
    (hx : mainExit c = []) (hx' : mainExit c' = []) : (SrcSem.source P p).step 0 c [] c' := by
  have hs : SrcSem.StepBy p P.k P.arch 0 c c' := .inl ⟨hm, ⟨_, .refl _, by simp [TermRun.noPromises, h0, hp]⟩⟩
  exact ⟨hx, .inl hs, (obs_nil (hP.trace_stepBy hs) hx hx').symm⟩

/-- **The source store of the store row** is a step of thread 0 of the
source instance with no event, pushing the message, when its continuation
is not at `ret`. -/
theorem src_store_step (hP : HookOK P p) (hS : SrcMem P p) {c : TermRun.Cfg}
    {th : TermRun.TTh} {x : String} {a b : At} {e : Expr} {ty tb : Ty} {pw wb : TermRun.Word}
    {sa : WeakMem.Address} (h0 : c.ths[0]? = some th) (hp : th.promises = [])
    (ht : th.term = .let_ x (.store true a b none) e) (hea : TermRun.evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : OneCellTy ty) (heb : TermRun.evalAt th.env b = some (tb, [wb]))
    (hr : ∀ a, e ≠ .ret a) :
    ∃ (th' : TermRun.TTh) (mv : Nat), (SrcSem.source P p).step 0 c []
        { c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, .unit, []) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack := by
  obtain ⟨th', mv, hm, hte, hen, hp', hσ, hst⟩ := hS.src_store_step_cfg c th x a b e ty tb pw wb sa h0 hp ht hea hpw
    hcell heb
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with mem := c.mem.push ⟨sa, wb.val, mv⟩, ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? =
      some th' := by simp [hlt]
  refine ⟨th', mv, src_step_of_threadSteps hP hm h0' hp' (mainExit_of_not_ret h0 ?_)
    (mainExit_of_not_ret h0' (hte ▸ hr)), hte, hen, hp', hσ, hst⟩
  intro a' h; rw [ht] at h; cases h

/-- **The source load of the load row** is a step of thread 0 of the source
instance with no event, reading the latest message, when its continuation
is not at `ret`. -/
theorem src_load_step (hP : HookOK P p) (hS : SrcMem P p) {c : TermRun.Cfg}
    {th : TermRun.TTh} {x : String} {a : At} {e : Expr} {ty : Ty} {pw : TermRun.Word} {sa : WeakMem.Address}
    {j : Nat} {m : WeakMem.Msg} (h0 : c.ths[0]? = some th) (hp : th.promises = [])
    (ht : th.term = .let_ x (.load true a) e) (hea : TermRun.evalAt th.env a = some (ty, [pw]))
    (hpw : pw.val = .loc sa 0) (hcell : OneCellTy ty) (hj : MemRel.SLatest c.mem sa j) (hm : c.mem[j]? = some m)
    (hr : ∀ a, e ≠ .ret a) :
    ∃ th' : TermRun.TTh, (SrcSem.source P p).step 0 c [] { c with ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, loadTy ty, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧
      th'.σs = th.σs ∧ th'.stack = th.stack := by
  obtain ⟨th', hst, hte, hen, hp', hσ, hsk⟩ := hS.src_load_step_cfg c th x a e ty pw sa j m h0 hp ht hea hpw hcell hj hm
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? = some th' := by simp [hlt]
  refine ⟨th', src_step_of_threadSteps hP hst h0' hp' (mainExit_of_not_ret h0 ?_)
    (mainExit_of_not_ret h0' (hte ▸ hr)), hte, hen, hp', hσ, hsk⟩
  intro a' h; rw [ht] at h; cases h

/-- **The source exchange** at an exchange site (`XchgSite`), as a step of
thread 0 of the source instance with no event (`SrcMem.src_swap_step_cfg`):
it reads the latest message `j` at `sa` and appends `v`'s word there,
binding the old word; the thread has no promise and its continuation is not
at `ret`. -/
theorem src_swap_step (hP : HookOK P p) {c : TermRun.Cfg} {th : TermRun.TTh} {x : String}
    {sa : WeakMem.Address} {u : Ty} {v : At} {e : Expr} {tv : Ty} {wv : TermRun.Word} {j : Nat} {m : WeakMem.Msg}
    (h0 : c.ths[0]? = some th) (hp : th.promises = []) (hs : XchgSite ⟨th.term, th.env, none⟩ x sa u v e)
    (hev : TermRun.evalAt th.env v = some (tv, [wv])) (hj : MemRel.SLatest c.mem sa j) (hm : c.mem[j]? = some m)
    (hr0 : ∀ a, th.term ≠ .ret a) (hr : ∀ a, e ≠ .ret a) :
    ∃ (th' : TermRun.TTh) (mv : Nat), (SrcSem.source P p).step 0 c []
        { c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! 0 th' } ∧
      th'.term = e ∧ th'.env = (x, u, [⟨m.val, m.view, j⟩]) :: th.env ∧ th'.promises = [] ∧ th'.σs = th.σs ∧
      th'.stack = th.stack := by
  obtain ⟨th', mv, hst, hte, hen, hp', hσ, hsk⟩ :=
    Spike.Lib.SrcMem.src_swap_step_cfg (p := p) (k := P.k) (arch := P.arch) h0 hs hev hp hj hm
  have hlt : 0 < c.ths.size := (Array.getElem?_eq_some_iff.mp h0).1
  have h0' : ({ c with mem := c.mem.push ⟨sa, wv.val, mv⟩, ths := c.ths.set! 0 th' } : TermRun.Cfg).ths[0]? =
      some th' := by simp [hlt]
  exact ⟨th', mv, src_step_of_threadSteps hP hst h0' hp' (mainExit_of_not_ret h0 hr0)
    (mainExit_of_not_ret h0' (hte ▸ hr)), hte, hen, hp', hσ, hsk⟩

/-- **A source address with a message has a latest message.** -/
theorem exists_sLatest {sm : WeakMem.Memory} {sa : WeakMem.Address}
    (h : ∃ (k : Nat) (m : WeakMem.Msg), sm[k]? = some m ∧ m.loc = sa) :
    ∃ j, MemRel.SLatest sm sa j := by
  obtain ⟨j, ⟨m, hm, hl⟩, hlast⟩ :=
    ExtRows.exists_last (fun k => ∃ m : WeakMem.Msg, sm[k]? = some m ∧ m.loc = sa) sm.size
    (fun k ⟨m, hm, _⟩ => (Array.getElem?_eq_some_iff.mp hm).1)
    (let ⟨k, m, h⟩ := h; ⟨k, m, h⟩)
  exact ⟨j, ⟨m, hm, hl⟩, fun k m' hk hm' hl' => hlast k hk ⟨m', hm', hl'⟩⟩

/-! ## The target memory -/

/-- **Every byte of the location `l` satisfies `P`** (the bytes `Kernel.fresh`
compares, `Kernel.locBytes`). -/
def LocIn (P : Nat → Prop) (l : Loc) : Prop := ∀ i < Kernel.locBytes l, P (l.addr.toNat + i)

theorem LocIn.addr {P : Nat → Prop} {l : Loc} (h : LocIn P l) : P l.addr.toNat := by
  have := h 0 (by unfold Kernel.locBytes; split <;> omega)
  simpa using this

/-- **A refused `write`** of `n` bytes with the result `r`: the kernel returns
`r` and emits `writeErr` exactly when `r` is a refusal
(`Kernel.writeRefused`) and not a byte count `1 … n` (once a byte is out
the call returns only the count, with no event; `Kernel.sysStep`). -/
def Refusal (n : Nat) (r : BitVec 64) : Prop :=
  Kernel.writeRefused r = true ∧ ∀ j, 0 < j → j ≤ n → r ≠ BitVec.ofNat 64 j

/-- **Every message is thread 0's** (for `Components.pre_alloc`: an
unmirrored promise is outstanding in its writer's promises). -/
def OwnMsgs (mem : Memory) : Prop := ∀ k m, mem.get? k = some m → m.tid = 0

/-- An instruction of thread 0 keeps `OwnMsgs`: its new messages are its
own, the old ones are kept. -/
theorem ownMsgs_step {I : ISA} {A : Arch} {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
    {o : Outcome I} (hs : stepOne A t 0 mem = some outs) (ho : .ok o ∈ outs) (h : OwnMsgs mem) :
    OwnMsgs o.mem := by
  intro k m hk
  by_cases hle : k ≤ mem.last
  · rw [(stepOne_dord _ hs ho).2.2.1.get? hle] at hk; exact h k m hk
  · exact (stepOne_own _ hs ho k m (Nat.lt_of_not_le hle) hk).1

/-- An appended message keeps a property of every message. -/
theorem msgs_append {Q : Msg → Prop} {mem : Memory} {w : Msg} (hw : Q w) (h : ∀ k m, mem.get? k = some m → Q m) :
    ∀ k m, (mem.append w).1.get? k = some m → Q m := by
  intro k m hk
  by_cases hle : k ≤ mem.last
  · rw [(Memory.Prefix.append _ _).get? hle] at hk; exact h k m hk
  · have hk' : k = mem.last + 1 := by
      have := (mem.append w).1.last_le_of_get?_eq_some hk; rw [Memory.last_append] at this
      exact Nat.le_antisymm this (Nat.lt_of_not_le hle)
    subst hk'; rw [Memory.get?_append_last] at hk; cases hk; exact hw

/-- A promise of thread 0 keeps `OwnMsgs`. -/
theorem ownMsgs_append {mem : Memory} {w : Msg} (hw : w.tid = 0) (h : OwnMsgs mem) : OwnMsgs (mem.append w).1 :=
  msgs_append (Q := fun m => m.tid = 0) hw h

/-! ## The runtime words the thread owns -/

/-- `WriteTree` is monotone in the predicate. -/
theorem writeTree_mono {G G' : Loc → Val → Prop} (h : ∀ l v, G l v → G' l v) {σ : Type} :
    ∀ {t : EvTree σ}, WriteTree G t → WriteTree G' t
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, hw => fun i => writeTree_mono h (hw i)
  | .load _ _ _ _, hw => fun v => writeTree_mono h (hw v)
  | .store _ _ _ _ _, hw => ⟨h _ _ hw.1, fun b => writeTree_mono h (hw.2 b)⟩
  | .rmw _ _ _ _ _, hw => ⟨fun o v hv => h _ _ (hw.1 o v hv), fun v => writeTree_mono h (hw.2 v)⟩
  | .fence _ _, hw => fun u => writeTree_mono h (hw u)

/-- Every tree writes as the trivial predicate says. -/
theorem writeTree_true {σ : Type} : ∀ t : EvTree σ, WriteTree (fun _ _ => True) t
  | .done _ => trivial
  | .fault _ => trivial
  | .choose _ k => fun i => writeTree_true (k i)
  | .load _ _ _ ret => fun v => writeTree_true (ret v)
  | .store _ _ _ _ ret => ⟨trivial, fun b => writeTree_true (ret b)⟩
  | .rmw _ _ _ _ ret => ⟨fun _ _ _ => trivial, fun v => writeTree_true (ret v)⟩
  | .fence _ ret => fun u => writeTree_true (ret u)

/-- Every tree keeps the trivial invariant. -/
theorem allInv_true {σ : Type} : ∀ t : EvTree σ, t.AllInv (fun _ _ => True) (fun _ => True)
  | .done _ => trivial
  | .fault _ => trivial
  | .choose _ k => fun i => allInv_true (k i)
  | .load _ _ _ ret => fun v _ => allInv_true (ret v)
  | .store _ _ _ _ ret => ⟨trivial, fun b _ => allInv_true (ret b)⟩
  | .rmw _ _ _ _ ret => fun old _ => ⟨fun _ _ => trivial, allInv_true (ret old)⟩
  | .fence _ ret => fun u => allInv_true (ret u)

/-- **The words owned after a write of `V` to the word `L`** (`ow'`, from
`ow` before it): `L` holding `V`, or a word other than `L` owned before
with its value (ownership of any word may be dropped). -/
def OwnUpd (ow ow' : List (Loc × Val)) (L : Loc) (V : Val) : Prop :=
  ∀ L' w, (L', w) ∈ ow' → (L' = L ∧ w = V) ∨ (L' ≠ L ∧ (L', w) ∈ ow)

/-- **The owned words across one instruction** (`own`, the runtime words a
thread state owns with their values, `MemSide.own`; `ow`, the words the
state before the instruction owns; `tree`, its instruction): either every
leaf owns `ow` and no write of the tree is to an owned word, or the state
owns nothing and the instruction is one plain store of `V` to the word `L`
whose leaf owns exactly `L` holding `V` (taking ownership of a word by
initialising it, as a stack limit's store), or the instruction is one
write of an owned word `L` (`OwnUpd`): a plain store of `V`, its leaf
owning `L` holding `V`, or an RMW of `L` (a runtime counter's), its leaf
from `L`'s owned value `v` owning `L` holding the RMW's result
`(op v).getD v`. -/
def OwnTree {σ : Type} (own : σ → List (Loc × Val)) (ow : List (Loc × Val)) (tree : EvTree σ) : Prop :=
  (tree.AllInv (fun _ _ => True) (fun s' => own s' = ow) ∧ WriteTree (fun l _ => ∀ w, (l, w) ∉ ow) tree) ∨
    (ow = [] ∧ ∃ kr L V s', tree = .store kr false L V (fun _ => .done s') ∧ L.bytes = 8 ∧ own s' = [(L, V)]) ∨
    (∃ kr L V s', tree = .store kr false L V (fun _ => .done s') ∧ L.bytes = 8 ∧ OwnUpd ow (own s') L V) ∨
    (∃ (k : Kraken.RmwKind) (noRet : Bool) (L : Loc) (op : Val → Option Val) (g : Val → σ),
      tree = .rmw k noRet L op (fun v => .done (g v)) ∧ L.bytes = 8 ∧ (∃ v, (L, v) ∈ ow) ∧
      ∀ v, (L, v) ∈ ow → OwnUpd ow (own (g v)) L ((op v).getD v))

/-- With no owned words, every tree keeps them. -/
theorem OwnTree.nil {σ : Type} (tree : EvTree σ) : OwnTree (fun _ => []) [] tree :=
  .inl ⟨(allInv_true tree).mono fun _ _ => rfl, writeTree_mono (fun _ _ _ _ h => by simp at h) (writeTree_true tree)⟩

/-- **One instruction keeps the owned words reading as their values**
(`ExtRows.OwnOk`), given its `OwnTree` and the thread's cover, its promises
distinct and at most `last`: a word kept is not written
(`Scc.Sem.stepOne_own`), a word taken or stored is the store's
(`stepOne_store_ownOf`), a word an RMW updates reads as its result
(`stepOne_rmw_own`). -/
theorem ownOk_step {I : ISA} {A : Arch} {own : I.State → List (Loc × Val)} {t : Thread I} {tid : Nat}
    {mem : Memory} {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hT : OwnTree own (own t.st) tree)
    (hc : CohCoversP t.views t.prom mem) (hn : t.prom.Nodup) (hl : ∀ p ∈ t.prom, p ≤ mem.last)
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) {o : Outcome I}
    (ho : .ok o ∈ outs) (h : ExtRows.OwnOk (own t.st) mem t.prom) :
    ExtRows.OwnOk (own o.thread.st) o.mem o.thread.prom := by
  rcases hT with ⟨hQ, hW⟩ | ⟨-, kr, L, V, s', rfl, hL8, hown⟩ | ⟨kr, L, V, s', rfl, hL8, hupd⟩ |
    ⟨k, noRet, L, op, g, rfl, hL8, ⟨v0, hv0⟩, hupd⟩
  · have hq := (stepOne_allInv A hs ho (fun tr he => by rw [hex] at he; cases he; exact hQ)
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    rw [hq]
    intro L v hm
    obtain ⟨hL8, hv⟩ := h L v hm
    refine ⟨hL8, (Scc.Sem.stepOne_own A hex (writeTree_mono (fun l w hw he => ?_) hW) hs ho
      ⟨hc, hn, hl, hv⟩).2.2.2⟩
    rw [he, ← ExtRows.loc_wordLoc hL8] at hw
    exact hw v hm
  · rw [ExtRows.loc_wordLoc hL8] at hex
    obtain ⟨hst, hi⟩ := Scc.Sem.stepOne_store_ownOf A hex hs ho hc hn hl
    rw [hst, hown]
    intro L' v hm
    obtain ⟨rfl, rfl⟩ := List.mem_singleton.mp hm
    exact ⟨hL8, hi.2.2.2⟩
  · have hex' := hex
    rw [ExtRows.loc_wordLoc hL8] at hex'
    obtain ⟨hst, hi⟩ := Scc.Sem.stepOne_store_ownOf A hex' hs ho hc hn hl
    rw [hst]
    intro L' w hm
    rcases hupd L' w hm with ⟨rfl, rfl⟩ | ⟨hne, hm'⟩
    · exact ⟨hL8, hi.2.2.2⟩
    · obtain ⟨hL8', hv⟩ := h L' w hm'
      exact ⟨hL8', (Scc.Sem.stepOne_own A hex
        ⟨fun he => hne ((ExtRows.loc_wordLoc hL8').trans he.symm), fun _ => trivial⟩ hs ho
        ⟨hc, hn, hl, hv⟩).2.2.2⟩
  · have hex' := hex
    rw [ExtRows.loc_wordLoc hL8] at hex'
    obtain ⟨-, hv⟩ := h L v0 hv0
    obtain ⟨hst, hi⟩ := Scc.Sem.stepOne_rmw_own A hex' hs ho ⟨hc, hn, hl, hv⟩
    rw [hst]
    intro L' w hm
    rcases hupd v0 hv0 L' w hm with ⟨rfl, rfl⟩ | ⟨hne, hm'⟩
    · exact ⟨hL8, hi.2.2.2⟩
    · obtain ⟨hL8', hv'⟩ := h L' w hm'
      exact ⟨hL8', (Scc.Sem.stepOne_own A hex
        ⟨fun _ _ _ he => hne ((ExtRows.loc_wordLoc hL8').trans he.symm), fun _ => trivial⟩ hs ho
        ⟨hc, hn, hl, hv'⟩).2.2.2⟩

/-- No owned word reads as anything. -/
theorem ownOk_nil {ow : List (Loc × Val)} (h : ow = []) (tm : Memory) (prom : List Time) :
    ExtRows.OwnOk ow tm prom := by
  subst h; intro _ _ h; simp at h

/-- **The owned words at load** (`ow`, of the loaded thread state, against
the loaded memory `tm`): each is a word holding its initial value. -/
def OwnInit (ow : List (Loc × Val)) (tm : Memory) : Prop :=
  ∀ L v, (L, v) ∈ ow → L.bytes = 8 ∧ tm.initVal L = v

/-- No owned word at load. -/
theorem OwnInit.nil (tm : Memory) : OwnInit [] tm := fun _ _ h => by simp at h

/-- **At load the owned words read as their values**: with no message, a
word reads as its initial value (`Scc.Sem.ownVal_init`). -/
theorem ownOk_init {ow : List (Loc × Val)} {tm : Memory} (hm : tm.msgs = #[]) (h : OwnInit ow tm)
    (prom : List Time) : ExtRows.OwnOk ow tm prom := by
  intro L v hv
  obtain ⟨hL8, hi⟩ := h L v hv
  refine ⟨hL8, ?_⟩
  have he : wordLoc L.addr.toNat = L := (ExtRows.loc_wordLoc hL8).symm
  have := Scc.Sem.ownVal_init hm prom L.addr.toNat
  rwa [he, hi] at this

/-- **A promise keeps the owned words reading as their values**: the
appended message is promised (`Scc.Sem.own_promise`). -/
theorem ownOk_promise {vs : Views} {ow : List (Loc × Val)} {prom : List Time} {mem : Memory}
    (hc : CohCoversP vs prom mem) (hn : prom.Nodup) (hl : ∀ p ∈ prom, p ≤ mem.last)
    (h : ExtRows.OwnOk ow mem prom) (w : Msg) :
    ExtRows.OwnOk ow (mem.append w).1 (prom ++ [(mem.append w).2]) := by
  intro L v hm
  obtain ⟨hL8, hv⟩ := h L v hm
  exact ⟨hL8, (Scc.Sem.own_promise ⟨hc, hn, hl, hv⟩ w).2.2.2⟩

/-- **An initial word in the layout**: every byte in a shared region, or an
aligned word starting in a shared region or in the `.rodata` image (a
region's or the image's size need not be a multiple of 8, so its last word
may stick out of it; the regions being 16-aligned, it overlaps no other). -/
def InitIn (Λ : Scc.Sem.Layout) (l : Loc) : Prop :=
  LocIn Λ.shared l ∨
    (l.bytes = 8 ∧ l.addr.toNat % 8 = 0 ∧ (Λ.shared l.addr.toNat ∨ Λ.rodata.contains l.addr.toNat))

/-- **The target memory is in the layout**: every byte of every message in a
shared region, every initial word as `InitIn` says. This is `InLayout`
(which constrains the first byte, with the `.rodata` image allowed in the
initial memory) for the bytes `Kernel.fresh` compares. -/
def MemIn (Λ : Scc.Sem.Layout) (mem : Memory) : Prop :=
  (∀ k m, mem.get? k = some m → LocIn Λ.shared m.loc) ∧
    ∀ q ∈ mem.init, InitIn Λ q.1

/-- A message to a shared region keeps `MemIn`. -/
theorem memIn_append {Λ : Scc.Sem.Layout} {mem : Memory} {w : Msg} (hw : LocIn Λ.shared w.loc)
    (h : MemIn Λ mem) : MemIn Λ (mem.append w).1 :=
  ⟨msgs_append (Q := fun m => LocIn Λ.shared m.loc) hw h.1, h.2⟩

/-- `MemIn`'s messages, as `InLayout` lists them. -/
theorem memIn_msgs {Λ : Scc.Sem.Layout} {mem : Memory} (h : MemIn Λ mem) :
    ∀ m ∈ mem.msgs.toList, LocIn Λ.shared m.loc := by
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  refine h.1 (i + 1) _ ?_
  simp [Memory.get?, Array.getElem?_eq_getElem (by simpa using hi)]

/-- `MemIn` gives `InLayout` (its first bytes). -/
theorem inLayout_of_memIn {Λ : Scc.Sem.Layout} {M : ExtMachine} {t : M.Cfg} (h : MemIn Λ t.1.mem) :
    InLayout Λ t := by
  refine ⟨fun m hm => (memIn_msgs h m hm).addr, fun q hq => ?_⟩
  rcases h.2 q hq with hl | ⟨-, -, hx⟩
  · exact .inl hl.addr
  · exact hx

/-- **A placed word is in a shared region** (its 8 bytes): placed labels
lie in the heap or the static image. -/
theorem shared_of_wordAddr {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat} (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp)
    {sa : WeakMem.Address} {a : Nat} (ha : wordAddr lbl sa = some a) (ho : sa.offset < lsize sa.label) :
    ∀ i < 8, Λ.shared (a + i) := by
  intro i hi
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨-, hr⟩ := hm.lbl_range _ _ hb
  have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := ho
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h0, -⟩
  · simp only [lrange] at h1 h2
    exact .inr (.inl ⟨by omega, by omega⟩)
  · simp only [lrange] at h1 h2
    exact .inl ⟨by omega, by omega⟩
  · omega

/-- **A one-word location is the word location of its address.** -/
theorem loc_eq_wordLoc {L : Loc} (h : L.bytes = 8) : L = wordLoc L.addr.toNat := by
  obtain ⟨a, b⟩ := L
  simp only at h
  subst h
  simp [wordLoc]

/-- **A placed word lies in the heap or the static image** (its first
byte): `shared_of_wordAddr` without the pinned region. -/
theorem heapData_of_wordAddr {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat} (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp)
    {sa : WeakMem.Address} {a : Nat} (ha : wordAddr lbl sa = some a) (ho : sa.offset < lsize sa.label) :
    Λ.heap.contains a ∨ Λ.data.contains a := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ha
  obtain ⟨-, hr⟩ := hm.lbl_range _ _ hb
  have ho' : @LT.lt Nat instLTNat sa.offset (lsize sa.label) := ho
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h0, -⟩
  · simp only [lrange] at h1 h2
    exact .inl ⟨by omega, by omega⟩
  · simp only [lrange] at h1 h2
    exact .inr ⟨by omega, by omega⟩
  · omega

/-- **Every target value is a 64-bit value** (`Scc/Sem/Fits.lean`): every
message's and every initial one. -/
def MemFits (mem : Memory) : Prop := MemRel.Fits mem ∧ InitFits mem

/-- **The hold of an exchange** (`Ctl.hold`, between `Out.holdLoad` and
`Out.xchgStore`) against the source memory `sm`: none, or the target word
address `A` is placed for an in-bounds source address `sa` whose latest
message is `j`, and the held word is that message's (what the exchange
reads at the store, the source memory unchanged in between). -/
def HoldInv (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (sm : WeakMem.Memory) :
    Option (Nat × TermRun.Word) → Prop
  | none => True
  | some (A, w) => ∃ (sa : WeakMem.Address) (j : Nat) (m : WeakMem.Msg), wordAddr lbl sa = some A ∧
      sa.offset < lsize sa.label ∧ MemRel.SLatest sm sa j ∧ sm[j]? = some m ∧ w = ⟨m.val, m.view, j⟩

/-- A local run keeps `HoldInv`: it holds the same or nothing. -/
theorem holdInv_run {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {sm : WeakMem.Memory} {c c' : Ctl}
    (hr : LocalRun p c c') (h : HoldInv lbl lsize sm c.hold) : HoldInv lbl lsize sm c'.hold := by
  cases hr with
  | refl => exact h
  | step hs hr => rw [hr.hold hs.1]; trivial

/-! ## Runs, ranges and the kernel -/

/-- A reachable configuration's run lands in a reachable configuration. -/
theorem reach_run {P : SrcSem.SrcParams} {p : Prog} {tr es : List Ev} {s s' : TermRun.Cfg}
    (h : (SrcSem.source P p).Reach tr s) (hr : (SrcSem.source P p).Run s es s') :
    (SrcSem.source P p).Reach (tr ++ es) s' :=
  let ⟨s0, hi, h0⟩ := h; ⟨s0, hi, h0.trans hr⟩

/-- **The source's reads satisfy `rd`**: every message of a reachable
one-thread configuration with no promise outstanding, represented by some
value (`ValRep`), read as a word satisfies `rd` (e.g. `IsNum`, from the
source's memory holding numbers). -/
def SrcRd (P : SrcSem.SrcParams) (p : Prog) (rd : TermRun.Word → Prop) : Prop :=
  ∀ (tr : List Ev) (s : TermRun.Cfg) (th : TermRun.TTh) (k : Nat) (m : WeakMem.Msg)
    (lbl : WeakMem.AllocLabel → Option Nat) (x : Nat),
    (SrcSem.source P p).Reach tr s → s.ths = #[th] → th.promises = [] → s.mem[k]? = some m →
    ValRep lbl m.val x → rd ⟨m.val, m.view, k⟩

/-- `SrcRd` for an `rd` admitting every word. -/
theorem SrcRd.of_all {P : SrcSem.SrcParams} {p : Prog} {rd : TermRun.Word → Prop} (h : ∀ w, rd w) :
    SrcRd P p rd :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ => h _

/-- One source step with no event is a run with no event. -/
theorem run_one {P : SrcSem.SrcParams} {p : Prog} {s s' : TermRun.Cfg} (h : (SrcSem.source P p).step 0 s [] s') :
    (SrcSem.source P p).Run s [] s' :=
  by have := LRun.step (step := fun c es c' => ∃ i, (SrcSem.source P p).step i c es c') ⟨0, h⟩ (.refl s'); exact this

/-- The one source thread replaced. -/
theorem set_one {s : TermRun.Cfg} {th th' : TermRun.TTh} (h : s.ths = #[th]) : s.ths.set! 0 th' = #[th'] := by
  rw [h]; rfl

/-- `Touches` is monotone in the predicate. -/
theorem touches_mono {σ : Type} {p q : Loc → Bool → Prop} (hpq : ∀ l w, p l w → q l w) {e : EvTree σ}
    (h : Kernel.Touches p e) : Kernel.Touches q e := by
  induction h with
  | load h => exact .load (hpq _ _ h)
  | loadRet v _ ih => exact .loadRet v ih
  | store h => exact .store (hpq _ _ h)
  | storeRet b _ ih => exact .storeRet b ih
  | rmw h => exact .rmw (hpq _ _ h)
  | rmwRet v _ ih => exact .rmwRet v ih
  | choose i _ ih => exact .choose i ih
  | fence _ ih => exact .fence ih

/-- A range in the stack pool contains only addresses of the pool. -/
theorem sub_contains {r s : Range} (h : r.Sub s) {a : Nat} (ha : r.contains a) : s.contains a := by
  unfold Range.Sub at h; unfold Range.contains at ha ⊢; omega

/-- **No shared address is in the stack pool** (`Layout.WF`). -/
theorem shared_not_pool {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {a : Nat} (hs : Λ.shared a)
    (hp : Λ.stackPool.contains a) : False := by
  rcases hs with h | h | h
  · exact hwf.disjoint.2.2.2.2.1.not_both h hp
  · exact hwf.disjoint.2.2.2.2.2.1.not_both h hp
  · exact hwf.disjoint.2.2.2.2.2.2.2.2.2.not_both hp h

/-- Overlapping nonempty ranges share a byte. -/
theorem overlaps_contains {r : Range} {lo n : Nat} (hr : 0 < r.size) (hn : 0 < n)
    (h : Kernel.overlaps r lo n = true) :
    ∃ i < n, r.contains (lo + i) := by
  simp only [Kernel.overlaps, Bool.and_eq_true, decide_eq_true_eq] at h
  by_cases hle : r.lo ≤ lo
  · exact ⟨0, by omega, by simp only [Range.contains]; omega⟩
  · exact ⟨r.lo - lo, by omega, by simp only [Range.contains]; omega⟩

/-- **An aligned word starting off the pool is off the 16-aligned pool**:
its region `X` is disjoint from the pool. -/
theorem word_off_pool {X sp : Range} {a i : Nat} (hx : X.contains a) (hd : X.Disjoint sp) (h8 : a % 8 = 0)
    (h16 : sp.lo % 16 = 0) (hi : i < 8) (hp : sp.contains (a + i)) : False := by
  unfold Range.Disjoint at hd; unfold Range.contains at hx hp; omega

/-- Off a system call, `stepOneWith cexec` is `stepOne`. -/
theorem stepOneWith_eq {I' : ISA} {A : Arch} {cexec : I'.State → Option (EvTree I'.State)} {t : Thread I'}
    {tid : Nat} {mem : Memory} (h : cexec t.st = I'.exec t.st) :
    stepOneWith A cexec t tid mem = stepOne A t tid mem := by
  unfold stepOneWith stepOne; rw [h]

/-- **The abort path follows a refusal**: if thread 0 is in the phase `Ab`,
the trace `tr` has a `writeErr`. -/
def TI {M : ExtMachine} (Ab : M.I.State → Prop) (tr : List Ev) (t : M.Cfg) : Prop :=
  ∀ th, t.1.threads[0]? = some th → Ab th.st → Ev.writeErr ∈ tr

/-- **A returning `write`**: the thread resumes at `Abi.ret` of the result,
and a refusal (`Refusal`) emits `writeErr`. -/
theorem sysStep_write_ret {I : ISA} {K : Kernel.Abi I} {A : Arch} {c c' : Config I × Kernel.KState}
    {th : Thread I} {fd buf n : Nat}
    {r : BitVec 64} {es : List Ev} (ht : c.1.threads[0]? = some th)
    (hc : Kernel.callOf K th = some (.write fd buf n)) (hwr : c.2.wr 0 ≤ n)
    (h : Kernel.sysStep K A 0 c (.ret r) = some (es, c')) :
    c'.1 = c.1.withThread 0 (Kernel.retThread K th r) c.1.mem ∧ (Refusal n r → es = [.writeErr]) := by
  unfold Kernel.sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  simp only at h
  split at h
  · split at h
    · simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i hj hr
      exact ⟨rfl, fun hf => absurd hr (hf.2 _ hj hwr)⟩
    · cases h
  · split at h
    · simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rename_i he
      refine ⟨rfl, fun hf => ?_⟩
      have := hf.1
      rcases he with rfl | rfl <;> exact absurd this (by decide)
    · split at h
      · simp only [Kernel.back, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, fun _ => rfl⟩
      · cases h

end Spike.Lib.Consumer1
