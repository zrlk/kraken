/-
**Segments with the worker's thread rows** (the worker's
half; `s1_threads.md` §1.4, §2.2 B item 5).

Two of the worker's target steps after its print have no `Out` row:

- **the source `unpark`**, committed at the worker's executed `swpal(1)` on
  the permit word of the thread it names (`tid + 16`): the source's step is
  an extern step that changes *another* thread's permit, which no
  `LocalRun` (one thread's control, memory and the other threads kept)
  expresses;
- **the worker's `exit`** (the thread ends; `SysOk` excludes `.exit`): the
  source worker is at `ret _` on an empty stack, finished, and takes no
  step (`WorkerSrc.worker_done`).

- `OutT`: `OutL` (`Spike/Lib/SegLd.lean`), or one of the two thread rows
  `unpk` (an RMW of the word `B + 16`, `B` what the source's thread-id word
  represents, writing `1`, at the source's `let x = ext unpark a in e`; the
  source takes its unpark step for every old value) and `texit` (a system
  call that decodes to `exit`, the source at `ret _`; no successor), or the
  target-only row `fnc` (a fence, `dmb ish` in hello's print: the target
  steps to the fence's continuation, the source stutters, `LocalRun` only);
- `OutT.mono`, `OutL.toT`, `Out.toT`, and `OutT.toL_of_term`: **away from
  an `unpark`, a `ret` and a fence the thread rows add nothing** (an `OutT`
  step whose source is at neither and whose instruction is no fence is an
  `OutL` step);
- `SegT`: `Seg` over `OutT`, with `Seg.toT`, `SegL.toT` and the
  combinators `step`, `seq`, `loop`, `mono_pre`, `mono_post`, `or_pre`,
  `cfg`, `exists_pre`.

`Out`, `Seg`, `OutL` and `SegL` are unchanged. The rows fix only the
source's moves. That the source steps exist in the whole program is the
consumer's business, named for its cases: `unpark_src` (the source unpark
of `unpk`: main's permit set, `WorkerSrc.unpark_src`) and `worker_done`
(`texit`: the worker finished, `WorkerSrc.worker_done`); `fnc` needs no
source step, only that the target's fence step keeps the consumer's
invariant. Main's park is no
commit point: main's source never parks (`Spike/Lib/A64WaitLoop.lean`), and
`unpk` needs the source at an `unpark`, which only the worker has.
-/
import Spike.Lib.SegLd

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising
open Scc.Sem (ValRep)

/-- **What one instruction does, with the worker's thread rows**: an
`OutL` row, or

- `unpk`: one RMW of `⟨A, 8⟩` writing `1`, at the source's `let x = ext
  unpark a in e` (no hold pending), `a`'s word `jw` representing `B` and
  `A = B + 16` (the permit word of the thread `jw` names), the word the
  runtime's (`ms.rt`) and mapped for writing (`ms.mp`): for every old value
  runtime memory may hold there (`ms.G`), the owned value if the thread owns
  it (`ms.own`), the new value may be held there too and the pair lands in
  `X` with the source's unpark taken (`x` bound to ``);
- `texit`: a system call that decodes to `exit` under the kernel model
  `ms.K`, the source at `ret a`: the thread ends, no successor. -/
inductive OutT {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (X : Frag I)
    (s : I.State) (c : Ctl) : Prop where
  /-- An `OutL` row. -/
  | outL : OutL p lbl ms X s c → OutT p lbl ms X s c
  /-- The source unpark, at the worker's exchange on the named thread's
  permit word. -/
  | unpk (k : Kraken.RmwKind) (A B : BitVec 64) (op : Val → Option Val) (g : Val → I.State) (x : String)
      (a : At) (e : Expr) (ty : Ty) (jw : TermRun.Word) :
      I.exec s = some (.rmw k false ⟨A, 8⟩ op fun v => .done (g v)) → ms.rt A.toNat → ms.mp ⟨A, 8⟩ true →
      (∀ old, op old = some 1) →
      c.term = .let_ x (.ext .unpark a) e → c.hold = none → TermRun.evalAt c.env a = some (ty, [jw]) →
      ValRep lbl jw.val B.toNat → A = B + 16#64 →
      (∀ old, ms.G ⟨A, 8⟩ old → (∀ w, (⟨A, 8⟩, w) ∈ ms.own s → old = w) →
        ms.G ⟨A, 8⟩ 1 ∧ X (g old) ⟨e, (x, ExtName.unpark.sig.2, []) :: c.env, none⟩) →
      OutT p lbl ms X s c
  /-- The thread's exit, the source at `ret a`. -/
  | texit (K : Scc.Sem.Kernel.Abi I) (a : At) :
      ms.K = some K → K.atSys s = true → Scc.Sem.Kernel.decode K.nrs (K.nr s) (K.arg s) = some .exit →
      c.term = .ret a → OutT p lbl ms X s c
  /-- A fence: no source event, the source takes a local run (it stutters,
  possibly none); target-only (the AArch64 `dmb ish` before a spawning
  program's `write`). -/
  | fnc (k : Kraken.FenceKind) (s' : I.State) (c' : Ctl) :
      I.exec s = some (.fence k fun _ => .done s') → LocalRun p c c' → X s' c' → OutT p lbl ms X s c

theorem OutT.mono {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X Y : Frag I} {s : I.State} {c : Ctl}
    (h : OutT p lbl ms X s c) (hXY : ∀ s c, X s c → Y s c) : OutT p lbl ms Y s c := by
  cases h with
  | outL h => exact .outL (h.mono hXY)
  | unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA hX =>
    exact .unpk k A B op g x a e ty jw he hrt hmp hop ht hh hev hv hA fun old hg ho =>
      ⟨(hX old hg ho).1, hXY _ _ (hX old hg ho).2⟩
  | texit K a hK hat hd ht => exact .texit K a hK hat hd ht
  | fnc k s' c' he hr hx => exact .fnc k s' c' he hr (hXY _ _ hx)

/-- An `OutL` row is an `OutT` row. -/
theorem OutL.toT {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl} (h : OutL p lbl ms X s c) : OutT p lbl ms X s c :=
  .outL h

/-- An `Out` row is an `OutT` row. -/
theorem Out.toT {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl} (h : Out p lbl ms X s c) : OutT p lbl ms X s c :=
  .outL (.out h)

/-- **Away from an `unpark`, a `ret` and a fence the thread rows add
nothing**: an `OutT` step whose source term is neither an `unpark` binding
nor a `ret`, at an instruction that is not a fence, is an `OutL` step. -/
theorem OutT.toL_of_term {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl} (h : OutT p lbl ms X s c)
    (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) (hr : ∀ a, c.term ≠ .ret a)
    (hf : ∀ k t, I.exec s ≠ some (.fence k t)) : OutL p lbl ms X s c := by
  cases h with
  | outL h => exact h
  | unpk _ _ _ _ _ x a e _ _ _ _ _ _ ht => exact absurd ht (hu x a e)
  | texit _ a _ _ _ ht => exact absurd ht (hr a)
  | fnc k _ _ he => exact absurd he (hf k _)

/-- **The thread rows are conservative**: away from an `unpark` binding, a
`ret` and a fence, `OutT` and `OutL` are the same rows. -/
theorem OutT.iff_L {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl}
    (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) (hr : ∀ a, c.term ≠ .ret a)
    (hf : ∀ k t, I.exec s ≠ some (.fence k t)) :
    OutT p lbl ms X s c ↔ OutL p lbl ms X s c :=
  ⟨fun h => h.toL_of_term hu hr hf, OutL.toT⟩

/-- **A thread row that is not an `OutL` row** is at an `unpark` binding, a
`ret` or a fence. -/
theorem OutT.unpk_term {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {X : Frag I} {s : I.State} {c : Ctl} (h : OutT p lbl ms X s c) (hl : ¬ OutL p lbl ms X s c) :
    (∃ x a e, c.term = .let_ x (.ext .unpark a) e) ∨ (∃ a, c.term = .ret a) ∨ ∃ k t, I.exec s = some (.fence k t) := by
  cases h with
  | outL h => exact absurd h hl
  | unpk _ _ _ _ _ x a e _ _ _ _ _ _ ht => exact .inl ⟨x, a, e, ht⟩
  | texit _ a _ _ _ ht => exact .inr (.inl ⟨a, ht⟩)
  | fnc k _ _ he => exact .inr (.inr ⟨k, _, he⟩)

/-- **Segment simulation with the worker's thread rows**: `Seg` over
`OutT`. -/
def SegT {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : MemSide I) (P Q : Frag I) : Prop :=
  ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧
    ∀ s c, inv s c → OutT p lbl ms (fun s c => inv s c ∨ Q s c) s c

/-- A segment with the load-or-stutter row is one with the thread rows. -/
theorem SegL.toT {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {P Q : Frag I} (h : SegL p lbl ms P Q) : SegT p lbl ms P Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c hi => .outL (ho s c hi)⟩

/-- A segment is one with the thread rows. -/
theorem Seg.toT {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
    {P Q : Frag I} (h : Seg p lbl ms P Q) : SegT p lbl ms P Q :=
  h.toL.toT

namespace SegT

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P P' Q Q' R : Frag I}

/-- **One instruction** from every pair of `P` into `Q`. -/
theorem step (h : ∀ s c, P s c → OutT p lbl ms Q s c) : SegT p lbl ms P Q :=
  ⟨P, fun _ _ h => h, fun s c hp => (h s c hp).mono fun _ _ h => .inr h⟩

/-- **Sequencing**. -/
theorem seq (h₁ : SegT p lbl ms P Q) (h₂ : SegT p lbl ms Q R) : SegT p lbl ms P R := by
  obtain ⟨i₁, hs₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => h.elim (fun h => .inl (.inl h)) fun h => .inl (.inr (hs₂ s c h))
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) .inr

/-- **A tail-call loop**. -/
theorem loop {H X : Frag I} (h : SegT p lbl ms H (fun s c => H s c ∨ X s c)) : SegT p lbl ms H X := by
  obtain ⟨i, hs, ho⟩ := h
  refine ⟨i, hs, fun s c hi => (ho s c hi).mono fun s c h => ?_⟩
  rcases h with h | h | h
  · exact .inl h
  · exact .inl (hs s c h)
  · exact .inr h

theorem mono_pre (h : SegT p lbl ms P Q) (hP : ∀ s c, P' s c → P s c) : SegT p lbl ms P' Q :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, fun s c h => hs s c (hP s c h), ho⟩

theorem mono_post (h : SegT p lbl ms P Q) (hQ : ∀ s c, Q s c → Q' s c) : SegT p lbl ms P Q' :=
  let ⟨i, hs, ho⟩ := h
  ⟨i, hs, fun s c h => (ho s c h).mono fun s c h => h.imp_right (hQ s c)⟩

/-- A case split on the entry. -/
theorem or_pre (h : SegT p lbl ms P Q) (h' : SegT p lbl ms P' Q) :
    SegT p lbl ms (fun s c => P s c ∨ P' s c) Q := by
  obtain ⟨i, hs, ho⟩ := h
  obtain ⟨i', hs', ho'⟩ := h'
  refine ⟨fun s c => i s c ∨ i' s c, fun s c h => h.imp (hs s c) (hs' s c), ?_⟩
  rintro s c (h | h)
  · exact (ho s c h).mono fun s c h => h.imp_left .inl
  · exact (ho' s c h).mono fun s c h => h.imp_left .inr

/-- **A control-flow graph** of segments with the thread rows. -/
theorem cfg {ι : Sort _} (N : ι → Frag I) {X : Frag I}
    (h : ∀ i, SegT p lbl ms (N i) (fun s c => (∃ j, N j s c) ∨ X s c)) :
    SegT p lbl ms (fun s c => ∃ i, N i s c) X := by
  refine ⟨fun s c => ∃ i, ∃ J : Frag I, (∀ s c, N i s c → J s c) ∧
      (∀ s c, J s c → OutT p lbl ms (fun s c => J s c ∨ ((∃ j, N j s c) ∨ X s c)) s c) ∧ J s c, ?_, ?_⟩
  · rintro s c ⟨i, hi⟩
    obtain ⟨J, hs, ho⟩ := h i
    exact ⟨i, J, hs, ho, hs s c hi⟩
  · rintro s c ⟨i, J, hs, ho, hJ⟩
    refine (ho s c hJ).mono fun s c h => ?_
    rcases h with h | ⟨j, hj⟩ | h
    · exact .inl ⟨i, J, hs, ho, h⟩
    · obtain ⟨J', hs', ho'⟩ := h j
      exact .inl ⟨j, J', hs', ho', hs' s c hj⟩
    · exact .inr h

/-- **Ghost parameters**. -/
theorem exists_pre {γ : Sort _} {P : γ → Frag I} {X : Frag I} (h : ∀ g, SegT p lbl ms (P g) X) :
    SegT p lbl ms (fun s c => ∃ g, P g s c) X :=
  cfg P fun g => (h g).mono_post fun _ _ h => .inr h

end SegT

/-! ### Conservativity checks (old rows are `outL` rows, unchanged) -/

section Checks
variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {X P Q : Frag I} {s : I.State} {c : Ctl}

/-- `OutT`/`OutL` are propositions, so equalities of rows are trivial; the
content is the iff: away from `unpark`/`ret`/a fence, an `OutT` row is
exactly an `OutL` row (`OutT.iff_L`), so lifting adds no behaviour on old
rows. -/
example (hu : ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e) (hr : ∀ a, c.term ≠ .ret a)
    (hf : ∀ k t, I.exec s ≠ some (.fence k t)) :
    OutT p lbl ms X s c ↔ OutL p lbl ms X s c := OutT.iff_L hu hr hf
/-- Every old row maps to `.outL`: an `Out` row through `Out.toT`, an
`OutL` row through `OutL.toT`, and an `OutT` row built by either lift is
not one of the thread rows (`unpk`, `texit`, `fnc`). -/
example (h : Out p lbl ms X s c) : Out.toT h = OutT.outL (.out h) := rfl
example (h : OutL p lbl ms X s c) : OutL.toT h = OutT.outL h := rfl
example (h : OutL p lbl ms X s c) : ∃ h' : OutL p lbl ms X s c, OutL.toT h = .outL h' := ⟨h, rfl⟩
/-- `SegL.toT` and `Seg.toT` keep the invariant and lift each row by
`outL` only. -/
example (h : SegL p lbl ms P Q) :
    ∃ inv : Frag I, (∀ s c, P s c → inv s c) ∧
      ∀ s c, inv s c → ∃ r : OutL p lbl ms (fun s c => inv s c ∨ Q s c) s c, True := by
  obtain ⟨i, hs, ho⟩ := h
  exact ⟨i, hs, fun s c hi => ⟨ho s c hi, trivial⟩⟩
end Checks

end Spike.Lib
