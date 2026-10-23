/-
The bridge spike: the source program, the memory relation and the lockstep
certification lemma, shared by the AArch64 and x64 halves.

The spike relates a Kraken machine run to a WeakCore `TermRun` run for the
smallest program with a release/acquire pair:

* source (WeakCore, written as a configuration): label `0` is the flag,
  initially `num 0`; thread 0 runs `let u = store rel f 1 in ret ()`, thread
  1 runs `let r = load acq f in ret r`, both with `f = loc ⟨0, 0⟩ 0` in their
  environment (`srcInit`);
* targets: one instruction per thread, a release store and an acquire load
  of the 8-byte flag (`Spike/Bridge/A64.lean`, `Spike/Bridge/X64.lean`).

This file holds what does not depend on the ISA:

* the source program and its configurations (`writerAt`, `reader0`,
  `srcInit`), and the source steps the simulation needs, in closed form:
  `writer_append` and `writer_fulfil` (the release store, appending or
  fulfilling an outstanding promise), `reader_read` (the acquire load of any
  message of the flag), `done_no_step` (a finished thread takes no thread
  step);
* `MemRel`: the memory part of the relation. Kraken timestamp `k` is source
  timestamp `k` (the timestamp map is the identity: Kraken's initial write
  of the flag, timestamp `0`, is the source's first message of label `0`,
  and every later Kraken message is the source message at the same index);
  every Kraken message is a write of the flag `⟨F, 8⟩`, and its source
  counterpart writes `num v` for the Kraken value `v` (the location map
  sends `⟨F, 8⟩` to `⟨0, 0⟩`);
* `certified_of_certOk`, **the lockstep lemma**: if a relation `TR` between
  a Kraken thread (with its memory) and a source configuration is preserved
  by every promise-free solo step of the Kraken thread, matched by a source
  thread step of the related source thread, and an empty Kraken promise set
  gives an empty source promise set, then Kraken certification (`CertOk`, a
  promise-free solo run that empties the promise set) gives WeakCore
  certification (`Certified`, a `Solo` run reaching `noPromises`), by running
  the two solo runs in lockstep.
-/
import Scc.Sem.Correct

namespace Spike.Bridge

open CoreLang CoreTerm
open WeakMem (Val Msg Memory Address VState)

/-! ## The source program -/

/-- The flag's address: label `0`, offset `0`. -/
def flagA : Address := ⟨0, 0⟩

/-- The flag reference's type. -/
def fTy : Ty := .ptr .pub .int

/-- The flag reference, a constant word. -/
def fW : TermRun.Word := TermRun.cst (.loc flagA 0)

/-- Both threads start with `f` bound to the flag. -/
def envF : TermRun.Env := [("f", fTy, [fW])]

/-- Thread 0: `let u = store rel f 1 in ret ()`. -/
def writerTerm : Expr := .let_ "u" (.store true (.var "f") (.lit 1) none) (.ret .unit)

/-- Thread 1: `let r = load acq f in ret r`. -/
def readerTerm : Expr := .let_ "r" (.load true (.var "f")) (.ret (.var "r"))

/-- Thread 0 before its store, with outstanding promises `P` (promise steps
change nothing else of a thread). -/
def writerAt (P : List Nat) : TermRun.TTh := { term := writerTerm, env := envF, promises := P }

/-- Thread 1 before its load. -/
def reader0 : TermRun.TTh := { term := readerTerm, env := envF }

/-- The flag's initial message. -/
def flagInit : Msg := ⟨flagA, .num 0, 0⟩

/-- The source start configuration: the flag allocated before the run
(`lbase = 1`), both threads at their first step. -/
def srcInit : TermRun.Cfg := { mem := #[flagInit], ths := #[writerAt [], reader0], lbase := 1 }

/-- The program: no code blocks (neither thread calls). -/
def prog : CoreTerm.Prog := []

/-- Thread 0 after its store, with outstanding promises `P`. -/
def WriterPost (P : List Nat) (th : TermRun.TTh) : Prop :=
  th.term = .ret .unit ∧ th.stack = [] ∧ th.promises = P ∧ th.env = ("u", .unit, []) :: envF

/-- Thread 1 after its load, `r` bound to the word `w`. -/
def ReaderPost (w : TermRun.Word) (th : TermRun.TTh) : Prop :=
  th.term = .ret (.var "r") ∧ th.stack = [] ∧ th.promises = [] ∧ th.env = ("r", .int, [w]) :: envF

/-! ## Source steps in closed form -/

/-- Thread 0 after its store, with views `vs` and outstanding promises `P`. -/
def writerDone (vs : VState) (P : List Nat) : TermRun.TTh :=
  { term := .ret .unit, env := ("u", .unit, []) :: envF, vs := vs, promises := P }

section SrcSteps

variable {k : Promises.Knobs} {arch : WeakMem.Arch} {pr : CoreTerm.Prog}

/-- The writer's step, as `Promises.stepStore` of the flag with the constant
`num 1`, released. -/
theorem tstep_writer (g : TermRun.G) (mem : Memory) (pairs : List Nat) (P : List Nat) :
    TermRun.tstep g mem pairs (writerAt P) =
      (Promises.stepStore g.k g.arch mem (TermRun.mth (TermRun.stOf mem pairs (writerAt P)) fW
          (TermRun.cst (.num 1)) (TermRun.cst (.num 1))) flagA (.const (.num 1)) [0] true).map
        fun x => (x.1, pairs, writerDone x.2.vs x.2.promises) := by
  simp [TermRun.tstep, writerAt, writerTerm, TermRun.evalOp, envF, TermRun.evalAt, TermRun.lookupE, fTy,
    cellOf, TermRun.addrOf, fW, TermRun.cst, Promises.TVal.mk0, flagA, TermRun.accs, TermRun.storeUnits,
    TermRun.offs, TermRun.dataE, TermRun.withS, TermRun.stOf, writerDone]
  generalize Promises.stepStore _ _ _ _ _ _ _ _ = L
  induction L <;> simp_all

/-- The writer's machine thread: its views and promises, the flag reference
in register 0 and the constant `num 1` as data. -/
def wTh (mem : Memory) (pairs P : List Nat) : Promises.Thread :=
  TermRun.mth (TermRun.stOf mem pairs (writerAt P)) fW (TermRun.cst (.num 1)) (TermRun.cst (.num 1))

/-- The thread after a store of `num 1` to the flag at timestamp `t`, with
promises `prom` (`commit` of `Promises.stepStore`). -/
def wCommit (k : Promises.Knobs) (th : Promises.Thread) (t : Nat) (prom : List Nat) : Promises.Thread :=
  { th with
    vs := { th.vs with
            coh := fun b => if b = flagA then t else th.vs.coh b
            vWr := max th.vs.vWr t, mine := t :: th.vs.mine
            fwd := if k.fwdView then (t, Promises.fwdOf th.regs (.const (.num 1)) [0]) :: th.vs.fwd
                   else th.vs.fwd }
    promises := prom }

/-- `Promises.stepStore` of the flag with the constant `num 1`, released:
append, or fulfil an outstanding promise. -/
theorem stepStore_flag (mem : Memory) (th : Promises.Thread) :
    Promises.stepStore k arch mem th flagA (.const (.num 1)) [0] true =
      (mem.push ⟨flagA, .num 1, Promises.storeMview th (.const (.num 1)) [0] true⟩,
        wCommit k th mem.size th.promises) ::
      th.promises.filterMap fun t =>
        match mem[t]? with
        | none => none
        | some m =>
          if (m.loc == flagA && m.val == .num 1 &&
              decide (Promises.storeMview th (.const (.num 1)) [0] true ≤ m.view) &&
              decide (Promises.storeOb k arch th flagA (.const (.num 1)) [0] < t)) = true
          then some (mem, wCommit k th t (th.promises.erase t)) else none := rfl

/-- The writer's message view: its views are the initial ones and its operands
constants, so a release store publishes view `0`. -/
theorem writer_mview (mem : Memory) (pairs P : List Nat) :
    Promises.storeMview (wTh mem pairs P) (.const (.num 1)) [0] true = 0 := by
  simp [Promises.storeMview, Promises.depView, wTh, TermRun.mth, TermRun.regsOf, TermRun.stOf, writerAt,
    VState.init, fW, TermRun.cst, Promises.TVal.mk0]

/-- The writer's ordering bound is `0`, for every knob setting and either
architecture. -/
theorem writer_ob (mem : Memory) (pairs P : List Nat) :
    Promises.storeOb k arch (wTh mem pairs P) flagA (.const (.num 1)) [0] = 0 := by
  simp [Promises.storeOb, Promises.depView, Promises.depRts, wTh, TermRun.mth, TermRun.regsOf, TermRun.stOf,
    writerAt, VState.init, fW, TermRun.cst, Promises.TVal.mk0]

theorem wTh_promises (mem : Memory) (pairs P : List Nat) : (wTh mem pairs P).promises = P := rfl

/-- **The writer appends**: thread 0 before its store can append the flag
write `num 1` with view `0`, and is then finished with its promises kept. -/
theorem writer_append (c : TermRun.Cfg) (P : List Nat) (h0 : c.ths[0]? = some (writerAt P)) :
    ∃ vs, { c with mem := c.mem.push ⟨flagA, .num 1, 0⟩, ths := c.ths.set! 0 (writerDone vs P) } ∈
      TermRun.threadSteps pr k arch c 0 := by
  unfold TermRun.threadSteps
  rw [h0]
  simp only [tstep_writer, List.map_map]
  rw [← wTh, stepStore_flag, writer_mview]
  exact ⟨_, List.mem_map.mpr ⟨_, List.mem_cons_self, rfl⟩⟩

/-- **The writer fulfils**: thread 0 before its store can fulfil an
outstanding promise of the flag write `num 1` (any message view: the store
publishes view `0`), and is then finished with that promise discharged. -/
theorem writer_fulfil (c : TermRun.Cfg) (P : List Nat) (h0 : c.ths[0]? = some (writerAt P)) {p : Nat}
    (hp : p ∈ P) (hp0 : 0 < p) {vw : Nat} (hm : c.mem[p]? = some ⟨flagA, .num 1, vw⟩) :
    ∃ vs, { c with ths := c.ths.set! 0 (writerDone vs (P.erase p)) } ∈ TermRun.threadSteps pr k arch c 0 := by
  unfold TermRun.threadSteps
  rw [h0]
  simp only [tstep_writer, List.map_map]
  rw [← wTh, stepStore_flag, writer_mview, writer_ob, wTh_promises]
  refine ⟨_, List.mem_map.mpr ⟨(c.mem, wCommit (TermRun.gOf pr k arch c 0).k (wTh c.mem c.pairs P) p (P.erase p)),
    List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨p, hp, ?_⟩), rfl⟩⟩
  simp [hm, hp0]

/-- Thread 1 after its load of `w`, with views `vs` and undefined-read count
`u`. -/
def readerDone (vs : VState) (w : TermRun.Word) (u : Nat) : TermRun.TTh :=
  { term := .ret (.var "r"), env := ("r", .int, [w]) :: envF, vs := vs, undefs := u }

/-- The reader's step, as `Promises.stepLoad` of the flag, acquiring. -/
theorem tstep_reader (g : TermRun.G) (mem : Memory) (pairs : List Nat) :
    TermRun.tstep g mem pairs reader0 =
      (Promises.stepLoad g.arch mem pairs (TermRun.mth (TermRun.stOf mem pairs reader0) fW fW fW) 1 flagA [0]
          true).map
        fun th => (mem, pairs, readerDone th.vs (th.regs 1) (TermRun.countUndef [th.regs 1])) := by
  simp [TermRun.tstep, reader0, readerTerm, TermRun.evalOp, envF, TermRun.evalAt, TermRun.lookupE, fTy,
    cellOf, TermRun.addrOf, fW, TermRun.cst, Promises.TVal.mk0, flagA, TermRun.accs, TermRun.loadUnits,
    TermRun.offs, TermRun.withS, TermRun.stOf, readerDone]
  generalize Promises.stepLoad _ _ _ _ _ _ _ _ = L
  induction L <;> simp_all

/-- **The reader reads**: thread 1 before its load can read any message of
the flag (its ordering bound is `0`, so no message is hidden), and is then
finished with `r` bound to the message's value, view and timestamp. -/
theorem reader_read (c : TermRun.Cfg) (h1 : c.ths[1]? = some reader0) {t : Nat} {m : Msg}
    (hm : c.mem[t]? = some m) (hl : m.loc = flagA) :
    ∃ vs u, { c with ths := c.ths.set! 1 (readerDone vs ⟨m.val, m.view, t⟩ u) } ∈
      TermRun.threadSteps pr k arch c 1 := by
  have ht : t < c.mem.size := by
    rcases Nat.lt_or_ge t c.mem.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hm
  have hm' : c.mem[t]! = m := by
    rw [getElem!_pos c.mem t ht]; exact Option.some.inj ((Array.getElem?_eq_getElem ht).symm.trans hm)
  unfold TermRun.threadSteps
  rw [h1]
  simp only [tstep_reader, List.map_map]
  unfold Promises.stepLoad
  simp only [List.map_map]
  rw [← hm']
  refine ⟨_, _, List.mem_map.mpr ⟨t, List.mem_filter.mpr ⟨List.mem_range.mpr ht, ?_⟩, rfl⟩⟩
  simp [WeakMem.readable, WeakMem.hiddenFrom, hm, hl, Promises.readBoundOf, Promises.depBound,
      Promises.depView, Promises.depRts, TermRun.mth, TermRun.regsOf, TermRun.stOf, reader0, VState.init, fW,
      TermRun.cst, Promises.TVal.mk0]

/-- A thread at `ret` with an empty stack takes no thread step. -/
theorem threadSteps_done {p : CoreTerm.Prog} (c : TermRun.Cfg) {i : Nat} {th : TermRun.TTh} {a : At}
    (h : c.ths[i]? = some th) (ht : th.term = .ret a) (hs : th.stack = []) :
    TermRun.threadSteps p k arch c i = [] := by
  unfold TermRun.threadSteps
  rw [h]
  simp [TermRun.tstep, ht, hs]

/-- A source promise of thread `i`: the message is appended and its
timestamp (the old memory size) joins the thread's promises. -/
theorem promise_eq (c : TermRun.Cfg) {i : Nat} {th : TermRun.TTh} (h : c.ths[i]? = some th) (a : Address)
    (v : Val) (w : Nat) :
    TermRun.promise c i a v w =
      { c with mem := c.mem.push ⟨a, v, w⟩, ths := c.ths.set! i { th with promises := th.promises ++ [c.mem.size] } } := by
  unfold TermRun.promise
  rw [h]

end SrcSteps

/-! ## The memory relation -/

/-- **The memory part of the relation**, for the flag at Kraken address `F`
and a property `V` of the values written. The timestamp map is the identity:
the source memory has one more message than Kraken's message array (Kraken
timestamp `0` is the initial write, held apart in `init`), the source's first
message is the flag's initial one, and Kraken's message at timestamp `j + 1`
(`msgs[j]`) is a write of the flag whose source counterpart is the message at
index `j + 1`, a write of `num v` for the Kraken value `v`, with some message
view (the target has no message views). -/
structure MemRel (F : BitVec 64) (V : Kraken.Promising.Val → Prop) (km : Kraken.Promising.Memory)
    (sm : Memory) : Prop where
  init : km.init = [(⟨F, 8⟩, 0)]
  size : sm.size = km.msgs.size + 1
  zero : sm[0]? = some flagInit
  msg : ∀ j (h : j < km.msgs.size), km.msgs[j].loc = ⟨F, 8⟩ ∧ V km.msgs[j].val ∧
    ∃ vw, sm[j + 1]? = some ⟨flagA, .num km.msgs[j].val.toNat, vw⟩

namespace MemRel

variable {F : BitVec 64} {V : Kraken.Promising.Val → Prop} {km : Kraken.Promising.Memory} {sm : Memory}

/-- The start memories are related. -/
theorem start : MemRel F V { init := [(⟨F, 8⟩, 0)], msgs := #[] } #[flagInit] :=
  ⟨rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem mono {V' : Kraken.Promising.Val → Prop} (h : MemRel F V km sm) (hV : ∀ v, V v → V' v) :
    MemRel F V' km sm :=
  ⟨h.init, h.size, h.zero, fun j hj => let ⟨a, b, c⟩ := h.msg j hj; ⟨a, hV _ b, c⟩⟩

/-- **Appending on both sides**: a Kraken write of the flag and the source
write of its value, with any message view. -/
theorem push (h : MemRel F V km sm) {w : Kraken.Promising.Msg} (hl : w.loc = ⟨F, 8⟩) (hv : V w.val)
    (vw : Nat) : MemRel F V (km.append w).1 (sm.push ⟨flagA, .num w.val.toNat, vw⟩) := by
  refine ⟨h.init, by simp [Kraken.Promising.Memory.append, h.size], ?_, ?_⟩
  · rw [Array.getElem?_push]
    have : (0 : Nat) ≠ sm.size := by rw [h.size]; omega
    simp [this, h.zero]
  · intro j hj
    simp only [Kraken.Promising.Memory.append, Array.size_push] at hj
    rcases Nat.lt_or_ge j km.msgs.size with hj' | hj'
    · obtain ⟨a, b, vw', c⟩ := h.msg j hj'
      refine ⟨by simpa [Kraken.Promising.Memory.append, Array.getElem_push_lt hj'] using a,
        by simpa [Kraken.Promising.Memory.append, Array.getElem_push_lt hj'] using b, vw', ?_⟩
      rw [Array.getElem?_push]
      have : j + 1 ≠ sm.size := by rw [h.size]; omega
      simpa [this, Kraken.Promising.Memory.append, Array.getElem_push_lt hj'] using c
    · have hj2 : j = km.msgs.size := by omega
      subst hj2
      refine ⟨by simpa [Kraken.Promising.Memory.append] using hl, by simpa [Kraken.Promising.Memory.append] using hv,
        vw, ?_⟩
      rw [Array.getElem?_push]
      simp [h.size, Kraken.Promising.Memory.append]

/-- **A Kraken message has its counterpart**: the message at timestamp `p`
is a flag write, `p > 0`, and the source message at index `p` writes its
value. -/
theorem get (h : MemRel F V km sm) {p : Nat} {w : Kraken.Promising.Msg} (hg : km.get? p = some w) :
    w.loc = ⟨F, 8⟩ ∧ V w.val ∧ 0 < p ∧ ∃ vw, sm[p]? = some ⟨flagA, .num w.val.toNat, vw⟩ := by
  unfold Kraken.Promising.Memory.get? at hg
  by_cases hp : p = 0
  · simp [hp] at hg
  · simp only [hp, ↓reduceIte] at hg
    have hlt : p - 1 < km.msgs.size := by
      rcases Nat.lt_or_ge (p - 1) km.msgs.size with h' | h'
      · exact h'
      · simp [Array.getElem?_eq_none h'] at hg
    have hw : km.msgs[p - 1] = w := Option.some.inj ((Array.getElem?_eq_getElem hlt).symm.trans hg)
    obtain ⟨a, b, c⟩ := h.msg (p - 1) hlt
    have hp1 : p - 1 + 1 = p := by omega
    rw [hw] at a b c
    rw [hp1] at c
    exact ⟨a, b, by omega, c⟩

/-- **A Kraken read of the flag has its counterpart**: reading timestamp `t`
returns `v` exactly when the source message at index `t` writes `num v` to
the flag (`t = 0`: the initial value `0`). -/
theorem read (h : MemRel F V km sm) {t : Nat} {v : Kraken.Promising.Val}
    (hr : km.read? ⟨F, 8⟩ t = some v) :
    ∃ m, sm[t]? = some m ∧ m.loc = flagA ∧ m.val = .num v.toNat := by
  unfold Kraken.Promising.Memory.read? at hr
  split at hr
  · rename_i ht
    subst ht
    have hv : v = 0 := by
      simp [Kraken.Promising.Memory.initVal, h.init] at hr; exact hr.symm
    subst hv
    exact ⟨flagInit, h.zero, rfl, rfl⟩
  · cases hg : km.get? t with
    | none => rw [hg] at hr; cases hr
    | some w =>
      rw [hg] at hr
      simp only at hr
      split at hr
      · cases hr
        obtain ⟨-, -, -, vw, hs⟩ := h.get hg
        exact ⟨_, hs, rfl, rfl⟩
      · cases hr

/-- Every source message is to the flag. -/
theorem loc (h : MemRel F V km sm) {t : Nat} {m : Msg} (hm : sm[t]? = some m) : m.loc = flagA := by
  rcases t with _ | j
  · rw [h.zero] at hm; cases hm; rfl
  · have hj : j < km.msgs.size := by
      rcases Nat.lt_or_ge j km.msgs.size with h' | h'
      · exact h'
      · have : sm.size ≤ j + 1 := by rw [h.size]; omega
        simp [Array.getElem?_eq_none this] at hm
    obtain ⟨-, -, vw, hs⟩ := h.msg j hj
    rw [hs] at hm; cases hm; rfl

end MemRel

/-! ## The lockstep lemma -/

/-- **Lockstep certification.** Let `TR` relate a Kraken thread with its
memory to a source configuration, such that (1) every promise-free solo step
of the Kraken thread (`ThreadStep`) from a related pair is matched by a
thread step of source thread `i` to a related pair, and (2) a related Kraken
thread with no outstanding promise has a source thread `i` with none. Then a
Kraken certification run (`CertOk`: a promise-free solo run emptying the
promise set) gives a WeakCore certification (`Certified`: a `Solo` run of
thread `i` reaching `noPromises`), the source run taking one thread step per
Kraken step. -/
theorem certified_of_certOk {I : Kraken.Promising.ISA} {A : Kraken.Promising.Arch} {tid : Nat}
    {p : CoreTerm.Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {i : Nat}
    (TR : Kraken.Promising.Thread I × Kraken.Promising.Memory → TermRun.Cfg → Prop)
    (hstep : ∀ q q' s, TR q s → Kraken.Promising.ThreadStep A tid q q' →
      ∃ s', s' ∈ TermRun.threadSteps p k arch s i ∧ TR q' s')
    (hdone : ∀ q s, TR q s → q.1.prom = [] → TermRun.noPromises s i = true)
    {t : Kraken.Promising.Thread I} {mem : Kraken.Promising.Memory} {s : TermRun.Cfg} (h : TR (t, mem) s)
    (hc : Kraken.Promising.CertOk A tid t mem) : TermRun.Certified p k arch s i := by
  obtain ⟨t', mem', hrun, hp⟩ := hc
  suffices H : ∀ q q', Kraken.Promising.ThreadNP A tid q q' → q'.1.prom = [] → ∀ s, TR q s →
      TermRun.Certified p k arch s i from H _ _ hrun hp s h
  intro q q' hrun hp
  induction hrun with
  | refl q => intro s h; exact ⟨s, .refl s, hdone q s h hp⟩
  | step hs _ ih =>
    intro s h
    obtain ⟨s', hs', h'⟩ := hstep _ _ s h hs
    obtain ⟨s'', hsolo, hn⟩ := ih hp s' h'
    exact ⟨s'', .thread hs' hsolo, hn⟩

end Spike.Bridge
