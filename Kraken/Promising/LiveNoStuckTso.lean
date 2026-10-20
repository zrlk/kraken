/-
**No stuck configuration on TSO** (ISA-neutral,
`Arch.tso`, any program without non-temporal stores and with at most one
write per instruction).

On TSO every store that is not non-temporal is a release (`Arch.tso`), so it
lands above `vwOld`, and every write raises `vwOld` to its timestamp. Hence a
fresh write (an append) by a thread with an outstanding promise raises `vwOld`
above every outstanding promise, which can then never be fulfilled
(`DeadT`). A certification therefore never needs a fresh write: it can be cut
to one against the same memory (`NACertG`), which replays against every larger
memory. So every configuration reachable on the semantic machine has every
thread certifiable (`ConsistentSem`), and by N1 (`LiveNoStuck.lean`) none is
stuck.

The cut needs the instruction that fulfils the last promise not to append
afterwards. The hypothesis `TsoCertInv P` asks, of a state invariant `P`
closed under TSO instruction steps, for no non-temporal store and at most one
write per instruction (`EvTree.OneWrite`); `ISA.NoNTInv Arch.tso` gives the
first and the closure (`TsoCertInv.of_noNTInv`). It is a per-program fact.

- `runTree_replay`, `stepOne_replay_same`, `threadNPn_replay_same`,
  `NACertG.replay`: any architecture, any program: an instruction outcome, a
  solo run, a certification that leaves memory alone replays against a larger
  memory (for a thread bounded by the smaller memory's `|M|`).
- `TsoRun`, `runTree_tso`, `stepOne_tso`: the TSO facts of one instruction
  (`vwOld` grows; promises only go; a fulfilled promise lies above `vwOld`; an
  append raises `vwOld` above the old `|M|`).
- `EvTree.NoWrite`, `EvTree.OneWrite`, `stepOne_oneWrite`.
- `DeadT`, `DeadT.step`, `deadT_threadNPn`, `not_certOkN_of_deadT`.
- **`tsoCertNoFresh`**, **`tsoConsistent`**, **`tsoNoStuck`**.
-/
import Kraken.Promising.LiveNoStuck
import Kraken.Promising.LiveSemShape
import Kraken.Promising.NTFreeTso

namespace Kraken.Promising.Live.NoStuck

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
  Kraken.Promising.Live.TicketStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Context updates that touch neither memory nor promises nor `vwOld` -/

theorem fenceStep_withMem (c : Ctx) (k : FenceKind) (m : Memory) :
    fenceStep { c with mem := m } k = { fenceStep c k with mem := m } := by
  cases k <;> rfl

theorem fenceOpt_withMem (b : Bool) (c : Ctx) (k : FenceKind) (m : Memory) :
    (if b then fenceStep { c with mem := m } k else { c with mem := m }) =
      { (if b then fenceStep c k else c) with mem := m } := by
  cases b
  · rfl
  · exact fenceStep_withMem c k m

theorem rmwPost_withMem (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) (m : Memory) :
    rmwPost A k noRet l { c with mem := m } = { rmwPost A k noRet l c with mem := m } := by
  unfold rmwPost
  cases (A.rmwKind k == RmwKind.acqRel && !noRet) <;> rfl

theorem fenceStep_same (c : Ctx) (k : FenceKind) :
    (fenceStep c k).views.vwOld = c.views.vwOld ∧ (fenceStep c k).prom = c.prom ∧ (fenceStep c k).mem = c.mem := by
  cases k <;> exact ⟨rfl, rfl, rfl⟩

/-- The bound a read checks lies within memory, for a bounded context. -/
theorem readBound_le (A : Arch) {iv : InstrViews} {c : Ctx} (hc : c.Bnd) (hiv : iv.Le c.mem.last) (k : LoadKind)
    (l : Loc) : max (readPre A iv c k) (c.views.getCoh l) ≤ c.mem.last := by
  have := hiv.addrR; have := hc.views.le.vrNew; have := hc.views.le.vRel; have := hc.views.le.coh l
  simp only [readPre]; split <;> omega_t

theorem fenceOpt_same (b : Bool) (c : Ctx) (k : FenceKind) :
    (if b then fenceStep c k else c).views.vwOld = c.views.vwOld ∧
      (if b then fenceStep c k else c).prom = c.prom ∧ (if b then fenceStep c k else c).mem = c.mem := by
  cases b
  · exact ⟨rfl, rfl, rfl⟩
  · cases k <;> exact ⟨rfl, rfl, rfl⟩

theorem rmwPost_same (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwPost A k noRet l c).views.vwOld = c.views.vwOld ∧ (rmwPost A k noRet l c).prom = c.prom ∧
      (rmwPost A k noRet l c).mem = c.mem := by
  unfold rmwPost
  cases (A.rmwKind k == RmwKind.acqRel && !noRet) <;> exact ⟨rfl, rfl, rfl⟩

/-! ## Replay of memory-preserving steps (any architecture, any program) -/

section Replay

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A run of any event tree that leaves memory alone replays against a
larger memory**, from a context bounded by the smaller memory's `|M|`. -/
theorem runTree_replay {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx) (mem : Memory), c.Bnd → iv.Le c.mem.last → c.mem.Prefix mem →
      .ok (s, c') ∈ runTree A tid iv c tree → c'.mem = c.mem →
      .ok (s, { c' with mem := mem }) ∈ runTree A tid iv { c with mem := mem } tree := by
  induction tree with
  | done s0 =>
    intro c s c' mem _ _ _ h _
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fault msg =>
    intro c s c' mem _ _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' mem hc hiv hp h hm
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi0, hi⟩ := h
    exact ⟨i, hi0, ih i c s c' mem hc hiv hp hi hm⟩
  | load k xcl l ret ih =>
    intro c s c' mem hc hiv hp h hm
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hr := readSuccs_bnd A iv hc hiv h0
    have hm0 : c0.mem = c.mem := hr.2.2
    have hbd := readBound_le A hc hiv k l
    refine ⟨(t, v, { c0 with mem := mem }), SemShape.readSuccs_replay A iv hp h0 hbd, ?_⟩
    exact ih v c0 s c' mem hr.1 (by rw [hm0]; exact hiv) (by rw [hm0]; exact hp) h (hm.trans hm0.symm)
  | store k xcl l v ret ih =>
    intro c s c' mem hc hiv hp h hm
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · left
      rw [List.mem_ite_nil_left, List.mem_flatMap] at h ⊢
      obtain ⟨hx, c0, hc0, h⟩ := h
      obtain ⟨hb0, hl0⟩ := writeSuccs_bnd A tid _ hc (hiv.forStore c.stores) (Nat.zero_le _) hc0
      obtain ⟨-, hl⟩ := runTree_bnd A tid iv (ret true) c0 s c' hb0 (hiv.mono hl0) h
      have hm0 : c0.mem = c.mem := by
        rcases SemShape.mem_writeSuccs A tid _ hc0 with ⟨e1, -⟩ | ⟨_, _, _, _, _, e, -⟩
        · exfalso
          have := congrArg Memory.last e1
          rw [Memory.last_append] at this
          rw [hm] at hl
          omega_t
        · exact e
      refine ⟨hx, { c0 with mem := mem }, SemShape.writeSuccs_replay A tid _ hp hc0 hm0, ?_⟩
      exact ih true c0 s c' mem hb0 (by rw [hm0]; exact hiv) (by rw [hm0]; exact hp) h (hm.trans hm0.symm)
    · right
      rw [List.mem_ite_nil_right] at h ⊢
      obtain ⟨hx, h⟩ := h
      refine ⟨hx, ?_⟩
      have h0 : Ctx.Bnd
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        ⟨hc.views.xclbNone, hc.loadViews, Nat.zero_le _⟩
      exact ih false _ s c' mem h0 hiv hp h hm
  | fence k ret ih =>
    intro c s c' mem hc hiv hp h hm
    simp only [runTree] at h ⊢
    rw [fenceStep_withMem]
    have hm1 := fenceStep_mem c k
    exact ih () _ s c' mem (fenceStep_bnd hc k) (by rw [hm1]; exact hiv) (by rw [hm1]; exact hp) h
      (by rw [hm, hm1])
  | rmw k noRet l op ret ih =>
    intro c s c' mem hc hiv hp h hm
    simp only [runTree] at h ⊢
    rw [fenceOpt_withMem]
    obtain ⟨hb1, hm1⟩ := fenceOpt_bnd hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hb1 hm1 ⊢
    rw [List.mem_flatMap] at h ⊢
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have hr := readSuccs_bnd A iv hb1 (by rw [hm1]; exact hiv) h2
    have hb2 : c2.Bnd := hr.1
    have hm2 : c2.mem = c.mem := hr.2.2.trans hm1
    have hbd := readBound_le A hb1 (by rw [hm1]; exact hiv) (if noRet then .plain else (A.rmwKind k).loadKind) l
    refine ⟨(tr, old, { c2 with mem := mem }),
      SemShape.readSuccs_replay A iv (by rw [hm1]; exact hp) h2 hbd, ?_⟩
    simp only at h ⊢
    cases hop : op old with
    | none =>
      simp only [hop] at h ⊢
      rw [fenceOpt_withMem]
      obtain ⟨hb3, hm3⟩ := fenceOpt_bnd hb2 A.rmwFence .sy
      exact ih old _ s c' mem hb3 (by rw [hm3, hm2]; exact hiv) (by rw [hm3, hm2]; exact hp) h
        (by rw [hm3, hm2]; exact hm)
    | some new =>
      simp only [hop] at h ⊢
      rw [List.mem_flatMap] at h ⊢
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨hb3, hl3⟩ := writeSuccs_bnd A tid iv hb2 (by rw [hm2]; exact hiv)
        (getLastD_le' hb2.loadViews) hc3
      obtain ⟨hb4, hm4⟩ := rmwPost_bnd A hb3 k noRet l
      obtain ⟨hb5, hm5⟩ := fenceOpt_bnd hb4 A.rmwFence .sy
      obtain ⟨-, hl⟩ := runTree_bnd A tid iv (ret old) _ s c' hb5 (by rw [hm5, hm4]; exact hiv.mono (hm2 ▸ hl3)) h
      rw [hm5, hm4, hm] at hl
      have hm3 : c3.mem = c2.mem := by
        rcases SemShape.mem_writeSuccs A tid _ hc3 with ⟨e1, -⟩ | ⟨_, _, _, _, _, e, -⟩
        · exfalso
          have := congrArg Memory.last e1
          rw [Memory.last_append, hm2] at this
          omega_t
        · exact e
      refine ⟨{ c3 with mem := mem }, SemShape.writeSuccs_replay A tid _ (by rw [hm2]; exact hp) hc3 hm3, ?_⟩
      change .ok (s, { c' with mem := mem }) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l { c3 with mem := mem }) .sy
          else rmwPost A k noRet l { c3 with mem := mem }) (ret old)
      rw [rmwPost_withMem, fenceOpt_withMem]
      have hm35 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3).mem =
          c.mem := by rw [hm5, hm4, hm3, hm2]
      exact ih old _ s c' mem hb5 (by rw [hm35]; exact hiv) (by rw [hm35]; exact hp) h (hm.trans hm35.symm)
where
  getLastD_le' {xs : List View} {n : Nat} (h : ∀ ν ∈ xs, ν ≤ n) : xs.getLastD 0 ≤ n := by
    cases xs with
    | nil => exact Nat.zero_le _
    | cons x xs =>
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (List.cons_ne_nil x xs)]
      exact h _ (List.getLast_mem _)

end Replay

/-- **An instruction outcome that leaves memory alone replays against a larger
memory** (any architecture, any program), for a thread bounded by the smaller
memory's `|M|`. -/
theorem stepOne_replay_same {A : Arch} {tid : Nat} {t : Thread I} {mem0 mem : Memory}
    {outs : List (Except String (Outcome I))} {o : Outcome I}
    (hb : t.Bnd mem0.last) (hp : mem0.Prefix mem) (hs : stepOne A t tid mem0 = some outs) (ho : .ok o ∈ outs)
    (hm : o.mem = mem0) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  obtain ⟨tree, -, hex, -⟩ := SLR.stepOne_runK A hs ho
  refine SemShape.stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  have hc : Ctx.Bnd (ctx0 tid t mem0) := ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  exact runTree_replay A tid _ tree _ st c0' mem hc (instrViews_le hb.regs (I.deps t.st)) hp hr hm'

/-- **A solo run that leaves memory alone replays against a larger memory**
(any architecture, any program). -/
theorem threadNPn_replay_same {A : Arch} {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadNPn A tid n p q) (he : p.2 = q.2) (hb : p.1.Bnd p.2.last) (mem : Memory) (hp : p.2.Prefix mem) :
    ThreadNPn A tid n (p.1, mem) (q.1, mem) :=
  nacertG_replay (fun _ => True) (fun _ _ _ => trivial)
    (fun _ hb hp hs ho hm => stepOne_replay_same hb hp hs ho hm) h he trivial hb mem hp

/-- **A certification without fresh writes replays against a larger memory**
(any architecture, any program). -/
theorem NACertG.replay {A : Arch} {fuel tid : Nat} {t : Thread I} {mem mem' : Memory}
    (h : NACertG A fuel tid t mem) (hb : t.Bnd mem.last) (hp : mem.Prefix mem') : NACertG A fuel tid t mem' := by
  obtain ⟨t', hr, ht'⟩ := h
  exact ⟨t', threadNPn_replay_same hr rfl hb mem' hp, ht'⟩

/-! ## One write per instruction -/

/-- The event tree makes no write (no store, no read-modify-write). -/
def _root_.Kraken.Promising.EvTree.NoWrite {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).NoWrite
  | .load _ _ _ ret => ∀ v, (ret v).NoWrite
  | .store .. => False
  | .rmw .. => False
  | .fence _ ret => (ret ()).NoWrite

/-- Every path of the event tree makes at most one write (store or
read-modify-write). -/
def _root_.Kraken.Promising.EvTree.OneWrite {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).OneWrite
  | .load _ _ _ ret => ∀ v, (ret v).OneWrite
  | .store _ _ _ _ ret => ∀ b, (ret b).NoWrite
  | .rmw _ _ _ _ ret => ∀ v, (ret v).NoWrite
  | .fence _ ret => (ret ()).OneWrite

/-- **The program's TSO certification invariant**: `P` is a state invariant
of the thread's TSO instruction steps under which no instruction makes a
non-temporal store and every instruction makes at most one write. Closure is
asked of `stepOne` (as the per-program `step_sinv` lemmas state it), which
`ISA.NoNTInv` implies (`TsoCertInv.of_noNTInv`). -/
structure TsoCertInv (I : ISA) (P : I.State → Prop) : Prop where
  /-- The instruction at a `P` state makes no non-temporal store. -/
  noNT : ∀ s, P s → ∀ tree, I.exec s = some tree → tree.NoNT Arch.tso
  /-- The instruction at a `P` state makes at most one write. -/
  oneWrite : ∀ s, P s → ∀ tree, I.exec s = some tree → tree.OneWrite
  /-- Every TSO instruction step from a `P` state ends in a `P` state. -/
  step : ∀ {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I},
    P t.st → stepOne Arch.tso t tid mem = some outs → .ok o ∈ outs → P o.thread.st

/-- A `NoNTInv` invariant of a one-write program is a `TsoCertInv`. -/
theorem TsoCertInv.of_noNTInv {P : I.State → Prop} (h : I.NoNTInv Arch.tso P)
    (hw : ∀ s, P s → ∀ tree, I.exec s = some tree → tree.OneWrite) : TsoCertInv I P :=
  ⟨h.noNT, hw, fun hS hs ho => stepOne_leaf Arch.tso hs ho fun tree hex => h.step _ hS tree hex⟩

section Write

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem mem_erase_append {p : List Time} {n x : Time} (h : x ∈ (p ++ [n]).erase n) : x ∈ p := by
  by_cases hn : n ∈ p
  · rw [List.erase_append_left _ hn] at h
    rcases List.mem_append.mp h with h | h
    · exact List.mem_of_mem_erase h
    · rw [List.mem_singleton] at h; subst h; exact hn
  · rw [List.erase_append_right _ hn] at h
    simpa using h

theorem mem_erase_append_of_mem {p : List Time} {n x : Time} (h : x ∈ p) : x ∈ (p ++ [n]).erase n := by
  by_cases hn : n ∈ p
  · rw [List.erase_append_left _ hn]
    by_cases e : x = n
    · subst e; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ ((List.mem_erase_of_ne e).mpr h)
  · rw [List.erase_append_right _ hn]
    exact List.mem_append_left _ h

/-- A run of a write-free tree changes neither promises nor memory. -/
theorem runTree_noWrite {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), tree.NoWrite → .ok (s, c') ∈ runTree A tid iv c tree →
      c'.prom = c.prom ∧ c'.mem = c.mem := by
  induction tree with
  | done s0 =>
    intro c s c' _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | fault msg => intro c s c' _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, hi⟩ := h
    exact ih i c s c' (hw i) hi
  | load k xcl l ret ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    obtain ⟨t', v', e, -⟩ := (mem_readSuccs A).mp h0
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have := ih v _ s c' (hw v) h
    exact this
  | store => intro c s c' hw; exact absurd hw id
  | rmw => intro c s c' hw; exact absurd hw id
  | fence k ret ih =>
    intro c s c' hw h
    simp only [runTree] at h
    obtain ⟨-, hp, hm⟩ := fenceStep_same c k
    obtain ⟨e1, e2⟩ := ih () _ s c' hw h
    exact ⟨e1.trans hp, e2.trans hm⟩

/-- **A run of a one-write tree that changes memory keeps every promise**: its
only write is the append. -/
theorem runTree_oneWrite {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), tree.OneWrite → .ok (s, c') ∈ runTree A tid iv c tree →
      c'.mem ≠ c.mem → ∀ x ∈ c.prom, x ∈ c'.prom := by
  induction tree with
  | done s0 =>
    intro c s c' _ h hm
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd rfl hm
  | fault msg => intro c s c' _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, hi⟩ := h
    exact ih i c s c' (hw i) hi
  | load k xcl l ret ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    obtain ⟨t', v', e, -⟩ := (mem_readSuccs A).mp h0
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have := ih v _ s c' (hw v) h
    exact this
  | store k xcl l v ret _ =>
    intro c s c' hw h hm
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨e1, e2⟩ := runTree_noWrite A tid iv (ret true) c0 s c' (hw true) h
      rcases SemShape.mem_writeSuccs A tid _ hc0 with ⟨-, ep, -⟩ | ⟨_, _, _, _, _, em, -⟩
      · intro x hx; rw [e1, ep]; exact mem_erase_append_of_mem hx
      · exact absurd (e2.trans em) hm
    · rw [List.mem_ite_nil_right] at h
      obtain ⟨e1, e2⟩ := runTree_noWrite A tid iv (ret false) _ s c' (hw false) h.2
      exact absurd e2 hm
  | fence k ret ih =>
    intro c s c' hw h hm
    simp only [runTree] at h
    obtain ⟨-, hp, hmf⟩ := fenceStep_same c k
    intro x hx
    exact ih () _ s c' hw h (by rw [hmf]; exact hm) x (by rw [hp]; exact hx)
  | rmw k noRet l op ret _ =>
    intro c s c' hw h hm
    simp only [runTree] at h
    obtain ⟨-, hp1, hm1⟩ := fenceOpt_same A.rmwFence c .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h hp1 hm1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    obtain ⟨t', v', e, -⟩ := (mem_readSuccs A).mp h2
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    simp only at h
    cases hop : op old with
    | none =>
      simp only [hop] at h
      obtain ⟨-, -, hm3⟩ := fenceOpt_same A.rmwFence (readNext A iv c1 (if noRet then LoadKind.plain else (A.rmwKind k).loadKind) false l noRet tr old) .sy
      obtain ⟨-, e2⟩ := runTree_noWrite A tid iv (ret old) _ s c' (hw old) h
      exact absurd (e2.trans (hm3.trans hm1)) hm
    | some new =>
      simp only [hop] at h
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨e1, e2⟩ := runTree_noWrite A tid iv (ret old) _ s c' (hw old) h
      obtain ⟨-, hp4, hm4⟩ := rmwPost_same A k noRet l c3
      obtain ⟨-, hp5, hm5⟩ := fenceOpt_same A.rmwFence (rmwPost A k noRet l c3) .sy
      rw [hp5, hp4] at e1
      rw [hm5, hm4] at e2
      rcases SemShape.mem_writeSuccs A tid _ hc3 with ⟨-, ep, -⟩ | ⟨_, _, _, _, _, em, -⟩
      · intro x hx
        rw [e1, ep]
        exact mem_erase_append_of_mem (by rw [← hp1] at hx; exact hx)
      · exact absurd (e2.trans (em.trans hm1)) hm

end Write

/-- **An instruction of a one-write program that changes memory keeps every
promise.** -/
theorem stepOne_oneWrite {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} {o : Outcome I}
    (hw : ∀ tree, I.exec t.st = some tree → tree.OneWrite) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem ≠ mem) : ∀ x ∈ t.prom, x ∈ o.thread.prom := by
  obtain ⟨tree, c', hex, hr, hp, -, hmo, -⟩ := SLR.stepOne_runK A hs ho
  rw [hp]
  exact runTree_oneWrite A tid _ tree _ _ c' (hw tree hex) hr (by rw [← hmo]; exact hm)

/-! ## One instruction on TSO -/

/-- The TSO facts of a run from `c` to `c'`: `vwOld` grows, promises only go,
a promise that goes lies above `vwOld`, and a change of memory raises `vwOld`
above the old `|M|`. -/
def TsoRun (c c' : Ctx) : Prop :=
  c.views.vwOld ≤ c'.views.vwOld ∧ (∀ x ∈ c'.prom, x ∈ c.prom) ∧
    (∀ x ∈ c.prom, x ∉ c'.prom → c.views.vwOld < x) ∧ (c'.mem ≠ c.mem → c.mem.last < c'.views.vwOld)

theorem TsoRun.of_same {c c' : Ctx} (h1 : c'.views.vwOld = c.views.vwOld) (h2 : c'.prom = c.prom)
    (h3 : c'.mem = c.mem) : TsoRun c c' :=
  ⟨Nat.le_of_eq h1.symm, fun _ hx => h2 ▸ hx, fun _ hx hn => absurd (h2 ▸ hx) hn, fun h => absurd h3 h⟩

theorem TsoRun.trans {c c' c'' : Ctx} (h : TsoRun c c') (h' : TsoRun c' c'') : TsoRun c c'' := by
  obtain ⟨a1, b1, c1, d1⟩ := h
  obtain ⟨a2, b2, c2, d2⟩ := h'
  refine ⟨Nat.le_trans a1 a2, fun x hx => b1 x (b2 x hx), fun x hx hn => ?_, fun hm => ?_⟩
  · by_cases hx' : x ∈ c'.prom
    · exact Nat.lt_of_le_of_lt a1 (c2 x hx' hn)
    · exact c1 x hx hx'
  · by_cases e : c'.mem = c.mem
    · rw [← e]; exact d2 (by rw [e]; exact hm)
    · exact Nat.lt_of_lt_of_le (d1 e) a2

/-- On TSO, a store that is not non-temporal is a release. -/
theorem tso_storeKind_rel {k : StoreKind} (h : Arch.tso.storeKind k ≠ .nt) : Arch.tso.storeKind k = .rel := by
  cases k <;> simp_all [Arch.storeKind, Arch.tso]

/-- A TSO write that is not non-temporal. -/
theorem tsoRun_write {xr : View} (tid : Nat) (iv : InstrViews) {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (hk : Arch.tso.storeKind k ≠ .nt)
    (h : c' ∈ writeSuccs Arch.tso tid iv c k xcl l v tr extra xr) : TsoRun c c' := by
  have hrel := tso_storeKind_rel hk
  rcases SemShape.mem_writeSuccs Arch.tso tid iv h with
    ⟨e1, e2, e3, e4, -⟩ | ⟨ts, hts, -, -, e3, e4, e5, e6, -⟩
  · refine ⟨e4, fun x hx => mem_erase_append (e2 ▸ hx), fun x hx hn => ?_, fun _ => ?_⟩
    · exact absurd (by rw [e2]; exact mem_erase_append_of_mem hx) hn
    · have := e3 (by rw [hrel]; rfl); omega_t
  · refine ⟨e6, fun x hx => List.mem_of_mem_erase (e5 ▸ hx), fun x hx hn => ?_, fun hm => absurd e4 hm⟩
    by_cases e : x = ts
    · subst e; exact e3 (by rw [hrel]; rfl)
    · exact absurd (by rw [e5]; exact (List.mem_erase_of_ne e).mpr hx) hn

/-- **The TSO facts of a run of any tree without non-temporal stores.** -/
theorem runTree_tso (tid : Nat) (iv : InstrViews) {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), tree.NoNT Arch.tso → .ok (s, c') ∈ runTree Arch.tso tid iv c tree →
      TsoRun c c' := by
  induction tree with
  | done s0 =>
    intro c s c' _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact TsoRun.of_same rfl rfl rfl
  | fault msg => intro c s c' _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, hi⟩ := h
    exact ih i c s c' (hw i) hi
  | load k xcl l ret ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    obtain ⟨t', v', e, -⟩ := (mem_readSuccs Arch.tso).mp h0
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have := ih v _ s c' (hw v) h
    exact (TsoRun.of_same rfl rfl rfl).trans this
  | store k xcl l v ret ih =>
    intro c s c' hw h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (tsoRun_write tid _ hw.1 hc0).trans (ih true c0 s c' (hw.2 true) h)
    · rw [List.mem_ite_nil_right] at h
      have := ih false _ s c' (hw.2 false) h.2
      exact (TsoRun.of_same rfl rfl rfl).trans this
  | fence k ret ih =>
    intro c s c' hw h
    simp only [runTree] at h
    obtain ⟨e1, e2, e3⟩ := fenceStep_same c k
    exact (TsoRun.of_same e1 e2 e3).trans (ih () _ s c' hw h)
  | rmw k noRet l op ret ih =>
    intro c s c' hw h
    simp only [runTree] at h
    obtain ⟨f1, f2, f3⟩ := fenceOpt_same Arch.tso.rmwFence c .sy
    have h01 := TsoRun.of_same f1 f2 f3
    generalize (if Arch.tso.rmwFence then fenceStep c .sy else c) = c1 at h h01
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    obtain ⟨t', v', e, -⟩ := (mem_readSuccs Arch.tso).mp h2
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have h12 : TsoRun c1 (readNext Arch.tso iv c1 (if noRet then LoadKind.plain else (Arch.tso.rmwKind k).loadKind) false l noRet tr old) := TsoRun.of_same rfl rfl rfl
    simp only at h
    cases hop : op old with
    | none =>
      simp only [hop] at h
      obtain ⟨g1, g2, g3⟩ := fenceOpt_same Arch.tso.rmwFence (readNext Arch.tso iv c1 (if noRet then LoadKind.plain else (Arch.tso.rmwKind k).loadKind) false l noRet tr old) .sy
      exact ((h01.trans h12).trans (TsoRun.of_same g1 g2 g3)).trans (ih old _ s c' (hw.2 old) h)
    | some new =>
      simp only [hop] at h
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree Arch.tso tid iv
        (if Arch.tso.rmwFence then fenceStep (rmwPost Arch.tso k noRet l c3) .sy
          else rmwPost Arch.tso k noRet l c3) (ret old) at h
      obtain ⟨p1, p2, p3⟩ := rmwPost_same Arch.tso k noRet l c3
      obtain ⟨g1, g2, g3⟩ := fenceOpt_same Arch.tso.rmwFence (rmwPost Arch.tso k noRet l c3) .sy
      exact ((((h01.trans h12).trans (tsoRun_write tid _ hw.1 hc3)).trans (TsoRun.of_same p1 p2 p3)).trans
        (TsoRun.of_same g1 g2 g3)).trans (ih old _ s c' (hw.2 old) h)

/-- **The TSO facts of one instruction without non-temporal stores.** -/
theorem stepOne_tso {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))}
    {o : Outcome I} (hnt : ∀ tree, I.exec t.st = some tree → tree.NoNT Arch.tso)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok o ∈ outs) :
    t.views.vwOld ≤ o.thread.views.vwOld ∧ (∀ x ∈ o.thread.prom, x ∈ t.prom) ∧
      (∀ x ∈ t.prom, x ∉ o.thread.prom → t.views.vwOld < x) ∧ (o.mem ≠ mem → mem.last < o.thread.views.vwOld) := by
  obtain ⟨tree, c', hex, hr, hp, hv, hm, -⟩ := SLR.stepOne_runK Arch.tso hs ho
  have hvw : o.thread.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld hv; exact this
  have := runTree_tso tid _ tree _ _ c' (hnt tree hex) hr
  rw [hvw, hp, hm]
  exact this

/-! ## Dead promises on TSO -/

/-- **A dead thread on TSO**: it has an outstanding promise, and every one
lies below `vwOld`, so none can be fulfilled by a (release) write. -/
def DeadT (t : Thread I) : Prop :=
  t.prom ≠ [] ∧ ∀ x ∈ t.prom, x < t.views.vwOld

theorem DeadT.step {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))}
    {o : Outcome I} (hnt : ∀ tree, I.exec t.st = some tree → tree.NoNT Arch.tso) (hd : DeadT t)
    (hs : stepOne Arch.tso t tid mem = some outs) (ho : .ok o ∈ outs) : DeadT o.thread := by
  obtain ⟨h1, h2, h3, -⟩ := stepOne_tso hnt hs ho
  obtain ⟨hne, hlt⟩ := hd
  have hkeep : ∀ y ∈ t.prom, y ∈ o.thread.prom := fun y hy =>
    Classical.byContradiction fun hn => Nat.lt_asymm (hlt y hy) (h3 y hy hn)
  refine ⟨fun he => ?_, fun y hy => Nat.lt_of_lt_of_le (hlt y (h2 y hy)) h1⟩
  cases hp : t.prom with
  | nil => exact hne hp
  | cons x xs =>
    have := hkeep x (by rw [hp]; exact List.mem_cons_self)
    rw [he] at this; cases this

/-- A dead thread stays dead along every solo run. -/
theorem deadT_threadNPn {P : I.State → Prop} (hP : TsoCertInv I P) {tid n : Nat} {p q : Thread I × Memory}
    (h : ThreadNPn Arch.tso tid n p q) (hS : P p.1.st) (hd : DeadT p.1) : DeadT q.1 := by
  induction h with
  | refl => exact hd
  | step hs _ ih =>
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    exact ih (hP.step hS hs ho)
      (hd.step (fun tree hex => hP.noNT _ hS tree hex) hs ho)

/-- A dead thread is not certifiable, at any fuel. -/
theorem not_certOkN_of_deadT {P : I.State → Prop} (hP : TsoCertInv I P) {tid n : Nat} {t : Thread I}
    {mem : Memory} (hS : P t.st) (hd : DeadT t) : ¬ CertOkN Arch.tso tid t mem n := by
  rintro ⟨t', mem', h, hp⟩
  exact (deadT_threadNPn hP h hS hd).1 hp

/-! ## N5 -/

/-- N5, the key lemma: on TSO, under `TsoCertInv`, every certification of a
thread whose promises are in memory can be cut to one without fresh writes. -/
def TsoCertNoFresh (I : ISA) : Prop :=
  ∀ (P : I.State → Prop), TsoCertInv I P →
    ∀ (tid n : Nat) (t : Thread I) (mem : Memory), P t.st → (∀ x ∈ t.prom, x ≤ mem.last) →
      CertOkN Arch.tso tid t mem n → NACertG Arch.tso n tid t mem

/-- The invariant behind N5: every configuration reachable on the TSO semantic
machine from a bounded, promise-free configuration whose threads satisfy `P`
has every thread certifiable. -/
def TsoConsistent (I : ISA) : Prop :=
  ∀ (P : I.State → Prop) (fuel : Nat) (c0 c : Config I), TsoCertInv I P → c0.Bnd →
    (∀ (tid : Nat) (t : Thread I), c0.threads[tid]? = some t → P t.st ∧ t.prom = []) →
    ReachableSem Arch.tso fuel c0 c → ConsistentSem Arch.tso fuel c

/-- N5: no stuck configuration is reachable on the TSO semantic machine (given
`OkStepsPF` along the run). -/
def TsoNoStuck (I : ISA) : Prop :=
  ∀ (P : I.State → Prop) (fuel : Nat) (c0 : Config I), TsoCertInv I P → c0.Bnd →
    (∀ (tid : Nat) (t : Thread I), c0.threads[tid]? = some t → P t.st ∧ t.prom = []) →
    (∀ c, ReachableSem Arch.tso fuel c0 c → OkStepsPF Arch.tso c) →
    NoStuckFrom Arch.tso fuel c0

/-- The cut, on runs. -/
theorem tso_cut {P : I.State → Prop} (hP : TsoCertInv I P) {tid : Nat} :
    ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn Arch.tso tid n p q → q.1.prom = [] → P p.1.st →
      (∀ x ∈ p.1.prom, x ≤ p.2.last) → NACertG Arch.tso n tid p.1 p.2 := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hS hle
    obtain ⟨outs, o, hs, ho, rfl⟩ := hs
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    have hnt : ∀ tree, I.exec p.1.st = some tree → tree.NoNT Arch.tso :=
      fun tree hex => hP.noNT _ hS tree hex
    have hS' : P o.thread.st := hP.step hS hs ho
    obtain ⟨-, h2, -, h4⟩ := stepOne_tso hnt hs ho
    by_cases hm : o.mem = p.2
    · have hle' : ∀ x ∈ o.thread.prom, x ≤ o.mem.last := fun x hx => hm ▸ hle x (h2 x hx)
      obtain ⟨t', hr, ht'⟩ := ih hq hS' hle'
      rw [hm] at hr
      exact ⟨t', .step ⟨outs, o, hs, ho, by rw [hm]⟩ hr, ht'⟩
    · have hkeep := stepOne_oneWrite (fun tree hex => hP.oneWrite _ hS tree hex) hs ho hm
      have hd : DeadT o.thread := by
        refine ⟨fun he => ?_, fun x hx => Nat.lt_of_le_of_lt (hle x (h2 x hx)) (h4 hm)⟩
        cases hp : p.1.prom with
        | nil => exact hp0 hp
        | cons x xs =>
          have := hkeep x (by rw [hp]; exact List.mem_cons_self)
          rw [he] at this; cases this
      exact absurd hq (deadT_threadNPn hP h hS' hd).1

/-- **N5, the key lemma.** -/
theorem tsoCertNoFresh (I : ISA) : TsoCertNoFresh I := by
  intro P hP tid n t mem hS hle ⟨t', mem', h, hp⟩
  exact tso_cut hP h hp hS hle

/-- The per-thread invariant of `tsoConsistent`: `P` and every promise in
memory. -/
def TsoInvAt (P : I.State → Prop) (c : Config I) : Prop :=
  ∀ (tid : Nat) (t : Thread I), c.threads[tid]? = some t → P t.st ∧ ∀ x ∈ t.prom, x ≤ c.mem.last

/-- A certifiable thread stays certifiable when memory grows (on TSO, under
`TsoCertInv`). -/
theorem certOkN_extend {P : I.State → Prop} (hP : TsoCertInv I P) {tid fuel : Nat} {u : Thread I}
    {mem mem' : Memory} (hS : P u.st) (hle : ∀ x ∈ u.prom, x ≤ mem.last) (hb : u.Bnd mem.last)
    (hp : mem.Prefix mem') (hc : CertOkN Arch.tso tid u mem fuel) : CertOkN Arch.tso tid u mem' fuel := by
  obtain ⟨t', hr, ht'⟩ := NACertG.replay (tsoCertNoFresh I P hP tid fuel u mem hS hle hc) hb hp
  exact ⟨t', mem', hr, ht'⟩

/-- One semantic step keeps the invariant and consistency. -/
theorem tsoConsistent_step {P : I.State → Prop} (hP : TsoCertInv I P) {fuel tid : Nat} {c c' : Config I}
    (hb : c.Bnd) (hI : TsoInvAt P c) (hC : ConsistentSem Arch.tso fuel c) (hs : StepSem Arch.tso fuel tid c c') :
    TsoInvAt P c' ∧ ConsistentSem Arch.tso fuel c' := by
  rcases hs with ⟨t, outs, o, ht, hs, ho, hc, rfl⟩ | ⟨t, w, ht, -, hc, rfl⟩
  · have hS := (hI tid t ht).1
    have hpre : c.mem.Prefix o.mem := (stepOne_dord _ hs ho).2.2.1
    have hl := hpre.last_le
    have hnt : ∀ tree, I.exec t.st = some tree → tree.NoNT Arch.tso :=
      fun tree hex => hP.noNT _ hS tree hex
    obtain ⟨-, h2, -, -⟩ := stepOne_tso hnt hs ho
    have hown : P o.thread.st ∧ ∀ x ∈ o.thread.prom, x ≤ o.mem.last :=
      ⟨hP.step hS hs ho,
        fun x hx => Nat.le_trans ((hI tid t ht).2 x (h2 x hx)) hl⟩
    refine ⟨fun j u hu => ?_, fun j u hu => ?_⟩
    · by_cases e : j = tid
      · subst e; rw [withThread_get_self ht] at hu; cases hu; exact hown
      · rw [withThread_get_ne ht e] at hu
        exact ⟨(hI j u hu).1, fun x hx => Nat.le_trans ((hI j u hu).2 x hx) hl⟩
    · by_cases e : j = tid
      · subst e; rw [withThread_get_self ht] at hu; cases hu; exact hc
      · rw [withThread_get_ne ht e] at hu
        exact certOkN_extend hP (hI j u hu).1 (hI j u hu).2 (hb j u hu) hpre (hC j u hu)
  · have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append _ _
    have hl : (c.mem.append w).1.last = c.mem.last + 1 := Memory.last_append _ _
    refine ⟨fun j u hu => ?_, fun j u hu => ?_⟩
    · by_cases e : j = tid
      · subst e; rw [withThread_get_self ht] at hu; cases hu
        refine ⟨(hI j t ht).1, fun x hx => ?_⟩
        show x ≤ (c.mem.append w).1.last
        rw [hl]
        rcases List.mem_append.mp hx with hx | hx
        · have := (hI j t ht).2 x hx; omega_t
        · rw [List.mem_singleton] at hx; rw [hx, Memory.append_time]; omega_t
      · rw [withThread_get_ne ht e] at hu
        exact ⟨(hI j u hu).1, fun x hx => by
          show x ≤ (c.mem.append w).1.last
          have := (hI j u hu).2 x hx; omega_t⟩
    · by_cases e : j = tid
      · subst e; rw [withThread_get_self ht] at hu; cases hu; exact hc
      · rw [withThread_get_ne ht e] at hu
        exact certOkN_extend hP (hI j u hu).1 (hI j u hu).2 (hb j u hu) hpre (hC j u hu)

/-- Along every semantic run, the invariant and consistency are kept. -/
theorem tsoConsistent_reach {P : I.State → Prop} (hP : TsoCertInv I P) {fuel : Nat} {c c' : Config I}
    (hr : ReachableSem Arch.tso fuel c c') (hb : c.Bnd) (hI : TsoInvAt P c) (hC : ConsistentSem Arch.tso fuel c) :
    TsoInvAt P c' ∧ ConsistentSem Arch.tso fuel c' := by
  induction hr with
  | refl => exact ⟨hI, hC⟩
  | step _ hs _ ih =>
    obtain ⟨hI', hC'⟩ := tsoConsistent_step hP hb hI hC hs
    exact ih (hb.semStep hs) hI' hC'

/-- **N5, the invariant**: on TSO, under `TsoCertInv`, every configuration
reachable on the semantic machine from a bounded, promise-free configuration
has every thread certifiable. -/
theorem tsoConsistent (I : ISA) : TsoConsistent I := by
  intro P fuel c0 c hP hb h0 hr
  refine (tsoConsistent_reach hP hr hb (fun j u hu => ⟨(h0 j u hu).1, fun x hx => ?_⟩) ?_).2
  · rw [(h0 j u hu).2] at hx; cases hx
  · intro j u hu
    exact ⟨u, c0.mem, .refl _ _, (h0 j u hu).2⟩

/-- **N5: no stuck configuration on TSO.** Under `TsoCertInv` (no
non-temporal store, at most one write per instruction), from a bounded,
promise-free configuration, no configuration reachable on the semantic
machine at any fuel is stuck, given `OkStepsPF` along the run. -/
theorem tsoNoStuck (I : ISA) : TsoNoStuck I := by
  intro P fuel c0 hP hb h0 hok
  exact noStuckFrom_of_consistent (fun c hr => tsoConsistent I P fuel c0 c hP hb h0 hr) hok

end Kraken.Promising.Live.NoStuck
