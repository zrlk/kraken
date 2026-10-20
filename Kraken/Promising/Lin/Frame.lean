/-
**The framed (c′) spec — fragment specs, the client
rely, the framing lemma, and the composition theorem** (ISA-neutral,
program-independent).

The goal: a push or pop fragment is verified
**once**, against a spec that mentions no client code, and the result
applies in **any** client program whose other steps respect a stated rely.
The earlier `treiber2` prototype stated its `Core` as a whole-program table indexed
by program position; here the invariant is split:

- the **structure part** `Struct` (`Lin/Spec.lean`): the `top` history, the
  per-node "frozen after publication" facts (carried by the lawfulness of
  committed messages), and the pending entries of `top` messages;
- the **per-thread part** of a thread inside fragment `i`: `J i`, the
  fragment's own internal invariant (existentially quantified in the
  fragment obligation `FragObl`; the client never sees it), together with
  ownership of an unpublished node (the arena of the layout);
- the **client's own state**: an abstract parameter `CI` over the
  configuration and the history, not a table indexed by program position.

All steps are on the **fuel-free semantic machine** (`InstrSemInf`,
`PromSemInf`, `StepSemInf`; `LiveSemInf.lean`), the lowering target. The
fuel-indexed (`StepSem A fuel`) and executable (`succs`) forms are
corollaries of the lifting (`RelLift.Obl.stepSem`, `Obl.reachSem`,
`Obl.reach_succs`, `Lin/Lift.lean`).

Contents:

- `Frag`: a code fragment with its calling convention (entry, inside, exit,
  argument and result registers, preserved state);
- `StackPre`/`StackPost`/`Landing`: the fragment's interface (pre: invoked
  with valid arguments; post: returned, its LP committed in the history,
  result in the result registers, a popped node acquired);
- `LinSpec L A F J`: **the fragment spec** — every step of a thread inside
  the fragment, from `Struct` and the other threads' lawful promises, is a
  `LinStep` (stutter / commit / empty pop) that keeps `Struct`, keeps the
  calling convention's preserved state, writes only `top` and the thread's
  own node words, and either stays inside (`J`) or exits with `StackPost`;
  `J` is stable under every other thread's move (`EnvMove`) and under the
  thread's own promises. `FragObl L A F := ∃ J, LinSpec L A F J`.
- `ClientRely L A F CI`: **the client rely** — a step of a thread outside
  every fragment commits no `top` message and no write to a word of a
  published node or of a node owned by another thread, and makes no new
  promise (`CommitOK`); it keeps `CI`, and if it lands inside a fragment, it
  lands at the entry with valid arguments; `CI` survives fragment steps
  (seen only through their interface) and promise steps.
- `struct_client`/`frame_client`: **the framing lemma** — a step satisfying
  `CommitOK` keeps `Struct` and every other thread's `J`, with the abstract
  state unchanged (a stutter);
- `struct_prom`: `Struct` survives every promise step with its pinned
  pending entry (no rely needed: lawfulness of the promise comes from its
  certification, `RelLift.run_pend`);
- `linObl_of_frag_rely`: **the composition theorem** — fragment specs for
  every fragment plus `ClientRely` give `RelLift.Obl` for the lifting
  `linLift`, hence (`Obl.step`) the per-step abstract relation at every
  reachable configuration, for any client program.

**Promises and client code.** A certifying run of a thread may run from a
fragment into client code and back (a promise made in client code may be
fulfilled in a later fragment, and conversely). This is why every
obligation here is quantified over all configurations satisfying the
invariant, never over reachable ones: `run_pend` replays the certifying
run through the same obligations.
-/
import Kraken.Promising.Lin.Spec
import Kraken.Promising.Lin.Lift

namespace Kraken.Promising.Lin

open Kraken Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Inf

variable {I : ISA}

/-! ## Fragments and their interface -/

/-- **A code fragment with its calling convention**, over the ISA state. -/
structure Frag (I : ISA) where
  /-- At the entry (the call target). -/
  entry : I.State → Prop
  /-- In the fragment's code (the entry included, the exits excluded). -/
  inside : I.State → Prop
  /-- At an exit (the return target). -/
  exit : I.State → Prop
  /-- The invocation the argument registers denote. -/
  arg : I.State → Call → Prop
  /-- The result registers hold the operation's result. -/
  res : I.State → Op → Prop
  /-- What one fragment step preserves (callee-saved registers, link,
  private memory, …): the complement of the clobbers. -/
  keeps : I.State → I.State → Prop

/-- `Lin.Φ` on the abstract state. -/
abbrev PhiA (L : StackLayout) : Nat → Time → Memory → AS → Prop := fun w q m a => PhiH L w q m a.H

/-- **The footprint of a fragment step of `w`**: every new message is to
`top` or to a word of a node of `w`'s arena. -/
def Foot (L : StackLayout) (w : Nat) (m m' : Memory) : Prop :=
  ∀ q msg, m.last < q → m'.get? q = some msg → msg.loc = L.top ∨ ∃ n, L.arena w n ∧ L.words n msg.loc

/-- **Valid arguments** of an invocation by `w`: a push is of a nonzero node
of `w`'s arena that `w` has not committed a push of (a pending own push, a
promise made before the call, is allowed). -/
def ArgOK (L : StackLayout) (w : Nat) : Call → List PEnt → Prop
  | .push n, H => L.arena w n ∧ n ≠ 0 ∧ ∀ e ∈ H, e.tid = w → e.op = .push n → e.pend = true
  | .pop, _ => True

/-- **The fragment's precondition** at its entry: invoked (the abstract
state records the call and the coherence view of `top` at the call) with
valid arguments. -/
def StackPre (L : StackLayout) (F : Frag I) (w : Nat) (t : Thread I) (a : AS) : Prop :=
  ∃ call, F.arg t.st call ∧ a.th w = .run call (t.views.getCoh L.top) ∧ ArgOK L w call a.H

/-- **The fragment's postcondition** at its exit: returned, its LP committed
in the history, the result in the result registers, and a popped node
acquired (`AcqOf`). -/
def StackPost (F : Frag I) (w : Nat) (t : Thread I) (a : AS) : Prop :=
  ∃ op k0 p, a.th w = .ret op k0 p ∧ (⟨p, w, op, false⟩ : PEnt) ∈ a.H ∧ F.res t.st op ∧
    ∀ n, op = .pop (some n) → AcqOf a.H t.views n

/-- **What a caller guarantees when control lands in a fragment**: at the
entry, with valid arguments. -/
def Landing (L : StackLayout) (F : Frag I) (w : Nat) (t : Thread I) (H : List PEnt) : Prop :=
  F.entry t.st ∧ ∃ call, F.arg t.st call ∧ ArgOK L w call H

/-- A history move of thread `v` (what any step of `v` does to the history):
none, an entry of `v` appended above `|M|`, `v`'s own pending entry tagged,
or a read-only entry of `v` inserted. -/
def HMove (v : Nat) (last : Time) (H H' : List PEnt) : Prop :=
  H' = H ∨ (∃ q op b, last < q ∧ H' = H ++ [⟨.wr q, v, op, b⟩]) ∨
  (∃ H1 H2 q op, H = H1 ++ ⟨.wr q, v, op, true⟩ :: H2 ∧ H' = H1 ++ ⟨.wr q, v, op, false⟩ :: H2) ∨
  (∃ r, H' = insertRdP H ⟨.rd r, v, .pop none, false⟩)

/-- **A move of thread `v`, seen from another thread**: memory extended,
other threads and their abstract states unchanged, the history moved by `v`
only, `Struct` before and after, and the other threads' promises lawful
before and after. Fragment invariants must be stable under it. -/
def EnvMove (L : StackLayout) (v : Nat) (c c' : Config I) (a a' : AS) : Prop :=
  c.mem.Prefix c'.mem ∧ (∀ j, j ≠ v → c'.threads[j]? = c.threads[j]?) ∧ OK v a a' ∧
    HMove v c.mem.last a.H a'.H ∧ Struct L c a.H ∧ Struct L c' a'.H ∧
    ∀ j, j ≠ v → PendOK (PhiA L) j c a ∧ PendOK (PhiA L) j c' a'

/-! ## The fragment spec -/

/-- **The fragment spec (c′), framed**: fragment `F` with internal
per-thread invariant `J`, on the fuel-free semantic machine. It mentions no
client code.

- `enter`: the precondition at the entry gives `J`;
- `step`: every instruction step of a thread inside `F`, from `Struct` and
  the **other** threads' lawful promises, is a `LinStep`, keeps `Struct`,
  keeps the preserved state (`keeps`), writes only `top` and own node words
  (`Foot`), stays inside with `J` or exits with `StackPost`, makes every
  promise it fulfils lawful, and makes no new promise;
- `stable`: `J` survives every other thread's move;
- `prom`: `J` survives the thread's own promise steps. -/
structure LinSpec (L : StackLayout) (A : Arch) (F : Frag I) (J : Nat → Thread I → Memory → AS → Prop) : Prop where
  enter : ∀ w t m a, F.entry t.st → StackPre L F w t a → J w t m a
  step : ∀ w c c' a t, Struct L c a.H → (∀ j, j ≠ w → PendOK (PhiA L) j c a) → c.threads[w]? = some t →
    F.inside t.st → J w t c.mem a → InstrSemInf A w c c' →
    ∃ a' t', c'.threads[w]? = some t' ∧ Struct L c' a'.H ∧ LinStep L w c c' a a' ∧ F.keeps t.st t'.st ∧
      Foot L w c.mem c'.mem ∧ (F.inside t'.st → J w t' c'.mem a') ∧
      (¬ F.inside t'.st → F.exit t'.st ∧ StackPost F w t' a') ∧
      (∀ p ∈ t.prom, p ∉ t'.prom → PhiH L w p c'.mem a'.H) ∧ (∀ p ∈ t'.prom, p ∈ t.prom)
  stable : ∀ v w c c' a a' t, v ≠ w → EnvMove L v c c' a a' → c.threads[w]? = some t →
    J w t c.mem a → J w t c'.mem a'
  prom : ∀ w c c' a a' t t', PromSemInf A w c c' → PStepL L w c c' a a' → Struct L c a.H → Struct L c' a'.H →
    c.threads[w]? = some t → c'.threads[w]? = some t' → J w t c.mem a → J w t' c'.mem a'

/-- **The fragment obligation**: some internal invariant makes `F` meet its
spec. It is about **node identities**: the payload is client data, so "a pop
returns the value pushed" is not part of it. A client wanting that adds a
frozen-payload fact (the payload word written once, by the owner, below the
push: a `ClientWriteOK`-style clause on payload words), a certification lemma,
and a release-order fact about its own pending promises, plus per-ISA instances. -/
def FragObl (L : StackLayout) (A : Arch) (F : Frag I) : Prop := ∃ J, LinSpec L A F J

/-! ## The client rely -/

/-- A message committed by a client step of `w` at `q`: of `w`, not to
`top`, and, if to a node word, to a node of `w`'s arena not pushed below
`q` (owned and unpublished). -/
def ClientWriteOK (L : StackLayout) (w : Nat) (q : Time) (msg : Msg) (H : List PEnt) : Prop :=
  msg.tid = w ∧ msg.loc ≠ L.top ∧ ∀ n, L.words n msg.loc → L.arena w n ∧ ¬ Pushed n q (wrUpTo q H)

/-- **The rely condition on one client step** of `w` (thread `t` to `t'`,
configuration `c` to `c'`): no new promise; no `top` promise fulfilled;
every message the step commits (fresh, or a fulfilled promise) is a
`ClientWriteOK` write. So the step writes neither `top` nor any word of a
published node or of a node owned by another thread. (Client **promise**
steps need no rely: a promise's lawfulness comes from its certification.)
"No new promise" constrains instruction steps only (`PromSemInf` steps are
free) and is what the semantics gives: `stepOne_promSub` with `FwdOk`, which
every reachable configuration has (`Config.Wf`); the per-instruction spec
lemmas (`spec_store_p`, …) give it without `FwdOk`. -/
def CommitOK (L : StackLayout) (w : Nat) (c c' : Config I) (t t' : Thread I) (H : List PEnt) : Prop :=
  (∀ p ∈ t'.prom, p ∈ t.prom) ∧
  (∀ p ∈ t.prom, ∀ msg, c.mem.get? p = some msg → msg.loc = L.top → p ∈ t'.prom) ∧
  ∀ q msg, c'.mem.get? q = some msg → (c.mem.last < q ∨ (q ∈ t.prom ∧ q ∉ t'.prom)) → ClientWriteOK L w q msg H

/-- **The client rely** for fragments `F` and client invariant `CI` (over
the configuration and the history; the client's own state is abstract):

- `step`: an instruction step of a thread outside every fragment satisfies
  `CommitOK`, keeps `CI`, and lands in a fragment only at its entry with
  valid arguments;
- `frag`: `CI` survives every fragment step, seen only through the
  fragment's interface (its `LinStep`, `keeps`, `Foot`, exit and
  `StackPost`), and a fragment exit that lands in another fragment lands
  at its entry with valid arguments;
- `prom`: `CI` survives every promise step. -/
structure ClientRely (L : StackLayout) (A : Arch) {ι : Type} (F : ι → Frag I) (CI : Config I → List PEnt → Prop) :
    Prop where
  step : ∀ w c c' (a : AS) t, Struct L c a.H → (∀ j, j ≠ w → PendOK (PhiA L) j c a) → CI c a.H →
    c.threads[w]? = some t → (∀ i, ¬ (F i).inside t.st) → InstrSemInf A w c c' →
    ∃ t', c'.threads[w]? = some t' ∧ CommitOK L w c c' t t' a.H ∧ CI c' a.H ∧
      ∀ i, (F i).inside t'.st → Landing L (F i) w t' a.H
  frag : ∀ i v c c' (a a' : AS) t t', Struct L c a.H → Struct L c' a'.H → CI c a.H → c.threads[v]? = some t →
    (F i).inside t.st → InstrSemInf A v c c' → c'.threads[v]? = some t' → LinStep L v c c' a a' →
    (F i).keeps t.st t'.st → Foot L v c.mem c'.mem →
    (¬ (F i).inside t'.st → (F i).exit t'.st ∧ StackPost (F i) v t' a') →
    CI c' a'.H ∧ (¬ (F i).inside t'.st → ∀ k, (F k).inside t'.st → Landing L (F k) v t' a'.H)
  prom : ∀ v c c' (a a' : AS), Struct L c a.H → PromSemInf A v c c' → PStepL L v c c' a a' → CI c a.H →
    CI c' a'.H

/-! ## The framing lemma -/

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, Memory.last] at *); omega))

theorem get?_some_le {m : Memory} {q : Time} {msg : Msg} (h : m.get? q = some msg) : 0 < q ∧ q ≤ m.last := by
  unfold Memory.get? at h
  split at h
  · cases h
  · refine ⟨by omega_t, Nat.le_of_not_lt fun hlt => ?_⟩
    rw [Array.getElem?_eq_none (by unfold Memory.last at hlt; omega_t)] at h
    cases h

theorem get?_of_bnd {m : Memory} {q : Time} (h0 : 0 < q) (h1 : q ≤ m.last) : ∃ msg, m.get? q = some msg := by
  unfold Memory.get?
  rw [ite_eq_right (by omega_t)]
  exact ⟨_, Array.getElem?_eq_getElem (by unfold Memory.last at h1; omega_t)⟩

/-- What an instruction step changes: thread `w` only, memory extended. -/
theorem instrSemInf_facts {A : Arch} {w : Nat} {c c' : Config I} {t : Thread I} (hI : InstrSemInf A w c c')
    (ht : c.threads[w]? = some t) :
    ∃ t', c'.threads[w]? = some t' ∧ (∀ j, j ≠ w → c'.threads[j]? = c.threads[j]?) ∧ c.mem.Prefix c'.mem := by
  obtain ⟨t0, outs, o, -, hstep, ho, -, rfl⟩ := hI
  exact ⟨o.thread, withThread_get_self ht, fun j hj => withThread_get_ne ht hj, Memory.Prefix.stepOne hstep ho⟩

/-- What a promise step changes: thread `w`'s promises, one message appended. -/
theorem promSemInf_facts {A : Arch} {w : Nat} {c c' : Config I} (hP : PromSemInf A w c c') :
    ∃ t msg, c.threads[w]? = some t ∧ msg.tid = w ∧ c'.threads[w]? = some (promThread t c.mem msg) ∧
      (∀ j, j ≠ w → c'.threads[j]? = c.threads[j]?) ∧ c'.mem = (c.mem.append msg).1 := by
  obtain ⟨t, msg, ht, hw, -, rfl⟩ := hP
  exact ⟨t, msg, ht, hw, withThread_get_self ht, fun j hj => withThread_get_ne ht hj, rfl⟩

theorem phiH_of_cw {L : StackLayout} {w : Nat} {q : Time} {m : Memory} {msg : Msg} {H : List PEnt}
    (hg : m.get? q = some msg) (h : ClientWriteOK L w q msg H) : PhiH L w q m H :=
  ⟨msg, by rw [cut_get? (Nat.le_refl q) (get?_some_le hg).2]; exact hg, h.1, fun e => absurd e h.2.1,
    fun _ => h.2.2⟩

theorem pendOK_mono {L : StackLayout} {j : Nat} {c c' : Config I} {a a' : AS}
    (hth : c'.threads[j]? = c.threads[j]?) (hm : c.mem.Prefix c'.mem) (hag : ∀ p, p ≤ c.mem.last → Agree p a a')
    (h : PendOK (PhiA L) j c a) : PendOK (PhiA L) j c' a' := by
  intro t ht p hp
  rw [hth] at ht
  obtain ⟨hle, hΦ⟩ := h t ht p hp
  exact ⟨Nat.le_trans hle hm.last_le, (phiH_prefix L j p hle hm (hag p hle)).mp hΦ⟩

/-- **The framing lemma, structure part**: an instruction step of `w`
satisfying `CommitOK` keeps `Struct` with the history unchanged. -/
theorem struct_client {L : StackLayout} {A : Arch} {w : Nat} {c c' : Config I} {H : List PEnt} {t t' : Thread I}
    (hS : Struct L c H) (hI : InstrSemInf A w c c') (ht : c.threads[w]? = some t)
    (ht' : c'.threads[w]? = some t') (hR : CommitOK L w c c' t t' H) : Struct L c' H := by
  obtain ⟨t1, ht1, hthj, hpre⟩ := instrSemInf_facts hI ht
  rw [ht'] at ht1; cases ht1
  obtain ⟨hR1, hR2, hR3⟩ := hR
  have hO : ∀ j q, j ≠ w → (Outst c' j q ↔ Outst c j q) := fun j q hj => by unfold Outst; rw [hthj j hj]
  have hOw : ∀ q, Outst c' w q ↔ q ∈ t'.prom := fun q => by unfold Outst; rw [ht']; simp
  have hOw0 : ∀ q, Outst c w q ↔ q ∈ t.prom := fun q => by unfold Outst; rw [ht]; simp
  refine ⟨fun j tj htj p hp => ?_, fun e he q hq => ?_, fun q msg hg hl => ?_, fun e he q hq => ?_, hS.sorted,
    fun q msg hg hno => ?_, fun e he r hr => ?_⟩
  · by_cases hj : j = w
    · subst hj; rw [ht'] at htj; cases htj
      obtain ⟨h0, h1⟩ := hS.bnd j t ht p (hR1 p hp); exact ⟨h0, Nat.le_trans h1 hpre.last_le⟩
    · rw [hthj j hj] at htj
      obtain ⟨h0, h1⟩ := hS.bnd j tj htj p hp; exact ⟨h0, Nat.le_trans h1 hpre.last_le⟩
  · obtain ⟨msg, hg, h1, h2⟩ := hS.topE e he q hq
    exact ⟨msg, by rw [hpre.get? (get?_some_le hg).2]; exact hg, h1, h2⟩
  · by_cases hq : q ≤ c.mem.last
    · rw [hpre.get? hq] at hg; exact hS.topM q msg hg hl
    · exact absurd hl (hR3 q msg hg (.inl (Nat.lt_of_not_le hq))).2.1
  · rw [hS.pend e he q hq]
    by_cases hj : e.tid = w
    · rw [hj, hOw, hOw0]
      obtain ⟨msg, hg, hl, -⟩ := hS.topE e he q hq
      exact ⟨fun h => hR2 q h msg hg hl, hR1 q⟩
    · exact (hO _ q hj).symm
  · by_cases hq : q ≤ c.mem.last
    · have hg0 : c.mem.get? q = some msg := by rw [← hpre.get? hq]; exact hg
      by_cases ho : Outst c msg.tid q
      · by_cases hj : msg.tid = w
        · rw [hj, hOw] at hno; rw [hj, hOw0] at ho
          have hc := hR3 q msg hg (.inr ⟨ho, hno⟩)
          rw [hc.1]; exact phiH_of_cw hg hc
        · exact absurd ((hO _ q hj).mpr ho) hno
      · exact (phiH_prefix L _ q hq hpre rfl).mp (hS.committed q msg hg0 ho)
    · have hc := hR3 q msg hg (.inl (Nat.lt_of_not_le hq))
      rw [hc.1]; exact phiH_of_cw hg hc
  · obtain ⟨h1, h2, h3, h4⟩ := hS.rd e he r hr
    exact ⟨h1, h2, Nat.le_trans h3 hpre.last_le, h4⟩

/-- **The framing lemma**: an instruction step of `w` satisfying `CommitOK`
is a stutter for everyone else: `Struct` is kept with the abstract state
unchanged, and the step is an `EnvMove` (so every other thread's fragment
invariant survives, `frame_client_J`). -/
theorem frame_client {L : StackLayout} {A : Arch} {w : Nat} {c c' : Config I} {a : AS} {t t' : Thread I}
    (hS : Struct L c a.H) (hP : ∀ j, j ≠ w → PendOK (PhiA L) j c a) (hI : InstrSemInf A w c c')
    (ht : c.threads[w]? = some t) (ht' : c'.threads[w]? = some t') (hR : CommitOK L w c c' t t' a.H) :
    Struct L c' a.H ∧ EnvMove L w c c' a a := by
  have hS' := struct_client hS hI ht ht' hR
  obtain ⟨-, -, hthj, hpre⟩ := instrSemInf_facts hI ht
  exact ⟨hS', hpre, hthj, fun _ _ => rfl, .inl rfl, hS, hS',
    fun j hj => ⟨hP j hj, pendOK_mono (hthj j hj) hpre (fun _ _ => rfl) (hP j hj)⟩⟩

/-- The framing lemma, per-thread part: every other thread's fragment
invariant survives a `CommitOK` step. -/
theorem frame_client_J {L : StackLayout} {A : Arch} {F : Frag I} {J : Nat → Thread I → Memory → AS → Prop}
    (hJ : LinSpec L A F J) {w v : Nat} {c c' : Config I} {a : AS} {t t' tv : Thread I}
    (hS : Struct L c a.H) (hP : ∀ j, j ≠ w → PendOK (PhiA L) j c a) (hI : InstrSemInf A w c c')
    (ht : c.threads[w]? = some t) (ht' : c'.threads[w]? = some t') (hR : CommitOK L w c c' t t' a.H)
    (hv : v ≠ w) (htv : c.threads[v]? = some tv) (hJv : J v tv c.mem a) : J v tv c'.mem a :=
  hJ.stable w v c c' a a tv (Ne.symm hv) (frame_client hS hP hI ht ht' hR).2 htv hJv

/-- **`Struct` survives every promise step** with its pinned pending entry. -/
theorem struct_prom {L : StackLayout} {A : Arch} {w : Nat} {c c' : Config I} {a a' : AS}
    (hS : Struct L c a.H) (hP : PromSemInf A w c c') (hA : PStepL L w c c' a a') : Struct L c' a'.H := by
  obtain ⟨t, msg, ht, hw, htw, hthj, hmem⟩ := promSemInf_facts hP
  obtain ⟨-, msg', hg', hH⟩ := hA
  rw [hmem, Memory.get?_append_last] at hg'; cases hg'
  have hpre : c.mem.Prefix c'.mem := hmem ▸ Memory.Prefix.append c.mem msg
  have hlast : c'.mem.last = c.mem.last + 1 := by rw [hmem, Memory.last_append]
  have hnew : c'.mem.get? (c.mem.last + 1) = some msg := by rw [hmem, Memory.get?_append_last]
  have hHle : ∀ e ∈ a.H, e.pos.ts ≤ c.mem.last := by
    intro e he
    cases hp : e.pos with
    | wr q => obtain ⟨m0, hg, -⟩ := hS.topE e he q hp; exact (get?_some_le hg).2
    | rd r => exact (hS.rd e he r hp).2.2.1
  have hag : ∀ p, p ≤ c.mem.last → wrUpTo p a.H = wrUpTo p a'.H := by
    intro p hp; rw [hH]; unfold pAppend; split
    · exact (wrUpTo_append_above _ _ _ _ (Nat.lt_succ_of_le hp)).symm
    · rfl
  have hO : ∀ j q, j ≠ w → (Outst c' j q ↔ Outst c j q) := fun j q hj => by unfold Outst; rw [hthj j hj]
  have hOw : ∀ q, Outst c' w q ↔ q ∈ t.prom ∨ q = c.mem.last + 1 := fun q => by
    unfold Outst; rw [htw]; simp [promThread, Memory.append_time]
  have hOw0 : ∀ q, Outst c w q ↔ q ∈ t.prom := fun q => by unfold Outst; rw [ht]; simp
  have hmemH : ∀ e, e ∈ a'.H ↔ e ∈ a.H ∨ (msg.loc = L.top ∧
      e = ⟨.wr (c.mem.last + 1), w, pinOf (wrUpTo (c.mem.last + 1) a.H) (c.mem.last + 1)
        (BitVec.setWidth 64 msg.val), true⟩) := by
    intro e; rw [hH]; unfold pAppend; split <;> simp_all
  -- a timestamp at most `|M| + 1` with a message, above `|M|`, is the new one
  have hq1 : ∀ q m0, c'.mem.get? q = some m0 → ¬ q ≤ c.mem.last → q = c.mem.last + 1 := fun q m0 hg hq => by
    have := (get?_some_le hg).2; omega_t
  refine ⟨fun j tj htj p hp => ?_, fun e he q hq => ?_, fun q m0 hg hl => ?_, fun e he q hq => ?_, ?_,
    fun q m0 hg hno => ?_, fun e he r hr => ?_⟩
  · by_cases hj : j = w
    · subst hj; rw [htw] at htj; cases htj
      simp only [Memory.append_time, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · obtain ⟨h0, h1⟩ := hS.bnd j t ht p hp; exact ⟨h0, by omega_t⟩
      · exact ⟨Nat.succ_pos _, by omega_t⟩
    · rw [hthj j hj] at htj
      obtain ⟨h0, h1⟩ := hS.bnd j tj htj p hp; exact ⟨h0, Nat.le_trans h1 hpre.last_le⟩
  · rcases (hmemH e).mp he with he | ⟨hl, rfl⟩
    · obtain ⟨m0, hg, h1, h2⟩ := hS.topE e he q hq
      exact ⟨m0, by rw [hpre.get? (get?_some_le hg).2]; exact hg, h1, h2⟩
    · cases hq; exact ⟨msg, hnew, hl, hw⟩
  · by_cases hq : q ≤ c.mem.last
    · rw [hpre.get? hq] at hg
      obtain ⟨e, he, h1, h2⟩ := hS.topM q m0 hg hl
      exact ⟨e, (hmemH e).mpr (.inl he), h1, h2⟩
    · obtain rfl := hq1 q m0 hg hq
      rw [hnew] at hg; cases hg
      exact ⟨_, (hmemH _).mpr (.inr ⟨hl, rfl⟩), rfl, hw.symm⟩
  · rcases (hmemH e).mp he with he | ⟨-, rfl⟩
    · have hle : q ≤ c.mem.last := by have := hHle e he; rw [hq] at this; exact this
      rw [hS.pend e he q hq]
      by_cases hj : e.tid = w
      · rw [hj, hOw, hOw0]; exact ⟨.inl, fun h => h.elim id (fun h => by omega_t)⟩
      · exact (hO _ q hj).symm
    · cases hq; exact ⟨fun _ => (hOw _).mpr (.inr rfl), fun _ => rfl⟩
  · rw [hH]; unfold pAppend; split
    · refine List.pairwise_append.mpr ⟨hS.sorted, List.pairwise_singleton _ _, fun e he e' he' => ?_⟩
      rw [List.mem_singleton] at he'; subst he'
      have := hHle e he
      left
      cases hp : e.pos <;> rw [hp] at this <;> simp only [Pos.lt, Pos.ts] at this ⊢ <;> omega_t
    · exact hS.sorted
  · by_cases hq : q ≤ c.mem.last
    · have hg0 : c.mem.get? q = some m0 := by rw [← hpre.get? hq]; exact hg
      have ho : ¬ Outst c m0.tid q := fun ho => hno <| by
        by_cases hj : m0.tid = w
        · rw [hj] at ho ⊢; exact (hOw q).mpr (.inl ((hOw0 q).mp ho))
        · exact (hO _ q hj).mpr ho
      exact (phiH_prefix L _ q hq hpre (hag q hq)).mp (hS.committed q m0 hg0 ho)
    · obtain rfl := hq1 q m0 hg hq
      rw [hnew] at hg; cases hg
      exact absurd ((hOw _).mpr (.inr rfl)) (hw ▸ hno)
  · rcases (hmemH e).mp he with he | ⟨-, rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hS.rd e he r hr
      exact ⟨h1, h2, Nat.le_trans h3 hpre.last_le, by rw [← hag r h3]; exact h4⟩
    · cases hr

/-! ## The composition theorem -/

/-- **The invocation at a call site** (ghost): a thread that is not in the
middle of an operation and lands at a fragment's entry records the call its
argument registers denote and its coherence view of `top`. -/
def InvokeAt (L : StackLayout) {ι : Type} (F : ι → Frag I) (w : Nat) (c' : Config I) (a1 a' : AS) : Prop :=
  a'.H = a1.H ∧ OK w a1 a' ∧ Idle a1 w ∧ ∃ t' i call, c'.threads[w]? = some t' ∧ (F i).entry t'.st ∧
    (F i).arg t'.st call ∧ a'.th w = .run call (t'.views.getCoh L.top)

/-- **The abstract step of an instruction step** of the composed program: a
`LinStep` (a stutter for client steps), possibly followed by an invocation
at the landing site. -/
def AStepL (L : StackLayout) {ι : Type} (F : ι → Frag I) (w : Nat) (c c' : Config I) (a a' : AS) : Prop :=
  ∃ a1, LinStep L w c c' a a1 ∧ (a' = a1 ∨ InvokeAt L F w c' a1 a')

/-- **The composed invariant's core**: the structure part, the client
invariant, and per thread: outside every fragment, not in the middle of an
operation; inside fragment `i`, its invariant `J i`. -/
def LinCore (L : StackLayout) {ι : Type} (F : ι → Frag I) (J : ι → Nat → Thread I → Memory → AS → Prop)
    (CI : Config I → List PEnt → Prop) (c : Config I) (a : AS) : Prop :=
  Struct L c a.H ∧ CI c a.H ∧ ∀ w t, c.threads[w]? = some t →
    ((∀ i, ¬ (F i).inside t.st) → Idle a w) ∧ ∀ i, (F i).inside t.st → J i w t c.mem a

/-- **The lifting of a composed program** (fragments `F` with invariants `J`,
client invariant `CI`). -/
def linLift (L : StackLayout) {ι : Type} (F : ι → Frag I) (J : ι → Nat → Thread I → Memory → AS → Prop)
    (CI : Config I → List PEnt → Prop) : RelLift I AS where
  Core := LinCore L F J CI
  Φ := PhiA L
  AStep := AStepL L F
  PStep := PStepL L
  Agree := Agree

/-- A `LinStep` of `w` moves no other thread's abstract state. -/
theorem linStep_ok {L : StackLayout} {w : Nat} {c c' : Config I} {a a' : AS} (h : LinStep L w c c' a a') :
    OK w a a' := by
  rcases h with rfl | ⟨h, -⟩ | ⟨h, -⟩
  · exact fun _ _ => rfl
  · exact h
  · exact h

/-- A `LinStep` of `w` is a history move of `w`. -/
theorem linStep_hmove {L : StackLayout} {w : Nat} {c c' : Config I} {a a' : AS} (h : LinStep L w c c' a a') :
    HMove w c.mem.last a.H a'.H := by
  rcases h with rfl | ⟨-, op, -, q, -, -, -, -, -, ⟨hlt, hH⟩ | ⟨H1, H2, h1, h2⟩⟩ | ⟨-, -, r, -, -, -, hH⟩
  · exact .inl rfl
  · exact .inr (.inl ⟨q, op, false, hlt, hH⟩)
  · exact .inr (.inr (.inl ⟨H1, H2, q, op, h1, h2⟩))
  · exact .inr (.inr (.inr ⟨r, hH⟩))

/-- A promise step's history change (`pAppend`) is a history move. -/
theorem pStep_hmove {L : StackLayout} {w : Nat} {c c' : Config I} {a a' : AS} (h : PStepL L w c c' a a') :
    HMove w c.mem.last a.H a'.H := by
  obtain ⟨-, msg, -, hH⟩ := h
  rw [hH]; unfold pAppend; split
  · exact .inr (.inl ⟨_, _, true, Nat.lt_succ_self _, rfl⟩)
  · exact .inl rfl

/-- The end of a composed step: from `w`'s status after the step (outside
and idle; inside with its invariant; or just landed at an entry, idle), the
others' status, `Struct` and `CI`, the core holds, after the ghost
invocation if `w` just landed. -/
theorem core_finish {L : StackLayout} {A : Arch} {ι : Type} {F : ι → Frag I}
    {J : ι → Nat → Thread I → Memory → AS → Prop} {CI : Config I → List PEnt → Prop}
    (hF : ∀ i, LinSpec L A (F i) (J i)) (hdisj : ∀ i k st, (F i).inside st → (F k).inside st → i = k)
    {w : Nat} {c' : Config I} {a1 : AS} {t' : Thread I} (hS' : Struct L c' a1.H) (hCI : CI c' a1.H)
    (hP' : ∀ j, j ≠ w → PendOK (PhiA L) j c' a1) (ht' : c'.threads[w]? = some t')
    (hoth : ∀ j tj, j ≠ w → c'.threads[j]? = some tj →
      ((∀ i, ¬ (F i).inside tj.st) → Idle a1 j) ∧ ∀ i, (F i).inside tj.st → J i j tj c'.mem a1)
    (hw : ((∀ i, ¬ (F i).inside t'.st) ∧ Idle a1 w) ∨ (∃ i, (F i).inside t'.st ∧ J i w t' c'.mem a1) ∨
      (∃ i, (F i).inside t'.st ∧ Landing L (F i) w t' a1.H ∧ Idle a1 w)) :
    ∃ a', LinCore L F J CI c' a' ∧ (a' = a1 ∨ InvokeAt L F w c' a1 a') ∧ a'.H = a1.H := by
  rcases hw with ⟨hout, hid⟩ | ⟨i, hin, hJ⟩ | ⟨i, hin, ⟨hent, call, harg, hok⟩, hid⟩
  · refine ⟨a1, ⟨hS', hCI, fun j tj htj => ?_⟩, .inl rfl, rfl⟩
    by_cases hj : j = w
    · subst hj; rw [ht'] at htj; cases htj; exact ⟨fun _ => hid, fun i h => absurd h (hout i)⟩
    · exact hoth j tj hj htj
  · refine ⟨a1, ⟨hS', hCI, fun j tj htj => ?_⟩, .inl rfl, rfl⟩
    by_cases hj : j = w
    · subst hj; rw [ht'] at htj; cases htj
      exact ⟨fun h => absurd hin (h i), fun k hk => by obtain rfl := hdisj k i _ hk hin; exact hJ⟩
    · exact hoth j tj hj htj
  · let a' : AS := { H := a1.H, th := fun j => if j = w then .run call (t'.views.getCoh L.top) else a1.th j }
    have hok' : OK w a1 a' := fun j hj => by simp [a', hj]
    have hE : EnvMove L w c' c' a1 a' :=
      ⟨Memory.Prefix.refl _, fun _ _ => rfl, hok', .inl rfl, hS', hS', fun j hj => ⟨hP' j hj, hP' j hj⟩⟩
    have hJw : J i w t' c'.mem a' := (hF i).enter w t' c'.mem a' hent ⟨call, harg, by simp [a'], hok⟩
    refine ⟨a', ⟨hS', hCI, fun j tj htj => ?_⟩, .inr ⟨rfl, hok', hid, t', i, call, ht', hent, harg, by simp [a']⟩, rfl⟩
    by_cases hj : j = w
    · subst hj; rw [ht'] at htj; cases htj
      exact ⟨fun h => absurd hin (h i), fun k hk => by obtain rfl := hdisj k i _ hk hin; exact hJw⟩
    · obtain ⟨h1, h2⟩ := hoth j tj hj htj
      refine ⟨fun h => ?_, fun k hk => (hF k).stable w j c' c' a1 a' tj (Ne.symm hj) hE htj (h2 k hk)⟩
      have := h1 h; unfold Idle at this ⊢; rw [hok' j hj]; exact this

/-- **The composition theorem**: fragment specs for every fragment, disjoint
fragments, and the client rely give the lifting's obligations on the
fuel-free semantic machine, for **any** client program (the client enters
only through `ClientRely`). With `RelLift.Obl.step`/`Obl.reach`, the
composed invariant `(linLift L F J CI).Inv` holds at every configuration
reachable from one satisfying it, with an `AStepL` or `PStepL` per step. -/
theorem linObl_of_frag_rely {L : StackLayout} {A : Arch} {ι : Type} {F : ι → Frag I}
    {J : ι → Nat → Thread I → Memory → AS → Prop} {CI : Config I → List PEnt → Prop}
    (hF : ∀ i, LinSpec L A (F i) (J i)) (hdisj : ∀ i k st, (F i).inside st → (F k).inside st → i = k)
    (hC : ClientRely L A F CI) : (linLift L F J CI).Obl A := by
  refine ⟨fun w c c' a hinv hI => ?_, fun w c c' a hinv hP => ?_,
    fun w p m m' a a' hp hm hag => phiH_prefix L w p hp hm hag, fun w c c' a a' h p hp => ?_,
    fun w c c' a a' h p hp => agree_pStep h p hp⟩
  · obtain ⟨⟨hS, hCI, hth⟩, hP⟩ := hinv
    obtain ⟨t, -, -, ht, -⟩ := id hI
    obtain ⟨-, -, hthj, hpre⟩ := instrSemInf_facts hI ht
    -- the others, after an `EnvMove` of `w`
    have hoth : ∀ a1, EnvMove L w c c' a a1 → ∀ j tj, j ≠ w → c'.threads[j]? = some tj →
        ((∀ i, ¬ (F i).inside tj.st) → Idle a1 j) ∧ ∀ i, (F i).inside tj.st → J i j tj c'.mem a1 := by
      intro a1 hE j tj hj htj
      rw [hthj j hj] at htj
      obtain ⟨h1, h2⟩ := hth j tj htj
      refine ⟨fun h => ?_, fun k hk => (hF k).stable w j c c' a a1 tj (Ne.symm hj) hE htj (h2 k hk)⟩
      have := h1 h; unfold Idle at this ⊢; rw [hE.2.2.1 j hj]; exact this
    by_cases hin : ∃ i, (F i).inside t.st
    · obtain ⟨i, hin⟩ := hin
      obtain ⟨a1, t', ht', hS', hLS, hkeep, hFoot, hJin, hexit, hful, hnew⟩ :=
        (hF i).step w c c' a t hS hP ht hin ((hth w t ht).2 i hin) hI
      obtain ⟨hCI', hland⟩ := hC.frag i w c c' a a1 t t' hS hS' hCI ht hin hI ht' hLS hkeep hFoot hexit
      have hE : EnvMove L w c c' a a1 := ⟨hpre, hthj, linStep_ok hLS, linStep_hmove hLS, hS, hS',
        fun j hj => ⟨hP j hj, pendOK_mono (hthj j hj) hpre (agree_linStep hLS) (hP j hj)⟩⟩
      have hw : ((∀ i, ¬ (F i).inside t'.st) ∧ Idle a1 w) ∨ (∃ i, (F i).inside t'.st ∧ J i w t' c'.mem a1) ∨
          (∃ i, (F i).inside t'.st ∧ Landing L (F i) w t' a1.H ∧ Idle a1 w) := by
        by_cases hin' : (F i).inside t'.st
        · exact .inr (.inl ⟨i, hin', hJin hin'⟩)
        · obtain ⟨op, k0, p, hret, -⟩ := (hexit hin').2
          have hid : Idle a1 w := .inr ⟨op, k0, p, hret⟩
          by_cases hk : ∃ k, (F k).inside t'.st
          · obtain ⟨k, hk⟩ := hk; exact .inr (.inr ⟨k, hk, hland hin' k hk, hid⟩)
          · exact .inl ⟨fun k h => hk ⟨k, h⟩, hid⟩
      obtain ⟨a', hcore, hinv, hH⟩ := core_finish hF hdisj hS' hCI' (fun j hj => (hE.2.2.2.2.2.2 j hj).2) ht'
        (hoth a1 hE) hw
      refine ⟨a', hcore, ⟨a1, hLS, hinv⟩, fun t0 t1 ht0 ht1 => ?_⟩
      rw [ht] at ht0; cases ht0; rw [ht'] at ht1; cases ht1
      exact ⟨fun p hp hp' => by show PhiH _ _ _ _ _; rw [hH]; exact hful p hp hp',
        fun p hp hp' => absurd (hnew p hp) hp'⟩
    · have hout : ∀ i, ¬ (F i).inside t.st := fun i h => hin ⟨i, h⟩
      obtain ⟨t', ht', hR, hCI', hland⟩ := hC.step w c c' a t hS hP hCI ht hout hI
      obtain ⟨hS', hE⟩ := frame_client hS hP hI ht ht' hR
      have hid : Idle a w := (hth w t ht).1 hout
      have hw : ((∀ i, ¬ (F i).inside t'.st) ∧ Idle a w) ∨ (∃ i, (F i).inside t'.st ∧ J i w t' c'.mem a) ∨
          (∃ i, (F i).inside t'.st ∧ Landing L (F i) w t' a.H ∧ Idle a w) := by
        by_cases hk : ∃ k, (F k).inside t'.st
        · obtain ⟨k, hk⟩ := hk; exact .inr (.inr ⟨k, hk, hland k hk, hid⟩)
        · exact .inl ⟨fun k h => hk ⟨k, h⟩, hid⟩
      obtain ⟨a', hcore, hinv, hH⟩ := core_finish hF hdisj hS' hCI' (fun j hj => (hE.2.2.2.2.2.2 j hj).2) ht'
        (hoth a hE) hw
      refine ⟨a', hcore, ⟨a, .inl rfl, hinv⟩, fun t0 t1 ht0 ht1 => ?_⟩
      rw [ht] at ht0; cases ht0; rw [ht'] at ht1; cases ht1
      refine ⟨fun p hp hp' => ?_, fun p hp hp' => absurd (hR.1 p hp) hp'⟩
      obtain ⟨h0, h1⟩ := hS.bnd w t ht p hp
      obtain ⟨msg, hg⟩ := get?_of_bnd h0 h1
      have hg' : c'.mem.get? p = some msg := by rw [hpre.get? h1]; exact hg
      show PhiH _ _ _ _ _; rw [hH]
      have hc := hR.2.2 p msg hg' (.inr ⟨hp, hp'⟩)
      exact phiH_of_cw hg' hc
  · obtain ⟨⟨hS, hCI, hth⟩, hPall⟩ := hinv
    obtain ⟨t, msg, ht, -, htw, hthj, hmem⟩ := promSemInf_facts hP
    let a' : AS := { H := pAppend L w (c.mem.last + 1) msg a.H, th := a.th }
    have hPS : PStepL L w c c' a a' := ⟨rfl, msg, by rw [hmem, Memory.get?_append_last], rfl⟩
    have hpre : c.mem.Prefix c'.mem := hmem ▸ Memory.Prefix.append c.mem msg
    have hS' := struct_prom hS hP hPS
    have hE : EnvMove L w c c' a a' := ⟨hpre, hthj, fun _ _ => rfl, pStep_hmove hPS, hS, hS',
      fun j hj => ⟨hPall j, pendOK_mono (hthj j hj) hpre (agree_pStep hPS) (hPall j)⟩⟩
    refine ⟨a', ⟨hS', hC.prom w c c' a a' hS hP hPS hCI, fun j tj htj => ?_⟩, hPS⟩
    by_cases hj : j = w
    · subst hj; rw [htw] at htj; cases htj
      obtain ⟨h1, h2⟩ := hth j t ht
      exact ⟨h1, fun k hk => (hF k).prom j c c' a a' t _ hP hPS hS hS' ht htw (h2 k hk)⟩
    · rw [hthj j hj] at htj
      obtain ⟨h1, h2⟩ := hth j tj htj
      exact ⟨h1, fun k hk => (hF k).stable w j c c' a a' tj (Ne.symm hj) hE htj (h2 k hk)⟩
  · obtain ⟨a1, hLS, rfl | hinv⟩ := h
    · exact agree_linStep hLS p hp
    · show wrUpTo p a.H = wrUpTo p a'.H; rw [hinv.1]; exact agree_linStep hLS p hp

/-- The composition theorem from the fragment obligations (`FragObl`, the
internal invariants chosen). -/
theorem linObl_of_fragObl {L : StackLayout} {A : Arch} {ι : Type} {F : ι → Frag I}
    {CI : Config I → List PEnt → Prop} (hF : ∀ i, FragObl L A (F i))
    (hdisj : ∀ i k st, (F i).inside st → (F k).inside st → i = k) (hC : ClientRely L A F CI) :
    ∃ J, (linLift L F J CI).Obl A :=
  ⟨fun i => Classical.choose (hF i), linObl_of_frag_rely (fun i => Classical.choose_spec (hF i)) hdisj hC⟩

end Kraken.Promising.Lin
