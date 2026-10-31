/-
# TermLiveMach — runs, fairness and livelocks on the promise machine (L1)

`TermLive` decides liveness on the explorer's finite graph; `TermLiveProps`
proves the facts its criterion rests on, one step at a time.  This module
states the second headline's vocabulary on *infinite runs* of
`TermRun.Step` (decisions §6) and lifts the
step facts to runs.

* **Runs** (§1.1).  A run is labelled and may stutter: `LRun` pairs a
  configuration sequence with labels `Option L`, `none` a stutter.  The labelled
  step relation is a parameter (`LSys`): the machine's labels are
  `(thread, isThreadStep)` (`machine`), and a later oracle step (L6's
  `Step.reclaim`) is added by a larger label type, without restating anything
  below; the lifts need only `LSys.Sound`.
* **Crash** (§1.2, A2).  A run comes with `D : Nat → Option Nat`;
  thread `i` takes no step at or after `D i`, and has no promise out at that
  point (`CrashOK`).  The crashed thread stays as it was, well typed.
* **Fairness** (§1.3, U3 = F4).  Weak thread fairness, plus: a live thread
  that infinitely often has an enabled thread step that appends a message or
  raises one of its coherence views takes one infinitely often.  Promise steps
  are never required.  A further conjunct `RF` is the extension point for the
  oracle's reclaim fairness (`OracleFair` is its intended shape).
* **Waits** (§1.4, U4 = R1, U8 = full).  `Frozen`, `Latest`, `Touches`,
  `StuckOn` (no `noPromises` requirement), `Livelock`; `HeldAt`/`Holder` are
  parameters (`HoldView`) until L3 supplies them from `TermStep` and S10's
  `SysInv`; `Induced` is R1.
* **Lifts** (§2.4).  Memory only grows along a run; a run appends infinitely
  often or freezes (`run_freeze_or_grow`); on a frozen suffix coherence views
  rise only finitely often (`frozen_noraise`, `frozen_views_const`), so A3
  and A4 hold on a frozen suffix of a fair run (`frozen_stale_cas`,
  `frozen_load_stale`).
* **Crash simulation** (`crash_sim`).  Replacing thread `i` (as
  `TermLive.crashCfg` does) changes no move of any other thread.
* **The explorer bridge** (`class_run`).  A finite strongly connected set of
  configurations, closed under the live threads' machine thread steps, with a
  step inside, carries an F4-fair run with crash set `{i}`.  What is still
  open between this and `TermLive.exploreG` is recorded in `ExplorerBridge`.
* **RMW promises** (`promised_rmw_may_block`).  A foreign write between the
  last matching message and an RMW promise makes every outcome of that RMW
  keep the promise: the case U8 states on its own and fairness does not cover.
* **Statements** (§1.5).  `no_induced_livelock_robust`, `robust_tokenFree`,
  `forced_wait_is_livelock`, `no_induced_livelock` are *propositions* (defs),
  not theorems: their inputs (C, `TokUniq`, stage B's `Setting`) are later
  steps (L3, L4, L6).
-/
import WeakCore.TermLiveProps
import WeakCore.TermLive
import WeakCore.TermExtStep

namespace TermLiveMach
open CoreLang CoreTerm TermRun TermLiveProps
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises.Sim (MemExt)

/-! ## §1 Labelled systems and runs -/

/-- A labelled step relation on configurations.  `actor l` is the thread a
step labelled `l` belongs to (`none` for an oracle step); `thr i` is the label
of thread `i`'s thread steps. -/
structure LSys where
  L : Type
  S : Cfg → L → Cfg → Prop
  actor : L → Option Nat
  thr : Nat → L

/-- The machine's labelled step: `(i, true)` a thread step of `i`,
`(i, false)` a promise of `i`; each followed by certification, as in
`TermRun.Step`. -/
def mstep (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) : Nat × Bool → Cfg → Prop
  | (i, true), c' => c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i
  | (i, false), c' => ∃ a v w, i < c.ths.size ∧ w < c.mem.size ∧
      Certified p k arch (promise c i a v w) i ∧ c' = promise c i a v w

/-- The promise machine as a labelled system (labels as in
`TermLive.successorsL`). -/
def machine (p : Prog) (k : Promises.Knobs) (arch : Arch) : LSys where
  L := Nat × Bool
  S := mstep p k arch
  actor l := some l.1
  thr i := (i, true)

/-- A labelled, stuttering run. -/
structure LRun (L : Type) where
  cfg : Nat → Cfg
  lbl : Nat → Option L

/-- One move of a run: a stutter or a labelled step. -/
def LSys.Move (sys : LSys) : Cfg → Option sys.L → Cfg → Prop
  | c, none, c' => c' = c
  | c, some l, c' => sys.S c l c'

def LSys.Run (sys : LSys) (r : LRun sys.L) : Prop :=
  ∀ n, sys.Move (r.cfg n) (r.lbl n) (r.cfg (n + 1))

/-- `P` holds infinitely often. -/
def Often (P : Nat → Prop) : Prop := ∀ n, ∃ m, n ≤ m ∧ P m

/-- `P` holds from some point on. -/
def Ev (P : Nat → Prop) : Prop := ∃ n, ∀ m, n ≤ m → P m

/-- Thread `i` takes the step at `n` (thread or promise step). -/
def Takes (sys : LSys) (r : LRun sys.L) (n i : Nat) : Prop :=
  ∃ l, r.lbl n = some l ∧ sys.actor l = some i

/-- A2 crash: thread `i` takes no step at or after `D i`, and has no promise
outstanding at that point (the crash guard, U1a). -/
def CrashOK (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∀ i n, D i = some n → noPromises (r.cfg n) i = true ∧ ∀ m, n ≤ m → ¬ Takes sys r m i

/-- A live thread: present, and never crashed. -/
def Live {L : Type} (r : LRun L) (D : Nat → Option Nat) (i : Nat) : Prop :=
  i < (r.cfg 0).ths.size ∧ D i = none

/-- The crash set `{i}`, crashed from the start. -/
def crashAt (i : Nat) : Nat → Option Nat := fun j => if j = i then some 0 else none

/-! ## §2 Fairness (F4) -/

/-- Thread `i`'s coherence view at `b` (`0` for a missing thread). -/
def cohOf (c : Cfg) (i : Nat) (b : Address) : Nat := (c.ths[i]?.map (·.vs.coh b)).getD 0

/-- A step that appends a message or raises one of thread `i`'s coherence
views: the steps F4 makes a thread take. -/
def Progress (c c' : Cfg) (i : Nat) : Prop :=
  c.mem.size < c'.mem.size ∨ ∃ b, cohOf c i b < cohOf c' i b

/-- **F4.**  `weak`: a live thread with a thread step enabled from some point
on takes thread steps infinitely often.  `prog`: a live thread that infinitely
often has an enabled progress step takes one infinitely often.  `ext`: the
extension point for steps that are not thread steps (L6's reclaim oracle,
`OracleFair`); `fun _ => True` for the bare machine. -/
structure Fair (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat)
    (RF : LRun sys.L → Prop) : Prop where
  weak : ∀ i, Live r D i → Ev (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c') →
    Often (fun n => r.lbl n = some (sys.thr i))
  prog : ∀ i, Live r D i →
    Often (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c' ∧ Progress (r.cfg n) c' i) →
    Often (fun n => r.lbl n = some (sys.thr i) ∧ Progress (r.cfg n) (r.cfg (n + 1)) i)
  ext : RF r

/-- The intended shape of the reclaim conjunct: if a step with a label in `Q`
is enabled from some point on, such a step is taken infinitely often. -/
def OracleFair (sys : LSys) (Q : sys.L → Prop) (r : LRun sys.L) : Prop :=
  Ev (fun n => ∃ l c', Q l ∧ sys.S (r.cfg n) l c') →
    Often (fun n => ∃ l, r.lbl n = some l ∧ Q l)

/-! ## §3 Waits and livelocks -/

/-- Memory is constant from `n₀` on. -/
def Frozen {L : Type} (r : LRun L) (n₀ : Nat) : Prop :=
  ∀ n, n₀ ≤ n → (r.cfg n).mem = (r.cfg n₀).mem

/-- The coherence-latest message at `b` has value `v`. -/
def Latest (c : Cfg) (b : Address) (v : Val) : Prop := Promises.LatestIs c.mem b v

/-- The location operand of a memory access at the head of a term: `cas`,
`casp`, `load`, `fetch`, `ldp`. -/
def targetOf (th : TTh) : Option At :=
  match th.term with
  | .cas _ _ w _ _ _ _ _ => some w
  | .casp _ _ w _ _ _ _ _ _ _ => some w
  | .let_ _ (.load _ a) _ => some a
  | .let_ _ (.fetch _ _ _ a _) _ => some a
  | .let_ _ (.ldp _ a _ _) _ => some a
  | .let_ _ (.isTy _ _) _ => none
  | _ => none

/-- Thread `i` is at an access to address `b` (the hypothesis shape of
`stale_cas`). -/
def Touches (c : Cfg) (i : Nat) (b : Address) : Prop :=
  ∃ th w t pw, c.ths[i]? = some th ∧ targetOf th = some w ∧
    evalAt th.env w = some (t, [pw]) ∧ addrOf pw = some b

/-- Thread `i` keeps coming back to `b`, and `b`'s latest value never changes.
No `noPromises` requirement (U8 = full). -/
def StuckOn (sys : LSys) (r : LRun sys.L) (i : Nat) (b : Address) : Prop :=
  (∃ n₀ v, ∀ n, n₀ ≤ n → Latest (r.cfg n) b v) ∧
  Often (fun n => r.lbl n = some (sys.thr i)) ∧
  Often (fun n => Touches (r.cfg n) i b)

/-- The machine form of the explorer's class: memory constant, a live thread
spins. -/
def Livelock (sys : LSys) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ n₀, Frozen r n₀ ∧ ∃ i, Live r D i ∧ Often (fun n => r.lbl n = some (sys.thr i))

/-- `HeldAt c b n P` (word `b` of protocol `P` naming region `n` is in a held
state) and `Holder c b n h` (thread `h`'s frame bound carries `rg n`).  Their
definitions need `TermStep.WordAt`/`WordHolds` and S10's `SysInv` witness;
L3 instantiates this structure. -/
structure HoldView where
  heldAt : Cfg → Address → Nat → Proto → Prop
  holder : Cfg → Address → Nat → Nat → Prop

/-- **R1.**  A live thread is stuck on a word that is held from some point on,
by a holder that crashed. -/
def Induced (sys : LSys) (hv : HoldView) (r : LRun sys.L) (D : Nat → Option Nat) : Prop :=
  ∃ i b n P h, Live r D i ∧ StuckOn sys r i b ∧ Ev (fun m => hv.heldAt (r.cfg m) b n P) ∧
    Ev (fun m => hv.holder (r.cfg m) b n h) ∧ D h ≠ none

/-- **U2(c).**  No thread finishes with an affine result (it would walk away
with a token).  A configuration-level hypothesis; `Doc.threads`' static
refusal (U2(b)) is later. -/
def ResNonAffine (c : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh) (a : At) (t : Ty) (ws : List Word),
    c.ths[i]? = some th → th.term = .ret a → th.stack = [] →
    evalAt th.env a = some (t, ws) → t.affine = false

/-- Every protocol the program mentions is `robust`.  `Mentioned` is the
program's protocol list (`Robust.mapTy`'s traversal). -/
def ProgRobust (Mentioned : Proto → Prop) : Prop := ∀ P, Mentioned P → P.robust = true

/-- `robust`, or `windowed` with a reclaimer (§4; `Reclaimed` is L6's). -/
def ProgRobustOrWindowed (Mentioned : Proto → Prop) (Reclaimed : Proto → Prop) : Prop :=
  ∀ P, Mentioned P → P.robust = true ∨ (P.isLocal = true ∧ Reclaimed P)

/-! ## §4 The headline statements (propositions, not proved here)

`Setting c₀` abstracts stage B's hypotheses on the program and the initial
configuration (`ProgT`, `RunScope`, `ProgIall`, `ProgDwf`, `InitOK`). -/

/-- The robust branch (§1.5): no fair run of a robust program has an induced
livelock. -/
def no_induced_livelock_robust (sys : LSys) (Setting : Cfg → Prop) (Mentioned : Proto → Prop)
    (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobust Mentioned →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat), sys.Run r → r.cfg 0 = c₀ → CfgCoh c₀ →
    (∀ n, ResNonAffine (r.cfg n)) → CrashOK sys r D → Fair sys r D (fun _ => True) →
    ¬ Induced sys hv r D

/-- The corollary that is the robust branch's real content: in a robust
program no word is ever held, so no frame holds a region token. -/
def robust_tokenFree (sys : LSys) (Setting : Cfg → Prop) (Mentioned : Proto → Prop)
    (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobust Mentioned →
  ∀ (r : LRun sys.L), sys.Run r → r.cfg 0 = c₀ → ∀ m b n P, ¬ hv.heldAt (r.cfg m) b n P

/-- The converse half the explorer's verdicts rely on (C): a live thread that
keeps trying a word held by a crashed holder is stuck on it.
Superseded by `TermLiveC.forced_wait_held_thm`; likely false once promises are allowed. -/
def forced_wait_is_livelock (sys : LSys) (Setting : Cfg → Prop) (hv : HoldView) : Prop :=
  ∀ c₀, Setting c₀ →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat) i b n P h m n₀, sys.Run r → r.cfg 0 = c₀ →
    CrashOK sys r D → Fair sys r D (fun _ => True) → Live r D i →
    hv.heldAt (r.cfg n₀) b n P → hv.holder (r.cfg n₀) b n h → D h = some m → m ≤ n₀ →
    Often (fun n => r.lbl n = some (sys.thr i)) → Often (fun n => Touches (r.cfg n) i b) →
    StuckOn sys r i b

/-- The headline, both branches; `RF` is the reclaim fairness and
`ReclaimerOK` the oracle's contract (L6). -/
def no_induced_livelock (sys : LSys) (Setting : Cfg → Prop) (Mentioned Reclaimed : Proto → Prop)
    (hv : HoldView) (RF : LRun sys.L → Prop)
    (ReclaimerOK : LRun sys.L → (Nat → Option Nat) → Prop) : Prop :=
  ∀ c₀, Setting c₀ → ProgRobustOrWindowed Mentioned Reclaimed →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat), sys.Run r → r.cfg 0 = c₀ → CfgCoh c₀ →
    (∀ n, ResNonAffine (r.cfg n)) → CrashOK sys r D → Fair sys r D RF → ReclaimerOK r D →
    ¬ Induced sys hv r D

/-! ## §5 Sound systems: the machine, and what the lifts need -/

/-- What the run lemmas need of a labelled system: memory only grows,
`CfgCoh` is kept and no view goes down, the thread count is constant, and the
thread labels are exactly the machine's certified thread steps.  An oracle
step that appends a message and changes no thread satisfies the first three. -/
structure LSys.Sound (sys : LSys) (p : Prog) (k : Promises.Knobs) (arch : Arch) : Prop where
  mem : ∀ c l c', sys.S c l c' → MemExt c.mem c'.mem
  coh : ∀ c l c', sys.S c l c' → CfgCoh c → CfgCoh c' ∧ CohLe c c'
  size : ∀ c l c', sys.S c l c' → c'.ths.size = c.ths.size
  thr : ∀ c i c', sys.S c (sys.thr i) c' ↔ (c' ∈ threadSteps p k arch c i ∧ Certified p k arch c' i)
  actor_thr : ∀ i, sys.actor (sys.thr i) = some i

theorem threadSteps_size {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : c'.ths.size = c.ths.size := by
  unfold threadSteps at h
  split at h
  · simp at h
  · simp only [List.mem_map] at h
    obtain ⟨⟨mem, pairs, th'⟩, _, rfl⟩ := h
    simp

theorem promise_size (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    (promise c i a v w).ths.size = c.ths.size := by
  unfold promise
  split
  · rfl
  · simp

theorem machine_sound (p : Prog) (k : Promises.Knobs) (arch : Arch) :
    (machine p k arch).Sound p k arch where
  mem := by
    rintro c ⟨i, (_ | _)⟩ c' h
    · obtain ⟨a, v, w, _, _, _, rfl⟩ := h
      exact promise_ext c i a v w
    · exact threadSteps_ext h.1
  coh := by
    rintro c ⟨i, (_ | _)⟩ c' h hc
    · obtain ⟨a, v, w, _, _, _, rfl⟩ := h
      exact promise_coh c i a v w hc
    · exact threadSteps_coh h.1 hc
  size := by
    rintro c ⟨i, (_ | _)⟩ c' h
    · obtain ⟨a, v, w, _, _, _, rfl⟩ := h
      exact promise_size c i a v w
    · exact threadSteps_size h.1
  thr := fun _ _ _ => Iff.rfl
  actor_thr := fun _ => rfl

/-- The machine's labelled steps are exactly `TermRun.Step`. -/
theorem mstep_iff_Step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} :
    (∃ l, mstep p k arch c l c') ↔ Step p k arch c c' := by
  constructor
  · rintro ⟨⟨i, (_ | _)⟩, h⟩
    · obtain ⟨a, v, w, hi, hw, hc, rfl⟩ := h
      exact Step.prom i a v w hi hw hc
    · exact Step.thread i h.1 h.2
  · intro h
    cases h with
    | thread i hs hc => exact ⟨(i, true), hs, hc⟩
    | prom i a v w hi hw hc => exact ⟨(i, false), a, v, w, hi, hw, hc, rfl⟩

section Runs
variable {sys : LSys} {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem Move_mem (hs : sys.Sound p k arch) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') : MemExt c.mem c'.mem := by
  cases o with
  | none => cases h; exact Promises.Sim.MemExt.refl _
  | some l => exact hs.mem _ _ _ h

theorem Move_coh (hs : sys.Sound p k arch) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') (hc : CfgCoh c) : CfgCoh c' ∧ CohLe c c' := by
  cases o with
  | none => cases h; exact ⟨hc, CohLe.refl _⟩
  | some l => exact hs.coh _ _ _ h hc

theorem Move_size (hs : sys.Sound p k arch) {c c' : Cfg} {o : Option sys.L}
    (h : sys.Move c o c') : c'.ths.size = c.ths.size := by
  cases o with
  | none => cases h; rfl
  | some l => exact hs.size _ _ _ h

/-- **A1 along a run.**  Memory only grows. -/
theorem Run_mem (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r) {n m : Nat}
    (h : n ≤ m) : MemExt (r.cfg n).mem (r.cfg m).mem := by
  induction h with
  | refl => exact Promises.Sim.MemExt.refl _
  | step _ ih => exact Promises.Sim.MemExt.trans ih (Move_mem hs (hr _))

theorem Run_size (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r) :
    ∀ n, (r.cfg n).ths.size = (r.cfg 0).ths.size
  | 0 => rfl
  | n + 1 => (Move_size hs (hr n)).trans (Run_size hs hr n)

theorem Run_coh (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) : ∀ n, CfgCoh (r.cfg n)
  | 0 => hc
  | n + 1 => (Move_coh hs (hr n) (Run_coh hs hr hc n)).1

theorem Run_cohLe (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) (n : Nat) : CohLe (r.cfg n) (r.cfg (n + 1)) :=
  (Move_coh hs (hr n) (Run_coh hs hr hc n)).2

theorem memExt_eq_of_size {m m' : Memory} (h : MemExt m m') (hs : m'.size ≤ m.size) : m' = m :=
  (memExt_antisymm h ⟨hs, fun t ht => (h.get t (Nat.lt_of_lt_of_le ht hs)).symm⟩).symm

/-- If from some point no step appends, memory is frozen from there. -/
theorem frozen_of_noAppend (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r) {n₀ : Nat}
    (h : ∀ m, n₀ ≤ m → ¬ (r.cfg m).mem.size < (r.cfg (m + 1)).mem.size) : Frozen r n₀ := by
  intro n hn
  induction hn with
  | refl => rfl
  | step hle ih =>
      rename_i m
      have he := Move_mem hs (hr m)
      rw [memExt_eq_of_size he (Nat.le_of_not_lt (h m hle)), ih]

/-- **A run appends infinitely often or freezes.** -/
theorem run_freeze_or_grow (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r) :
    (∃ n₀, Frozen r n₀) ∨ Often (fun n => (r.cfg n).mem.size < (r.cfg (n + 1)).mem.size) := by
  refine Classical.byCases (fun (h : Often _) => Or.inr h) fun h => Or.inl ?_
  refine Classical.byContradiction fun hno => h fun n => Classical.byContradiction fun h' => ?_
  exact hno ⟨n, frozen_of_noAppend hs hr fun m hm ha => h' ⟨m, hm, ha⟩⟩

end Runs

/-! ## §6 Frozen suffixes: views settle, A3 and A4 lift -/

theorem cohOf_le {c c' : Cfg} (hl : CohLe c c') (i : Nat) (b : Address) :
    cohOf c i b ≤ cohOf c' i b := by
  unfold cohOf
  cases h1 : c.ths[i]? with
  | none => simp
  | some th =>
    cases h2 : c'.ths[i]? with
    | none =>
        have := lt_of_get h1
        rw [Array.getElem?_eq_none_iff] at h2
        have := hl.1
        omega
    | some th' => simpa using hl.2 i th th' h1 h2 b

theorem cohOf_le_size {c : Cfg} (hc : CfgCoh c) (i : Nat) (b : Address) :
    cohOf c i b ≤ c.mem.size := by
  unfold cohOf
  cases h1 : c.ths[i]? with
  | none => simp
  | some th => simpa using (hc i th h1).le_size b

theorem cohOf_loc {c : Cfg} (hc : CfgCoh c) {i : Nat} {b : Address} (h : 0 < cohOf c i b) :
    ∃ m, c.mem[cohOf c i b]? = some m ∧ m.loc = b := by
  unfold cohOf at h ⊢
  cases h1 : c.ths[i]? with
  | none => simp [h1] at h
  | some th =>
    simp only [h1, Option.map_some, Option.getD_some] at h ⊢
    rcases hc i th h1 b with h0 | hm
    · simp only [WeakMem.Ts] at h0; omega
    · exact hm

/-- `f 0 + … + f (n-1)`. -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_le {f g : Nat → Nat} : ∀ n, (∀ t, t < n → f t ≤ g t) → sumR f n ≤ sumR g n
  | 0, _ => Nat.le_refl _
  | n + 1, h => Nat.add_le_add (sumR_le n fun t ht => h t (by omega)) (h n (by omega))

theorem sumR_lt {f g : Nat → Nat} : ∀ n, (∀ t, t < n → f t ≤ g t) → ∀ t₀, t₀ < n →
    f t₀ < g t₀ → sumR f n < sumR g n
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, h, t₀, ht, hlt => by
      simp only [sumR]
      by_cases e : t₀ = n
      · subst e
        exact Nat.add_lt_add_of_le_of_lt (sumR_le _ fun t ht' => h t (by omega)) hlt
      · exact Nat.add_lt_add_of_lt_of_le (sumR_lt n (fun t ht' => h t (by omega)) t₀ (by omega) hlt)
          (h n (by omega))

theorem sumR_bound {f : Nat → Nat} {B : Nat} : ∀ n, (∀ t, t < n → f t ≤ B) → sumR f n ≤ n * B
  | 0, _ => by simp [sumR]
  | n + 1, h => by
      simp only [sumR, Nat.succ_mul]
      exact Nat.add_le_add (sumR_bound n fun t ht => h t (by omega)) (h n (by omega))

/-- The potential: thread `i`'s views at the locations of `M`'s messages. -/
def phi (M : Memory) (c : Cfg) (i : Nat) : Nat :=
  sumR (fun t => match M[t]? with | some m => cohOf c i m.loc | none => 0) M.size

theorem phi_le {M : Memory} {c c' : Cfg} (hl : CohLe c c') (i : Nat) : phi M c i ≤ phi M c' i :=
  sumR_le _ fun t _ => by
    split
    · exact cohOf_le hl i _
    · exact Nat.le_refl _

theorem phi_lt {M : Memory} {c c' : Cfg} (hl : CohLe c c') (hc' : CfgCoh c') (hm : c'.mem = M)
    {i : Nat} {b : Address} (h : cohOf c i b < cohOf c' i b) : phi M c i < phi M c' i := by
  obtain ⟨m, hget, hloc⟩ := cohOf_loc hc' (Nat.lt_of_le_of_lt (Nat.zero_le _) h)
  rw [hm] at hget
  refine sumR_lt _ (fun t _ => ?_) (cohOf c' i b) (lt_of_get hget) ?_
  · split
    · exact cohOf_le hl i _
    · exact Nat.le_refl _
  · simp only [hget, hloc]
    exact h

theorem phi_bound {M : Memory} {c : Cfg} (hc : CfgCoh c) (hm : c.mem = M) (i : Nat) :
    phi M c i ≤ M.size * M.size :=
  sumR_bound _ fun t _ => by
    split
    · exact hm ▸ cohOf_le_size hc i _
    · exact Nat.zero_le _

/-- A sequence that does not decrease and is bounded from `n₀` on is
eventually constant. -/
theorem ev_const (f : Nat → Nat) (B : Nat) :
    ∀ d n₀, B - f n₀ = d → (∀ m, n₀ ≤ m → f m ≤ f (m + 1)) → (∀ m, n₀ ≤ m → f m ≤ B) →
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → f m = f n₁ := by
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro n₀ hd hmono hb
    have up : ∀ m, n₀ ≤ m → f n₀ ≤ f m := by
      intro m hm
      induction hm with
      | refl => exact Nat.le_refl _
      | step hle ih' => exact Nat.le_trans ih' (hmono _ hle)
    refine Classical.byCases (fun (h : ∀ m, n₀ ≤ m → f m = f n₀) => ⟨n₀, Nat.le_refl _, h⟩)
      fun h => ?_
    obtain ⟨m, hm, hne⟩ : ∃ m, n₀ ≤ m ∧ f m ≠ f n₀ :=
      Classical.byContradiction fun hc => h fun m hm =>
        Classical.byContradiction fun hne => hc ⟨m, hm, hne⟩
    have hlt : f n₀ < f m := Nat.lt_of_le_of_ne (up m hm) (Ne.symm hne)
    have hbm := hb m hm
    obtain ⟨n₁, h1, h2⟩ := ih (B - f m) (by omega) m rfl (fun x hx => hmono x (by omega))
      (fun x hx => hb x (by omega))
    exact ⟨n₁, by omega, h2⟩

section Frozen
variable {sys : LSys} {p : Prog} {k : Promises.Knobs} {arch : Arch}

/-- **Views settle on a frozen suffix.**  Coherence views only rise, and on
constant memory each sits at a message of that memory, so each thread's
views rise only finitely often. -/
theorem frozen_noraise (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → ∀ b, cohOf (r.cfg (m + 1)) i b ≤ cohOf (r.cfg m) i b := by
  obtain ⟨M, hM⟩ : ∃ M, M = (r.cfg n₀).mem := ⟨_, rfl⟩
  obtain ⟨n₁, h01, hconst⟩ := ev_const (fun m => phi M (r.cfg m) i) (M.size * M.size) _ n₀ rfl
    (fun m _ => phi_le (Run_cohLe hs hr hc m) i)
    (fun m hm => phi_bound (Run_coh hs hr hc m) ((hfz m hm).trans hM.symm) i)
  refine ⟨n₁, h01, fun m hm b => Nat.le_of_not_lt fun hlt => ?_⟩
  have := phi_lt (Run_cohLe hs hr hc m) (Run_coh hs hr hc (m + 1))
    ((hfz (m + 1) (by omega)).trans hM.symm) hlt
  have e1 := hconst m hm
  have e2 := hconst (m + 1) (by omega)
  try dsimp only at e1 e2
  omega

/-- Each thread's coherence views are eventually constant on a frozen
suffix. -/
theorem frozen_views_const (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → ∀ b, cohOf (r.cfg m) i b = cohOf (r.cfg n₁) i b := by
  obtain ⟨n₁, h01, hnr⟩ := frozen_noraise hs hr hc hfz i
  refine ⟨n₁, h01, fun m hm b => ?_⟩
  induction hm with
  | refl => rfl
  | step hle ih =>
      rename_i m'
      exact Nat.le_antisymm (Nat.le_trans (hnr m' hle b) (Nat.le_of_eq ih))
        (ih ▸ cohOf_le (Run_cohLe hs hr hc m') i b)

/-- Thread `i` waits at a `cas` whose expected value is the latest at the
word, with no promise out: a step that appends is enabled (`tstep_cas_appends`). -/
def FreshCas (c : Cfg) (i : Nat) : Prop :=
  ∃ (th : TTh) (acq rel : Bool) (w e v : At) (t : String) (ok fail : Expr) (tw te tv : Ty)
    (pw ew nw : Word) (b : Address),
    c.ths[i]? = some th ∧ th.promises = [] ∧ th.term = .cas acq rel w e v t ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ evalAt th.env e = some (te, [ew]) ∧
    evalAt th.env v = some (tv, [nw]) ∧ addrOf pw = some b ∧ Promises.LatestIs c.mem b ew.val

theorem freshCas_enabled (hs : sys.Sound p k arch) {c : Cfg} {i : Nat} (h : FreshCas c i) :
    ∃ c', sys.S c (sys.thr i) c' ∧ Progress c c' i := by
  obtain ⟨th, acq, rel, w, e, v, t, ok, fail, tw, te, tv, pw, ew, nw, b, hth, hnp, hterm, hw, he,
    hv, hb, hl⟩ := h
  obtain ⟨⟨m', p', t'⟩, hr, hsz⟩ :=
    tstep_cas_appends (gOf p k arch c i) c.mem c.pairs th hterm hw he hv hb hl
  have hin : ({ c with mem := m', pairs := p', ths := c.ths.set! i t' } : Cfg) ∈
      threadSteps p k arch c i := by
    simp only [threadSteps, hth]
    exact List.mem_map.2 ⟨(m', p', t'), hr, rfl⟩
  have hp' : t'.promises = [] := by
    have := (tstep_ext _ _ _ _ _ hr).prom
    simp only [stOf, hnp] at this
    exact List.eq_nil_iff_forall_not_mem.2 fun x hx => List.not_mem_nil (this x hx)
  have hget : (c.ths.set! i t')[i]? = some t' := by
    rw [getElem?_set!]; simp [lt_of_get hth]
  refine ⟨_, (hs.thr _ _ _).2 ⟨hin, _, Solo.refl _, ?_⟩, Or.inl ?_⟩
  · rw [noPromises, hget]
    simp [hp']
  · simp only at hsz ⊢
    omega

/-- **A3 on a frozen suffix of a fair run.**  From some point on, no live
thread waits at a fresh `cas` (with no promise out): F4 would make it append
or raise a view, and on a frozen suffix neither happens any more. -/
theorem frozen_stale_cas (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {D : Nat → Option Nat} {RF : LRun sys.L → Prop}
    (hF : Fair sys r D RF) {i : Nat} (hi : Live r D i) {n₀ : Nat} (hfz : Frozen r n₀) :
    Ev (fun n => ¬ FreshCas (r.cfg n) i) := by
  obtain ⟨n₁, h01, hnr⟩ := frozen_noraise hs hr hc hfz i
  refine Classical.byContradiction fun hno => ?_
  have hio : Often (fun n => ∃ c', sys.S (r.cfg n) (sys.thr i) c' ∧ Progress (r.cfg n) c' i) := by
    intro n
    obtain ⟨m, hm, hf⟩ : ∃ m, n ≤ m ∧ FreshCas (r.cfg m) i :=
      Classical.byContradiction fun h' => hno ⟨n, fun m hm hf => h' ⟨m, hm, hf⟩⟩
    exact ⟨m, hm, freshCas_enabled hs hf⟩
  obtain ⟨m, hm, -, hpr⟩ := hF.prog i hi hio n₁
  rcases hpr with hsz | ⟨b, hb⟩
  · rw [hfz m (by omega), hfz (m + 1) (by omega)] at hsz
    exact Nat.lt_irrefl _ hsz
  · exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hb (hnr m hm b))

/-- **A4 on a frozen suffix.**  From some point on, a one-word load step of
thread `i` reads no write newer than the thread's view at the address.  (No
fairness needed: views settle on any frozen suffix.) -/
theorem frozen_load_stale (hs : sys.Sound p k arch) {r : LRun sys.L} (hr : sys.Run r)
    (hc : CfgCoh (r.cfg 0)) {n₀ : Nat} (hfz : Frozen r n₀) (i : Nat) :
    ∃ n₁, n₀ ≤ n₁ ∧ ∀ m, n₁ ≤ m → r.lbl m = some (sys.thr i) →
      ∀ (th : TTh) (x : String) (acq : Bool) (a : At) (e : Expr) (t : Ty) (pw : Word) (μ : Mode)
        (u : Ty) (b : Address),
      (r.cfg m).ths[i]? = some th → th.term = .let_ x (.load acq a) e →
      evalAt th.env a = some (t, [pw]) → cellOf t = some (μ, u) → addrOf pw = some b →
      accs u = some [.one] →
      ∃ th1 t' w, (r.cfg (m + 1)).ths[i]? = some th1 ∧ th1.env.head? = some (x, t', [w]) ∧
        w.rts ≤ th.vs.coh b := by
  obtain ⟨n₁, h01, hnr⟩ := frozen_noraise hs hr hc hfz i
  refine ⟨n₁, h01, fun m hm hl th x acq a e t pw μ u b hth hterm ha hcell hb hus => ?_⟩
  have hmv := hr m
  rw [hl] at hmv
  have hstep := ((hs.thr _ _ _).1 hmv).1
  have hle := cohOf_le (Run_cohLe hs hr hc m) i b
  have hge := hnr m hm b
  generalize r.cfg (m + 1) = c1 at hstep hle hge ⊢
  simp only [threadSteps, hth] at hstep
  obtain ⟨⟨mem, pairs, th1⟩, hin, rfl⟩ := List.mem_map.1 hstep
  have h1 : (((r.cfg m).ths.set! i th1))[i]? = some th1 := by
    rw [getElem?_set!]; simp [lt_of_get hth]
  simp only [cohOf, hth, h1, Option.map_some, Option.getD_some] at hle hge
  obtain ⟨t', w, hw, hle'⟩ :=
    tstep_load_stale hterm ha hcell hb hus hin (Nat.le_antisymm hge hle)
  exact ⟨th1, t', w, h1, hw, hle'⟩

end Frozen

/-! ## §7 Crash simulation

`TermLive.crashCfg` replaces thread `i` by a finished one.  Replacing a
thread changes nothing another thread can see: `tstep` of `j` reads only
`c.ths[j]`, the thread count, memory and `pairs`.  So the explorer's crashed
configurations and the A2 run's (thread `i` frozen as it was) have the same
moves for every `j ≠ i` (`mstep_setTh`, `crash_sim`). -/

/-- Replace thread `i`. -/
def setTh (c : Cfg) (i : Nat) (x : TTh) : Cfg := { c with ths := c.ths.set! i x }

theorem setTh_get_ne {c : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) :
    (setTh c i x).ths[j]? = c.ths[j]? := by
  simp only [setTh, getElem?_set!, Ne.symm h, ↓reduceIte]

theorem setTh_comm {c : Cfg} {i j : Nat} {x y : TTh} (h : j ≠ i) {mem : Memory} {pairs : List Ts} :
    ({ setTh c i x with mem := mem, pairs := pairs, ths := (setTh c i x).ths.set! j y } : Cfg) =
      setTh { c with mem := mem, pairs := pairs, ths := c.ths.set! j y } i x := by
  simp only [setTh, Array.set!_eq_setIfInBounds, Array.setIfInBounds_comm _ _ (Ne.symm h)]

theorem setTh_setTh (c : Cfg) (i : Nat) (x y : TTh) : setTh (setTh c i x) i y = setTh c i y := by
  simp only [setTh, Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds]

theorem setTh_self {c : Cfg} {i : Nat} {y : TTh} (h : c.ths[i]? = some y) : setTh c i y = c := by
  have e : c.ths.set! i y = c.ths := by
    apply Array.ext_getElem?
    intro j
    rw [getElem?_set!]
    split
    · rename_i hij
      subst hij
      simp only [lt_of_get h, ↓reduceIte, h]
    · rfl
  unfold setTh
  rw [e]

theorem setTh_none {c : Cfg} {i : Nat} {x : TTh} (h : c.ths[i]? = none) : setTh c i x = c := by
  have e : c.ths.set! i x = c.ths := by
    apply Array.ext_getElem?
    intro j
    rw [getElem?_set!]
    split
    · rename_i hij
      subst hij
      rw [Array.getElem?_eq_none_iff] at h
      simp [Nat.not_lt.2 h]
    · rfl
  unfold setTh
  rw [e]

/-- The replacement keeps thread `i`'s allocation records. -/
def TysAt (c : Cfg) (i : Nat) (x : TTh) : Prop := ∀ y, c.ths[i]? = some y → x.tys = y.tys

theorem tysOf_setTh {c : Cfg} {i : Nat} {x : TTh} (hx : TysAt c i x) : tysOf (setTh c i x) = tysOf c := by
  cases hy : c.ths[i]? with
  | none => rw [setTh_none hy]
  | some y =>
    funext l
    simp only [tysOf, setTh, Array.toList_set!]
    have hl : c.ths.toList[i]? = some y := by simpa using hy
    refine findSome_set_same _ ?_ _ _ hl
    simp [hx y hy]

section Crash
variable {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem threadSteps_get_ne {c c' : Cfg} {i j : Nat} (h : c' ∈ threadSteps p k arch c j) (hij : i ≠ j) :
    c'.ths[i]? = c.ths[i]? := by
  unfold threadSteps at h
  split at h
  · simp at h
  · obtain ⟨⟨mem, pairs, th'⟩, -, rfl⟩ := List.mem_map.1 h
    simp only [getElem?_set!, Ne.symm hij, ↓reduceIte]

theorem promise_get_ne {c : Cfg} {i j : Nat} (hij : i ≠ j) (a : Address) (v : Val) (w : Ts) :
    (promise c j a v w).ths[i]? = c.ths[i]? := by
  unfold promise
  split
  · rfl
  · simp only [getElem?_set!, Ne.symm hij, ↓reduceIte]

theorem threadSteps_setTh {c : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) (hx : TysAt c i x) :
    threadSteps p k arch (setTh c i x) j =
      (threadSteps p k arch c j).map (fun d => setTh d i x) := by
  unfold threadSteps
  rw [setTh_get_ne h]
  split
  · rfl
  · rw [List.map_map]
    have hg : gOf p k arch (setTh c i x) j = gOf p k arch c j := by
      simp only [gOf, tysOf_setTh hx]; simp [setTh, Cfg.n]
    rw [hg]
    apply List.map_congr_left
    intro ⟨mem, pairs, th'⟩ _
    exact setTh_comm h

theorem promise_setTh {c : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) (a : Address) (v : Val) (w : Ts) :
    promise (setTh c i x) j a v w = setTh (promise c j a v w) i x := by
  unfold promise
  rw [setTh_get_ne h]
  split
  · rfl
  · exact setTh_comm h

/-- Another thread's extern move commutes with replacing thread `i`. -/
theorem extSteps_setTh {c d : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) (hd : d ∈ extSteps c j) :
    setTh d i x ∈ extSteps (setTh c i x) j := by
  obtain ⟨th, y, n, a, e, rt, ws, rs, hth, hterm, hn, hev, hrs, rfl⟩ := extSteps_elim hd
  have hth' : (setTh c i x).ths[j]? = some th := by rw [setTh_get_ne h]; exact hth
  have hm := extSteps_intro (rs := rs) hth' hterm hn hev hrs
  have hc : ∀ (t : TTh) (tr : List Event), setTh { c with ths := c.ths.set! j t, trace := tr } i x =
      { setTh c i x with ths := (setTh c i x).ths.set! j t, trace := tr } := by
    intro t tr
    simp only [setTh, Array.set!_eq_setIfInBounds, Array.setIfInBounds_comm _ _ h]
  have e1 : setTh (extCfg c j th y n e ws rs) i x = extCfg (setTh c i x) j th y n e ws rs := by
    cases n with
    | current =>
      cases hl : th.tidLbl with
      | none => exact absurd (Or.inr (Or.inl ⟨rfl, hl⟩)) hn
      | some l => simp only [extCfg, curCfg, hl]; exact hc _ c.trace
    | exitEv => exact absurd (Or.inl rfl) hn
    | _ => exact hc _ _
  rw [e1]; exact hm

theorem noPromises_setTh {c : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) :
    noPromises (setTh c i x) j = noPromises c j := by
  unfold noPromises
  rw [setTh_get_ne h]

theorem Solo_setTh {c d : Cfg} {i j : Nat} (x : TTh) (h : j ≠ i) (hs : Solo p k arch j c d) (hx : TysAt c i x) :
    Solo p k arch j (setTh c i x) (setTh d i x) := by
  induction hs with
  | refl c => exact Solo.refl _
  | thread hs' _ ih =>
      exact Solo.thread (by rw [threadSteps_setTh h hx]; exact List.mem_map_of_mem hs')
        (ih fun y hy => hx y (by rwa [threadSteps_get_ne hs' (Ne.symm h)] at hy))
  | prom a v w hw _ ih =>
      exact Solo.prom a v w hw (by
        rw [promise_setTh h]; exact ih fun y hy => hx y (by rwa [promise_get_ne (Ne.symm h)] at hy))
  | ext hs' _ ih =>
      exact Solo.ext (extSteps_setTh h hs') (ih fun y hy => hx y (by rwa [extSteps_ne hs' (Ne.symm h)] at hy))

theorem Certified_setTh {c : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) (hx : TysAt c i x) :
    Certified p k arch (setTh c i x) j ↔ Certified p k arch c j := by
  constructor
  · rintro ⟨d, hs, hn⟩
    cases hc : c.ths[i]? with
    | none => rw [setTh_none hc] at hs; exact ⟨d, hs, hn⟩
    | some y =>
        have hxi : (setTh c i x).ths[i]? = some x := by
          simp only [setTh, getElem?_set!, ↓reduceIte, lt_of_get hc]
        have := Solo_setTh y h hs (fun z hz => by rw [hxi] at hz; cases hz; exact (hx y hc).symm)
        rw [setTh_setTh, setTh_self hc] at this
        exact ⟨_, this, by rw [noPromises_setTh h]; exact hn⟩
  · rintro ⟨d, hs, hn⟩
    exact ⟨_, Solo_setTh x h hs hx, by rw [noPromises_setTh h]; exact hn⟩

/-- Replacing thread `i` changes no move of any other thread `j`. -/
theorem mstep_setTh {c d' : Cfg} {i j : Nat} {x : TTh} (h : j ≠ i) (b : Bool) (hx : TysAt c i x) :
    mstep p k arch (setTh c i x) (j, b) d' ↔ ∃ d, mstep p k arch c (j, b) d ∧ d' = setTh d i x := by
  cases b with
  | true =>
    simp only [mstep, threadSteps_setTh h hx, List.mem_map]
    constructor
    · rintro ⟨⟨d, hd, rfl⟩, hc⟩
      exact ⟨d, ⟨hd, (Certified_setTh h (fun y hy => hx y (by rwa [threadSteps_get_ne hd (Ne.symm h)] at hy))).1 hc⟩, rfl⟩
    · rintro ⟨d, ⟨hd, hc⟩, rfl⟩
      exact ⟨⟨d, hd, rfl⟩, (Certified_setTh h (fun y hy => hx y (by rwa [threadSteps_get_ne hd (Ne.symm h)] at hy))).2 hc⟩
  | false =>
    simp only [mstep, promise_setTh h]
    constructor
    · rintro ⟨a, v, w, hj, hw, hc, rfl⟩
      exact ⟨_, ⟨a, v, w, by simpa [setTh] using hj, hw, (Certified_setTh h (fun y hy => hx y (by rwa [promise_get_ne (Ne.symm h)] at hy))).1 hc, rfl⟩, rfl⟩
    · rintro ⟨d, ⟨a, v, w, hj, hw, hc, rfl⟩, rfl⟩
      exact ⟨a, v, w, by simpa [setTh] using hj, hw, (Certified_setTh h (fun y hy => hx y (by rwa [promise_get_ne (Ne.symm h)] at hy))).2 hc, rfl⟩

/-- **Crash simulation.**  `TermLive.crashCfg c i = some c'` leaves memory
alone (`crash_mem`), happens only with no promise of `i` out (the crash
guard), and `c'` has the same moves as `c` for every other thread, up to
thread `i`'s slot. -/
theorem crash_sim {c c' : Cfg} {i : Nat} (h : TermLive.crashCfg c i = some c') :
    c'.mem = c.mem ∧ noPromises c i = true ∧ ∃ thc, c' = setTh c i thc ∧
      ∀ j, j ≠ i → ∀ b d', mstep p k arch c' (j, b) d' ↔
        ∃ d, mstep p k arch c (j, b) d ∧ d' = setTh d i thc := by
  unfold TermLive.crashCfg at h
  split at h
  · rename_i th hth
    split at h
    · cases h
    · rename_i hc
      cases h
      simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hc
      refine ⟨crash_mem c i _, ?_, _, rfl, fun j hj b d' => mstep_setTh hj b (fun y hy => by rw [hth] at hy; cases hy; rfl)⟩
      simp only [noPromises, hth, Option.map_some, Option.getD_some]
      cases hp : th.promises.isEmpty
      · rw [hp] at hc; exact absurd hc.2 (by decide)
      · rfl
  · cases h

end Crash

/-! ## §8 The explorer bridge: a closed class carries a fair run -/

/-- A thread-step edge: `(thread, source, target)`. -/
abbrev Edge := Nat × Cfg × Cfg

/-- A walk along edges of `E`. -/
inductive Chain (E : List Edge) : Cfg → List Edge → Cfg → Prop
  | nil (c : Cfg) : Chain E c [] c
  | cons {c d : Cfg} {e : Edge} {es : List Edge} : e ∈ E → e.2.1 = c → Chain E e.2.2 es d →
      Chain E c (e :: es) d

theorem Chain.append {E : List Edge} {c d f : Cfg} {es fs : List Edge} (h1 : Chain E c es d)
    (h2 : Chain E d fs f) : Chain E c (es ++ fs) f := by
  induction h1 with
  | nil => exact h2
  | cons he hs _ ih => exact Chain.cons he hs (ih h2)

/-- The `k`-th node of a walk from `c`. -/
def nodeAt (c : Cfg) (L : List Edge) : Nat → Cfg
  | 0 => c
  | k + 1 => match L[k]? with
    | some e => e.2.2
    | none => c

theorem nodeAt_succ {c : Cfg} {L : List Edge} {k : Nat} (hk : k < L.length) :
    nodeAt c L (k + 1) = L[k].2.2 := by
  simp [nodeAt, List.getElem?_eq_getElem hk]

theorem nodeAt_cons (c : Cfg) (e : Edge) (es : List Edge) {k : Nat} (hk : k ≤ es.length) :
    nodeAt c (e :: es) (k + 1) = nodeAt e.2.2 es k := by
  cases k with
  | zero => simp [nodeAt]
  | succ k =>
      rw [nodeAt_succ (by simp; omega), nodeAt_succ (by omega)]
      simp

theorem chain_get {E : List Edge} {c d : Cfg} {L : List Edge} (h : Chain E c L d) :
    (∀ k (hk : k < L.length), L[k] ∈ E ∧ L[k].2.1 = nodeAt c L k) ∧ nodeAt c L L.length = d := by
  induction h with
  | nil c => exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), rfl⟩
  | cons he hs hc ih =>
    rename_i c d e es
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => exact ⟨he, hs⟩
      | succ k =>
        have hk' : k < es.length := by simpa using hk
        obtain ⟨h1, h2⟩ := ih.1 k hk'
        simp only [List.getElem_cons_succ]
        exact ⟨h1, by rw [h2, nodeAt_cons _ _ _ (Nat.le_of_lt hk')]⟩
    · simp only [List.length_cons]
      rw [nodeAt_cons _ _ _ (Nat.le_refl _)]
      exact ih.2

section Bridge
variable {sys : LSys} {p : Prog} {k : Promises.Knobs} {arch : Arch}

theorem chain_mem (hs : sys.Sound p k arch) {E : List Edge}
    (hE : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2) {c d : Cfg} {L : List Edge}
    (h : Chain E c L d) : MemExt c.mem d.mem := by
  induction h with
  | nil => exact Promises.Sim.MemExt.refl _
  | cons he hsrc _ ih =>
      subst hsrc
      exact Promises.Sim.MemExt.trans (hs.mem _ _ _ (hE _ he)) ih

theorem chain_coh (hs : sys.Sound p k arch) {E : List Edge}
    (hE : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2) {c d : Cfg} {L : List Edge}
    (h : Chain E c L d) (hc : CfgCoh c) : CfgCoh d ∧ CohLe c d := by
  induction h with
  | nil c => exact ⟨hc, CohLe.refl _⟩
  | cons he hsrc _ ih =>
      subst hsrc
      obtain ⟨h1, l1⟩ := hs.coh _ _ _ (hE _ he) hc
      obtain ⟨h2, l2⟩ := ih h1
      exact ⟨h2, l1.trans l2⟩

/-- A closed walk from `c₀` through every edge. -/
theorem cover {C : List Cfg} {E : List Edge} {c₀ : Cfg} (hEC : ∀ e ∈ E, e.2.1 ∈ C ∧ e.2.2 ∈ C)
    (hconn : ∀ c ∈ C, ∀ d ∈ C, ∃ L, Chain E c L d) (h0 : c₀ ∈ C) :
    ∀ (Es : List Edge), (∀ e ∈ Es, e ∈ E) → ∀ s ∈ C, ∃ L, Chain E s L c₀ ∧ ∀ e ∈ Es, e ∈ L
  | [], _, s, hs =>
      let ⟨L, hL⟩ := hconn s hs c₀ h0
      ⟨L, hL, fun _ h => absurd h List.not_mem_nil⟩
  | e :: Es, hsub, s, hs => by
      have he := hsub e (by simp)
      obtain ⟨L1, h1⟩ := hconn s hs e.2.1 (hEC e he).1
      obtain ⟨L2, h2, hc2⟩ := cover hEC hconn h0 Es (fun x hx => hsub x (by simp [hx]))
        e.2.2 (hEC e he).2
      refine ⟨L1 ++ e :: L2, h1.append (Chain.cons he rfl h2), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · simp
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (hc2 x hx))

/-- The run that walks a closed walk `L` round and round. -/
def lapRun (sys : LSys) (c₀ : Cfg) (L : List Edge) (hN : 0 < L.length) : LRun sys.L where
  cfg n := nodeAt c₀ L (n % L.length)
  lbl n := some (sys.thr (L[n % L.length]'(Nat.mod_lt _ hN)).1)

theorem succ_mod_cases (n N : Nat) (hN : 0 < N) :
    ((n + 1) % N = n % N + 1 ∧ n % N + 1 < N) ∨ ((n + 1) % N = 0 ∧ n % N + 1 = N) := by
  have h1 := Nat.mod_add_div n N
  have h2 := Nat.mod_lt n hN
  by_cases h : n % N + 1 < N
  · refine Or.inl ⟨?_, h⟩
    have e : n + 1 = (n % N + 1) + N * (n / N) := by omega
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  · refine Or.inr ⟨?_, by omega⟩
    have e : n + 1 = N * (n / N + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e, Nat.mul_mod_right]

theorem getElem_idx {α : Type} {L : List α} {i j : Nat} (h : i = j) (hi : i < L.length) :
    L[i] = L[j]'(h ▸ hi) := by
  subst h; rfl

theorem lapRun_run {E : List Edge} (hE : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2) {c₀ : Cfg}
    {L : List Edge} (hL : Chain E c₀ L c₀) (hN : 0 < L.length) : sys.Run (lapRun sys c₀ L hN) := by
  intro n
  obtain ⟨hget, hend⟩ := chain_get hL
  have hk := Nat.mod_lt n hN
  obtain ⟨hmem, hsrc⟩ := hget _ hk
  have htgt : nodeAt c₀ L ((n + 1) % L.length) = (L[n % L.length]'hk).2.2 := by
    rcases succ_mod_cases n L.length hN with ⟨h1, _⟩ | ⟨h1, h2⟩
    · rw [h1, nodeAt_succ hk]
    · rw [h1]
      have := hend
      rw [← h2, nodeAt_succ hk] at this
      exact this.symm
  show sys.S (nodeAt c₀ L (n % L.length)) (sys.thr (L[n % L.length]'hk).1)
    (nodeAt c₀ L ((n + 1) % L.length))
  rw [← hsrc, htgt]
  exact hE _ hmem

theorem lapRun_cfg {E : List Edge} {c₀ : Cfg} {L : List Edge} (hL : Chain E c₀ L c₀)
    (hN : 0 < L.length) (n : Nat) :
    (lapRun sys c₀ L hN).cfg n = (L[n % L.length]'(Nat.mod_lt _ hN)).2.1 :=
  ((chain_get hL).1 _ (Nat.mod_lt _ hN)).2.symm

theorem lapRun_often {L : List Edge} (hN : 0 < L.length) {e : Edge} (he : e ∈ L) :
    Often (fun n => ∃ hk : n % L.length < L.length, L[n % L.length]'hk = e) := by
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
  intro n
  have hle := Nat.le_mul_of_pos_left n hN
  have hm : (k + L.length * n) % L.length = k := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hk2 : (k + L.length * n) % L.length < L.length := Nat.mod_lt _ hN
  exact ⟨k + L.length * n, by omega, hk2, by rw [getElem_idx hm hk2]; exact hke⟩

/-- The hypotheses `class_run` needs of a class `C` with inside edges `E`
and crashed thread `i`: every edge is a certified thread step of a thread
`≠ i` inside `C`; `C` is strongly connected by `E`; there is an edge (a thread
step inside); `C` is closed under every machine thread step of every thread
`≠ i`; the start `c₀ ∈ C` has `CfgCoh` and no promise of `i` out.  (An
out-of-range `i` encodes "nobody crashed".) -/
structure ClassHyp (sys : LSys) (C : List Cfg) (E : List Edge) (c₀ : Cfg) (i : Nat) : Prop where
  edge : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2 ∧ e.2.1 ∈ C ∧ e.2.2 ∈ C ∧ e.1 ≠ i
  conn : ∀ c ∈ C, ∀ d ∈ C, ∃ L, Chain E c L d
  inside : E ≠ []
  start : c₀ ∈ C
  closed : ∀ c ∈ C, ∀ j c', j ≠ i → sys.S c (sys.thr j) c' → (j, c, c') ∈ E
  coh : CfgCoh c₀
  guard : noPromises c₀ i = true

/-- **The explorer's class is a fair run.**  A closed class with a thread
step inside carries an F4-fair run that stays in it, with crash set `{i}`,
in which a live thread steps at every step; it is a `Livelock`. -/
theorem class_run (hs : sys.Sound p k arch) {C : List Cfg} {E : List Edge} {c₀ : Cfg} {i : Nat}
    (h : ClassHyp sys C E c₀ i) :
    ∃ r : LRun sys.L, sys.Run r ∧ r.cfg 0 = c₀ ∧ (∀ n, r.cfg n ∈ C) ∧
      CrashOK sys r (crashAt i) ∧ Fair sys r (crashAt i) (fun _ => True) ∧
      (∀ n, ∃ j, j ≠ i ∧ r.lbl n = some (sys.thr j)) ∧ Livelock sys r (crashAt i) := by
  have hE : ∀ e ∈ E, sys.S e.2.1 (sys.thr e.1) e.2.2 := fun e he => (h.edge e he).1
  obtain ⟨L, hL, hcov⟩ := cover (fun e he => ⟨(h.edge e he).2.1, (h.edge e he).2.2.1⟩) h.conn
    h.start E (fun e he => he) c₀ h.start
  obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil E h.inside
  have hN : 0 < L.length := List.length_pos_of_mem (hcov e₀ he₀)
  have hLE : ∀ e ∈ L, e ∈ E := fun e he => by
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    exact ((chain_get hL).1 k hk).1
  let r := lapRun sys c₀ L hN
  have hin : ∀ n, r.cfg n ∈ C := fun n => by
    rw [lapRun_cfg hL]
    exact (h.edge _ (hLE _ (List.getElem_mem _))).2.1
  have h0 : r.cfg 0 = c₀ := by show nodeAt c₀ L (0 % L.length) = c₀; simp [nodeAt]
  have hlbl : ∀ n, ∃ j, j ≠ i ∧ r.lbl n = some (sys.thr j) := fun n =>
    ⟨_, (h.edge _ (hLE _ (List.getElem_mem _))).2.2.2, rfl⟩
  have hreach : ∀ x ∈ C, ∀ y ∈ C, x.mem.size = y.mem.size ∧ ∀ j b, cohOf x j b = cohOf y j b := by
    intro x hx y hy
    obtain ⟨L0, h0x⟩ := h.conn c₀ h.start x hx
    obtain ⟨Lxy, hxy⟩ := h.conn x hx y hy
    obtain ⟨Lyx, hyx⟩ := h.conn y hy x hx
    have hcx := (chain_coh hs hE h0x h.coh).1
    obtain ⟨hcy, lxy⟩ := chain_coh hs hE hxy hcx
    obtain ⟨_, lyx⟩ := chain_coh hs hE hyx hcy
    exact ⟨Nat.le_antisymm (chain_mem hs hE hxy).size (chain_mem hs hE hyx).size,
      fun j b => Nat.le_antisymm (cohOf_le lxy j b) (cohOf_le lyx j b)⟩
  refine ⟨r, lapRun_run hE hL hN, h0, hin, ?_, ?_, hlbl, ⟨0, fun n _ => ?_, ?_⟩⟩
  rotate_right 2
  · obtain ⟨Ln, hn⟩ := h.conn c₀ h.start _ (hin n)
    rw [h0]
    exact memExt_eq_of_size (chain_mem hs hE hn) (Nat.le_of_eq (hreach _ (hin n) _ h.start).1)
  · have he0 := (chain_get hL).1 0 hN
    have hS := (hs.thr _ _ _).1 (hE _ he0.1)
    simp only [nodeAt] at he0
    rw [he0.2] at hS
    have hlt : (L[0]'hN).1 < c₀.ths.size := by
      have hne := hS.1
      unfold threadSteps at hne
      split at hne
      · simp at hne
      · rename_i th hth
        exact lt_of_get hth
    refine ⟨(L[0]'hN).1, ⟨h0 ▸ hlt, ?_⟩, fun n => ?_⟩
    · simp only [crashAt]
      split
      · rename_i e
        exact absurd e (h.edge _ he0.1).2.2.2
      · rfl
    · obtain ⟨m, hm, hk, hke⟩ := lapRun_often hN (List.getElem_mem hN) n
      refine ⟨m, hm, ?_⟩
      show some (sys.thr (L[m % L.length]'hk).1) = some (sys.thr (L[0]'hN).1)
      rw [hke]
  · intro j n hD
    simp only [crashAt] at hD
    split at hD
    · rename_i hji
      cases hD
      subst hji
      refine ⟨h0 ▸ h.guard, fun m _ ⟨l, hl, ha⟩ => ?_⟩
      obtain ⟨j', hj', hl'⟩ := hlbl m
      rw [hl'] at hl
      cases hl
      rw [hs.actor_thr] at ha
      cases ha
      exact hj' rfl
    · cases hD
  · refine ⟨fun j hj ⟨n₀, hen⟩ => ?_, fun j hj hio => ?_, trivial⟩
    · obtain ⟨c', hc'⟩ := hen n₀ (Nat.le_refl _)
      have hji : j ≠ i := fun e => by
        have h2 := hj.2
        subst e
        simp [crashAt] at h2
      have hcl := hcov _ (h.closed _ (hin n₀) j c' hji hc')
      intro n
      obtain ⟨m, hm, hk, hke⟩ := lapRun_often hN hcl n
      refine ⟨m, hm, ?_⟩
      show some (sys.thr (L[m % L.length]'hk).1) = some (sys.thr j)
      rw [hke]
    · exfalso
      obtain ⟨m, -, c', hc', hpr⟩ := hio 0
      have hji : j ≠ i := fun e => by
        have h2 := hj.2
        subst e
        simp [crashAt] at h2
      have hc'C := (h.edge _ (h.closed _ (hin m) j c' hji hc')).2.2.1
      obtain ⟨hsz, hcoh⟩ := hreach _ (hin m) _ hc'C
      rcases hpr with hlt | ⟨b, hb⟩
      · rw [hsz] at hlt; exact Nat.lt_irrefl _ hlt
      · rw [hcoh j b] at hb; exact Nat.lt_irrefl _ hb

end Bridge

/-- Bounded certification is certification. -/
theorem certB_sound {p : Prog} {k : Promises.Knobs} {arch : Arch} :
    ∀ (f : Nat) (c : Cfg) (i : Nat), certB p k arch f c i = true → Certified p k arch c i
  | 0, c, i, h => ⟨c, Solo.refl _, by simpa [certB] using h⟩
  | f + 1, c, i, h => by
      simp only [certB, Bool.or_eq_true, List.any_eq_true] at h
      rcases h with (h | ⟨c', hc', hcert⟩) | ⟨c', hc', hcert⟩
      · exact ⟨c, Solo.refl _, h⟩
      · obtain ⟨d, hs, hd⟩ := certB_sound f c' i hcert
        exact ⟨d, Solo.thread hc' hs, hd⟩
      · obtain ⟨d, hs, hd⟩ := certB_sound f c' i hcert
        exact ⟨d, Solo.ext hc' hs, hd⟩

/-- (M1) The explorer's result lists are admitted (`devChoice`: the bounded value set `b.io`, masked). -/
theorem extRs_admits {b : Bounds} {n : ExtName} {i : Nat} {ws : List Word} {tr : List Event} {rs : List Word}
    (h : rs ∈ extRs b n i ws tr) : n.Admits i ws tr rs := by
  unfold extRs at h
  split at h
  · simp only [List.mem_map, List.mem_filter] at h
    obtain ⟨v, ⟨-, hv⟩, rfl⟩ := h
    exact ⟨v, by simpa using hv, rfl⟩
  · exact (mem_resultsL _ _ _ _ _).1 h

/-- (F2) An extern move the explorer offers is a machine extern step. -/
theorem extSuccs_sound {p : Prog} {k : Promises.Knobs} {arch : Arch} {b : Bounds} {c c' : Cfg} {i : Nat}
    (h : c' ∈ extSuccs p k arch b c i) : TermExtStep.Ext p k arch c c' := by
  unfold extSuccs at h
  cases hth : c.ths[i]? with
  | none => simp [hth] at h
  | some th =>
    simp only [hth] at h
    cases hterm : th.term with
    | let_ x op e =>
      simp only [hterm] at h
      cases op with
      | ext n a =>
        simp only at h
        split at h
        · simp at h
        · rename_i hg
          cases hev : evalAt th.env a with
          | none => simp [hev] at h
          | some rw =>
            obtain ⟨rt, ws⟩ := rw
            rw [hev] at h
            dsimp only at h
            obtain ⟨rs, hm1, rfl⟩ := List.mem_map.mp h
            obtain ⟨hm, hc⟩ := List.mem_filter.mp hm1
            refine TermExtStep.Ext.mk i x n a e th rt ws rs hth hterm (fun hn => ?_) hev (extRs_admits hm)
              (certB_sound _ _ _ hc)
            cases hp : th.promises with
            | nil => rfl
            | cons t ts => exact absurd (by simp [hp, decide_eq_true hn]) hg
      | _ => simp at h
    | _ => simp [hterm] at h

/-- **Open: the explorer's half of the bridge.**  Every fair livelock
`TermLive.analyse` reports on `exploreG` (with `crashCfg` edges for thread `i`)
comes from a class satisfying `ClassHyp` on the machine, its configurations
read with thread `i` restored (`crash_sim`).  Needs: `cfgKey` identifies only
configurations with the same moves; the partial-order reduction loses no
exit (`TermLive`'s header argues it); bounded certification (`certB_sound`
is one direction) finds every certified step from the class. -/
def ExplorerBridge (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (fuel : Nat)
    (c : Cfg) (i : Nat) : Prop :=
  let g := TermLive.exploreG p k arch b fuel c (fun d => (TermLive.crashCfg d i).toList)
  ∀ ll ∈ (TermLive.analyse g).livelocks, ∃ C E c₀ j, (j = i ∨ c.ths.size ≤ j) ∧
    ClassHyp (machine p k arch) C E c₀ j ∧ C.length = ll.size

/-! ## §9 RMW promises (U8 = full)

Fairness asks nothing of a thread with no enabled step.  A thread with an
outstanding RMW promise can lose all of them: its RMW must read the message
immediately before the promise at the address (`rmwAdjacent`), with the
expected value.  Once another thread's write sits between the last such
message and the promise, every outcome of the RMW keeps the promise, and if
no other path discharges it the thread is uncertifiable for ever. -/

theorem lockFence_promises {arch : Arch} (t : Promises.Thread) :
    (if arch = .tso then Promises.stepFence t .sy else t).promises = t.promises := by
  split <;> rfl

/-- **An RMW cannot fulfil a promise behind a foreign write.**  If every
message at `a` below the promise `tw` with the expected value `e` has another
message at `a` between it and `tw`, no outcome of a `cas` RMW at `a`
discharges `tw`. -/
theorem promised_rmw_may_block_at {k : Promises.Knobs} {arch : Arch} {mem : Memory}
    {pairs : List Ts} {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {e : Val}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory}
    {th' : Promises.Thread} {tw : Ts}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a (.cas e) newv deps acq rel)
    (htw : tw ∈ th.promises)
    (hblk : ∀ t m, t < tw → mem[t]? = some m → m.loc = a → m.val = e →
      WeakMem.betweenAt mem a t tw = true) :
    tw ∈ th'.promises := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, hbody⟩ := h
  obtain ⟨m, hm, hl⟩ := loc_of_readable hr
  have hm! : mem[t]! = m := by simp [getElem!_def, hm]
  split at hbody
  · rw [List.mem_singleton] at hbody
    cases hbody
    rw [lockFence_promises]
    exact htw
  · rename_i hsucc
    rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    · split at happ
      · rw [List.mem_singleton] at happ
        cases happ
        rw [lockFence_promises]
        exact htw
      · simp at happ
    · obtain ⟨tw', _, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      · cases hft
      · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
        obtain ⟨hcond, hft⟩ := hft
        cases hft
        rw [lockFence_promises]
        by_cases heq : tw = tw'
        · subst heq
          exfalso
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
          have hadj := hcond.2
          simp only [WeakMem.rmwAdjacent, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hadj
          have hv : m.val = e := by
            rw [hm!] at hsucc
            simpa [WeakMem.rmwSucceeds, WeakMem.RmwKind.succeeds] using hsucc
          rw [hblk t m hadj.1 hm hl hv] at hadj
          exact Bool.noConfusion hadj.2
        · exact (List.mem_erase_of_ne heq).2 htw

theorem promised_rmw_may_block {k : Promises.Knobs} {arch : Arch} {mem : Memory}
    {pairs : List Ts} {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {e : Val}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory}
    {th' : Promises.Thread} {tw : Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a (.cas e) newv deps acq rel)
    (htw : tw ∈ th.promises)
    (hblk : ∀ t m, t < tw → mem[t]? = some m → m.loc = a → m.val = e →
      WeakMem.betweenAt mem a t tw = true) :
    tw ∈ th'.promises := by
  exact promised_rmw_may_block_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockFence_promises]; exact htw) hblk

#print axioms run_freeze_or_grow
#print axioms frozen_noraise
#print axioms frozen_stale_cas
#print axioms frozen_load_stale
#print axioms crash_sim
#print axioms class_run
#print axioms certB_sound
#print axioms extSuccs_sound
#print axioms promised_rmw_may_block
#print axioms TermLiveMach.extSteps_setTh

end TermLiveMach
