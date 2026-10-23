/-
**Silent trees**: the ISA-neutral part of the undefined-flag rows
(`Lower/EventsX64Flags.lean`), importing no ISA's syntax.

A `SilentTree P t` is a finite choice (at least one branch at every node) of
`done` leaves, each satisfying `P`: no event, no fault. x64's undefined-flag
operations (`and`/`or`/`xor`/`test`/`imul`/shifts) have such trees.

- `SilentTree.run`, `SilentTree.exists_run`: every run of the tree is a
  leaf, and some leaf is run;
- machine level (`InstrSemInf`): `instrSemInf_silent`,
  `instrSemInf_of_silent_leaf`, `instrSemInf_silent_exists`,
  `instrSemInf_silent_stutter`, `stepOne_silent_no_error`;
- thread level (`stepOne`): `stepOne_silent_ok` (every successful outcome
  is `finishInstr` at a leaf, memory unchanged) and `stepOne_silent_exists`
  (some leaf has every finished thread as an outcome), the counterparts of
  `stepOne_ok_iff` at a `.done` leaf.
-/
import Kraken.Promising.Lower.Events

namespace Kraken.Promising.Lower

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-! ## Silent trees -/

/-- **A silent tree**: a finite choice (at least one branch at every node) of
`done` leaves, each satisfying `P`. No event, no fault. -/
def SilentTree {σ : Type} (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .choose n k => 0 < n ∧ ∀ i, SilentTree P (k i)
  | _ => False

theorem silentTree_done {σ : Type} (s : σ) : SilentTree (· = s) (.done s) := rfl

/-- A two-way choice of `done`s is silent, each leaf one of the branches. -/
theorem silentTree_choose2 {σ : Type} (f : Fin 2 → σ) :
    SilentTree (fun s => ∃ i, s = f i) (.choose 2 fun i => .done (f i)) :=
  ⟨by decide, fun i => ⟨i, rfl⟩⟩

theorem SilentTree.mono {σ : Type} {P Q : σ → Prop} (hPQ : ∀ s, P s → Q s) :
    ∀ {t : EvTree σ}, SilentTree P t → SilentTree Q t
  | .done s, h => hPQ s h
  | .choose _ _, h => ⟨h.1, fun i => SilentTree.mono hPQ (h.2 i)⟩
  | .fault _, h => h.elim
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .fence .., h => h.elim
  | .rmw .., h => h.elim

section Run

variable {I : ISA} (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Every run of a silent tree is a leaf**, successful, in the context it
started from. -/
theorem SilentTree.run {σ : Type} {P : σ → Prop} {c : Ctx} :
    ∀ {t : EvTree σ}, SilentTree P t → ∀ {x}, x ∈ runTree A tid iv c t → ∃ s, P s ∧ x = .ok (s, c)
  | .done s, h, x, hx => by
    simp only [runTree, List.mem_singleton] at hx
    exact ⟨s, h, hx⟩
  | .choose _ k, h, x, hx => by
    obtain ⟨i, hi⟩ := (run_choose_iff A tid iv).mp hx
    exact SilentTree.run (t := k i) (h.2 i) hi
  | .fault _, h, _, _ => h.elim
  | .load .., h, _, _ => h.elim
  | .store .., h, _, _ => h.elim
  | .fence .., h, _, _ => h.elim
  | .rmw .., h, _, _ => h.elim

/-- **Some leaf of a silent tree is run.** -/
theorem SilentTree.exists_run {σ : Type} {P : σ → Prop} {c : Ctx} :
    ∀ {t : EvTree σ}, SilentTree P t → ∃ s, P s ∧ .ok (s, c) ∈ runTree A tid iv c t
  | .done s, h => ⟨s, h, by simp [runTree]⟩
  | .choose n k, h => by
    obtain ⟨s, hs, hr⟩ := SilentTree.exists_run (c := c) (t := k ⟨0, h.1⟩) (h.2 _)
    exact ⟨s, hs, (run_choose_iff A tid iv).mpr ⟨_, hr⟩⟩
  | .fault _, h => h.elim
  | .load .., h => h.elim
  | .store .., h => h.elim
  | .fence .., h => h.elim
  | .rmw .., h => h.elim

end Run

section Machine

variable {I : ISA} (A : Arch) (tid : Nat) {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
  {tree : EvTree I.State} {P : I.State → Prop}

include ht

/-- **A step at a silent tree** is the no-event outcome of one of its leaves:
`finishInstr` at the thread's own context, memory unchanged. -/
theorem instrSemInf_silent (hex : I.exec t.st = some tree) (hs : SilentTree P tree)
    (h : InstrSemInf A tid c c') :
    ∃ s, P s ∧ ∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t c.mem) ∧
      CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  obtain ⟨th, mem', ⟨st, c1, hr, hth, rfl⟩, hc, rfl⟩ := (instrSemInf_iff_of_exec A tid ht hex).mp h
  obtain ⟨s, hPs, he⟩ := hs.run A tid _ hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨st, hPs, th, hth, hc, rfl⟩

/-- **A leaf of the tree, finished and certified, is a step.** -/
theorem instrSemInf_of_silent_leaf (hex : I.exec t.st = some tree) {s : I.State}
    (hr : .ok (s, ctx0 tid t c.mem) ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) tree)
    {th : Thread I} (hth : th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t c.mem))
    (hc : CertOk A tid th c.mem) : InstrSemInf A tid c (c.withThread tid th c.mem) :=
  (instrSemInf_iff_of_exec A tid ht hex).mpr ⟨th, c.mem, ⟨s, _, hr, hth, rfl⟩, hc, rfl⟩

/-- **Some leaf of a silent tree can be stepped to**: every finished,
certified thread at it is a step. -/
theorem instrSemInf_silent_exists (hex : I.exec t.st = some tree) (hs : SilentTree P tree) :
    ∃ s, P s ∧ ∀ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t c.mem) →
      CertOk A tid th c.mem → InstrSemInf A tid c (c.withThread tid th c.mem) := by
  obtain ⟨s, hPs, hr⟩ := hs.exists_run A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t c.mem)
  exact ⟨s, hPs, fun th hth hc => instrSemInf_of_silent_leaf A tid ht hex hr hth hc⟩

/-- **The source-stutter case for a silent tree**: `instrSemInf_done_stutter`
at one of its leaves. -/
theorem instrSemInf_silent_stutter (hex : I.exec t.st = some tree) (hs : SilentTree P tree)
    (h : InstrSemInf A tid c c') :
    ∃ s, P s ∧ ∃ th, c' = c.withThread tid th c.mem ∧ th.st = s ∧ th.prom = t.prom ∧
      (th.views = t.views ∨
        th.views = { t.views with vCAP := max t.views.vCAP (instrViews t (I.deps t.st)).condW }) ∧
      CertOk A tid th c.mem := by
  obtain ⟨s, hPs, th, hth, hc, rfl⟩ := instrSemInf_silent A tid ht hex hs h
  exact ⟨s, hPs, th, rfl, finishInstr_st hth, (finishInstr_relKey hth).1, CertCut.finishInstr_views hth, hc⟩

omit ht in
/-- **No error outcome** at a silent tree. -/
theorem stepOne_silent_no_error {mem : Memory} (hex : I.exec t.st = some tree) (hs : SilentTree P tree)
    {outs : List (Except String (Outcome I))} (hso : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Outcome I)) ∉ outs := by
  unfold stepOne at hso
  rw [hex] at hso
  have hs' : _ = outs := Option.some.inj hso
  subst hs'
  intro hm
  rw [List.mem_flatMap] at hm
  obtain ⟨r, hr, hm⟩ := hm
  obtain ⟨s, -, rfl⟩ := hs.run A tid _ hr
  simp at hm

end Machine

section Thread

variable {I : ISA} (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {tree : EvTree I.State}
  {P : I.State → Prop}

/-- **Every successful `stepOne` outcome at a silent tree** is `finishInstr`
at a leaf satisfying `P`, from `stepOne`'s context, with the memory
unchanged. -/
theorem stepOne_silent_ok (hex : I.exec t.st = some tree) (hs : SilentTree P tree) {th : Thread I}
    {mem' : Memory} (h : ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem') :
    ∃ s, P s ∧ th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t mem) ∧ mem' = mem := by
  obtain ⟨st, c', hr, hth, rfl⟩ := (stepOne_ok_iff A tid hex).mp h
  obtain ⟨s, hPs, he⟩ := hs.run A tid _ hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨st, hPs, hth, rfl⟩

/-- **Some leaf of a silent tree is a `stepOne` outcome**: at a leaf
satisfying `P`, every thread `finishInstr` gives is a successful outcome,
with the memory unchanged. -/
theorem stepOne_silent_exists (hex : I.exec t.st = some tree) (hs : SilentTree P tree) :
    ∃ s, P s ∧ ∀ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (ctx0 tid t mem) →
      ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem := by
  obtain ⟨s, hPs, hr⟩ := hs.exists_run A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem)
  exact ⟨s, hPs, fun th hth => (stepOne_ok_iff A tid hex).mpr ⟨s, _, hr, hth, rfl⟩⟩

end Thread

end Kraken.Promising.Lower
