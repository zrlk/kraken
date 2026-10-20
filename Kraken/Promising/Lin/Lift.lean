/-
**The relational write-invariant lifting on the
fuel-free semantic machine** (ISA-neutral, program-independent).

This is route A′ of the earlier `treiber2` prototype, restated on
the fuel-free machine `StepSemInf` (`LiveSemInf.lean`, the lowering target)
and tracked. It generalises `InvLink.configInv_reachableK` from a per-thread
ISA predicate plus a per-message predicate to a relation between
configurations and an abstract state `S`, with a **per-step** abstract step.

Decomposition (forced by promises):

- `Core c a`: everything except the lawfulness of outstanding promises;
- `Φ tid p m a`: the lawfulness of thread `tid`'s outstanding promise at
  timestamp `p`; it must be **prefix-local** (`Obl.prefixLocal`): it depends
  only on the memory up to `p` and on the abstract state "up to `p`"
  (`Agree p`);
- `Inv c a := Core c a ∧ ∀ j, PendOK Φ j c a`.

Obligations (`RelLift.Obl`):

- `instr`: an instruction step of `tid` (`InstrSemInf`, certification
  built in) from `Core` and the **other** threads' `PendOK` gives `Core` and
  an abstract step; every promise of `tid` the step fulfils gets `Φ`. The
  stepping thread's own outstanding promises are not assumed lawful: this is
  what lets the certifying run use the obligation.
- `prom`: a promise step from `Inv` gives `Core` and an abstract step. It
  need **not** prove the new promise lawful.
- `prefixLocal`/`agreeA`/`agreeP`.

Results: `RelLift.Obl.step` (every `StepSemInf` step carries `Inv`, with an
abstract step; no liveness hypothesis), `Obl.reach` (`ReachableSemInf`), and
the transfers to the fuel-indexed machine (`Obl.stepSem`, `Obl.reachSem`)
and to the executable machine (`Obl.reach_succs`, via
`reachableSem_of_reachable'`). The promise case (`run_pend`) runs the
certifying run that `CertOk` provides (the thread alone, the others frozen)
through `instr`, and carries each `Φ` obtained at a fulfilment back to the
post-promise configuration by `prefixLocal`.
-/
import Kraken.Promising.LiveSemInf
import Kraken.Promising.StepSemOfSuccs

namespace Kraken.Promising.Lin

open Kraken Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem Kraken.Promising.Live.Bridge
open Kraken.Promising.Live.Inf

variable {I : ISA} {S : Type}

/-- Thread `tid`'s outstanding promises are below `|M|` and lawful. -/
def PendOK (Φ : Nat → Time → Memory → S → Prop) (tid : Nat) (c : Config I) (a : S) : Prop :=
  ∀ t, c.threads[tid]? = some t → ∀ p ∈ t.prom, p ≤ c.mem.last ∧ Φ tid p c.mem a

/-- The data of a relational lifting. -/
structure RelLift (I : ISA) (S : Type) where
  /-- The relation without the lawfulness of outstanding promises. -/
  Core : Config I → S → Prop
  /-- Lawfulness of thread `tid`'s outstanding promise at `p` (prefix-local). -/
  Φ : Nat → Time → Memory → S → Prop
  /-- The abstract step of an instruction step of `tid`. -/
  AStep : Nat → Config I → Config I → S → S → Prop
  /-- The abstract step of a promise step of `tid`. -/
  PStep : Nat → Config I → Config I → S → S → Prop
  /-- Two abstract states agree up to timestamp `p`. -/
  Agree : Time → S → S → Prop

namespace RelLift

variable (L : RelLift I S)

/-- The full relation. -/
def Inv (c : Config I) (a : S) : Prop := L.Core c a ∧ ∀ j, PendOK L.Φ j c a

/-- The relation without `tid`'s own promises' lawfulness. -/
def InvExcept (tid : Nat) (c : Config I) (a : S) : Prop :=
  L.Core c a ∧ ∀ j, j ≠ tid → PendOK L.Φ j c a

/-- **The obligations of the relational lifting** (route A′), on the
fuel-free semantic machine. -/
structure Obl (A : Arch) : Prop where
  instr : ∀ tid c c' a, L.InvExcept tid c a → InstrSemInf A tid c c' →
    ∃ a', L.Core c' a' ∧ L.AStep tid c c' a a' ∧
      ∀ t t', c.threads[tid]? = some t → c'.threads[tid]? = some t' →
        (∀ p ∈ t.prom, p ∉ t'.prom → L.Φ tid p c'.mem a') ∧
        (∀ p ∈ t'.prom, p ∉ t.prom → p ≤ c'.mem.last ∧ L.Φ tid p c'.mem a')
  prom : ∀ tid c c' a, L.Inv c a → PromSemInf A tid c c' → ∃ a', L.Core c' a' ∧ L.PStep tid c c' a a'
  prefixLocal : ∀ tid p (m m' : Memory) a a', p ≤ m.last → m.Prefix m' → L.Agree p a a' →
    (L.Φ tid p m a ↔ L.Φ tid p m' a')
  agreeA : ∀ tid c c' a a', L.AStep tid c c' a a' → ∀ p, p ≤ c.mem.last → L.Agree p a a'
  agreeP : ∀ tid c c' a a', L.PStep tid c c' a a' → ∀ p, p ≤ c.mem.last → L.Agree p a a'

variable {L}

/-- Other threads' lawfulness is carried by a step of `tid` that only
extends memory and keeps the abstract state up to `|M|`. -/
theorem pendOK_frame {tid j : Nat} {c c' : Config I} {a a' : S} {A : Arch} (h : L.Obl A)
    (_hj : j ≠ tid) (hth : c'.threads[j]? = c.threads[j]?) (hm : c.mem.Prefix c'.mem)
    (hag : ∀ p, p ≤ c.mem.last → L.Agree p a a') (hp : PendOK L.Φ j c a) : PendOK L.Φ j c' a' := by
  intro t ht p hpt
  rw [hth] at ht
  obtain ⟨hle, hΦ⟩ := hp t ht p hpt
  exact ⟨Nat.le_trans hle hm.last_le, (h.prefixLocal j p c.mem c'.mem a a' hle hm (hag p hle)).mp hΦ⟩

/-- Installing thread `tid` twice keeps the second installation. -/
theorem withThread_withThread (c : Config I) (tid : Nat) (t t' : Thread I) (m m' : Memory) :
    (c.withThread tid t m).withThread tid t' m' = c.withThread tid t' m' := by
  simp only [Config.withThread]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [Array.set!, Array.getElem?_setIfInBounds, Array.size_setIfInBounds]
  split <;> simp_all

/-- **The certifying run carries lawfulness back.** Along a promise-free run
of `tid` alone (others frozen in `c`) that ends with no promise, every
outstanding promise of the start is lawful at the start, provided the start
satisfies `InvExcept tid`. -/
theorem run_pend {A : Arch} (h : L.Obl A) {tid : Nat} {c : Config I} {t0 : Thread I}
    (ht0 : c.threads[tid]? = some t0) :
    ∀ (p q : Thread I × Memory), ThreadNP A tid p q → q.1.prom = [] →
      ∀ a, L.InvExcept tid (c.withThread tid p.1 p.2) a →
        ∀ ts ∈ p.1.prom, ts ≤ p.2.last → L.Φ tid ts p.2 a := by
  intro p q hr
  induction hr with
  | refl p =>
    intro hq a _ ts hts
    rw [hq] at hts
    cases hts
  | @step p p1 q hs hrest ih =>
    intro hq a hinv ts hts hle
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    have hget : (c.withThread tid p.1 p.2).threads[tid]? = some p.1 := withThread_get_self ht0
    have hI : InstrSemInf A tid (c.withThread tid p.1 p.2) (c.withThread tid o.thread o.mem) := by
      refine ⟨p.1, outs, o, hget, hstep, ho, ⟨q.1, q.2, hrest, hq⟩, ?_⟩
      rw [withThread_withThread]
    obtain ⟨a1, hcore, hstepA, hful⟩ := h.instr tid _ _ a hinv hI
    have hget1 : (c.withThread tid o.thread o.mem).threads[tid]? = some o.thread := withThread_get_self ht0
    obtain ⟨hgone, -⟩ := hful p.1 o.thread hget hget1
    have hpre : p.2.Prefix o.mem := Memory.Prefix.stepOne hstep ho
    have hag : ∀ x, x ≤ p.2.last → L.Agree x a a1 := fun x hx => h.agreeA tid _ _ a a1 hstepA x hx
    have hinv1 : L.InvExcept tid (c.withThread tid o.thread o.mem) a1 := by
      refine ⟨hcore, fun j hj => ?_⟩
      have hth : (c.withThread tid o.thread o.mem).threads[j]? = (c.withThread tid p.1 p.2).threads[j]? := by
        rw [withThread_get_ne ht0 hj, withThread_get_ne ht0 hj]
      exact pendOK_frame h hj hth hpre hag (hinv.2 j hj)
    have hΦ1 : L.Φ tid ts o.mem a1 := by
      by_cases hin : ts ∈ o.thread.prom
      · exact ih hq a1 hinv1 ts hin (Nat.le_trans hle hpre.last_le)
      · exact hgone ts hts hin
    exact (h.prefixLocal tid ts p.2 o.mem a a1 hle hpre (hag ts hle)).mpr hΦ1

/-- **The relational lifting, one step**: `Inv` is carried by every step of
the fuel-free semantic machine, with an abstract `AStep` (instruction) or
`PStep` (promise). No liveness hypothesis. -/
theorem Obl.step {A : Arch} (h : L.Obl A) {tid : Nat} {c c' : Config I} {a : S}
    (hinv : L.Inv c a) (hs : StepSemInf A tid c c') :
    ∃ a', L.Inv c' a' ∧ (L.AStep tid c c' a a' ∨ L.PStep tid c c' a a') := by
  rcases hs with hI | hP
  · obtain ⟨t, outs, o, ht, hstep, ho, hc, rfl⟩ := hI
    obtain ⟨a', hcore, hA, hful⟩ :=
      h.instr tid c _ a ⟨hinv.1, fun j _ => hinv.2 j⟩ ⟨t, outs, o, ht, hstep, ho, hc, rfl⟩
    have hpre : c.mem.Prefix o.mem := Memory.Prefix.stepOne hstep ho
    have hag : ∀ x, x ≤ c.mem.last → L.Agree x a a' := fun x hx => h.agreeA tid _ _ a a' hA x hx
    refine ⟨a', ⟨hcore, fun j => ?_⟩, .inl hA⟩
    by_cases hj : j = tid
    · subst hj
      intro t' ht' p hp
      rw [withThread_get_self ht] at ht'
      cases ht'
      obtain ⟨-, hnew⟩ := hful t o.thread ht (withThread_get_self ht)
      by_cases hin : p ∈ t.prom
      · obtain ⟨hle, hΦ⟩ := hinv.2 j t ht p hin
        exact ⟨Nat.le_trans hle hpre.last_le, (h.prefixLocal j p c.mem o.mem a a' hle hpre (hag p hle)).mp hΦ⟩
      · exact hnew p hp hin
    · exact pendOK_frame h hj (withThread_get_ne ht hj) hpre hag (hinv.2 j)
  · obtain ⟨t, w, ht, hw, hc, rfl⟩ := hP
    obtain ⟨a', hcore, hPs⟩ := h.prom tid c _ a hinv ⟨t, w, ht, hw, hc, rfl⟩
    have hpre : c.mem.Prefix (c.mem.append w).1 := Memory.Prefix.append c.mem w
    have hag : ∀ x, x ≤ c.mem.last → L.Agree x a a' := fun x hx => h.agreeP tid _ _ a a' hPs x hx
    have hexc : L.InvExcept tid (c.withThread tid (promThread t c.mem w) (c.mem.append w).1) a' :=
      ⟨hcore, fun j hj => pendOK_frame h hj (withThread_get_ne ht hj) hpre hag (hinv.2 j)⟩
    refine ⟨a', ⟨hcore, fun j => ?_⟩, .inr hPs⟩
    by_cases hj : j = tid
    · subst hj
      intro t' ht' p hp
      rw [withThread_get_self ht] at ht'
      cases ht'
      have hle : p ≤ (c.mem.append w).1.last := by
        simp only [List.mem_append, List.mem_singleton] at hp
        rw [Memory.last_append]
        rcases hp with hp | rfl
        · exact Nat.le_succ_of_le (hinv.2 j t ht p hp).1
        · exact Nat.le_refl _
      refine ⟨hle, ?_⟩
      obtain ⟨tq, mq, hrun, hq⟩ := hc
      have hc0 : (c.withThread j (promThread t c.mem w) (c.mem.append w).1).threads[j]? =
          some (promThread t c.mem w) := withThread_get_self ht
      exact run_pend h hc0 (promThread t c.mem w, (c.mem.append w).1) (tq, mq) hrun hq a'
        (by dsimp only; rw [withThread_withThread]; exact hexc) p hp hle
    · exact pendOK_frame h hj (withThread_get_ne ht hj) hpre hag (hinv.2 j)

/-- **The relational lifting**: `Inv` at every configuration reachable on
the fuel-free semantic machine. -/
theorem Obl.reach {A : Arch} (h : L.Obl A) {c0 c : Config I} {a0 : S}
    (h0 : L.Inv c0 a0) (hr : ReachableSemInf A c0 c) : ∃ a, L.Inv c a := by
  induction hr generalizing a0 with
  | refl => exact ⟨a0, h0⟩
  | step tid hs _ ih =>
    obtain ⟨a1, h1, -⟩ := h.step h0 hs
    exact ih h1

/-! ## Transfers to the fuel-indexed and executable machines

The obligations are stated on the fuel-free machine, which contains the
fuel-indexed one (`stepSemInf_of_stepSem`), so the fuel-indexed results are
corollaries and need no separate obligations. -/

/-- One step of the fuel-indexed semantic machine (`StepSem A fuel`). -/
theorem Obl.stepSem {A : Arch} {fuel : Nat} (h : L.Obl A) {tid : Nat} {c c' : Config I} {a : S}
    (hinv : L.Inv c a) (hs : StepSem A fuel tid c c') :
    ∃ a', L.Inv c' a' ∧ (L.AStep tid c c' a a' ∨ L.PStep tid c c' a a') :=
  h.step hinv (stepSemInf_of_stepSem hs)

/-- Every configuration reachable on the fuel-indexed semantic machine. -/
theorem Obl.reachSem {A : Arch} {fuel : Nat} (h : L.Obl A) {c0 c : Config I} {a0 : S}
    (h0 : L.Inv c0 a0) (hr : ReachableSem A fuel c0 c) : ∃ a, L.Inv c a :=
  h.reach h0 (ReachableSemInf.of_reachableSem hr)

/-- **The executable machine** (`succs`/`Reachable`), from an initial
configuration: `reachableSem_of_reachable'` (the `certify` bridge, via
`stepSemOfSuccs`) with `Config.init_bnd`. -/
theorem Obl.reach_succs [I.LawfulState] {A : Arch} {fuel : Nat} (h : L.Obl A) {states : List I.State}
    {initMem : List (Loc × Val)} {a0 : S} (h0 : L.Inv (Config.init states initMem) a0) {c : Config I}
    (hr : Reachable A fuel (Config.init states initMem) c) : ∃ a, L.Inv c a :=
  h.reachSem h0 (reachableSem_of_reachable' (Config.init_bnd states initMem) hr)

end RelLift

end Kraken.Promising.Lin
