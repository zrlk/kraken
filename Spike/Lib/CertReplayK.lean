/-
**The solo projection across a system-call step of another thread**
(`certSem_kframe`).

`Kernel.certSem K A μ x tid` reads the kernel state `x` only through the solo
configuration (`Kernel.solo`), which overwrites `tid`'s slot and `exited` and
keeps the slot count, the held ranges, the pool and its bytes. A system-call
step (`Kernel.sysStep`) of any thread changes only one slot and `exited`
(`sysStep_kframe`), so the certification semantics of every thread is the same
before and after it.

- `KRel`: two kernel states that agree on the slot of `tid`, `exited`, the
  held ranges, the pool and its bytes; `sysStep_krel`, `xferStep_krel`: the
  kernel's steps of `tid` read nothing else (the same events and
  configuration).
- `KFrame`: the same slot count, held ranges, pool and pool bytes;
  `soloExec_kframe`, `certSem_kframe`: the solo projection reads nothing else.
- `sysStep_kframe`: a system-call step leaves its kernel state in `KFrame`.
-/
import Scc.Sem.CertLift

namespace Spike.Lib.CertReplay

open Kraken Kraken.Promising Scc.Sem Scc.Sem.Kernel

variable {I : ISA} {K : Abi I}

/-! ## The kernel's steps of `tid` read little of the kernel state -/

/-- Kernel states that agree on what a step of `tid` reads. -/
def KRel (tid : Nat) (y y' : KState) : Prop :=
  y'.slots[tid]? = y.slots[tid]? ∧ y'.exited = y.exited ∧ y'.held = y.held ∧ y'.pmem = y.pmem ∧ y'.pool = y.pool

theorem KRel.runs {tid : Nat} {y y' : KState} (h : KRel tid y y') : y'.runs tid = y.runs tid := by
  simp only [KState.runs, h.1]

theorem KRel.wr {tid : Nat} {y y' : KState} (h : KRel tid y y') : y'.wr tid = y.wr tid := by
  simp only [KState.wr, h.1]

/-- **A system-call step of `tid` reads only `KRel`'s parts**: the same
events and configuration. -/
theorem sysStep_krel {A : Arch} {tid : Nat} {c1 : Config I} {y y' : KState} (h : KRel tid y y') (p : Pick) :
    (sysStep K A tid (c1, y') p).map (fun q => (q.1, q.2.1)) =
      (sysStep K A tid (c1, y) p).map (fun q => (q.1, q.2.1)) := by
  unfold sysStep
  cases c1.threads[tid]? with
  | none => rfl
  | some t =>
    have hr : ready K tid (c1, y') t = ready K tid (c1, y) t := by
      simp only [ready, h.runs, h.2.1]
    have hw : y'.wr tid = y.wr tid := h.wr
    simp only [hr, hw]
    split
    · rfl
    · split <;> (try simp only [back]) <;> (repeat' split) <;> simp_all [Function.comp_def]

/-- **A transfer of `tid` reads only `KRel`'s parts** (and the memory): the
same configuration. -/
theorem xferStep_krel {k : XferKind} {tid : Nat} {c1 : Config I} {y y' : KState} (h : KRel tid y y') :
    (xferStep K k tid (c1, y')).map (·.1) = (xferStep K k tid (c1, y)).map (·.1) := by
  have hru := h.runs
  obtain ⟨-, he, hh, hm, hp⟩ := h
  cases k
  · show (takeStep K tid (c1, y')).map (·.1) = (takeStep K tid (c1, y)).map (·.1)
    unfold takeStep
    cases c1.threads[tid]? with
    | none => rfl
    | some t =>
      have hf : fresh (c1, y') (siteRange K t.st) = fresh (c1, y) (siteRange K t.st) := by
        simp only [fresh, hh, hp]
      simp only [hf, he, hm, hru]
      split <;> simp_all
  · show (releaseStep K tid (c1, y')).map (·.1) = (releaseStep K tid (c1, y)).map (·.1)
    unfold releaseStep
    cases c1.threads[tid]? with
    | none => rfl
    | some t =>
      simp only [he, hh, hru]
      split <;> simp_all

/-! ## The solo projection reads little of the kernel state -/

/-- Kernel states with the same slot count, held ranges, pool and pool
bytes. -/
def KFrame (x x' : KState) : Prop :=
  x'.slots.size = x.slots.size ∧ x'.held = x.held ∧ x'.pmem = x.pmem ∧ x'.pool = x.pool

theorem KFrame.refl (x : KState) : KFrame x x := ⟨rfl, rfl, rfl, rfl⟩

/-- The solo configurations of `KFrame` kernel states: the same threads and
memory, kernel states in `KRel`. -/
theorem solo_kframe {site : Option XferKind} {x x' : KState} (hx : KFrame x x') (tid : Nat) (s : I.State) :
    (solo K site x' tid s).1 = (solo K site x tid s).1 ∧
      KRel tid (solo K site x tid s).2 (solo K site x' tid s).2 := by
  obtain ⟨hs, hh, hm, hp⟩ := hx
  refine ⟨by simp only [solo, hs], ?_, rfl, ?_, hm, hp⟩
  · simp only [solo, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hs, ite_true]
  · simp only [solo, soloHeld, hh]

/-- **The solo projection is the same at `KFrame` kernel states.** -/
theorem soloExec_kframe {A : Arch} {μ : Marks} {x x' : KState} (hx : KFrame x x') (tid : Nat) (s : I.State) :
    soloExec K A μ x' tid s = soloExec K A μ x tid s := by
  unfold soloExec
  split
  · rename_i k _
    obtain ⟨h1, h2⟩ := solo_kframe (K := K) (site := some k) hx tid s
    have e : solo K (some k) x' tid s = ((solo K (some k) x tid s).1, (solo K (some k) x' tid s).2) := by
      rw [← h1]
    rw [e, bind_stOf_congr (xferStep_krel h2)]
  · split
    · obtain ⟨h1, h2⟩ := solo_kframe (K := K) (site := none) hx tid s
      have e : solo K none x' tid s = ((solo K none x tid s).1, (solo K none x' tid s).2) := by
        rw [← h1]
      have hr : ∀ r : BitVec 64,
          (sysStep K A tid (solo K none x' tid s) (.ret r)).bind (fun q => stOf tid q.2) =
            (sysStep K A tid (solo K none x tid s) (.ret r)).bind (fun q => stOf tid q.2) := by
        intro r
        have hc := sysStep_krel (K := K) (A := A) (c1 := (solo K none x tid s).1) h2 (.ret r)
        rw [e]
        revert hc
        generalize sysStep K A tid ((solo K none x tid s).1, (solo K none x' tid s).2) (.ret r) = o'
        generalize sysStep K A tid (solo K none x tid s) (.ret r) = o
        cases o <;> cases o' <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq, Option.bind_none, Option.bind_some, imp_self, false_implies]
        rename_i a b
        obtain ⟨es, c, z⟩ := a
        obtain ⟨es', c', z'⟩ := b
        intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        rfl
      dsimp only
      rw [show (fun r : BitVec 64 => (sysStep K A tid (solo K none x' tid s) (.ret r)).bind
            (fun q => stOf tid q.2)) =
          (fun r : BitVec 64 => (sysStep K A tid (solo K none x tid s) (.ret r)).bind
            (fun q => stOf tid q.2)) from funext hr]
    · rfl

/-- **`certSem` is the same at `KFrame` kernel states.** -/
theorem certSem_kframe {A : Arch} {μ : Marks} {x x' : KState} (hx : KFrame x x') (tid : Nat) :
    certSem K A μ x' tid = certSem K A μ x tid := by
  unfold certSem
  congr 1
  funext s
  exact soloExec_kframe hx tid s

/-! ## A system-call step keeps `KFrame` -/

theorem KFrame.set (x : KState) (tid : Nat) (s : Slot) : KFrame x (x.set tid s) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [KState.set, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

theorem KFrame.exited (x : KState) (e : Option Outcome) : KFrame x { x with exited := e } := ⟨rfl, rfl, rfl, rfl⟩

/-- **A system-call step keeps the slot count, the held ranges, the pool and
its bytes.** -/
theorem sysStep_kframe {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : KFrame c.2 c'.2 := by
  have hback : ∀ (u : Thread I) r x es', KFrame c.2 x → back K tid c u r x es' = some (es, c') →
      KFrame c.2 c'.2 := by
    intro u r x es' hx hb
    simp only [back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact hx
  unfold sysStep at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | exact hback _ _ _ _ (KFrame.refl _) h
    | exact hback _ _ _ _ (KFrame.set _ _ _) h
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       first | exact KFrame.set _ _ _ | exact KFrame.exited _ _)
    | (simp only at h
       repeat' split at h
       all_goals first
         | (simp at h; done)
         | exact hback _ _ _ _ (KFrame.refl _) h
         | exact hback _ _ _ _ (KFrame.set _ _ _) h
         | (simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            first | exact KFrame.set _ _ _ | exact KFrame.exited _ _)
         | (obtain ⟨⟨b, t'⟩, -, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨-, rfl⟩ := he
            exact KFrame.set _ _ _))

/-- info: 'Spike.Lib.CertReplay.certSem_kframe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certSem_kframe

/-- info: 'Spike.Lib.CertReplay.sysStep_kframe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sysStep_kframe

end Spike.Lib.CertReplay
