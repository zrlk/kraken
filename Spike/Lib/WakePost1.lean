/-
**wake.w on AArch64: the worker's steps after the spawn** (the worker half of `WakeObligations`: `worker_done`, `unpark_src`,
`post_step1`, and the worker's promise case `post_prom1`).

- `atSvc_atNop`: a thread at an `svc` is not at a `nop` (no transfer site).
- `step_texit`: **a step of thread 1 at an `exit` system call** is the
  kernel's `exit`: no event, the configuration unchanged but slot 1
  `exited` (no instruction or promise step at a system call, no `clone`,
  no transfer).
- `worker_done`: the `worker_done` obligation, from the two facts about
  the relation's data it needs (`TexitFacts`: at `atTexit` the worker is at
  an `exit` call; the kernel relation `KR` is kept by slot 1 exiting). The
  source stutters; `Inv2` reads the threads and memory only, which the
  `exit` keeps.
-/
import Spike.Lib.WakeA64

namespace Spike.Lib.WakePost1

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.WakeA64 Spike.Lib.WakeT1

/-! ## The worker's `exit` -/

/-- **A thread at an `svc` is not at a `nop`.** -/
theorem atSvc_atNop {s : State} (h : atSvc s = true) : atNop s = false := by
  unfold atSvc at h; unfold atNop
  split at h
  · rename_i hd; rw [hd]
  · cases h

/-- **A step of thread 1 at an `exit` system call** is the kernel's `exit`:
no event, slot 1 set to `exited`, nothing else changed. -/
theorem step_texit {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev} {t1 : Thread isaLSE2}
    (h1 : t.1.threads[tid]? = some t1) (hsys : abi.atSys t1.st = true) (hc : callOf abi t1 = some .exit)
    (hs : (machine (kernel 2)).Step μ tid t es t') : es = [] ∧ t' = (t.1, t.2.set tid .exited) := by
  cases hs with
  | instr _ hns _ _ => exact absurd ⟨t1, h1, hsys⟩ hns
  | spawn _ h =>
    obtain ⟨j, r, hsp, -⟩ := h
    unfold spawnStep at hsp
    erw [h1] at hsp
    simp only at hsp
    split at hsp
    · cases hsp
    · rw [hc] at hsp; cases hsp
  | sys _ h _ _ _ =>
    obtain ⟨p, hp, -⟩ := h
    unfold sysStep at hp
    erw [h1] at hp
    simp only at hp
    split at hp
    · cases hp
    rw [hc] at hp
    cases p with
    | byte rd => cases hp
    | abort k => cases hp
    | ret r =>
      simp only at hp
      split at hp
      · simp only [Option.some.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨rfl, rfl⟩
      · cases hp
  | xfer k _ _ h =>
    have hn : abi.atNop t1.st = false := atSvc_atNop hsys
    cases k with
    | take =>
      change takeStep abi tid t = some t' at h
      unfold takeStep at h
      erw [h1] at h
      simp only [hn, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
      cases h
    | release =>
      change releaseStep abi tid t = some t' at h
      unfold releaseStep at h
      erw [h1] at h
      simp only [hn, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
      cases h

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel}

/-- **What `worker_done` needs of the relation's data**: at `atTexit` the
worker is at an `exit` system call (the `texit` row's `svc` with
`x8 = 93`); the kernel relation is kept by slot 1 exiting (`kr_exit1`). -/
structure TexitFacts (Q : WakeRel) : Prop where
  call : ∀ t s, Q.atTexit t s →
    ∃ t1, t.1.threads[1]? = some t1 ∧ abi.atSys t1.st = true ∧ callOf abi t1 = some .exit
  kr_exit1 : ∀ w t s, Q.KR w t s → Q.atTexit t s → Q.KR w (t.1, t.2.set 1 .exited) s

/-- **The `worker_done` obligation**: at the worker's exit row the source
stutters and `Post` is kept. -/
theorem worker_done (F : TexitFacts Q) {μ : Marks} :
    ∀ t es t' s, Q.Post Λ t s → Q.atTexit t s → (machine (kernel 2)).Step μ 1 t es t' →
      ∃ s', (wakeS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  intro t es t' s hP hx hs
  obtain ⟨t1, h1, hsys, hc⟩ := F.call t s hx
  obtain ⟨rfl, rfl⟩ := step_texit h1 hsys hc hs
  obtain ⟨w, hI, hK⟩ := hP
  exact ⟨s, .refl s, w, hI, F.kr_exit1 w t s hK hx⟩

/-- `worker_done` has the type of the `WakeObligations` field. -/
example {B : Budget} {asm : String} {E : Entry} {Ti : Cfg → List Ev → Prop} (F : TexitFacts Q)
    (k : WakeObligations arch Λ B asm Q E Ti → Prop)
    (hk : ∀ O : WakeObligations arch Λ B asm Q E Ti, k O) (O : WakeObligations arch Λ B asm Q E Ti) :
    k { O with worker_done := worker_done F } := hk _

/-- info: 'Spike.Lib.WakePost1.worker_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms worker_done

end Spike.Lib.WakePost1
