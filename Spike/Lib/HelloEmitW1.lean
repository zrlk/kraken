/-
**hello.w on AArch64: `print`'s `write` keeps `Post`** (C4, row
B8-gen1-EmitStepP, design (a′), step S5). The worker at its
`write(1, buf, n)`: a byte pick by `HelloEmitStep.post_byteH`/`post_byteE`,
a return by `EmitRetP` (S4, `HelloEmitRet`), no abort pick.

- `EmitRetP`: a return of the worker's `write(1, …)` keeps `Post` (S4's
  statement, at the common parts); `emitRetP_of`: from
  `HelloEmitRet.post_retC`.
- `write1StepP_of`: `HelloStep1Sys.Write1StepP` (from `PartsH` in the print
  phase).
- `Write1StepE`, `write1StepE_of`: every step of the worker from `PartsE`
  off its invariant (mid-`write`) keeps `Post`.
- `step_twriteC`: a step at a `write` call is a `sysStep` with `CertAfter`;
  `emitStep1_of`: `HelloStep1.EmitStep1` from `Write1StepE`.
-/
import Spike.Lib.HelloEmitStep
import Spike.Lib.HelloEmitRet
import Spike.Lib.HelloStep1Sys

namespace Spike.Lib.HelloEmitW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PartsH PrintPh WCompatH)
open Spike.Lib.HelloEmitPh (PartsE PT1hE)
open Spike.Lib.HelloEmitShapeF (EmitShapeF)
open Spike.Lib.HelloEmitPost (PartsC)
open Spike.Lib.HelloEmitStep (ByteFrz post_byteH post_byteE)
open Spike.Lib.HelloByteOutP (ByteOutP)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.HelloStep1Sys (Write1StepP)

/-- (S4, `HelloEmitRet.post_retC`) **A return of the worker's
`write(1, buf, n)` keeps `Post`**: at the common parts with the worker in
its invariant at some control and, with no byte out, at the source worker's
control. -/
def EmitRetP (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc buf n (r : BitVec 64) es t', PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc →
    SrcSem.mainExit s = [] → (∃ c fs, D.Wi w t1.st c fs) → abi.atSys t1.st = true →
    (t.2.wr 1 = 0 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n) →
    sysStep abi Arch.armv8 1 t (.ret r) = some (es, t') → CertAfter abi Arch.armv8 μ 1 t' →
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **Every step of the worker mid-`write` keeps `Post`**: from `PartsE`
off the worker's invariant. -/
def Write1StepE (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → HelloStep1.PrivAt Λ t →
    ¬ D.Wi w t1.st (Ctl.of s1) s1.stack → SrcSem.mainExit s = [] → (machine (kernel 2)).Step μ 1 t es t' →
    CertAfter abi Arch.armv8 μ 1 t' → ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **No abort pick at a `write`** (`sysStep` aborts at `exit_group` only). -/
theorem sysStep_write_abort {A : Arch} {tid : Nat} {c : Cfg} {k : AbortKind} {t : Thread isaLSE2}
    {fd buf n : Nat} (ht : c.1.threads[tid]? = some t) (hc : callOf abi t = some (.write fd buf n)) {x} :
    sysStep abi A tid c (.abort k) ≠ some x := by
  intro h
  unfold sysStep at h
  rw [ht] at h
  simp only at h
  split at h
  · cases h
  rw [hc] at h
  simp at h

/-- **A step of thread `tid` at a `write` system call** is a `sysStep`
with `CertAfter` (`A64HelloWriteK.step_twrite`'s proof, keeping the latter). -/
theorem step_twriteC {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev}
    {t1 : Thread isaLSE2} {fd buf n : Nat} (h1 : t.1.threads[tid]? = some t1) (hsys : abi.atSys t1.st = true)
    (hc : callOf abi t1 = some (.write fd buf n)) (hs : (machine (kernel 2)).Step μ tid t es t') :
    ∃ p, sysStep abi Arch.armv8 tid t p = some (es, t') ∧ CertAfter abi Arch.armv8 μ tid t' := by
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
    obtain ⟨p, hp, hca⟩ := h
    exact ⟨p, hp, hca⟩
  | xfer k _ _ h =>
    have hn : abi.atNop t1.st = false := WakePost1.atSvc_atNop hsys
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

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isaLSE2.State → Prop} {r0 r1 : Q.ι → Range}

/-- **`EmitRetP` by `HelloEmitRet.post_retC`.** -/
theorem emitRetP_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hES : EmitShapeF D) (hown : Q.own = WakeOwn.wakeOwn)
    (hNP : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 1) 1 t mem → t.prom = []) :
    EmitRetP Q D μ Λ arch :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hex hW hat hWi0 hd hs hca =>
    HelloEmitRet.post_retC hC hKR hpt1 hES hown hNP h hex hW hat hWi0 hd hs hca

/-- **`print`'s `write` to fd 1 keeps `Post`** (`Write1StepP`): a byte pick
by `post_byteH`, a return by `EmitRetP`; `sysStep` takes no abort pick. -/
theorem write1StepP_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hown : Q.own = WakeOwn.wakeOwn) (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w))
    (hES : EmitShapeF D) (hRet : EmitRetP Q D μ Λ arch) : Write1StepP Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' p buf n h ⟨_, hE, hpk⟩ hP hex hat hc _ hs hca
  cases p with
  | byte rd => exact post_byteH hC hKR hpt1 hlbl hfz hpk hE hown hbo hES h hP hex hat hc hs hca
  | ret r =>
    exact hRet w t s t0 t1 s0 s1 ts tp sp oc buf n r es t' (HelloEmitPost.PartsH.toC hC h hP) hex
      ⟨_, _, h.pt1.1⟩ hat (fun _ => h.pt1.1) hc hs hca
  | abort k => exact absurd hs (sysStep_write_abort (by rw [h.th]; rfl) hc)

/-- **Every step of the worker mid-`write` keeps `Post`** (`Write1StepE`):
the worker is at its `write(1, …)` (`EmitPh`), so the step is a system
call (`A64HelloWriteK.step_twrite`): a byte pick by `post_byteE`, a return
by `EmitRetP` (bytes out by the link's converse), no abort pick. -/
theorem write1StepE_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hown : Q.own = WakeOwn.wakeOwn) (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w))
    (hES : EmitShapeF D) (hRet : EmitRetP Q D μ Λ arch) : Write1StepE Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' h ⟨_, hE, hpk⟩ hn hex hst hca
  obtain ⟨-, hat, ⟨buf, n, hd⟩, -⟩ := h.pt1
  obtain ⟨p, hs⟩ := A64HelloWriteK.step_twrite h.t1_get hat hd hst
  cases p with
  | byte rd => exact post_byteE hC hKR hpt1 hlbl hfz hpk hE hown hbo hES h hn hex hd hs hca
  | ret r =>
    have hk := h.kr
    rw [hKR] at hk
    have hp := hk.2.2 t1 s1 h.t1_get h.s1_get hn
    exact hRet w t s t0 t1 s0 s1 ts tp sp oc buf n r es t' (HelloEmitPost.PartsE.toC h) hex h.pt1.1 hat
      (fun h0 => absurd hp (by rw [h0]; exact Nat.lt_irrefl 0)) hd hs hca
  | abort k => exact absurd hs (sysStep_write_abort h.t1_get hd)

/-- **`HelloStep1.EmitStep1` from `Write1StepE`** (row B8-W1E): main's
source is off its exit while the process runs (`hml`, as
`HelloStep1D.printStep1_of`'s), and the step at the worker's `write` is a
`sysStep` with `CertAfter` (`step_twriteC`). -/
theorem emitStep1_of (hpt1 : Q.PT1 = PT1hE D) (hwe : Write1StepE Q D μ Λ arch)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = []) :
    HelloStep1.EmitStep1 Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' h hpk hn hs
  have hex := hml t s (h.post hpt1) hs.runs.2.1
  obtain ⟨-, hat, ⟨buf, n, hd⟩, -⟩ := h.pt1
  obtain ⟨-, -, hca⟩ := step_twriteC h.t1_get hat hd hs
  exact hwe w t s t0 t1 s0 s1 ts tp sp oc es t' h hpk hn hex hs hca

/-- info: 'Spike.Lib.HelloEmitW1.write1StepP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write1StepP_of

/-- info: 'Spike.Lib.HelloEmitW1.write1StepE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write1StepE_of

/-- info: 'Spike.Lib.HelloEmitW1.emitRetP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emitRetP_of

/-- info: 'Spike.Lib.HelloEmitW1.emitStep1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emitStep1_of

end Spike.Lib.HelloEmitW1
