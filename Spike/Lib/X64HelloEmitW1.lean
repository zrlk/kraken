/-
**hello.w on x86-64: `print`'s `write` keeps `Post`** (the twin of
`Spike/Lib/HelloEmitW1.lean`). The worker at its
`write(1, buf, n)`: a byte pick by `X64HelloEmitStep.post_byteH`/`post_byteE`,
a return by `EmitRetP` (`X64HelloEmitRet`), no abort pick.

- `EmitRetP`: a return of the worker's `write(1, …)` keeps `Post` (at the
  common parts); `emitRetP_of`: from
  `X64HelloEmitRet.post_retC`.
- `write1StepP_of`: `X64HelloStep1Sys.Write1StepP` (from `PartsH` in the print
  phase).
- `Write1StepE`, `write1StepE_of`: every step of the worker from `PartsE`
  off its invariant (mid-`write`) keeps `Post`.
- `step_twriteC`: a step at a `write` call is a `sysStep` with `CertAfter`;
  `emitStep1_of`: `X64HelloStep1.EmitStep1` from `Write1StepE`.

## Differences from the AArch64 version

- The target threads are over `X64.isa` and the kernel's architecture is `Arch.tso` (AArch64: `isaLSE2`,
  `Arch.armv8`); the runtime facts are `X64WakeA64`'s and the source, worker side, phases and kernel relation are
  the x86-64 twins (`X64HelloSrc`, `X64HelloW1`, `X64HelloEmitPh`, `X64HelloEmitPost`, `X64HelloKRE`,
  `X64HelloWriteK`, `X64HelloStep1`, `X64HelloStep1Sys`; a `syscall` is off the transfer sites by
  `X64WakePost1.atSvc_atNop`). The statements and proofs are otherwise the AArch64 ones.
-/
import Spike.Lib.X64HelloEmitStep
import Spike.Lib.X64HelloEmitRet
import Spike.Lib.X64HelloStep1Sys
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloEmitW1

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH PartsH PrintPh WCompatH)
open Spike.Lib.X64HelloEmitPh (PartsE PT1hE)
open Spike.Lib.X64HelloEmitShapeF (EmitShapeF)
open Spike.Lib.X64HelloEmitPost (PartsC)
open Spike.Lib.X64HelloEmitStep (ByteFrz post_byteH post_byteE)
open Spike.Lib.X64HelloByteOutP (ByteOutP)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloStep1Sys (Write1StepP)

/-- (`X64HelloEmitRet.post_retC`) **A return of the worker's
`write(1, buf, n)` keeps `Post`**: at the common parts with the worker in
its invariant at some control and, with no byte out, at the source worker's
control. -/
def EmitRetP (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc buf n (r : BitVec 64) es t', PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc →
    SrcSem.mainExit s = [] → (∃ c fs, D.Wi w t1.st c fs) → abi.atSys t1.st = true →
    (t.2.wr 1 = 0 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n) →
    sysStep abi Arch.tso 1 t (.ret r) = some (es, t') → CertAfter abi Arch.tso μ 1 t' →
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **Every step of the worker mid-`write` keeps `Post`**: from `PartsE`
off the worker's invariant. -/
def Write1StepE (Q : WakeRel) (D : WSideH Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) (arch : WeakMem.Arch) : Prop :=
  ∀ w t s t0 t1 s0 s1 ts tp sp oc es t', PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc → X64HelloStep1.PrivAt Λ t →
    ¬ D.Wi w t1.st (Ctl.of s1) s1.stack → SrcSem.mainExit s = [] → (machine (kernel 2)).Step μ 1 t es t' →
    CertAfter abi Arch.tso μ 1 t' → ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s'

/-- **No abort pick at a `write`** (`sysStep` aborts at `exit_group` only). -/
theorem sysStep_write_abort {A : Arch} {tid : Nat} {c : Cfg} {k : AbortKind} {t : Thread isa}
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
with `CertAfter` (`X64HelloWriteK.step_twrite`'s proof, keeping the latter). -/
theorem step_twriteC {μ : Marks} {tid : Nat} {t t' : (machine (kernel 2)).Cfg} {es : List Ev}
    {t1 : Thread isa} {fd buf n : Nat} (h1 : t.1.threads[tid]? = some t1) (hsys : abi.atSys t1.st = true)
    (hc : callOf abi t1 = some (.write fd buf n)) (hs : (machine (kernel 2)).Step μ tid t es t') :
    ∃ p, sysStep abi Arch.tso tid t p = some (es, t') ∧ CertAfter abi Arch.tso μ tid t' := by
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
    have hn : abi.atNop t1.st = false := X64WakePost1.atSvc_atNop hsys
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
  {AbW : isa.State → Prop} {r0 r1 : Q.ι → Range}

/-- **`EmitRetP` by `X64HelloEmitRet.post_retC`.** -/
theorem emitRetP_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hES : EmitShapeF D) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hNP : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = []) :
    EmitRetP Q D μ Λ arch :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hex hW hat hWi0 hd hs hca =>
    X64HelloEmitRet.post_retC hC hKR hpt1 hES hown hNP h hex hW hat hWi0 hd hs hca

/-- **`print`'s `write` to fd 1 keeps `Post`** (`Write1StepP`): a byte pick
by `post_byteH`, a return by `EmitRetP`; `sysStep` takes no abort pick. -/
theorem write1StepP_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hown : X64HelloOwn1.Own1H Q D Λ) (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w))
    (hES : EmitShapeF D) (hRet : EmitRetP Q D μ Λ arch) : Write1StepP Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' p buf n h ⟨_, hE, hpk⟩ hP hex hat hc _ hs hca
  cases p with
  | byte rd => exact post_byteH hC hKR hpt1 hlbl hfz hpk hE hown hbo hES h hP hex hat hc hs hca
  | ret r =>
    exact hRet w t s t0 t1 s0 s1 ts tp sp oc buf n r es t' (X64HelloEmitPost.PartsH.toC hC h hP) hex
      ⟨_, _, h.pt1.1⟩ hat (fun _ => h.pt1.1) hc hs hca
  | abort k => exact absurd hs (sysStep_write_abort (by rw [h.th]; rfl) hc)

/-- **Every step of the worker mid-`write` keeps `Post`** (`Write1StepE`):
the worker is at its `write(1, …)` (`EmitPh`), so the step is a system
call (`X64HelloWriteK.step_twrite`): a byte pick by `post_byteE`, a return
by `EmitRetP` (bytes out by the link's converse), no abort pick. -/
theorem write1StepE_of (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (hpt1 : Q.PT1 = PT1hE D)
    (hlbl : ∀ w, D.lbl w = (Q.SR w).lbl) (hfz : ByteFrz Q D Λ)
    (hown : X64HelloOwn1.Own1H Q D Λ) (hbo : ∀ w fs, (D.ms w fs).bo = ByteOutP helloSrc (D.lbl w))
    (hES : EmitShapeF D) (hRet : EmitRetP Q D μ Λ arch) : Write1StepE Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' h ⟨_, hE, hpk⟩ hn hex hst hca
  obtain ⟨-, hat, ⟨buf, n, hd⟩, -⟩ := h.pt1
  obtain ⟨p, hs⟩ := X64HelloWriteK.step_twrite h.t1_get hat hd hst
  cases p with
  | byte rd => exact post_byteE hC hKR hpt1 hlbl hfz hpk hE hown hbo hES h hn hex hd hs hca
  | ret r =>
    have hk := h.kr
    rw [hKR] at hk
    have hp := hk.2.2 t1 s1 h.t1_get h.s1_get hn
    exact hRet w t s t0 t1 s0 s1 ts tp sp oc buf n r es t' (X64HelloEmitPost.PartsE.toC h) hex h.pt1.1 hat
      (fun h0 => absurd hp (by rw [h0]; exact Nat.lt_irrefl 0)) hd hs hca
  | abort k => exact absurd hs (sysStep_write_abort h.t1_get hd)

/-- **`X64HelloStep1.EmitStep1` from `Write1StepE`**: main's
source is off its exit while the process runs (`hml`, as
`X64HelloStep1D.printStep1_of`'s), and the step at the worker's `write` is a
`sysStep` with `CertAfter` (`step_twriteC`). -/
theorem emitStep1_of (hpt1 : Q.PT1 = PT1hE D) (hwe : Write1StepE Q D μ Λ arch)
    (hml : ∀ t s, Q.Post Λ t s → t.2.exited = none → SrcSem.mainExit s = []) :
    X64HelloStep1.EmitStep1 Q D μ Λ arch := by
  intro w t s t0 t1 s0 s1 ts tp sp oc es t' h hpk hn hs
  have hex := hml t s (h.post hpt1) hs.runs.2.1
  obtain ⟨-, hat, ⟨buf, n, hd⟩, -⟩ := h.pt1
  obtain ⟨-, -, hca⟩ := step_twriteC h.t1_get hat hd hs
  exact hwe w t s t0 t1 s0 s1 ts tp sp oc es t' h hpk hn hex hs hca

/-- info: 'Spike.Lib.X64HelloEmitW1.write1StepP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write1StepP_of

/-- info: 'Spike.Lib.X64HelloEmitW1.write1StepE_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms write1StepE_of

/-- info: 'Spike.Lib.X64HelloEmitW1.emitRetP_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emitRetP_of

/-- info: 'Spike.Lib.X64HelloEmitW1.emitStep1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms emitStep1_of

end Spike.Lib.X64HelloEmitW1
