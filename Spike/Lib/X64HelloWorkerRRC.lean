/-
**hello.w's worker compatibility facts after the freeze** (x86-64; the part
of `Spike/Lib/HelloWorkerRR.lean` that does not read the worker side):

- `krh_permit`: `WCompatX.krp`'s congruence at `KRH` (the twin of
  `X64WakeKR.kr_permit`).
- `WCompatXH`, `hx_IR`: wake's `WCompatX` over `WSideH` (its fields do not
  read the worker side), closed at `helloQ` but for `Gc` (the flag store's
  value at `cT`, a premise as in `X64WakeAssembly.wCompatX_of`). `hx_IR` is
  `WCompatXH`'s producer; `X64HelloAssembly.HelloCompat` consumes it.

**Unlike AArch64** these three declarations sit in their own module (same namespace
`Spike.Lib.X64HelloWorkerRR` as the rest of the twin of `HelloWorkerRR`), so that
`X64HelloAssembly` does not wait on the worker side's placement (`helloDR`, `hC_IR`); the
statements are the AArch64 ones over x86-64's `X64HelloQ`, `X64HelloKRE` and `X64WakeM0`.
-/
import Spike.Lib.X64HelloQ
import Spike.Lib.X64WakeKRP

namespace Spike.Lib.X64HelloWorkerRR

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloQ (helloQ)
open Spike.Lib.X64HelloWriteK (KRH)

/-- **`WCompatX.krp` at `KRH`**: the kernel relation is stable under a
worker step that keeps the kernel state, main's target thread and the
source trace and sets main's source permit. -/
theorem krh_permit {ι : Type} {r0 r1 : ι → Range} :
    ∀ w (t t' : Cfg) (s s' : TermRun.Cfg) (s0 : TermRun.TTh) (p : Option Nat), KRH r0 r1 w t s → t'.2 = t.2 →
      t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
      SrcSem.traceOf s' = SrcSem.traceOf s → KRH r0 r1 w t' s' := by
  intro w t t' s s' s0 p ⟨hn, h0, h1, hh, hm, htr⟩ ht _ hs0 hs0' hs'
  rw [KRH, ht]
  exact ⟨hn, h0, h1, hh, fun hx s0' h => by rw [hs0'] at h; cases h; exact hm hx s0 hs0, hs' ▸ htr⟩

/-- **The worker's compatibility facts after the `WCompat` freeze, over
`WSideH`**: `X64WakeW1.WCompatX`'s fields (none reads the worker side). -/
structure WCompatXH (Q : WakeRel) (D : WSideH Q.ι) : Prop where
  /-- The worker's flag store value `1` is a `G` value at `cT`. -/
  Gc : ∀ w, Q.G w (Q.C w).cT 1
  /-- (as `X64WakeW1.WCompatX.ownConst1`) The worker's owned words after the spawn do not depend on its state ... -/
  ownConst1 : ∀ w s s', Q.own w 1 s' [] = Q.own w 1 s []
  /-- ... and it never writes one as the runtime's at its empty stack (`X64WakeW1.WCompatX.ownMp1`). -/
  ownMp1 : ∀ w s L v, (L, v) ∈ Q.own w 1 s [] → ¬ (D.ms w []).mp L true
  /-- main's source thread has no promise after the spawn. -/
  sp0 : ∀ w tm sm t0 s0, Q.PT0 w tm sm t0 s0 → s0.promises = []
  /-- main's per-thread relation is stable under a worker step that also
  sets main's source permit. -/
  pt0p : ∀ w tm sm t0 s0 tm' sm' (p : Option Nat), Q.PT0 w tm sm t0 s0 →
    X64WakeW1.W1Mem (Q.P w) (Q.C w).cS tm sm tm' sm' → Q.PT0 w tm' sm' t0 { s0 with permit := p }
  /-- The kernel relation is stable under a worker step, with no byte of the
  worker's `write` out, that keeps the kernel state, main's target thread and
  the source trace and sets main's source permit, the worker after it in
  `Wi` (`Lk`'s reverse conjunct). -/
  krp : ∀ w t t' s s' (s0 : TermRun.TTh) (p : Option Nat), Q.KR w t s → t.2.wr 1 = 0 → t'.2 = t.2 →
    t'.1.threads[0]? = t.1.threads[0]? → s.ths[0]? = some s0 → s'.ths[0]? = some { s0 with permit := p } →
    s'.trace = s.trace →
    (∀ t1 s1, t'.1.threads[1]? = some t1 → s'.ths[1]? = some s1 → D.Wi w t1.st (Ctl.of s1) s1.stack) →
    Q.KR w t' s'

section Compat

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {SR : ι → SpawnRec}
  {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc} {Pa : ι → Inv2Params isa}
  {G : ι → Loc → Val → Prop} {passT : State → Prop} {M : X64WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range}

/-- **`WCompatXH`** at `helloQ` (any worker side whose owned words at its empty stack do not depend on its state,
`hconst1`, and are none of its runtime writes, `hmp1`); open: `Gc`. -/
theorem hx_IR (hconst1 : ∀ w s s', (D.ms w []).own s' = (D.ms w []).own s)
    (hmp1 : ∀ w s L v, (L, v) ∈ (D.ms w []).own s → ¬ (D.ms w []).mp L true) (Gc : ∀ w, G w (cT w) 1) :
    WCompatXH (helloQ arch R1 ι SR cT cS pT Pa G passT M D r0 r1) D where
  Gc := Gc
  ownConst1 := hconst1
  ownMp1 := hmp1
  sp0 _ tm sm _ _ h := X64WakeM0.PT0.promises_nil (tm := tm) (sm := sm) h
  pt0p _ tm sm _ _ tm' sm' p h _ := X64WakeM0.pt0_permit (tm := tm) (sm := sm) (tm' := tm') (sm' := sm') p h
  krp w t t' s s' s0 p h hw a b c d e hW :=
    ⟨krh_permit w t t' s s' s0 p h.1 a b c d (by simp only [SrcSem.traceOf, e]),
      X64HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩

/-- `WCompatXH` is inhabited: at the trivial `G` the flag premise holds, at a worker side owning no word. -/
example (hown1 : ∀ w s, (D.ms w []).own s = []) :
    WCompatXH (helloQ arch R1 ι SR cT cS pT Pa (fun _ _ _ => True) passT M D r0 r1) D :=
  hx_IR (fun w s s' => (hown1 w s').trans (hown1 w s).symm)
    (fun w s L v h => absurd (hown1 w s ▸ h : (L, v) ∈ ([] : List (Loc × Val))) List.not_mem_nil) fun _ => trivial

end Compat

/-- info: 'Spike.Lib.X64HelloWorkerRR.hx_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hx_IR

end Spike.Lib.X64HelloWorkerRR

/-- info: 'Spike.Lib.X64HelloWorkerRR.krh_permit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerRR.krh_permit
