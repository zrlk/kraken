/-
**hello.w on x86-64: aborts after the spawn at `hello_obligations`** (`Spike/Lib/X64HelloAssembly.lean`;
the twin of `Spike/Lib/HelloPostAbH.lean`):
its `tw_load`, `tw_step` and `post_abort` premises at `Tw := TwH Λ E AbT`
(`Spike/Lib/X64HelloPostAb.lean`), from `X64HelloPostAbW`'s at hello's data:

- `tw_load_hello`: `X64HelloPostAbW.tw_load` (`hw`: the program is `wideIn`,
  as `X64HelloMainG.hw_IH` gives at the placed output).
- `tw_step_hello`: `X64HelloPostAbW.tw_stepK` with the worker's facts read off
  `PT1h`'s `D.Wi` (`WCompatH.pt1`): `AbFacts` (`hab1W`) and no
  transfer site (`WCompatH.noSite`); `hcl`.
- `post_abort_hello`: `X64HelloPostAbW.post_abortK` with main off every abort
  site (`MSide.off` at `hPT0`, `hMμ`, as `X64WakeAssembly`'s `post_abort`) and
  `hab1W`; the witness is `post_wit`'s (`hwit`).

`AbT` is the worker's abort-write phase (at the instance `WriteAb.Ab lab`
and the dispatcher/stub pcs of `PrintGAb`), not `Pre1T`'s `Ab`.

Unlike AArch64, the program is an `asm : Asm` whose cells the load reads (`cellsOf asm`, not `textProgram`),
so `tw_load_hello`'s `hw` is on `cellsOf asm`; the rest is AArch64's at x86-64's `HelloCompat`.
-/
import Spike.Lib.X64HelloAssembly
import Spike.Lib.X64HelloPostAbW

namespace Spike.Lib.X64HelloPostAbH

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH PT1h WCompatH)
open Spike.Lib.X64HelloW1Store (NoWrite)
open Spike.Lib.X64HelloAssembly (HelloCompat)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloPostAb (TwH AbFacts)
open Scc.Cert.WideX64 (wideIn)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : X64WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isa.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {AbT : State → Prop}

/-- **`hello_obligations`' `tw_load` at `TwH`.** -/
theorem tw_load_hello (hw : ∀ cells, cellsOf asm = some cells → wideIn (cells.map (·.1)) = true) :
    ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → TwH Λ E AbT t0 [] :=
  X64HelloPostAbW.tw_load hw

/-- **`hello_obligations`' `tw_step` at `TwH`.** -/
theorem tw_step_hello (hKR : Q.KR = KRHE D r0 r1)
    (hC : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem)
    /- Hypothesis: the worker's states keep `AbT` but at a refused
    `write`, and are at an abort site only at `writeErr`, in `AbT`. True only
    under the worker/thread prologues' stack-limit hedge (else `scc_rt_grow`
    → `abort_stack`). Discharged together with that hedge in concrete-Z step. -/
    (hab1W : ∀ w s c fs, D.Wi w s c fs → AbFacts ((target (kernel 2) E).marks asm Λ) AbT s)
    /- Hypothesis: at `R1`'s `clone` one thread, the child out of
    `AbT`. -/
    (hcl : ∀ d s tid th stack tls, Q.R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (childAfter abi d.2 tid th stack tls).st) :
    ∀ tid t es t' s pre, Q.Rw Λ t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' →
      TwH Λ E AbT t pre → TwH Λ E AbT t' (pre ++ es) :=
  X64HelloPostAbW.tw_stepK hKR
    (fun w _ _ t1 s1 h => by
      rw [hC.1.pt1] at h; obtain ⟨_, _, hw⟩ := h.wi; exact hab1W w _ _ _ hw)
    (fun w _ _ t1 s1 h => by
      rw [hC.1.pt1] at h; obtain ⟨_, _, hw⟩ := h.wi; exact hC.1.noSite w _ _ _ hw) hcl

/-- **`hello_obligations`' `post_abort` at `TiPre Ab Ac ∧ TwH`.** -/
theorem post_abort_hello {Ab Ac : State → Prop} (hKR : Q.KR = KRHE D r0 r1) (hPT0 : Q.PT0 = X64WakeM0.PT0 M)
    (hMμ : M.μ = (target (kernel 2) E).marks asm Λ)
    /- Hypothesis, as at `tw_step_hello`: true only under the
    worker/thread prologues' stack-limit hedge (else `scc_rt_grow` →
    `abort_stack`). Discharged together with that hedge in concrete-Z
    step. -/
    (hab1W : ∀ w s c fs, D.Wi w s c fs → AbFacts ((target (kernel 2) E).marks asm Λ) AbT s)
    (hwit : ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
      ∀ tr t s tid es t' k, (srcS helloSrc arch).Reach (obs tr) s → Q.Post Λ t s →
        TiPre Ab Ac t tr ∧ TwH Λ E AbT t tr →
        (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
        ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
          AbortJustified B (srcS helloSrc arch) tr s i k := fun hC =>
  X64HelloPostAbW.post_abortK hKR
    (fun w _ _ t0 s0 h hl => by rw [hPT0] at h; exact hMμ ▸ M.off w _ _ (h.1.resolve_right hl))
    (fun w _ _ t1 s1 h => by
      rw [hC.1.pt1] at h; obtain ⟨_, _, hw⟩ := h.wi; exact hab1W w _ _ _ hw) hwit

/-- info: 'Spike.Lib.X64HelloPostAbH.post_abort_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_abort_hello

/-- info: 'Spike.Lib.X64HelloPostAbH.tw_step_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tw_step_hello

end Spike.Lib.X64HelloPostAbH

/-- info: 'Spike.Lib.X64HelloPostAbH.tw_load_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPostAbH.tw_load_hello
