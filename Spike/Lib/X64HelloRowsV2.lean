/-
**hello.w on x86-64: `HelloRowsW1` from the post-spawn abort lemmas** (the twin of `Spike/Lib/HelloRowsV2.lean`):
at the trace invariant `Tw := X64HelloPostAb.TwH Λ E AbT`, `HelloRowsW1`'s `tw_load`, `tw_step` and `post_abort`
are `X64HelloPostAbH`'s `tw_load_hello`, `tw_step_hello` and `post_abort_hello`; `post_wit` is the witness
(`hwit`), which `post_abort_hello` also reads.

The open inputs are carried as named premises: `hab1W` (the worker's abort facts), `hcl` (at `R1`'s `clone` one
thread, the child out of `AbT`), `hwit` (the witness). Further: the program is in the wide fragment (`hw`),
hello's `KR`/`PT0` (`hKR`, `hPT0`) and main's marks the target's (`hMμ`).

- `helloRowsW1_of`: the rows.

## Unlike AArch64

- The program is an `asm : Asm` whose cells the load reads, so `hw` is on `cellsOf asm` (AArch64 `textProgram`).
-/
import Spike.Lib.X64HelloRowsV1
import Spike.Lib.X64HelloPostAbH

namespace Spike.Lib.X64HelloRowsV2

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloW1Store (NoWrite)
open Spike.Lib.X64HelloRowsV1 (HelloRowsW1)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloPostAb (TwH AbFacts)
open Scc.Cert.WideX64 (wideIn)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : X64WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isa.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {Ab Ac AbT : State → Prop}

/-- **`HelloRowsW1` at `TwH`** from `X64HelloPostAbH`'s lemmas, the open inputs `hab1W`, `hcl` and `hwit`. -/
theorem helloRowsW1_of (hw : ∀ cells, cellsOf asm = some cells → wideIn (cells.map (·.1)) = true)
    (hKR : Q.KR = KRHE D r0 r1) (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hMμ : M.μ = (target (kernel 2) E).marks asm Λ)
    /- the worker's abort facts (as `X64HelloPostAbH.tw_step_hello`'s) -/
    (hab1W : ∀ w s c fs, D.Wi w s c fs → AbFacts ((target (kernel 2) E).marks asm Λ) AbT s)
    /- at `R1`'s `clone` one thread, the child out of `AbT` (as `X64HelloPostAbH.tw_step_hello`'s) -/
    (hcl : ∀ d s tid th stack tls, Q.R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (childAfter abi d.2 tid th stack tls).st)
    /- the witness (as `HelloRowsW.post_wit`) -/
    (hwit : ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac (TwH Λ E AbT) where
  post_abort := X64HelloPostAbH.post_abort_hello hKR hPT0 hMμ hab1W hwit
  post_wit := hwit
  tw_load := X64HelloPostAbH.tw_load_hello hw
  tw_step hC := X64HelloPostAbH.tw_step_hello hKR hC hab1W hcl

/-- info: 'Spike.Lib.X64HelloRowsV2.helloRowsW1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms helloRowsW1_of

end Spike.Lib.X64HelloRowsV2
