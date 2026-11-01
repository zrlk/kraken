/-
**hello.w: `HelloRowsW1` from row 5i's lemmas** (rows 5i wired): at the
trace invariant `Tw := HelloPostAb.TwH Λ E AbT`, `HelloRowsW1`'s `tw_load`,
`tw_step` and `post_abort` are `HelloPostAbH`'s `tw_load_hello`,
`tw_step_hello` and `post_abort_hello`; `post_wit` is the witness row
(`hwit`, row 5j-wit), which `post_abort_hello` also reads.

The open inputs are carried as named premises: `hab1W` (the worker's abort facts), `hcl` (at `R1`'s `clone` one
thread, the child out of `AbT`), `hwit` (row 5j-wit). Further: the program
is in the wide fragment (`hw`), hello's `KR`/`PT0` (`hKR`, `hPT0`) and
main's marks the target's (`hMμ`).

- `helloRowsW1_of`: the rows.
-/
import Spike.Lib.HelloRowsV1
import Spike.Lib.HelloPostAbH

namespace Spike.Lib.HelloRowsV2

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Handover
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloW1Store (NoWrite)
open Spike.Lib.HelloRowsV1 (HelloRowsW1)
open Spike.Lib.HelloKRE (KRHE)
open Spike.Lib.HelloPostAb (TwH AbFacts)
open Scc.Cert.WideA64 (wideIn)

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isaLSE2.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D} {Ab Ac AbT : State → Prop}

/-- **`HelloRowsW1` at `TwH`** from `HelloPostAbH`'s row-5i lemmas, the
open inputs `hab1W` (5i-hab1), `hcl` (5i-hcl) and `hwit` (5j-wit). -/
theorem helloRowsW1_of (hw : ∀ prog, (textProgram asm).toOption = some prog → wideIn prog = true)
    (hKR : Q.KR = KRHE D r0 r1) (hPT0 : Q.PT0 = WakeM0.PT0 M) (hMμ : M.μ = (target (kernel 2) E).marks asm Λ)
    /- row: 5i-hab1 (as `HelloPostAbH.tw_step_hello`'s). -/
    (hab1W : ∀ w s c fs, D.Wi w s c fs → AbFacts ((target (kernel 2) E).marks asm Λ) AbT s)
    /- row: 5i-hcl (as `HelloPostAbH.tw_step_hello`'s). -/
    (hcl : ∀ d s tid th stack tls, Q.R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ AbT (childAfter abi d.2 tid th stack tls).st)
    /- row: 5j-wit (as `HelloRowsW.post_wit`). -/
    (hwit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    HelloRowsW1 arch Λ B asm Q E D M AbW hcw hem Ab Ac (TwH Λ E AbT) where
  post_abort := HelloPostAbH.post_abort_hello hKR hPT0 hMμ hab1W hwit
  post_wit := hwit
  tw_load := HelloPostAbH.tw_load_hello hw
  tw_step hC := HelloPostAbH.tw_step_hello hKR hC hab1W hcl

/-- info: 'Spike.Lib.HelloRowsV2.helloRowsW1_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms helloRowsW1_of

end Spike.Lib.HelloRowsV2
