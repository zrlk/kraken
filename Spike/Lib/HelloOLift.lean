/-
**hello.w's pre-spawn `O` with its source conjuncts** (the slot `X` of
`Spike.Lib.HelloO.R1OH`, filled as `WakeO.wake_O_at` fills wake's): the
base relation `R1H` strengthened by `NoObs` (`HelloNoObs.Pre1T.noObsH`,
from `HelloO.hello_hw`), `VPreH`, `VPreCH`, `VFlagH` and `VBufR` (`pre1T_vpreH`, `pre1T_vpreCH`, `pre1T_vflagH`,
`pre1T_vbufR`).

- `Pre1T.congr`: `Pre1T` at a pointwise equivalent relation;
- `XH d s`: `NoObs d s ∧ VPreH s ∧ VPreCH s ∧ VFlagH s ∧ VBufR s`;
- `liftH`: `HelloO.hello_O_at`'s lifter at `X := XH` (the lifters applied
  in order, the conjuncts reassociated by `Pre1T.congr`);
- `hello_O_X`, `hello_O_XE`: `Pre1T` at `R1OH … XH` at one entry and at
  every admissible entry.
-/
import Spike.Lib.HelloO
import Spike.Lib.HelloNoObs
import Spike.Lib.HelloVPre
import Spike.Lib.HelloVPreC
import Spike.Lib.HelloVFlag
import Spike.Lib.HelloVBuf

namespace Spike.Lib.HelloOLift

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.WakeT1 Spike.Lib.WakeA64
open Spike.Lib.WakePreTi (Pre1T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloO (ODataH OPremH R1H R1OH hello_O_at)
open Spike.Lib.WakeNoObs (NoObs)
open Spike.Lib.HelloVPre (VPreH pre1T_vpreH)
open Spike.Lib.HelloVPreC (VPreCH pre1T_vpreCH)
open Spike.Lib.HelloVFlag (VFlagH pre1T_vflagH)
open Spike.Lib.HelloVBuf (VBufR pre1T_vbufR)

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 R2 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop} {p : CoreTerm.Prog}

/-- **`Pre1T` at a pointwise equivalent relation.** -/
theorem congr (O : Pre1T arch Λ B asm E R1 Ab Ac p) (h : ∀ d s, R1 d s ↔ R2 d s) :
    Pre1T arch Λ B asm E R2 Ab Ac p where
  init d hd := by
    obtain ⟨s0, hi, hR⟩ := O.init d hd
    exact ⟨s0, hi, (h _ _).1 hR⟩
  step tid d es d' s hR hn hs := by
    obtain ⟨s', hr, hR', hn'⟩ := O.step tid d es d' s ((h _ _).2 hR) hn hs
    exact ⟨s', hr, (h _ _).1 hR', hn'⟩
  progress d s hR := O.progress d s ((h _ _).2 hR)
  progressClone d u s hR := O.progressClone d u s ((h _ _).2 hR)
  abort tr d s tid es d' k hr hR := O.abort tr d s tid es d' k hr ((h _ _).2 hR)
  wit d s hR := O.wit d s ((h _ _).2 hR)
  held d s hR := O.held d s ((h _ _).2 hR)
  ti0 := O.ti0
  tiStep tid d es d' s pre hR := O.tiStep tid d es d' s pre ((h _ _).2 hR)

end Pre1T

/-- **hello's source conjuncts before the spawn** (the slot `X` of
`R1OH`). -/
def XH (d : Cfg) (s : TermRun.Cfg) : Prop :=
  NoObs d s ∧ VPreH s ∧ VPreCH s ∧ VFlagH s ∧ VBufR s

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {Ab Ac : State → Prop} {D : ODataH}

/-- **The lifter at `XH`**: `noObsH` (from `hw`), then `VPreH`, `VPreCH`,
`VFlagH`, `VBufR`, reassociated into `R1H ∧ XH`. -/
theorem liftH {R1 : Cfg → TermRun.Cfg → Prop} (O : Pre1T arch Λ B asm E R1 Ab Ac helloSrc)
    (hw : ∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isaLSE2), R1 d s → d.2.exited = none →
      d.1.threads[tid]? = some t → abi.atSys t.st = true → ∀ buf n, Kernel.callOf abi t ≠ some (.write 1 buf n)) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ XH d s) Ab Ac helloSrc :=
  Pre1T.congr (pre1T_vbufR (pre1T_vflagH (pre1T_vpreCH (pre1T_vpreH
    (Spike.Lib.HelloNoObs.Pre1T.noObsH O hw)))))
    fun _ _ => ⟨fun ⟨⟨⟨⟨⟨hR, hN⟩, hV⟩, hC⟩, hF⟩, hB⟩ => ⟨hR, hN, hV, hC, hF, hB⟩,
      fun ⟨hR, hN, hV, hC, hF, hB⟩ => ⟨⟨⟨⟨⟨hR, hN⟩, hV⟩, hC⟩, hF⟩, hB⟩⟩

/-- **`Pre1T` at one entry with the source conjuncts**: `hello_O_at` at
`X := XH`, lifter `liftH`. -/
theorem hello_O_X (h : OPremH arch Λ B asm E Ab Ac D) :
    Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) D XH) Ab Ac helloSrc :=
  hello_O_at h liftH

/-- **`O` at every admissible entry with the source conjuncts.** -/
theorem hello_O_XE {D : Entry → ODataH} (h : ∀ E : Entry, E.Ok Λ → OPremH arch Λ B asm E Ab Ac (D E)) :
    ∀ E : Entry, E.Ok Λ →
      Pre1T arch Λ B asm E (R1OH arch Λ ((target (kernel 2) E).marks asm Λ) (D E) XH) Ab Ac helloSrc :=
  fun E hE => hello_O_X (h E hE)

/-- info: 'Spike.Lib.HelloOLift.hello_O_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello_O_X

end Spike.Lib.HelloOLift
