/-
**hello.w's start glue facts** (x86-64; twin of
`Spike/Lib/A64HelloStartGlue.lean`, the hello twin of `X64WakeStartGlue` /
`X64WakeX0`): `W0`'s per-state facts at hello, the parameter `X0` of
`WakeWf.W0` under which `HelloPh.StartWf.startEWP_W0SH` and
`HelloPh.MainWf`'s pre-main obligations are stated, so that any invariant
inside `W0` owes `H0StmtH`'s clone clause, `H0TakeH` and `H0TakeOwnH`
(`X64HelloWcInv3`).

Most of wake's glue is layout-generic and is reused as is (no hello copy):
`WakePh.StartGlue.hmemB_of_wordsNone`, `hcellB_of_wordsNone`. This file has
the pieces that are fixed to hello's program:

- `X0WH L a`: `W0`'s per-state facts at hello (wake's `X0W` at
  `clonePcH`): off the clone's pc; at the take pc `a`, the site's range
  main's stack `r0Of`, not in private memory.
- `x0WH_of_freeNH`: `X0WH` at a free pc (`StartWf`'s `hX0`), the take pc
  the site's.
- `x0WH_inv`, `noCloneH_of`, `h0TakeH_of`, `h0TakeOwnH_of`: `X0WH` at an
  invariant inside `W0 … (X0WH L a)`, and from it `H0StmtH`'s clone clause,
  `H0TakeH`, `H0TakeOwnH`.

## Differences from the AArch64 version

The clone's pc is x86-64's `X64HelloPreA.clonePcH` (the `syscall` at
`.Lwc_main.x25 + 94`), and a free pc is off it by
`X64HelloWcClonePc.ne_clonePc_of_freeNH` (AArch64: `A64HelloWcPreWI`'s);
code labels are read by `codeLabel lo helloCells` (AArch64's
`codeOf lo helloProg`). AArch64's `StartEW.toF` (adding `Fw`) has no use
here: on x86-64 the start's `Fw` is carried by
`StartWf.startEWP_W0SH` itself (`Rt.StartEWFP`). wake's `room_gW` twins
at hello's value invariant are elsewhere (`GOf2H`), as on AArch64.
-/
import Spike.Lib.X64HelloWcClonePc
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64WakeWf

namespace Spike.Lib.X64.HelloPh.StartGlue

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize Own)
open Spike.Lib.X64ConsumerA (SegInvS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.HelloPh.WcW (freeNH)

/-! ## `W0`'s per-state facts -/

/-- **`h0`'s per-state facts at `W0`, at hello**: off the clone's pc
(`clonePcH`), and at the take pc `a` main's stack the site's range, not in
private memory (`¬ StackM`: not yet taken). -/
def X0WH (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ Spike.Lib.X64HelloPreA.clonePcH L ∧
    (pcOf s = a.toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.X64.Rt.Ti2.r0Of L.lab ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s.st.1)

/-- **`X0WH` at a free pc** (`StartWf`'s `hX0`): off the clone's pc and off
the take pc `a`, the take site's. -/
theorem x0WH_of_freeNH {L : RuntimeLayout} {a : Int64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (ha : a.toBitVec.toNat = (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s, freeNH (pcOf s) = true → X0WH L a s :=
  fun _ h => ⟨Spike.Lib.X64.HelloPh.WcW.ne_clonePc_of_freeNH hlab h,
    fun he => absurd (he.trans ha) (Spike.Lib.X64.HelloPh.WcW.site_ne_of_freeNH hlab h)⟩

section Inv

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isa} {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame} {K : State → State → Prop}
  {ms0 : List TermRun.Frame → Spike.Lib.MemSide isa} {inv0 : FragS isa} {L : RuntimeLayout}
  {a : Int64}

/-- **`X0WH` at an invariant inside `W0`.** -/
theorem x0WH_inv (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → X0WH L a s :=
  fun s c fs hi => (h s c fs hi).1.2.1

/-- **`H0StmtH`'s clone clause** at an invariant inside `W0 … (X0WH L a)`. -/
theorem noCloneH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    ∀ s c fs, inv0 s c fs → pcOf s ≠ Spike.Lib.X64HelloPreA.clonePcH L :=
  fun s c fs hi => (x0WH_inv h s c fs hi).1

/-- **`H0TakeH`** at an invariant inside `W0 … (X0WH L a)`. -/
theorem h0TakeH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    Spike.Lib.X64HelloPreA.H0TakeH L a inv0 :=
  fun s c fs hi hpc => ((x0WH_inv h s c fs hi).2 hpc).1

/-- **`H0TakeOwnH`** at an invariant inside `W0 … (X0WH L a)`. -/
theorem h0TakeOwnH_of (h : SegInvS (W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM (X0WH L a)) K p L0 ms0 inv0) :
    Spike.Lib.X64HelloPreA.H0TakeOwnH L a inv0 :=
  fun s c fs hi hpc => ((x0WH_inv h s c fs hi).2 hpc).2

end Inv

end Spike.Lib.X64.HelloPh.StartGlue

/-- info: 'Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH

/-- info: 'Spike.Lib.X64.HelloPh.StartGlue.noCloneH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartGlue.noCloneH_of

/-- info: 'Spike.Lib.X64.HelloPh.StartGlue.h0TakeH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartGlue.h0TakeH_of

/-- info: 'Spike.Lib.X64.HelloPh.StartGlue.h0TakeOwnH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartGlue.h0TakeOwnH_of
