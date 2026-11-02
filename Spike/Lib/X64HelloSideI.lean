/-
**hello.w on x86-64: `HelloRowsW1.toW`'s side facts at the placed instance** (the twin of
`Spike/Lib/HelloSideI.lean`: the relation `X64HelloAssemblyI.QH`, the worker side `DH`, the target's marks at the
placed layout; `X64HelloRowsV1.HelloRowsW1.toWV`'s premises other than `hwf`, `hE`, `hms`, `hKR`).

- `hml_I`: main has not returned while the process runs (`X64HelloLive.mainLiveH`).
- `hAbX_I`: the abort phase's `exit_group` at an abort site (`X64HelloAbExit.abExit_DR` with `exitSite_P`; the
  program is hello's, `ho`).
- `hfz_I`: the buffer frozen (`X64HelloEmitFrzI.byteFrz_I`).
- `hES_I`: the emit row's shape (`X64HelloEmitShapeF.emitShapeF_I`).

## Unlike AArch64

- The loader's parse is `cellsOf asm = some o.prog` and the program the cell list `helloCells` (AArch64
  `textProgram`, `helloProg`).
- AArch64's `hown_I`, `hlbl_I`, `hbo_I` and `hNP_I` are dead (their uses are `rfl` or inline) and not twinned.
-/
import Spike.Lib.X64HelloRowsV1
import Spike.Lib.X64HelloEmitFrzI
import Spike.Lib.X64HelloEmitShapeF
import Spike.Lib.X64HelloLive
import Spike.Lib.X64HelloAbExit

namespace Spike.Lib.X64HelloSideI

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH μH)
open Spike.Lib.X64HelloEmitStep (ByteFrz)
open SccCode (helloCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (G0 : ιH hp i → Loc → Val → Prop) (P Z X : ιH hp i → FragS isa)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w) helloSrc (SRH hp i w).lbl
    (fun _ => Spike.Lib.X64HelloOwnLift.msWHX (LH hp i) (GH hp i G0) (SRH hp i) w) (P w) (fun _ _ _ => False))
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {E : Entry} {asm : Asm}
  (hpa : cellsOf asm = some o.prog) {passT : State → Prop} {Dd : X64HelloO.ODataH} {r1c : Range}

/-- main has not returned while the process runs (`X64HelloLive.mainLiveH`). -/
theorem hml_I : ∀ t s, (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c).Post (LH hp i).Λ t s →
    t.2.exited = none → SrcSem.mainExit s = [] :=
  X64HelloLive.mainLiveH

/-- **The abort phase's `exit_group` is at an abort site** of the target's marks (`abExit_DR`, the exit call by
`exitSite_P`), of cells that are hello's. -/
theorem hAbX_I (ho : o.prog = helloCells) (hpa' : cellsOf asm = some o.prog) :
    X64HelloStep1Sys.AbExit (DH hp i G0 P Z X hseg) ((target (kernel 2) E).marks asm (LH hp i).Λ)
      (AbW (LH hp i).exe) :=
  haveI := (LH hp i).valid
  X64HelloAbExit.abExit_DR (by rw [← ho]; exact (LH hp i).lays) rfl (X64HelloAbExit.exitSite_P hp i hpa')

/-- The buffer is frozen (`byteFrz_I`). -/
theorem hfz_I : ByteFrz (QH hp i G0 P Z X hseg arch R1 E hpa passT Dd r1c) (DH hp i G0 P Z X hseg) (LH hp i).Λ :=
  X64HelloEmitFrzI.byteFrz_I hp i E asm

/-- The emit row's shape (`emitShapeF_I`). -/
theorem hES_I : X64HelloEmitShapeF.EmitShapeF (DH hp i G0 P Z X hseg) :=
  X64HelloEmitShapeF.emitShapeF_I hp i G0 P Z X hseg

/-- info: 'Spike.Lib.X64HelloSideI.hml_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hml_I

/-- info: 'Spike.Lib.X64HelloSideI.hAbX_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hAbX_I

/-- info: 'Spike.Lib.X64HelloSideI.hfz_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hfz_I

/-- info: 'Spike.Lib.X64HelloSideI.hES_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hES_I

end Spike.Lib.X64HelloSideI
