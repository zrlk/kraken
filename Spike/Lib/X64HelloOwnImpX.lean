/-
**hello's start level with both self words appended** (x86-64 only; the hello counterpart of the non-generic part
of `X64WakeOwnImp`): the start's level `StartWf.WSH` (at `ownGH`) restated at `ownGHXW` (`WSHX`), and the
per-state lift predicate `LftH` the start's assemblies are mirrored with, as wake's `Lft` / `WSX`.

- `WSHX`: `StartWf.WSH` at `ownGHXW`.
- `LftH`: a state of `WSH` is one of `WSHX`; `lft_of_cstOkH` (`W0.liftHX`), `wshx_of`.
- `BlkW.lftH`, `NodeW.lftH`: `LftH` at a block / a node from `CstOkH` there.

The start's obligation families' `imp` lemmas (`TcbW.imp`, `TakeW.imp`, `TiWAt.imp`, `EntryW.imp`,
`XStartW.imp`, `St0W.imp`, `X0WAt.imp`, `SwEW.imp`, `StartE1W.imp`, `StartEW.imp`, in `X64WakeOwnImp`) are
generic in the fragments and are used as they are, at `W2 := LftH`.

## Differences from the AArch64 version

AArch64 has no counterpart (main owns no TCB word there). Against wake's `WSX`/`Lft`: the start's level is hello's
`WSH` (`ownGH`, hello's threads-abort phases `Hello.ThreadsAb.AcH` at hello's `pfxM`), lifted to `ownGHXW`
through `CstOkH` (the worker's word at `pinA + 112`).
-/
import Spike.Lib.X64HelloOwnCstX
import Spike.Lib.X64HelloStartWfL
import Spike.Lib.X64WakeOwnImp

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

/-- **The start's level at `ownGHXW`**: `StartWf.WSH` with main's and the worker's TCB words appended. -/
abbrev WSHX (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isa := fun s c =>
  W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.X64.Hello.ThreadsAb.AcH L.lab StartWf.pfxM) Ctx lbl lsize frM X0 s c []

/-- **A state of `WSH` is one of `WSHX`.** -/
def LftH (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isa := fun s c =>
  StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c → WSHX L a ar p Dt Cl Ctx lbl lsize frM X0 s c

variable {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}

/-- `LftH` where `CstOkH` (`W0.liftHX`). -/
theorem lft_of_cstOkH {s : State} {c : Spike.Lib.Ctl} (h : CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) :
    LftH L a ar p Dt Cl Ctx lbl lsize frM X0 s c := fun hw => hw.liftHX h

/-- The combination step: `WSH ∧ LftH` is `WSHX`. -/
theorem wshx_of {s : State} {c : Spike.Lib.Ctl} (h1 : StartWf.WSH L a ar p Dt Cl Ctx lbl lsize frM X0 s c)
    (h2 : LftH L a ar p Dt Cl Ctx lbl lsize frM X0 s c) : WSHX L a ar p Dt Cl Ctx lbl lsize frM X0 s c := h2 h1

/-- `LftH` at a block from `CstOkH` there. -/
theorem BlkW.lftH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hD hJ k hk m hA' hD' =>
    ⟨lft_of_cstOkH (h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- `LftH` at a node from `CstOkH` there. -/
theorem NodeW.lftH {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : ND} (h : NodeW (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n) :
    NodeW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨lft_of_cstOkH (h s c hA).1, fun _ h => h⟩

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.lft_of_cstOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.lft_of_cstOkH

/-- info: 'Spike.Lib.X64.HelloPh.BlkW.lftH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.BlkW.lftH

/-- info: 'Spike.Lib.X64.HelloPh.NodeW.lftH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.NodeW.lftH
