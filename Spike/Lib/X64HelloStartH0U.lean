/-
**hello's root memory sides with the child's stack unmapped** (x86-64; the live part of the twin of
`Spike/Lib/A64HelloStartH0U.lean`): the fragment `I` asked only with the child's stack `r1Of` unmapped (`invUH`),
and the root's memory sides at it (`msUH`), at the root's immediate table `X64.HelloImms.immsH Λ0 i0`, the layout
`RuntimeLayout.ofPlaceWX`, the arena `X64.WakeOD.arW`, hello's guarantee `X64HelloGOf2H.gWH` at the dummy flag
`X64WakeHG.cTW`, the ownership `X64.HelloPh.ownGH` at `scc_rt_nthreads`, the start's placement `L0T` and sizes
`ls0T`.

- `invUH`, `msUH`: the fragment asked only with `r1Of` unmapped, the memory sides at it (wake's `invU`, `msU`).
- `msUHg`: the memory sides at an own map `own`; `msUH` is it at `ownGH`.

Unlike AArch64, only `invUH` and `msUH` are stated: AArch64's start segment at them (`hst0_ofHU_i0`, `hst0_ofHU`)
is superseded there by the level-0 segment ending at rodata's landing and kept frozen, and the root's arena facts
(`HrdArena`) read only these two; the memory side is x86-64's (`X64ConsumerA.msOfA`, `Scc.Sem.X64.target`'s marks)
over `PlaceWX`.
-/
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64WakeHG
import Spike.Lib.X64KeepUnS
import Spike.Lib.X64HelloOwnG
import Spike.Lib.X64HelloImms
import Spike.Lib.X64WakeOD

namespace Spike.Lib.X64.HelloPh.StartH0U

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib (PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

/-- **The fragment `I` asked only with the child's stack unmapped** (wake's `StartH0U.invU`). -/
abbrev invUH (I : Spike.Lib.X64ConsumerS.InvS) : Spike.Lib.X64ConsumerS.InvS := fun lbl lsize s c fs =>
  U R1 s → I lbl lsize s c fs

/-- **The root's memory sides at `invUH I`, at an own map `own`** (wake's `StartH0U.msU`). `msUH` is it at
`ownGH`. -/
noncomputable abbrev msUHg (own : State → List (Loc × Val)) (E : Entry) (rd : TermRun.Word → Prop)
    (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize) (fs : List TermRun.Frame) : MemSide isa :=
  Spike.Lib.X64ConsumerA.msOfA (Ly).Λ ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ)
    rd (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH)) (fun s _ => own s)
    (AR) (invUH hpw i0 I) (LB) (ls0T ls) fs

/-- **The root's memory sides at `invUH I`** (wake's `StartH0U.msU`): `msUHg` at `ownGH`. -/
noncomputable abbrev msUH (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize)
    (fs : List TermRun.Frame) : MemSide isa :=
  msUHg (asm := asm) hpw i0 (Spike.Lib.X64.HelloPh.ownGH (Ly) NT) E rd I ls fs

/-- `invUH` asks `I` only where the child's stack is unmapped: off `U r1Of` it holds (non-vacuity of the
weakening). -/
example (I : Spike.Lib.X64ConsumerS.InvS) (lbl : Lbl) (lsize : Lsize) (s : State) (c : Spike.Lib.Ctl)
    (fs : List TermRun.Frame) (h : ¬ U (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) s) :
    invUH hpw i0 I lbl lsize s c fs := fun hu => (h hu).elim

end Spike.Lib.X64.HelloPh.StartH0U
