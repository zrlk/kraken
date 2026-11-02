/-
**hello's root: the level before the allocation as an explicit-invariant segment** (x86-64; the twin of
`Spike/Lib/A64HelloRootH0.lean`, itself the twin of `WakeRoot`'s `msBot` / `inv0R` / `h0` / `hst`): `OPremH`'s
`h0` and `hinit`'s start fact from a start segment.

As at wake, the root's `inv0` is the greatest closed invariant inside `W0H` under the take at the memory side
`msBotH`, which reads `I3` with its `inv0` disjunct `⊥` (`inv0H`, `X64GfpS.GfpS`); a closed invariant there is
one at `I3 … inv0H …` (its `xa` only grows, `X64GfpS.segInvS_mono_xa`), and the start pair of a segment with no
exit is in it (`X64GfpS.gfpS_of_segWS`).

- `msH`, `msBotH`, `inv0H`: the root's memory sides, those with `inv0 := ⊥`, and the level's invariant.
- `h0H`: `OPremH.h0`'s shape at `I3 … inv0H inv1 inv2`.
- `hstH`: the start pair (`StartPH`) in `inv0H`, from the start segment.
- `msHg`, `msBotHg`, `inv0Hg`, `h0Hg`, `hstHg`: the same at any own map `own` (`StartH0B.W0Hg`); the names above
  are these at `ownGH`.

Unlike AArch64 (`isaLSE2`, the assembly a `String`, the placement `PlaceW`, the root's table `ImmsRd.iRd`), the
level is over x86-64's `isa`, the assembly is an `Asm`, the placement a `PlaceWX` (`RuntimeLayout.ofPlaceWX`),
the memory side is `X64ConsumerA.msOfA` at `Scc.Sem.X64.target`'s marks, and the start segment `hstH` takes is a
premise at any immediate table (it is `X64HelloCtxRdU.hst0_RdU`'s at the root).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): `hst0_iRd`.
-/
import Spike.Lib.X64HelloStartH0B
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64GfpS
import Spike.Lib.X64SegInstA3
import Spike.Lib.X64HelloGOf2H

namespace Spike.Lib.X64.HelloPh.RootH0

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS I3 TakeCKS msOfA)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H W0Hg)
open Spike.Lib (FragS SegWS MemSide PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isa) (ls0 ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

/-! ## At an own map `own` -/

section Own

variable (own : State → List (Loc × Val))

/-- **The root's memory sides at a fragment `I`, at an own map `own`** (`StartH0U.msUHg`'s, without the `U r1Of`
guard). -/
noncomputable abbrev msHg (I : Spike.Lib.X64ConsumerS.InvS) (fs : List TermRun.Frame) : MemSide isa :=
  msOfA (Ly).Λ ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw i (Spike.Lib.X64WakeHG.cTW hpw i)) (fun s _ => own s) (AR) I (LB) (ls0T ls) fs

/-- **`msHg` with `I3`'s `inv0` disjunct `⊥`** (wake's `WakeRoot.msBot`). -/
noncomputable abbrev msBotHg : List TermRun.Frame → MemSide isa :=
  msHg (asm := asm) hpw i E rd ls own (I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2)

/-- **The level's invariant before the allocation at `own`**: the greatest closed invariant inside `W0Hg own`
under the take at `msBotHg own` (wake's `WakeRoot.inv0R`). -/
noncomputable abbrev inv0Hg : FragS isa :=
  Spike.Lib.X64GfpS.GfpS (W0Hg (asm := asm) hpw i own E DtW Ctx (ls0T ls0) frM)
    (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (msBotHg (asm := asm) hpw i E rd ls inv1 inv2 own)

/-- **`OPremH.h0`'s shape at `own`**: `inv0Hg own` is a closed invariant inside `W0Hg own` at
`I3 … (inv0Hg own) inv1 inv2` (`GfpS`'s, the allocation fragment only grown; wake's `WakeRoot`'s `h0`). -/
theorem h0Hg :
    SegInvS (W0Hg (asm := asm) hpw i own E DtW Ctx (ls0T ls0) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msHg (asm := asm) hpw i E rd ls own
        (I3 (AR) (LB) (ls0T ls) (inv0Hg (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2 own) inv1 inv2))
      (inv0Hg (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2 own) :=
  Spike.Lib.X64GfpS.segInvS_mono_xa Spike.Lib.X64GfpS.segInvS_gfpS (fun fs => Spike.Lib.X64GfpS.msOfA_with_xa fs)
    fun fs _ _ _ _ _ h =>
      Spike.Lib.X64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) fs h

/-- **The start pair is in `inv0Hg own`**, given the start segment at `msBotHg own` with no exit (wake's
`WakeRoot`'s `hst`). -/
theorem hstHg
    (hst0 : SegWS (W0Hg (asm := asm) hpw i own E DtW Ctx (ls0T ls0) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB)
      (msBotHg (asm := asm) hpw i E rd ls inv1 inv2 own) (StartPH hpw i E) (fun _ _ _ => False)) :
    inv0Hg (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2 own
      (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))
      Spike.Lib.X64.HelloPh.C0S.c0S [] :=
  Spike.Lib.X64GfpS.gfpS_of_segWS hst0 _ _ _ ⟨rfl, rfl, rfl⟩

end Own

/-! ## At hello's global map `ownGH` -/

set_option hygiene false in
local notation "OG" => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

/-- **The root's memory sides at a fragment `I`** (`StartH0U.msUH`'s, without the `U r1Of` guard): `msHg` at
`ownGH`. -/
noncomputable abbrev msH (I : Spike.Lib.X64ConsumerS.InvS) (fs : List TermRun.Frame) : MemSide isa :=
  msHg (asm := asm) hpw i E rd ls (OG) I fs

/-- **The root's memory sides with `I3`'s `inv0` disjunct `⊥`** (wake's `WakeRoot.msBot`). -/
noncomputable abbrev msBotH : List TermRun.Frame → MemSide isa :=
  msH (asm := asm) hpw i E rd ls (I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2)

/-- **The level's invariant before the allocation**: the greatest closed invariant inside `W0H` under the take
at `msBotH` (wake's `WakeRoot.inv0R`). -/
noncomputable abbrev inv0H : FragS isa :=
  Spike.Lib.X64GfpS.GfpS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM)
    (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (msBotH (asm := asm) hpw i E rd ls inv1 inv2)

/-- **`OPremH.h0`'s shape**: `inv0H` is a closed invariant inside `W0H` at `I3 … inv0H inv1 inv2` (`h0Hg` at
`ownGH`). -/
theorem h0H :
    SegInvS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)))
      helloSrc (LB)
      (msH (asm := asm) hpw i E rd ls
        (I3 (AR) (LB) (ls0T ls) (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) inv1 inv2))
      (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) :=
  h0Hg hpw i E rd Ctx ls0 ls frM inv1 inv2 (OG)

/-- **The start pair is in `inv0H`**, given the start segment at `msBotH` with no exit (`hstHg` at `ownGH`). -/
theorem hstH
    (hst0 : SegWS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (LB) (msBotH (asm := asm) hpw i E rd ls inv1 inv2)
      (StartPH hpw i E) (fun _ _ _ => False)) :
    inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2
      (Scc.Sem.X64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))
      Spike.Lib.X64.HelloPh.C0S.c0S [] :=
  hstHg hpw i E rd Ctx ls0 ls frM inv1 inv2 (OG) hst0

end Spike.Lib.X64.HelloPh.RootH0

/-- info: 'Spike.Lib.X64.HelloPh.RootH0.h0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootH0.h0H

/-- info: 'Spike.Lib.X64.HelloPh.RootH0.hstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootH0.hstH

/-- info: 'Spike.Lib.X64.HelloPh.RootH0.h0Hg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootH0.h0Hg

/-- info: 'Spike.Lib.X64.HelloPh.RootH0.hstHg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootH0.hstHg
