/-
**hello's root: the level before the allocation as an explicit-invariant segment** (AArch64,
the root; the twin of `WakeRoot`'s `msBot` / `inv0R` / `h0` / `hst`): from the start segment
`StartH0U.hst0_ofHU_i0` at the root's table `ImmsRd.iRd Λ0 = immsH Λ0 i0Rd` (`hst0_iRd`), `OPremH`'s `h0` and
`hinit`'s start fact.

As at wake, the root's `inv0` is the greatest closed invariant inside `W0H` under the take at the memory side
`msBotH`, which reads `I3` with its `inv0` disjunct `⊥` (`inv0H`, `A64GfpS.GfpS`); a closed invariant there is
one at `I3 … inv0H …` (its `xa` only grows, `A64GfpS.segInvS_mono_xa`), and the start pair of a segment with no
exit is in it (`A64GfpS.gfpS_of_segWS`).

- `hst0_iRd`: `hst0_ofHU_i0` at `i0 := i0Rd` (the root's table `iRd Λ0`).
- `msBotH`, `inv0H`: the memory side with `inv0 := ⊥` and the level's invariant.
- `h0H`: `OPremH.h0`'s shape at `I3 … inv0H inv1 inv2`.
- `hstH`: the start pair (`StartPH`) in `inv0H`, from the start segment.
-/
import Spike.Lib.A64HelloStartH0U
import Spike.Lib.A64HelloImmsRd
import Spike.Lib.A64GfpS
import Spike.Lib.A64SegInstA3
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.RootH0

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (SegInvS I3)
open Spike.Lib.A64ConsumerA (TakeCKS msOfA)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib (FragS SegWS MemSide)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- **The start segment at the root's table `iRd Λ0`** (`StartH0U.hst0_ofHU_i0` at `i0 := i0Rd`). -/
theorem hst0_iRd {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpw : PlaceW pcfg Λ0 o) :
    type_of% (Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU_i0 (asm := asm) hpw Spike.Lib.A64.HelloPh.ImmsRd.i0Rd) :=
  Spike.Lib.A64.HelloPh.StartH0U.hst0_ofHU_i0 (asm := asm) hpw Spike.Lib.A64.HelloPh.ImmsRd.i0Rd

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw i

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isaLSE2) (ls0 ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)

/-- **The root's memory sides at a fragment `I`** (the start segment's `ms`, `StartH0U`'s `MSF`). -/
noncomputable abbrev msH (I : Spike.Lib.A64ConsumerS.InvS) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  msOfA (Ly).Λ ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw i (Spike.Lib.WakeHG.cTW hpw i))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) I (LB) (ls0T ls) fs

/-- **The root's memory sides with `I3`'s `inv0` disjunct `⊥`** (wake's `WakeRoot.msBot`). -/
noncomputable abbrev msBotH : List TermRun.Frame → MemSide isaLSE2 :=
  msH (asm := asm) hpw i E rd ls (I3 (AR) (LB) (ls0T ls) (fun _ _ _ => False) inv1 inv2)

/-- **The level's invariant before the allocation**: the greatest closed invariant inside `W0H` under the take
at `msBotH` (wake's `WakeRoot.inv0R`). -/
noncomputable abbrev inv0H : FragS isaLSE2 :=
  Spike.Lib.A64GfpS.GfpS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH
      (Ly)))
    helloSrc (LB) (msBotH (asm := asm) hpw i E rd ls inv1 inv2)

/-- **`OPremH.h0`'s shape**: `inv0H` is a closed invariant inside `W0H` at `I3 … inv0H inv1 inv2` (from
`GfpS`'s, the allocation fragment only grown; wake's `WakeRoot`'s `h0`). -/
theorem h0H :
    SegInvS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH
        (Ly))) helloSrc (LB)
      (msH (asm := asm) hpw i E rd ls
        (I3 (AR) (LB) (ls0T ls) (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) inv1 inv2))
      (inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2) :=
  Spike.Lib.A64GfpS.segInvS_mono_xa Spike.Lib.A64GfpS.segInvS_gfpS (fun fs => Spike.Lib.A64GfpS.msOfA_with_xa fs)
    fun fs _ _ _ _ _ h =>
      Spike.Lib.A64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) fs h

/-- **The start pair is in `inv0H`**, given the start segment at `msBotH` with no exit (`hst0_iRd` at
`I := I3 … ⊥ inv1 inv2`; wake's `WakeRoot`'s `hst`). -/
theorem hstH
    (hst0 : SegWS (W0H (asm := asm) hpw i E DtW Ctx (ls0T ls0) frM) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly)))
        helloSrc
      (LB) (msBotH (asm := asm) hpw i E rd ls inv1 inv2) (StartPH hpw i E) (fun _ _ _ => False)) :
    inv0H (asm := asm) hpw i E rd Ctx ls0 ls frM inv1 inv2
      (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata))
      Spike.Lib.A64.HelloPh.C0S.c0S [] :=
  Spike.Lib.A64GfpS.gfpS_of_segWS hst0 _ _ _ ⟨rfl, rfl, rfl⟩

end Spike.Lib.A64.HelloPh.RootH0

/-- info: 'Spike.Lib.A64.HelloPh.RootH0.hst0_iRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootH0.hst0_iRd

/-- info: 'Spike.Lib.A64.HelloPh.RootH0.h0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootH0.h0H

/-- info: 'Spike.Lib.A64.HelloPh.RootH0.hstH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootH0.hstH
