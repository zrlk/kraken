/-
**The allocator's code at hello's root layout** (x86-64; the twin of `Spike/Lib/A64HelloLandR.lean`'s live part):
the root's layout `RuntimeLayout.ofPlaceWX hpw (HelloImms.immsH Λ0 i0)` of an output whose cells are `helloCells`
lays out `helloCells`, ends at their `endOf`, and the cells contain the allocator (`HelloRd.hello_alloc`). These are
the code premises `hp`, `hend`, `hin` of x86-64's counter-add rows (`CtrF.ctrAtF_wr`, `WakeCtr.ctrRow_allocS_c2`),
read by the level-1 counter rows at the root (`LandRU`, `LandR1U`).

- `hcode_H`: the three code premises at the root's layout.

**Unlike AArch64**, x86-64 has no `Alloc.Code` record: its counter rows take the layout's `Lays`, `endOf` and
`allocIn` facts directly, so `hcode_H` is their conjunction (AArch64: `∀ ms0 q, Alloc.Code ms0 q (Ly).exe
(Ly).endPc`, from `alloc_code_of`); the program comes from `cellsOf asm` (AArch64: `textProgram asm`), the layout is
`ofPlaceWX` at `X64.HelloImms.immsH` (AArch64: `ofPlaceW` at `C0S.immsH`).

Not twinned (unreachable from the AArch64 root `hello_linkedA`, so twins only live constants): `HLandRd`,
`HLandM`, `HLand1`, `hctr0_RH`, `hnew0_RH`, `hW0_RH` (and so the import of `HelloRootO`, which only they read).
-/
import Spike.Lib.X64HelloCtrF
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64HelloImms

namespace Spike.Lib.X64.HelloPh.LandR

variable {asm : Scc.Sem.X64.Asm}

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib (PlaceWX)
open Scc.Cert.Rt.X64 (Lays endOf)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's layout at the certificate's table `i0`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw (Spike.Lib.X64.HelloImms.immsH Λ0 i0)

/-- **The allocator's code** in hello's layout: `helloCells` laid out at the layout's executable, its end the
layout's `endPc`, and the allocator in the cells (the counter rows' `hp`, `hend`, `hin`). -/
theorem hcode_H (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) :
    Lays (Ly).exe SccCode.helloCells (Ly).pfx ∧
      (Ly).endPc = endOf (Ly).exe SccCode.helloCells (Ly).pfx ∧
      Spike.Lib.X64.Alloc.allocIn SccCode.helloCells = true := by
  have hprog : (Ly).prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  exact ⟨hprog ▸ (Ly).lays, by rw [← hprog], Spike.Lib.X64.Flow.HelloRd.hello_alloc⟩

end Spike.Lib.X64.HelloPh.LandR

/-- info: 'Spike.Lib.X64.HelloPh.LandR.hcode_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.LandR.hcode_H
