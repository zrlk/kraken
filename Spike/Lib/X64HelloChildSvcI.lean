/-
**hello.w's child print `write` at the placed layout on x86-64** (the twin of
`Spike/Lib/HelloChildSvcI.lean`; the child premise `hsvc` at the instance's
memory side `X64HelloMsW.msWH`): `msWH`'s byte step is `print`'s and its abort
justification is the write abort's phase `WriteAb.Ab`, so
`SegR.hsvc_IW` (`Spike/Lib/X64HelloChildSvc.lean`) closes `hsvc` with no
premise on the memory side.

- `lays_H`: hello's cells are laid out in the placed executable.
- `hsvc_I`: `ChildPrem.hsvc` at the instance's memory side.

## Differences from the AArch64 version

- The placed program is the cells `SccCode.helloCells` (`ho : o.prog =
  helloCells`; AArch64 `helloProg`), the layout `RuntimeLayout.ofPlaceWX`
  (`X64HelloAssemblyI.LH`).
- AArch64's `msWH_we_svc` and its `example` are not twinned: they are dead in
  hello.
- The module imports `X64HelloChildSvc` and `X64HelloAssemblyI` (AArch64:
  through `HelloSegI`, which `hsvc_I` does not use).
-/
import Spike.Lib.X64HelloChildSvc
import Spike.Lib.X64HelloAssemblyI

namespace Spike.Lib.X64HelloAssemblyI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloMsW (msWH)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- hello's cells are laid out in the placed executable. -/
theorem lays_H (ho : o.prog = SccCode.helloCells) :
    Scc.Cert.Rt.X64.Lays (LH hp i).exe SccCode.helloCells (LH hp i).pfx := by
  rw [← ho]; exact (LH hp i).lays

/-- **`ChildPrem.hsvc` at the instance's memory side** (`hsvc_IW` with `msWH`'s
byte step and abort justification exactly the ones it asks). -/
theorem hsvc_I (ho : o.prog = SccCode.helloCells) (G0 : ιH hp i → Loc → Val → Prop) (w : ιH hp i)
    {F : MachineData → Prop} {w' : Words} {tp : BitVec 64} {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat}
    {l : WeakMem.AllocLabel} (hpw : w0.val = .loc ⟨l, 0⟩ 0)
    (hl : (SRH hp i w).lbl l = some (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat) (hwn : w2.val = .num n)
    (hfit : (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat + printN n m < 2 ^ 64)
    (hlen : printN n m < 2 ^ 63) :
    Hello.SegR.SvcX (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
      (fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) F w' tp w0 w1 w2 w3 w4 n m := by
  haveI := (LH hp i).valid
  exact Hello.SegR.hsvc_IW (F := F) (ms := fun _ => msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (lays_H hp i ho)
    rfl (fun _ => rfl) hpw hl hwn hfit hlen (fun _ _ _ _ _ h => h) (fun _ _ _ h => h)

end Inst

/-- info: 'Spike.Lib.X64HelloAssemblyI.lays_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lays_H

/-- info: 'Spike.Lib.X64HelloAssemblyI.hsvc_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hsvc_I

end Spike.Lib.X64HelloAssemblyI
