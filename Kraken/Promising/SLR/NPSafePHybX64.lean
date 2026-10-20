/-
`NPSafeP (GHyb g.rel)` for the x64 spinlock worker (`spin_relPure`,
`SLR/RelPureX64.lean`), through `NPSafeP.of_relPure`
(`SLR/NPSafePHyb.lean`). Proved, no `sorry`. Also in option (S)'s frame
`K2Scope AllocIds` (`spin_npSafeP_hyb_S`).
-/
import Kraken.Promising.SLR.NPSafePHyb
import Kraken.Promising.SLR.RelPureX64

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- **The x64 spinlock worker is `NPSafeP (GHyb g.rel)`** (`spin_relPure`). -/
theorem spin_npSafeP_hyb (P : Params) (tid : Nat) (H : HardCellsX P Arch.tso tid) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (spinRuleX P Arch.tso tid H).Inv cl c r g) :
    NPSafeP (model isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid (GHyb g.rel) (K2₀ (model isa)) n m cl c r g :=
  NPSafeP.of_relPure _ (spin_relPure P tid H) n m cl c r g h

/-- `spin_npSafeP_hyb` in option (S)'s frame `K2Scope AllocIds`
(`theorem1IIPure_Hyb_S`). -/
theorem spin_npSafeP_hyb_S (P : Params) (tid : Nat) (H : HardCellsX P Arch.tso tid) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (spinRuleX P Arch.tso tid H).Inv cl c r g) :
    NPSafeP (model isa) Arch.tso (fun _ r _ => Post P.N P.Lk P.K r) tid (GHyb g.rel)
      (K2Scope (model isa) AllocIds) n m cl c r g :=
  (spin_npSafeP_hyb P tid H n m cl c r g h).toAllocIds

end Kraken.Promising.SLR.X64SpinInv

#print axioms Kraken.Promising.SLR.X64SpinInv.spin_npSafeP_hyb
#print axioms Kraken.Promising.SLR.X64SpinInv.spin_npSafeP_hyb_S
