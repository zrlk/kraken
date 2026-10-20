/-
`NPSafeP (GHyb g.rel)` for the AArch64 rules with (i‴) (`SLR/RelPureA64.lean`),
through `NPSafeP.of_relPure` (`SLR/NPSafePHyb.lean`): the MP writer and
reader, and the SWP spinlock worker. Proved, no `sorry`. Each also in option
(S)'s frame `K2Scope AllocIds` (`…_hyb_S`, via `NPSafeP.toAllocIds`), the
form `theorem1IIPure_Hyb_S` takes.
-/
import Kraken.Promising.SLR.NPSafePHyb
import Kraken.Promising.SLR.RelPureA64

namespace Kraken.Promising.SLR.Mp

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees

variable [layout : _root_.Layout]

/-- **The MP writer is `NPSafeP (GHyb g.rel)`** (`mpW_relPure`). -/
theorem mpW_npSafeP_hyb [Executable.ValidLayout (layout mpWriter)] (P : Params) (A : Arch) (tid rd : Nat)
    (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt) (hA' : A.plainStore ≠ .rel) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (mpRuleW P A tid rd hL hA hA').Inv cl c r g) :
    NPSafeP (model isa) A (MpPost P rd) tid (GHyb g.rel) (K2₀ (model isa)) n m cl c r g :=
  NPSafeP.of_relPure _ (mpW_relPure P A tid rd hL hA hA') n m cl c r g h

/-- `mpW_npSafeP_hyb` in option (S)'s frame `K2Scope AllocIds`
(`theorem1IIPure_Hyb_S`). -/
theorem mpW_npSafeP_hyb_S [Executable.ValidLayout (layout mpWriter)] (P : Params) (A : Arch) (tid rd : Nat)
    (hL : MpLocs P) (hA : A.storeKind .plain ≠ .nt) (hA' : A.plainStore ≠ .rel) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (mpRuleW P A tid rd hL hA hA').Inv cl c r g) :
    NPSafeP (model isa) A (MpPost P rd) tid (GHyb g.rel) (K2Scope (model isa) AllocIds) n m cl c r g :=
  (mpW_npSafeP_hyb P A tid rd hL hA hA' n m cl c r g h).toAllocIds

/-- **The MP reader is `NPSafeP (GHyb g.rel)`** (`mpR_relPure`). -/
theorem mpR_npSafeP_hyb [Executable.ValidLayout (layout mpReader)] (P : Params) (A : Arch) (tid : Nat)
    (hA1 : (A.loadKind .acq).isAcquire = true) (hA2 : (A.loadKind .acq == .plain) = false) (n m : Nat)
    (cl : Prop) (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost)
    (h : (mpRuleR P A tid hA1 hA2).toRX.Inv cl c r g) :
    NPSafeP (model isa) A (MpPost P tid) tid (GHyb g.rel) (K2₀ (model isa)) n m cl c r g :=
  NPSafeP.of_relPure _ (mpR_relPure P A tid hA1 hA2) n m cl c r g h

/-- `mpR_npSafeP_hyb` in option (S)'s frame `K2Scope AllocIds`
(`theorem1IIPure_Hyb_S`). -/
theorem mpR_npSafeP_hyb_S [Executable.ValidLayout (layout mpReader)] (P : Params) (A : Arch) (tid : Nat)
    (hA1 : (A.loadKind .acq).isAcquire = true) (hA2 : (A.loadKind .acq == .plain) = false) (n m : Nat)
    (cl : Prop) (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost)
    (h : (mpRuleR P A tid hA1 hA2).toRX.Inv cl c r g) :
    NPSafeP (model isa) A (MpPost P tid) tid (GHyb g.rel) (K2Scope (model isa) AllocIds) n m cl c r g :=
  (mpR_npSafeP_hyb P A tid hA1 hA2 n m cl c r g h).toAllocIds

end Kraken.Promising.SLR.Mp

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

/-- **The SWP spinlock worker is `NPSafeP (GHyb g.rel)`** (`swp_relPure`). -/
theorem swp_npSafeP_hyb (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (swpRuleX P A tid H).Inv cl c r g) :
    NPSafeP (model isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid (GHyb g.rel) (K2₀ (model isa)) n m cl c r g :=
  NPSafeP.of_relPure _ (swp_relPure P A tid H) n m cl c r g h

/-- `swp_npSafeP_hyb` in option (S)'s frame `K2Scope AllocIds`
(`theorem1IIPure_Hyb_S`). -/
theorem swp_npSafeP_hyb_S (P : Params) (A : Arch) (tid : Nat) (H : HardCellsX P A tid) (n m : Nat) (cl : Prop)
    (c : Config isa) (r : (model isa).R) (g : (model isa).Ghost) (h : (swpRuleX P A tid H).Inv cl c r g) :
    NPSafeP (model isa) A (fun _ r _ => Post P.N P.Lk P.K r) tid (GHyb g.rel) (K2Scope (model isa) AllocIds)
      n m cl c r g :=
  (swp_npSafeP_hyb P A tid H n m cl c r g h).toAllocIds

end Kraken.Promising.SLR.SwpInv

#print axioms Kraken.Promising.SLR.Mp.mpW_npSafeP_hyb
#print axioms Kraken.Promising.SLR.Mp.mpR_npSafeP_hyb
#print axioms Kraken.Promising.SLR.SwpInv.swp_npSafeP_hyb
#print axioms Kraken.Promising.SLR.Mp.mpW_npSafeP_hyb_S
#print axioms Kraken.Promising.SLR.Mp.mpR_npSafeP_hyb_S
#print axioms Kraken.Promising.SLR.SwpInv.swp_npSafeP_hyb_S
