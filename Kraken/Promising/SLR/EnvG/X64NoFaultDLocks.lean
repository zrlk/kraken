/-
**No fault at the runner's declarations for the x64 locks**: `spinlock2/3.kl`, `spinlock_cmpxchg2/3.kl`, `dekker_mfence.kl`,
`ticketlock3.kl`.

Each `*_runner` theorem (`X64SpinAbsRunner`, `X64CmpxAbsRunner`,
`DekkerAbsRunner`, `TicketXPublic`) proves its property from the runner's
exact configuration with its rule at `decls = ds`; the `*_runner_noFault`
theorem here is that rule's no-fault (`NoFaultRule…`, as the `decls = {}`
rules' `…_noFault`), under `ds` resolving each of the proof's locations to
itself (`Decls.AgreesOn`, `X64NoFaultD`). The `…_concrete` instances take
the runner's declarations (`spinDeclsD`, …), where `decls_agrees_on` closes
the agreement.
-/
import Kraken.Promising.SLR.EnvG.X64NoFaultD
import Kraken.Promising.SLR.EnvG.X64SpinAbsRunner
import Kraken.Promising.SLR.EnvG.X64CmpxAbsRunner
import Kraken.Promising.SLR.EnvG.DekkerAbsRunner
import Kraken.Promising.SLR.EnvG.TicketXRunner

/-! ## `spinlock2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.SpinAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spinImageV)]

/-- **The verbatim spinlock worker's rule at `decls = ds` excludes faults**
(`spinRuleV_envGD`), for `ds` agreeing on the two words. -/
theorem x64_spin_counter_envG_runner_noFault {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symV "lock", 4), (symV "counter", 4)]) (P : Sys) (tid : Nat) (rel₀ : Loc → Pred) :
    NoFaultRule (spinRuleV_envGD hsz P tid (symV "lock") (symV "counter") rel₀) :=
  noFaultRule_ofSafelyEnvGRXMD_rootD _ _ _ _ _ _ _ _ _ spinImageV_noFaultCode hag

end Kraken.Promising.X64.EnvG.SpinAbs

namespace Kraken.Promising.X64.EnvG.SpinAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.SpinAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock

section
attribute [local instance] spinLayoutV

/-- **No fault for `spinlock2/3.kl`'s workers at the runner's declarations**
(`spinDeclsD`). -/
theorem x64_spin_counter_envG_runner_noFault_concrete (P : Kraken.Promising.SLR.SpinCommon.Sys) (tid : Nat) (rel₀ : Loc → Pred) :
    NoFaultRule (spinRuleV_envGD spinDeclsD_sized P tid (symV "lock") (symV "counter") rel₀) :=
  x64_spin_counter_envG_runner_noFault spinDeclsD_sized (by rw [symV_lock, symV_counter]; decls_agrees_on) P tid rel₀

end

end Kraken.Promising.X64.EnvG.SpinAbs.Concrete

/-! ## `spinlock_cmpxchg2/3.kl` -/

namespace Kraken.Promising.X64.EnvG.CmpxAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.CmpxPublic
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

variable [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxImageV)]

/-- **The verbatim `lock cmpxchg` spinlock worker's rule at `decls = ds`
excludes faults** (`cmpxRuleV_envGD`). -/
theorem x64_cmpx_counter_envG_runner_noFault {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symC "lock", 4), (symC "counter", 4)]) (P : Sys) (tid : Nat) (rel₀ : Loc → Pred) :
    NoFaultRuleF (cmpxRuleV_envGD hsz P tid (symC "lock") (symC "counter") rel₀) :=
  noFaultRuleF_ofSafelyEnvGFXMD_rootD _ _ _ _ _ _ _ _ _ cmpxImageV_noFaultCode hag

end Kraken.Promising.X64.EnvG.CmpxAbs

namespace Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.CmpxAbs Kraken.Promising.X64.EnvG.Concrete Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock

section
attribute [local instance] cmpxLayoutV

/-- **No fault for `spinlock_cmpxchg2/3.kl`'s workers at the runner's
declarations** (`cmpxDeclsD`). -/
theorem x64_cmpx_counter_envG_runner_noFault_concrete (P : Kraken.Promising.SLR.SpinCommon.Sys) (tid : Nat) (rel₀ : Loc → Pred) :
    NoFaultRuleF (cmpxRuleV_envGD cmpxDeclsD_sized P tid (symC "lock") (symC "counter") rel₀) :=
  x64_cmpx_counter_envG_runner_noFault cmpxDeclsD_sized (by rw [symC_lock, symC_counter]; decls_agrees_on) P tid rel₀

end

end Kraken.Promising.X64.EnvG.CmpxAbs.Concrete

/-! ## `dekker_mfence.kl` -/

namespace Kraken.Promising.X64.EnvG.DekkerAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Dekker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout dkImageV)]

/-- **The verbatim Dekker worker's rule at `decls = ds` excludes faults**
(`dkRuleVD`; thread `tid` with own flag `f`, other flag `o`). -/
theorem x64_dekker_public_runner_noFault {ds : Decls} (hsz : ds.Sized) (tid : Nat) (f o c : BitVec 64)
    (hag : ds.AgreesOn [(f, 4), (o, 4), (c, 4)])
    {B : Config isa → Res → Ghost → Prop} (hB : ∀ cfg r g, DkThreadEnd tid f o c cfg r → B cfg r g) :
    NoFaultRule (dkRuleVD hsz tid f o c hB) :=
  noFaultRule_ofSafelyEnvGXMD_rootD _ _ _ _ _ _ _ _ dkImageV_noFaultCode hag

end Kraken.Promising.X64.EnvG.DekkerAbs

namespace Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.DekkerAbs Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Dekker
open Kraken.Promising.X64.EnvG.Dekker

section
attribute [local instance] dkLayoutV

/-- **No fault for both of `dekker_mfence.kl`'s threads at the runner's
declarations** (`dkDeclsD`; thread 0 owns `flag0`, thread 1 `flag1`). -/
theorem x64_dekker_public_runner_noFault_concrete {B : Config isa → Res → Ghost → Prop}
    (hB0 : ∀ cfg r g, DkThreadEnd 0 (symD "flag0") (symD "flag1") (symD "counter") cfg r → B cfg r g)
    (hB1 : ∀ cfg r g, DkThreadEnd 1 (symD "flag1") (symD "flag0") (symD "counter") cfg r → B cfg r g) :
    NoFaultRule (dkRuleVD dkDeclsD_sized 0 (symD "flag0") (symD "flag1") (symD "counter") hB0) ∧
      NoFaultRule (dkRuleVD dkDeclsD_sized 1 (symD "flag1") (symD "flag0") (symD "counter") hB1) :=
  ⟨x64_dekker_public_runner_noFault dkDeclsD_sized 0 _ _ _
      (by rw [symD_flag0, symD_flag1, symD_counter]; decls_agrees_on) hB0,
    x64_dekker_public_runner_noFault dkDeclsD_sized 1 _ _ _
      (by rw [symD_flag0, symD_flag1, symD_counter]; decls_agrees_on) hB1⟩

end

end Kraken.Promising.X64.EnvG.DekkerAbs.Concrete

/-! ## `ticketlock3.kl` -/

namespace Kraken.Promising.X64.EnvG.TicketX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock
open Kraken.Promising.X64.EnvG

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk3ImageV)]

/-- **The verbatim ticket-lock worker's rule at `decls = ds` excludes
faults** (`ruleTk3 (Or.inl hsz)`; `ruleTk3_noFault` at `ds`). -/
theorem ticket3_counter_envG_runner_noFault {ds : Decls} (hsz : ds.Sized) (N : Nat) (x o c : BitVec 64)
    (hL : Locs (tkSysX N x o c)) (tid : Nat) (hag : ds.AgreesOn [(x, 4), (o, 4), (c, 4)]) :
    NoFaultRuleSXE (ruleTk3 (Or.inl hsz) N x o c hL tid) :=
  NoFaultRuleSXE.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGTDR.q_at rF t h he hg ht E hnp
    exact noFault_QX64MD_rootD
      (E := Kraken.Promising.SLR.EnvGTDR isa Arch.tso tid (tkPlan (tkSysX N x o c)) (disp (tkSysX N x o c) hL.xo))
      hag (fun _ _ => ⟨_, rfl⟩) (MaskOf.refl _) (tkS_le16 x o c) tk3ImageV_noFaultCode (postTk3_end _ tid)
      (rootOnlyD_of_phase1TreeRX tk3ImageV_phase1) t.st σ tree hQ hex

end Kraken.Promising.X64.EnvG.TicketX

namespace Kraken.Promising.X64.EnvG.TicketX.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.TicketX Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.TicketLock

section
attribute [local instance] tk3LayoutV

/-- **No fault for `ticketlock3.kl`'s workers at the runner's declarations**
(`tk3DeclsD`). -/
theorem ticket3_counter_envG_runner_noFault_concrete (N : Nat) (hL : Locs (tkSysX N (symTk "next")
    (symTk "owner") (symTk "counter"))) (tid : Nat) :
    NoFaultRuleSXE (ruleTk3 (Or.inl tk3DeclsD_sized) N (symTk "next") (symTk "owner") (symTk "counter") hL tid) :=
  ticket3_counter_envG_runner_noFault tk3DeclsD_sized N _ _ _ hL tid
    (by rw [symTk_next, symTk_owner, symTk_counter]; decls_agrees_on)

end

end Kraken.Promising.X64.EnvG.TicketX.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpinAbs.Concrete.x64_spin_counter_envG_runner_noFault_concrete
#print axioms Kraken.Promising.X64.EnvG.CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_noFault_concrete
#print axioms Kraken.Promising.X64.EnvG.DekkerAbs.Concrete.x64_dekker_public_runner_noFault_concrete
#print axioms Kraken.Promising.X64.EnvG.TicketX.Concrete.ticket3_counter_envG_runner_noFault_concrete
