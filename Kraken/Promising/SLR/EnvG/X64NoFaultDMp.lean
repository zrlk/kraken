/-
**No fault at the runner's declarations for the x64 message-passing
programs and the Treiber pusher**: `spsc_queue.kl`,
`mp_relay3_xchg.kl`, `mp_incl.kl`'s reader, and `treiber_pp.kl`'s pusher.

As in `X64NoFaultDLocks`: each `*_runner_noFault` theorem is the no-fault of
the rules the `*_runner` theorem (`X64SpscAbsRunner`, `X64RelayAbsRunner`,
`X64MpInclAbsRunner`, `X64TreiberAbsRunner`) uses at `decls = ds`, under
`Decls.AgreesOn ds S` on the rule's fixed layout `S`; `…_concrete` at the
runner's declarations.

Not here:
- `mp_incl.kl`'s writer: its `incl` is a load and a store, a multi-access
  tree (`X64NoFaultDMpIncl`);
- `treiber_pp.kl`'s popper: its rule's layout is `sAll` (every footprint),
  so `E.within sAll` says nothing about addresses and `AgreesOn ds sAll` is
  false. Its accesses through the loaded `top` need a value invariant the
  proof does not carry (`X64_KNOWN_GAPS.md`).
-/
import Kraken.Promising.SLR.EnvG.X64NoFaultD
import Kraken.Promising.SLR.EnvG.X64SpscAbsRunner
import Kraken.Promising.SLR.EnvG.X64RelayAbsRunner
import Kraken.Promising.SLR.EnvG.X64MpInclAbsRunner
import Kraken.Promising.SLR.EnvG.X64TreiberAbsRunner

/-! ## `spsc_queue.kl` -/

namespace Kraken.Promising.X64.EnvG.SpscAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.SpscX Kraken.Promising.X64.EnvG.TreiberX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageV)]

/-- **The producer's and the consumer's rules at `decls = ds` exclude
faults** (`prodRuleAD`, `consRuleAD`), for `ds` agreeing on the four words
(`buf0`, `buf0 + 256`, `head`, `tail`). -/
theorem x64_spsc_envG_runner_noFault {ds : Decls} (hsz : ds.Sized) (P : SP) (hL : SpscLocs P)
    (hag : ds.AgreesOn (spscS P)) (tid : Nat) :
    NoFaultRuleSX (prodRuleAD hsz P hL tid) ∧ NoFaultRuleSX (consRuleAD hsz P hL) :=
  ⟨noFaultRule_ofSafelyEnvGTXMD_rootD _ _ _ _ _ _ _ _ spscImageV_noFaultCode hag,
    noFaultRule_ofSafelyEnvGTXMD_rootD _ _ _ _ _ _ _ _ spscImageV_noFaultCode hag⟩

end Kraken.Promising.X64.EnvG.SpscAbs

namespace Kraken.Promising.X64.EnvG.SpscAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.SpscAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.SpscX

section
attribute [local instance] spscLayoutV

/-- **No fault for `spsc_queue.kl`'s threads at the runner's declarations**
(`spscDeclsD`). -/
theorem x64_spsc_envG_runner_noFault_concrete (hL : SpscLocs spscP) (tid : Nat) :
    NoFaultRuleSX (prodRuleAD spscDeclsD_sized spscP hL tid) ∧ NoFaultRuleSX (consRuleAD spscDeclsD_sized spscP hL) :=
  x64_spsc_envG_runner_noFault spscDeclsD_sized spscP hL (by
    show spscDeclsD.AgreesOn [(symS "buf0", 4), (symS "buf0" + 256, 4), (symS "head", 4), (symS "tail", 4)]
    rw [symS_buf0, symS_head, symS_tail]; decls_agrees_on) tid

end

end Kraken.Promising.X64.EnvG.SpscAbs.Concrete

/-! ## `mp_relay3_xchg.kl` -/

namespace Kraken.Promising.X64.EnvG.RelayAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.TakeMp Kraken.Promising.X64.EnvG.RelayX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout relayImageV)]

set_option linter.unusedSimpArgs false in
/-- **The writer's, the relay's and the reader's rules at `decls = ds`
exclude faults** (`relayRuleWVD`, `relayRuleYVD`, `relayRuleDVD`), for `ds`
agreeing on `f1`, `d` and `f2`. -/
theorem mp_relay3_xchg_envG_runner_noFault {ds : Decls} (hsz : ds.Sized) (rp : RP)
    (hag : ds.AgreesOn [(rp.f1, 4), (rp.d, 4), (rp.f2, 4)]) (hLP : MpLocs rp.P) (hLQ : MpLocs rp.Q)
    (tW tY : Nat) :
    NoFaultRule (relayRuleWVD hsz rp hLP tW) ∧ NoFaultRuleSX (relayRuleYVD hsz rp hLQ tY) ∧
      NoFaultRuleSX (relayRuleDVD hsz rp) := by
  have hsub : ∀ S : SharedEnv.Layout, (∀ p ∈ S, p ∈ [(rp.f1, 4), (rp.d, 4), (rp.f2, 4)]) → ds.AgreesOn S :=
    fun S h p hp => hag p (h p hp)
  refine ⟨noFaultRule_ofSafelyEnvGXMD_rootD _ _ _ _ _ _ _ _ relayImageV_noFaultCode (hsub _ ?_),
    noFaultRule_ofSafelyEnvGTRCXMD_rootD _ _ _ _ _ _ _ _ relayImageV_noFaultCode hag,
    noFaultRule_ofSafelyEnvGTXMD_rootD _ _ _ _ _ _ _ _ relayImageV_noFaultCode (hsub _ ?_)⟩ <;>
  · intro p hp
    simp only [mpS, RP.P, RP.Q, List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
    rcases hp with rfl | rfl <;> simp

end Kraken.Promising.X64.EnvG.RelayAbs

namespace Kraken.Promising.X64.EnvG.RelayAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.RelayAbs Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG.RelayX
open Kraken.Promising.X64.EnvG.Mp

section
attribute [local instance] relayLayoutV

/-- **No fault for `mp_relay3_xchg.kl`'s three threads at the runner's
declarations** (`relayDeclsD`). -/
theorem mp_relay3_xchg_envG_runner_noFault_concrete (hLP : MpLocs rpV.P) (hLQ : MpLocs rpV.Q) :
    NoFaultRule (relayRuleWVD relayDeclsD_sized rpV hLP 0) ∧ NoFaultRuleSX (relayRuleYVD relayDeclsD_sized rpV hLQ 1) ∧
      NoFaultRuleSX (relayRuleDVD relayDeclsD_sized rpV) :=
  mp_relay3_xchg_envG_runner_noFault relayDeclsD_sized rpV (by
    show relayDeclsD.AgreesOn [(symY "f1", 4), (symY "d", 4), (symY "f2", 4)]
    rw [symY_f1, symY_d, symY_f2]; decls_agrees_on) hLP hLQ 0 1

end

end Kraken.Promising.X64.EnvG.RelayAbs.Concrete

/-! ## `mp_incl.kl`'s reader -/

namespace Kraken.Promising.X64.EnvG.MpInclAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic
open Kraken.Promising.X64.EnvG.MpInc Kraken.Promising.X64.EnvG.MpIncV

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpInclImageV)]

/-- **The reader's rule at `decls = ds` excludes faults** (`mpInclRuleRMD`),
for `ds` agreeing on `f` and `d`. -/
theorem x64_mp_incl_reader_runner_noFault {ds : Decls} (hsz : ds.Sized) (P : Params) (hL : MpLocs P) (tid : Nat)
    (hag : ds.AgreesOn (mpS P)) : NoFaultRule (mpInclRuleRMD hsz P hL tid) :=
  noFaultRule_ofSafelyEnvGXMD_rootD _ _ _ _ _ _ _ _ mpInclImageV_noFaultCode hag

end Kraken.Promising.X64.EnvG.MpInclAbs

/-! ## `treiber_pp.kl`'s pusher -/

namespace Kraken.Promising.X64.EnvG.TreiberAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageV)]

/-- **The pusher's rule at `decls = ds` excludes faults** (`pushRuleVD`),
for `ds` agreeing on `top`, the node's value word and its `next` field. The
popper's rule (`popRuleVD`, layout `sAll`) is not covered. -/
theorem x64_treiber_pp_pusher_runner_noFault {ds : Decls} (hsz : ds.Sized) (t n : BitVec 64) (hL : TLocs (tPX t n))
    (hag : ds.AgreesOn (pushS t n)) : NoFaultRuleF (pushRuleVD hsz t n hL) :=
  noFaultRuleF_ofSafelyEnvGFCXMD_rootD _ _ _ _ _ _ _ _ treiberImageV_noFaultCode hag

end Kraken.Promising.X64.EnvG.TreiberAbs

namespace Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.TreiberAbs Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.Treiber
open Kraken.Promising.X64.EnvG.TreiberX

section
attribute [local instance] treiberLayoutV

/-- **No fault for `treiber_pp.kl`'s pusher at the runner's declarations**
(`treiberDeclsD`: `top` 8 bytes, `n1` 4 bytes; `next` at `n1 + 8`
undeclared, its own footprint). -/
theorem x64_treiber_pp_pusher_runner_noFault_concrete (hL : TLocs (tPX (symT "top") (symT "n1"))) :
    NoFaultRuleF (pushRuleVD treiberDeclsD_sized (symT "top") (symT "n1") hL) :=
  x64_treiber_pp_pusher_runner_noFault treiberDeclsD_sized _ _ hL (by
    show treiberDeclsD.AgreesOn [(symT "top", 8), (symT "n1", 4), (symT "n1" + 8, 8)]
    rw [symT_top, symT_n1]; decls_agrees_on)

end

end Kraken.Promising.X64.EnvG.TreiberAbs.Concrete

#print axioms Kraken.Promising.X64.EnvG.SpscAbs.Concrete.x64_spsc_envG_runner_noFault_concrete
#print axioms Kraken.Promising.X64.EnvG.RelayAbs.Concrete.mp_relay3_xchg_envG_runner_noFault_concrete
#print axioms Kraken.Promising.X64.EnvG.MpInclAbs.x64_mp_incl_reader_runner_noFault
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.Concrete.x64_treiber_pp_pusher_runner_noFault_concrete
