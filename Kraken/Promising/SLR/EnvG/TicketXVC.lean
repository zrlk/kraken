/-
**Part 1: the x64 ticket lock worker's VCs**
(`X64/ticketlock3.kl`) on the ticket environment with a release-kind ticket
RMW `EnvGTDR` (`EnvG/TicketREnv.lean`), under **`Arch.tso`**. ISA-neutral
in the ISA (the `vcgen` proof is `EnvG/TicketXVCGen.lean`).

`EnvG/TicketLockVC.lean`'s VCs are stated at `Arch.armv8`; under `Arch.tso`
every plain load is an acquire that may take (`.acqPc`), every plain store a
release (`.rel`), every `lock` RMW `.acqRel`. The invariants (`Start`,
`Spin`, `Got`, `Read`, `Stored`, `QEnd`), the plan `tkPlan` and the world
are `TicketLock`'s, reused unchanged. The VCs:

- `vcX_xadd` (`lock xaddl %eax,(next)`, `rmw .acqRel`; `vc_ldaddK` with the
  claim condition by `A.rmwKind .acqRel = .acqRel`);
- `vcX_spin` (`movl (owner),%ecx`, a taking plain load; `vc_ldar`);
- `vcX_ldc` (`movl (counter),%edx`, a taking plain load: the take keeps the
  full counter, `takeEff_wr_full`; `vc_ldr`);
- `vcX_stc` (`movl %edx,(counter)`, a release-kind plain store to the
  unplanned counter; `vc_str`);
- `vcX_rel` (`movl %ecx,(owner)`, the planned release; `vc_stlr`).

Each VC is now the `Arch.tso` instance of
the architecture-generic VC in `EnvG/TicketLockVC.lean` (`vc_ldaddKA`,
`vc_ldarA`, `vc_ldrA`, `vc_strA`, `vc_stlrA`), whose `Arch.armv8` instances
are `TicketLock`'s VCs; `takeEffX_q_ge` is `EnvG.takeEff_q_ge`.
-/
import Kraken.Promising.SLR.EnvG.TicketLockVC
import Kraken.Promising.SLR.EnvG.TicketREnv
import Kraken.Promising.SLR.EnvG.TakeX64VCGen

namespace Kraken.Promising.X64.EnvG.TicketX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.TicketLock

variable {I : ISA} {P : Sys}

/-- The x64 ticket lock's environment for thread `tid` (before the layout
restriction): `EnvGTDR` under `Arch.tso`. -/
noncomputable abbrev ETkX (I : ISA) (P : Sys) (hL : Locs P) (tid : Nat) : SharedEnv :=
  EnvGTDR I Arch.tso tid (tkPlan P) (disp P hL.xo)

/-- A load's resource effect only adds to the thread's write permissions
(`EnvG.takeEff_q_ge`). -/
theorem takeEffX_q_ge {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) (x : Loc) : (r.wr x).q ≤ (a.r.wr x).q :=
  takeEff_q_ge ha x

variable (hL : Locs P) {tid : Nat}

include hL in
/-- **VC `lock xaddl %eax,(next)`** (the hand-out, `rmw .acqRel`): permitted
at `Start`, and every outcome is in `Spin` at the ticket read, below `N + 1`. -/
theorem vcX_xadd (σ : SLR.EnvG.State I) (h : Start P tid σ) {op : Val → Option Val}
    (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (ETkX I P hL tid).ok (.rmw .acqRel P.X.addr P.X.bytes op) σ ∧
      ∀ old (σ' : SLR.EnvG.State I), (ETkX I P hL tid).step (.rmw .acqRel P.X.addr P.X.bytes op) σ old σ' →
        Spin P tid old.toNat σ' :=
  vc_ldaddKA hL Arch.tso (k := .acqRel) (by decide) σ h hop

include hL in
/-- **VC `movl (owner),%ecx`** (the spin's load, an acquire under `Arch.tso`):
a value of another low word keeps `Spin`, the ticket's value gives `Got`. -/
theorem vcX_spin {t : Nat} (σ : SLR.EnvG.State I) (h : Spin P tid t σ) :
    ∀ v (σ' : SLR.EnvG.State I), (ETkX I P hL tid).step (.load .plain false P.O.addr P.O.bytes) σ v σ' →
      (lo v ≠ t → Spin P tid t σ') ∧ (lo v = t → Got P tid t σ') :=
  vc_ldarA hL Arch.tso (k := .plain) (by decide) σ h

include hL in
/-- **VC `movl (counter),%edx`** (an acquire under `Arch.tso`, which may
take): the full counter is kept (`takeEff_wr_full`); under the clean flag the
value read is the ticket, or there is a surplus. -/
theorem vcX_ldc {t : Nat} (σ : SLR.EnvG.State I) (h : Got P tid t σ) :
    ∀ v (σ' : SLR.EnvG.State I), (ETkX I P hL tid).step (.load .plain false P.C.addr P.C.bytes) σ v σ' →
      Read P tid t v σ' :=
  vc_ldrA hL Arch.tso σ h

include hL in
/-- **VC `movl %edx,(counter)`** (a release under `Arch.tso`, to the unplanned
counter): permitted, and afterwards the maximal write is the stored `u`, at
or below `vwOld`, of value `t + 1` under the clean flag without a surplus
(`hu`: the stored value is the loaded one plus one). -/
theorem vcX_stc {t : Nat} {v u : Val} (σ : SLR.EnvG.State I) (h : Read P tid t v σ) (hu : v.toNat = t → u.toNat = t + 1) :
    (ETkX I P hL tid).ok (.store .plain false P.C.addr P.C.bytes u) σ ∧
      ∀ b (σ' : SLR.EnvG.State I), (ETkX I P hL tid).step (.store .plain false P.C.addr P.C.bytes u) σ b σ' →
        Stored P tid t σ' :=
  vc_strA hL Arch.tso (by decide) σ h hu

include hL in
/-- **VC `movl %ecx,(owner)`** (the release of `u4`, low word `t + 1`, a
release under `Arch.tso`): permitted (`CS (t + 1)`), and afterwards `QEnd`. -/
theorem vcX_rel {t : Nat} {u4 : Val} (σ : SLR.EnvG.State I) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1) :
    (ETkX I P hL tid).ok (.store .plain false P.O.addr P.O.bytes u4) σ ∧
      ∀ b (σ' : SLR.EnvG.State I), (ETkX I P hL tid).step (.store .plain false P.O.addr P.O.bytes u4) σ b σ' →
        QEnd P tid σ' :=
  vc_stlrA hL Arch.tso (k := .plain) rfl σ h hu4

end Kraken.Promising.X64.EnvG.TicketX

#print axioms Kraken.Promising.X64.EnvG.TicketX.vcX_xadd
#print axioms Kraken.Promising.X64.EnvG.TicketX.vcX_spin
#print axioms Kraken.Promising.X64.EnvG.TicketX.vcX_ldc
#print axioms Kraken.Promising.X64.EnvG.TicketX.vcX_stc
#print axioms Kraken.Promising.X64.EnvG.TicketX.vcX_rel
