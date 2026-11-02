/-
**hello.w's worker side: the compatibility fields** (x86-64; the twin of `Spike/Lib/HelloWorkerFields.lean`,
`X64HelloW1Print.WCompatH`'s `wide`, `noSite`, `sysExec`, `sysOkH`): from an invariant `Wi` inside `NNH ∧ WideX`,
each field in `WCompatH`'s exact form, generic in the record type and the frames (no source program here: the
per-record layer instantiates `Wi := D.Wi`).

- `wideH`, `noSiteH`, `sysExecH`, `sysOkH_of`: the four fields.

## Differences from the AArch64 version

- The fragments are x86-64's: `NNH` (`X64HelloNN`), `WideX` (`X64WideKeep`), the kernel model `Scc.Sem.X64.abi`
  and `Scc.Cert.WideX64.WideSt`.
- `noSiteH` is `X64HelloSites.siteAt_none_of_nnP` (which twins both `A64HelloSites` and `A64HelloSitesH`);
  `sysExecH` is `X64SvcFault.sysExec_of_exe`.
- The cells are `SccCode.helloCells` (AArch64 `helloProg`).
-/
import Spike.Lib.X64HelloSites
import Spike.Lib.X64SvcFault
import Spike.Lib.X64WideKeep

namespace Spike.Lib.X64HelloWorkerFields

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Flow.Worker (NNH safeH AbW AbC)
open Spike.Lib.X64.WideKeep (WideX)

variable {ι κ φ : Type} {Wi : ι → State → κ → φ → Prop} {exe : _root_.Executable} {endPc : Int64}

/-- (`WCompatH.wide`) The worker's states are in the wide fragment. -/
theorem wideH (hW : ∀ w s c fs, Wi w s c fs → NNH exe endPc s ∧ WideX exe s) :
    ∀ w s c fs, Wi w s c fs → Scc.Cert.WideX64.WideSt s :=
  fun w s c fs h => (hW w s c fs h).2.1

/-- (`WCompatH.noSite`) The worker is at no transfer site, at marks whose sites are the two labels' addresses
(`hμ`). -/
theorem noSiteH [Kraken.Executable.ValidLayout exe] {kp : Nat} {μ : Scc.Sem.Marks}
    (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (hW : ∀ w s c fs, Wi w s c fs → NNH exe endPc s ∧ WideX exe s) :
    ∀ w s c fs, Wi w s c fs → Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi μ s = none :=
  fun w s c fs h => Spike.Lib.X64.HelloSites.siteAt_none_of_nnP hp hend hμ (hW w s c fs h).1

/-- (`WCompatH.sysExec`) At a system call the worker's instruction, if any, faults. -/
theorem sysExecH [Kraken.Executable.ValidLayout exe]
    (hW : ∀ w s c fs, Wi w s c fs → NNH exe endPc s ∧ WideX exe s) :
    ∀ w s c fs t, Wi w s c fs → Scc.Sem.X64.abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m :=
  fun w s c fs t h =>
    Spike.Lib.X64.SvcFault.sysExec_of_exe (Wi := fun (w : ι) s (cf : κ × φ) => Wi w s cf.1 cf.2)
      (fun w s cf h => (hW w s cf.1 cf.2 h).1.1) w s (c, fs) t h

/-- (`WCompatH.sysOkH`) The worker's system calls are `exit`, a `write` to fd 1, at the write abort stub
(`AbW exe`) a `write` to fd 2 or `exit_group(abortStatus)`, or neither a `write` nor `exit_group`. -/
theorem sysOkH_of (hW : ∀ w s c fs, Wi w s c fs → NNH exe endPc s ∧ WideX exe s) :
    ∀ w s c fs call, Wi w s c fs → Scc.Sem.X64.abi.atSys s = true →
      Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) = some call →
      call = .exit ∨ (∃ buf n, call = .write 1 buf n) ∨
        (AbW exe s ∧ ((∃ buf n, call = .write 2 buf n) ∨ call = .exitGroup Scc.Sem.Kernel.abortStatus)) ∨
        ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v) :=
  fun w s c fs call h ha hd => ((hW w s c fs h).1.2.2.2 ha call hd).imp_right fun h =>
    h.imp_right fun h => h.imp_left AbC.toAbW

end Spike.Lib.X64HelloWorkerFields

/-- info: 'Spike.Lib.X64HelloWorkerFields.wideH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerFields.wideH

/-- info: 'Spike.Lib.X64HelloWorkerFields.noSiteH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerFields.noSiteH

/-- info: 'Spike.Lib.X64HelloWorkerFields.sysExecH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerFields.sysExecH

/-- info: 'Spike.Lib.X64HelloWorkerFields.sysOkH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerFields.sysOkH_of
