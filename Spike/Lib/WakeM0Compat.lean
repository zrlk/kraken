/-
**main's compatibility facts after the spawn** (`post_step0`): what main's steps after the spawn need of the other
owners' data, as one hypothesis `WCompat0` with a named owner per field.
The thread-0 counterpart of `Spike/Lib/WakeW1Compat.lean`'s `WCompat`, for a
relation whose `PT0` is `WakeM0.PT0 M` (main's side `M`), whose owned words
are `WakeOwn.wakeOwn` and whose `KR` is `WakeKR.KR r0 r1` (the assembly's
`hPT0`, `hown`, `hKR`).
-/
import Spike.Lib.WakeM0
import Spike.Lib.WakeW1Compat
import Spike.Lib.RelW1

namespace Spike.Lib.WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.Inv2Core
open Spike.Lib.WakeMLive (wlRet)

/-- **main's compatibility facts**, per ghost record `w`; each field names
its owner. `M` is main's side, `μ` the loaded program's marks, `Λ` the
layout. -/
structure WCompat0 (Q : WakeRel) (M : MSide Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) : Prop where
  /-- main's rows' placement is the spawn's. -/
  lbl0 : ∀ w, M.lbl w = (Q.SR w).lbl
  /-- main's rows' kernel model is the machine's. -/
  K0 : ∀ w, (M.ms w).K = some abi
  /-- main's rows' runtime invariant is the relation's. -/
  G0 : ∀ w, (M.ms w).G = Q.G w
  /-- (`rfl` at `Q.own = WakeOwn.wakeOwn`) main's rows own no word. -/
  own0 : ∀ w s, (M.ms w).own s = []
  /-- A word main may write as the runtime's (the permit's `swpal`,
  the stack growth) is in its footprint, outside every label placed at the
  spawn (so not the flag's `cT`), in a shared region. -/
  mpW0 : ∀ w L, (M.ms w).mp L true →
    (Q.P w).foot 0 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L
  /-- main's states are in the wide fragment. -/
  wide0 : ∀ w s c, M.Mi w s c → Scc.Cert.WideA64.WideSt s
  /-- main is at no transfer site after the spawn. -/
  noSite0 : ∀ w s c, M.Mi w s c → siteAt abi μ s = none
  /-- At a system call main's instruction, if any, faults. -/
  sysExec0 : ∀ w s c t, M.Mi w s c → abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m
  /-- main writes nothing after the spawn, to any descriptor (no
  `Out.emit` row, no `write` returning through `Out.sys`). -/
  noWrite0 : ∀ w s c fd buf n, M.Mi w s c → abi.atSys s = true →
    decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write fd buf n)
  /-- main's pointer word for `c` is an untagged locative to `cS`. -/
  cw0 : ∀ w, (M.cw w).val = .loc (Q.C w).cS 0
  /-- main's source is not at its return in the invariant (it gets
  there only within the `exit_group` row, `MainExit`), so `KR`'s
  `MainLive` is kept. -/
  live0 : ∀ w s c, M.Mi w s c → c.term ≠ wlRet
  /-- **main's flag load**: at `wlBody`, a load of the flag's word
  (the address `c`'s word represents) stutters on every value but `1` and
  takes the source's load on `1` (in place of `OutL.ldSt`'s free value and
  of an `Out.load` at the flag). -/
  flagLd : ∀ w s c (kl : Kraken.LoadKind) (A : BitVec 64) (k : Val → isaLSE2.State) (ty : Ty) (wd : TermRun.Word),
    M.Mi w s c → c.term = wlBody → isaLSE2.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (k v)) →
    TermRun.evalAt c.env (.var "c") = some (ty, [wd]) → ValRep (M.lbl w) wd.val A.toNat →
    (∀ v : Val, (v.setWidth 64).toNat ≠ 1 → M.Mi w (k v) c) ∧
    (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = 1 → (M.ms w).rd w' → ValRep (M.lbl w) w'.val 1 →
      M.Mi w (k v) ⟨wlIf, ("d", loadTy ty, [w']) :: c.env, none⟩)
  /-- A certified main at a no-promise state has no promise. -/
  noProm0 : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
    CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 0) 0 t mem → t.prom = []
  /-- main's rows let the source read every word of the number `1`
  (`flagLd`'s value-`1` branch binds `d` to one: the source's load of the
  flag, and a witness inside a certification run). -/
  rd1 : ∀ w (w' : TermRun.Word), w'.val = .num 1 → (M.ms w).rd w'
  /-- main's rows' abort sites are the program's (`rfl`-like at the
  consumers' `abortAt`, vacuous at the default): the `exit_group` the
  kernel lets exit (off every abort site, `Step.sys`) is off `abortAt`, so
  `SysOk`'s `MainExit` applies. -/
  abortAt0 : ∀ w s, (M.ms w).abortAt s → ∃ k a, μ.abortAt k = some a ∧ pcOf s = a
  /-- (the 16th field, for `CertReplay.certOkCNA_of_certOkC`) every write of main's instructions is a
  release write, at most one per path (`EvTree.RelW1`): a fresh write kills
  every outstanding promise, so a certification run fulfils before it
  appends. -/
  relW0 : ∀ w s c e, M.Mi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e

end Spike.Lib.WakeM0
