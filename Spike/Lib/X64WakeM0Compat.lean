/-
**main's compatibility facts after the spawn** (hello plan 1.6,
`post_step0`): what main's steps after the spawn need of the rest of the
proof's data, as one hypothesis `WCompat0`, one field per fact.
The thread-0 counterpart of `Spike/Lib/WakeW1Compat.lean`'s `WCompat`, for a
relation whose `PT0` is `WakeM0.PT0 M` (main's side `M`), whose owned words
are constant (`WakeOwn.wakeOwn` or `X64WakeOwnX.wakeOwnX`) and whose `KR` is `WakeKR.KR r0 r1` (the assembly's
`hPT0`, `hown`, `hKR`).

Difference from AArch64: `own0` reads
`Q.own w 0 s []` in place of `[]`, with the new fields `ownConst0`, `ownMp0`,
`ownCov0`, so that main may own `tcbM` (`X64WakeOwnX.wakeOwnX`). The AArch64
original is unchanged.

x86-64 twin of `Spike/Lib/WakeM0Compat.lean` (same names, namespaces with the
`X64` prefix).
-/
import Spike.Lib.X64WakeM0
import Spike.Lib.X64WakeW1Compat
import Spike.Lib.RelW1

namespace Spike.Lib.X64WakeM0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.Inv2Core
open Spike.Lib.WakeMLive (wlRet)

/-- **main's compatibility facts**, per ghost record `w`. `M` is main's side, `μ` the loaded program's marks, `Λ` the
layout. -/
structure WCompat0 (Q : WakeRel) (M : MSide Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout) : Prop where
  /-- main's rows' placement is the spawn's. -/
  lbl0 : ∀ w, M.lbl w = (Q.SR w).lbl
  /-- main's rows' kernel model is the machine's. -/
  K0 : ∀ w, (M.ms w).K = some abi
  /-- main's rows' runtime invariant is the relation's. -/
  G0 : ∀ w, (M.ms w).G = Q.G w
  /-- (`rfl` at `Q.own = X64WakeOwn.wakeOwn` and at `X64WakeOwnX.wakeOwnX`)
  main's rows own the relation's owned words for thread 0 (at main's empty
  source stack, `PT0`). AArch64 has
  `(M.ms w).own s = []`; on x86-64 main owns its TCB word `tcbM` after the
  spawn (`scc_rt_park` reads it as an owned value). -/
  own0 : ∀ w s, (M.ms w).own s = Q.own w 0 s []
  /-- (with `own0`'s change) main's owned words do not depend on
  its state. -/
  ownConst0 : ∀ w s s', Q.own w 0 s' [] = Q.own w 0 s []
  /-- (with `own0`'s change) main never writes an owned word as
  the runtime's (park's exchange is at `tcbM + 16`, not `tcbM`). -/
  ownMp0 : ∀ w s L v, (L, v) ∈ Q.own w 0 s [] → ¬ (M.ms w).mp L true
  /-- (with `own0`'s change) main's owned words are in its cover
  set (`WakeP.wakeP_own_cov` at the instance). -/
  ownCov0 : ∀ w s L v, (L, v) ∈ Q.own w 0 s [] → (Q.P w).cov 0 L
  /-- A word main may write as the runtime's (the permit's `xchg`,
  the stack growth) is in its footprint, outside every label placed at the
  spawn (so not the flag's `cT`), in a shared region. -/
  mpW0 : ∀ w L, (M.ms w).mp L true →
    (Q.P w).foot 0 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L
  /-- main's states are in the wide fragment. -/
  wide0 : ∀ w s c, M.Mi w s c → Scc.Cert.WideX64.WideSt s
  /-- main is at no transfer site after the spawn. -/
  noSite0 : ∀ w s c, M.Mi w s c → siteAt abi μ s = none
  /-- At a system call main's instruction, if any, faults. -/
  sysExec0 : ∀ w s c t, M.Mi w s c → abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m
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
  flagLd : ∀ w s c (kl : Kraken.LoadKind) (A : BitVec 64) (k : Val → isa.State) (ty : Ty) (wd : TermRun.Word),
    M.Mi w s c → c.term = wlBody → isa.exec s = some (.load kl false ⟨A, 8⟩ fun v => .done (k v)) →
    TermRun.evalAt c.env (.var "c") = some (ty, [wd]) → ValRep (M.lbl w) wd.val A.toNat →
    (∀ v : Val, (v.setWidth 64).toNat ≠ 1 → M.Mi w (k v) c) ∧
    (∀ (v : Val) (w' : TermRun.Word), (v.setWidth 64).toNat = 1 → (M.ms w).rd w' → ValRep (M.lbl w) w'.val 1 →
      M.Mi w (k v) ⟨wlIf, ("d", loadTy ty, [w']) :: c.env, none⟩)
  /-- A certified main at a no-promise state has no promise. -/
  noProm0 : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
    CertOkC Arch.tso (certSem abi Arch.tso μ x 0) 0 t mem → t.prom = []
  /-- main's rows let the source read every word of the number `1`
  (`flagLd`'s value-`1` branch binds `d` to one: the source's load of the
  flag, and a witness inside a certification run). -/
  rd1 : ∀ w (w' : TermRun.Word), w'.val = .num 1 → (M.ms w).rd w'
  /-- main's rows' abort sites are the program's (`rfl`-like at the
  consumers' `abortAt`, vacuous at the default): the `exit_group` the
  kernel lets exit (off every abort site, `Step.sys`) is off `abortAt`, so
  `SysOk`'s `MainExit` applies. -/
  abortAt0 : ∀ w s, (M.ms w).abortAt s → ∃ k a, μ.abortAt k = some a ∧ pcOf s = a
  /-- (the 16th field, for
  `CertReplay.certOkCNA_of_certOkC`) every write of main's instructions is a
  release write, at most one per path (`EvTree.RelW1`): a fresh write kills
  every outstanding promise, so a certification run fulfils before it
  appends. -/
  relW0 : ∀ w s c e, M.Mi w s c → isa.exec s = some e → EvTree.RelW1 Arch.tso e

end Spike.Lib.X64WakeM0
