/-
**hello.w on AArch64: the emit row at the worker's `write(1, …)`, read off its invariant** (row
B8-EmitShape). The worker's invariant `D.Wi` is closed under `OutTS` (`WSideH.closed`); at a system call
whose instruction faults (`WCompatH.sysExec`) decoding to `write(1, buf, n)`, the only row `OutTS` offers is
`Out.emit`, reached by a frame run (`OutTS.pre`, or `OutTS.top` with `OutT.outL`): `Out.sys` excludes a
`write` to `1` (`SysOk`), `OutT.texit` decodes to `exit`, and every other row executes a non-faulting tree.

The emit row is at the frames the frame run reaches, which need not be the source worker's (the run may
enter or leave `print`), so the shape proved is `EmitShape`'s with a frame run for its local run and the
emit row's clauses (`EmitCl`) at the frames reached (`EmitShapeF`).

- `outL_emit`: an `OutL` row at such a system call is `Out.emit`'s data.
- `outTS_emit`: an `OutTS` row at such a system call is a frame run, then `Out.emit`'s data at the frames
  reached.
- `EmitShapeF`, `emitShapeF`: the shape at any frame-aware worker side whose memory sides model the
  kernel by `abi` and whose system-call instructions fault.
- `emitShapeF_I`: the shape at the placed instance `HelloAssemblyI.DH`.
-/
import Spike.Lib.HelloEmitPh
import Spike.Lib.HelloAssemblyI

namespace Spike.Lib.HelloEmitShapeF

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSegThrS (OutTS)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloKRE (EmitCl)

/-! ## Inverting the rows at a `write(1, …)` -/

section Rows

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {s : isaLSE2.State} {c : Ctl} {buf n : Nat}

/-- **An `OutL` row at a faulting system call decoding to `write(1, buf, n)` is an emit row**: a local run
into the byte controls' `Pw 0`, and `Out.emit`'s byte, return and refusal clauses. -/
theorem outL_emit {ms : MemSide isaLSE2} {X : Frag isaLSE2} (hK : ms.K = some abi)
    (hsx : ∀ t, isaLSE2.exec s = some t → ∃ m, t = .fault m)
    (hd : decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n)) (h : OutL p lbl ms X s c) :
    ∃ (c' : Ctl) (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop), LocalRun p c c' ∧ Pw 0 c' ∧
      (∀ j < n, ∀ c1, Pw j c1 → ms.bo s (buf + j) c1 (Pw (j + 1))) ∧
      (∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ results (.write 1 buf n), WriteRetOk j r →
        X (abi.ret s r) c1 ∧ (j = 0 → writeRefused r = true → Qw c1)) ∧
      (∀ c1, Qw c1 → ms.we s c1) := by
  cases h with
  | out r =>
    cases r with
    | emit K buf' n' Pw Qw hK' _ hd' h0 hb hr hq =>
      rw [hK] at hK'; cases hK'
      rw [hd] at hd'; cases hd'
      obtain ⟨c', hloc, hp⟩ := h0
      exact ⟨c', Pw, Qw, hloc, hp, hb, hr, hq⟩
    | sys K call hK' _ hd' hok =>
      rw [hK] at hK'; cases hK'
      rw [hd] at hd'; cases hd'
      exact absurd rfl (hok.2.2.1 1 buf n rfl)
    | choice P tree he hsil _ =>
      obtain ⟨m, rfl⟩ := hsx _ he
      cases hsil
    | _ =>
      obtain ⟨m, hm⟩ := hsx _ ‹isaLSE2.exec s = some _›
      cases hm
  | ldSt _ _ _ _ _ _ _ _ _ he =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm

/-- **An `OutTS` row at a faulting system call decoding to `write(1, buf, n)`** is a frame run to some
control and frames, then an emit row there: a local run into `Pw 0` (folded into the frame run), and
`Out.emit`'s clauses at the memory side and fragment of the frames reached. -/
theorem outTS_emit {ms : List TermRun.Frame → MemSide isaLSE2} {X : FragS isaLSE2} {fs : List TermRun.Frame}
    (hK : ∀ fs, (ms fs).K = some abi) (hsx : ∀ t, isaLSE2.exec s = some t → ∃ m, t = .fault m)
    (hd : decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n)) (h : OutTS p lbl ms X s c fs) :
    ∃ (c' : Ctl) (fs' : List TermRun.Frame) (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop),
      FrameRun p (c, fs) (c', fs') ∧ Pw 0 c' ∧
      (∀ j < n, ∀ c1, Pw j c1 → (ms fs').bo s (buf + j) c1 (Pw (j + 1))) ∧
      (∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ results (.write 1 buf n), WriteRetOk j r →
        X (abi.ret s r) c1 fs' ∧ (j = 0 → writeRefused r = true → Qw c1)) ∧
      (∀ c1, Qw c1 → (ms fs').we s c1) := by
  cases h with
  | pre c₁ fs₁ hr hL =>
    obtain ⟨c', Pw, Qw, hloc, hp, hb, hret, hq⟩ := outL_emit (hK fs₁) hsx hd hL
    exact ⟨c', fs₁, Pw, Qw, hr.trans (FrameRun.ofLocal hloc fs₁), hp, hb, hret, hq⟩
  | frame s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | fnc k s' c' fs' he _ _ =>
    obtain ⟨m, hm⟩ := hsx _ he
    cases hm
  | top c₁ hr hT =>
    cases hT with
    | outL hL =>
      obtain ⟨c', Pw, Qw, hloc, hp, hb, hret, hq⟩ := outL_emit (hK []) hsx hd hL
      exact ⟨c', [], Pw, Qw, hr.trans (FrameRun.ofLocal hloc []), hp, hb, hret, hq⟩
    | unpk _ _ _ _ _ _ _ _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm
    | texit K _ hK' _ hd' _ =>
      rw [hK []] at hK'; cases hK'
      rw [hd] at hd'; cases hd'
    | fnc _ _ _ he =>
      obtain ⟨m, hm⟩ := hsx _ he
      cases hm

end Rows

/-! ## The emit row's shape -/

variable {ι : Type}

/-- (row B8-EmitShape, with a frame run) **At the worker's `write(1, buf, n)` there is an emit row at the
frames a frame run of the source worker reaches**: at `D.Wi w st (Ctl.of s1) s1.stack`, a frame run of the
source worker to `(c', fs')`, byte controls `Pw` with `Pw 0 c'` and refusal controls `Qw`, and the emit row's
clauses (`EmitCl`) at `fs'`. (`HelloEmitPh.EmitShape` with its local run widened to a frame run and its
clauses at the frames reached.) -/
def EmitShapeF (D : WSideH ι) : Prop :=
  ∀ w st s1 buf n, D.Wi w st (Ctl.of s1) s1.stack → abi.atSys st = true →
    decode abi.nrs (abi.nr st) (abi.arg st) = some (.write 1 buf n) →
    ∃ (c' : Ctl) (fs' : List TermRun.Frame) (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop),
      FrameRun helloSrc (Ctl.of s1, s1.stack) (c', fs') ∧ Pw 0 c' ∧ EmitCl D w st fs' buf n Pw Qw

/-- **The emit row's shape at any frame-aware worker side** whose memory sides model the kernel by `abi`
(`hK`) and whose system-call instructions fault (`hsx`, `WCompatH.sysExec`). -/
theorem emitShapeF {D : WSideH ι} (hK : ∀ w fs, (D.ms w fs).K = some abi)
    (hsx : ∀ w s c fs t, D.Wi w s c fs → abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m) :
    EmitShapeF D := by
  intro w st s1 buf n hW ha hd
  obtain ⟨c', fs', Pw, Qw, hr, hp, hb, hret, hq⟩ :=
    outTS_emit (hK w) (fun t => hsx w st _ _ t hW ha) hd (D.closed w st _ _ hW)
  exact ⟨c', fs', Pw, Qw, hr, hp, hb, hret, hq⟩

/-! ## At the placed instance -/

section Inst

open Spike.Lib.HelloAssemblyI

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (G0 : ιH hp i → Loc → Val → Prop) (P Z X : ιH hp i → FragS isaLSE2)
  (hseg : ∀ w, HelloSegTCSX.SegTCSX (fun s c fs => A64.Flow.Worker.NNH (LH hp i).exe (endH hp i) s ∧ Z w s c fs) (X w)
    helloSrc (SRH hp i w).lbl (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) (P w)
    (fun _ _ _ => False))

/-- **The emit row's shape at the placed instance** (`DH`, any entry `P`, control fact `Z` and segment
`hseg`): `msWH`'s kernel model is `abi`, and the invariant's system-call instructions fault
(`HelloWorkerFields.sysExecH` at `HelloWorkerRR.helloDR_nn`). -/
theorem emitShapeF_I : EmitShapeF (DH hp i G0 P Z X hseg) :=
  haveI := (LH hp i).valid
  emitShapeF (fun _ _ => rfl) (HelloWorkerFields.sysExecH (HelloWorkerRR.helloDR_nn _ _ _ _ _ _ _ _ _ _ _ _ _ _))

end Inst

end Spike.Lib.HelloEmitShapeF

/-- info: 'Spike.Lib.HelloEmitShapeF.outTS_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitShapeF.outTS_emit

/-- info: 'Spike.Lib.HelloEmitShapeF.emitShapeF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitShapeF.emitShapeF

/-- info: 'Spike.Lib.HelloEmitShapeF.emitShapeF_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloEmitShapeF.emitShapeF_I
