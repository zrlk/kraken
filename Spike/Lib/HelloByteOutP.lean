/-
**hello.w: the output's byte step for the published `print` loop and the
worker's memory side with it** (C4 §0: the prerequisite of
EmitStepP; the twin of `ByteOut.ByteOut` at `HelloPrintSrcPub`'s controls).

`helloMs` (`HelloMs`) has the defaults `bo := False`, `we := False`, so no
`Out.emit` row exists under it (`Out.we_of_emit`); the worker's `write(1, …)`
in `print` needs a memory side with a byte step and an abort justification.

- `ByteOutP p lbl s a c1 Q`: byte `a` is byte `k` of the location `l` placed
  at `b` (`a = b + k`); from `c1` the source runs locally to the published
  loop's element `idx` of byte `k` (`HelloPrintSrcPub.loadCP`), and whatever
  number `n` the load reads, the control after the byte's `emit` (`nextCP`,
  at the element's locative `elemW pw l (k / 8)`, lane `k % 8` of `n`) runs
  locally into `Q`. The source side of a byte is `loadCP_byte_i` (thread
  `i ≠ 0`).
- `ByteOutP.closed`, `ByteOutP.load`: closed under local runs before and
  after; at `loadCP` into the controls after the `emit`.
- `helloMsW L G lbl lsize AbW`: `helloMs` with `bo := ByteOutP helloSrc lbl`
  and `we := A64ConsumerA.WeAb abi AbW` (a refused `write` resumes the
  worker in the abort-write phase); `helloMsW_K`, `helloMsW_sysOk`: the
  fields the non-emit rows read are `helloMs`'s, so `Out.withBW` moves every
  row under `helloMs` to it.
-/
import Spike.Lib.HelloPrintSrcPub
import Spike.Lib.HelloMs
import Spike.Lib.A64ConsumerA

namespace Spike.Lib.HelloByteOutP

open CoreLang CoreTerm TermRun
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloPrintSrcPub (loadCP nextCP elemW)

/-- **The byte step of the published `print` loop at byte `a`** in state
`s`, from the source control `c1` into `Q` (see the module docstring). -/
def ByteOutP {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (_s : I.State)
    (a : Nat) (c1 : Ctl) (Q : Ctl → Prop) : Prop :=
  ∃ (pw wn : Word) (l b m k : Nat), pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some b ∧ a = b + k ∧
    LocalRun p c1 (loadCP pw wn m k) ∧
    ∀ mw n, mw.val = .num n →
      ∃ c2, LocalRun p (nextCP pw wn m k (elemW pw l (k / 8)) mw (laneN .w8 n (k % 8))) c2 ∧ Q c2

/-- **`ByteOutP` is closed under local runs** before its control and after
its landing. -/
theorem ByteOutP.closed {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {a : Nat} {c c' : Ctl} {Φ Ψ : Ctl → Prop} (hr : LocalRun p c c') (h : ByteOutP p lbl s a c' Φ)
    (hΦ : ∀ c1, Φ c1 → ∃ c2, LocalRun p c1 c2 ∧ Ψ c2) : ByteOutP p lbl s a c Ψ := by
  obtain ⟨pw, wn, l, b, m, k, hpw, hl, ha, hrun, hQ⟩ := h
  refine ⟨pw, wn, l, b, m, k, hpw, hl, ha, hr.trans hrun, fun mw n hmw => ?_⟩
  obtain ⟨c2, r2, h2⟩ := hQ mw n hmw
  obtain ⟨c3, r3, h3⟩ := hΦ c2 h2
  exact ⟨c3, r2.trans r3, h3⟩

/-- **`ByteOutP` at the published loop's element `idx`** of byte `k` of the
location `l` placed at `b`: into the controls after the byte's `emit`. -/
theorem ByteOutP.load {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {pw wn : Word} {l b m k : Nat} (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b) :
    ByteOutP p lbl s (b + k) (loadCP pw wn m k) (fun c => ∃ mw v, c = nextCP pw wn m k (elemW pw l (k / 8)) mw v) :=
  ⟨pw, wn, l, b, m, k, hpw, hl, rfl, .refl _, fun mw _ _ => ⟨_, .refl _, mw, _, rfl⟩⟩

/-- **The worker's memory side with `print`'s byte step and the write
abort's justification**: `helloMs` with `bo := ByteOutP helloSrc lbl`, `we :=
WeAb abi AbW`. -/
def helloMsW (L : RuntimeLayout) (G : Loc → Val → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (AbW : isaLSE2.State → Prop) : MemSide isaLSE2 :=
  (HelloMs.helloMs L G lbl lsize).withBW (ByteOutP HelloSrc.helloSrc lbl) (A64ConsumerA.WeAb Scc.Sem.A64.abi AbW)

variable {L : RuntimeLayout} {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
  {lsize : WeakMem.AllocLabel → Nat} {AbW : isaLSE2.State → Prop}

/-- `helloMsW`'s kernel model is `helloMs`'s. -/
theorem helloMsW_K : (helloMsW L G lbl lsize AbW).K = (HelloMs.helloMs L G lbl lsize).K := rfl

/-- A system call matched under `helloMs` is matched under `helloMsW`. -/
theorem helloMsW_sysOk {p : Prog} {s : isaLSE2.State} {c : Ctl} {call : Scc.Sem.Kernel.Call}
    (h : SysOk p (HelloMs.helloMs L G lbl lsize) s c call) : SysOk p (helloMsW L G lbl lsize AbW) s c call :=
  h

/-- `helloMsW`'s byte step. -/
theorem helloMsW_bo : (helloMsW L G lbl lsize AbW).bo = ByteOutP HelloSrc.helloSrc lbl := rfl

/-- `helloMsW`'s abort justification. -/
theorem helloMsW_we : (helloMsW L G lbl lsize AbW).we = A64ConsumerA.WeAb Scc.Sem.A64.abi AbW := rfl

end Spike.Lib.HelloByteOutP
