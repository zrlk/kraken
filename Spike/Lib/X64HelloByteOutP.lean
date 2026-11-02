/-
**hello.w on x86-64: the output's byte step for the published `print` loop and the worker's memory side with
it** (the twin of `Spike/Lib/HelloByteOutP.lean`; `ByteOut.ByteOut` at `X64HelloPrintSrcPub`'s controls).

`helloMs` (`X64HelloMs`) has the defaults `bo := False`, `we := False`, so no `Out.emit` row exists under it
(`Out.we_of_emit`); the worker's `write(1, …)` in `print` needs a memory side with a byte step and an abort
justification.

- `ByteOutP p lbl s a c1 Q`: byte `a` is byte `k` of the location `l` placed at `b` (`a = b + k`); from `c1` the
  source runs locally to the published loop's element `idx` of byte `k` (`X64HelloPrintSrcPub.loadCP`), and
  whatever number `n` the load reads, the control after the byte's `emit` (`nextCP`, at the element's locative
  `elemW pw l (k / 8)`, lane `k % 8` of `n`) runs locally into `Q`.
- `ByteOutP.closed`, `ByteOutP.load`: closed under local runs before and after; at `loadCP` into the controls
  after the `emit`.
- `helloMsW L G lbl lsize AbW`: `helloMs` with `bo := ByteOutP helloSrc lbl` and `we := X64ConsumerA.WeAb abi
  AbW` (a refused `write` resumes the worker in the abort-write phase).

**Where this differs from AArch64** (forced by the x86-64 shape): the memory side is over `X64.isa`, its runtime
layout `X64.Rt.RuntimeLayout`, the source `X64HelloSrc.helloSrc`, the published loop's controls
`X64HelloPrintSrcPub`'s and the abort justification `X64ConsumerA.WeAb` at `Scc.Sem.X64.abi` (AArch64:
`isaLSE2`, `A64ConsumerA`, `Scc.Sem.A64.abi`). `ByteOutP` itself is ISA-generic, as on AArch64. A64's
`helloMsW_K`, `helloMsW_sysOk`, `helloMsW_bo`, `helloMsW_we` are dead in the hello proof and are not twinned.
-/
import Spike.Lib.X64HelloPrintSrcPub
import Spike.Lib.X64HelloMs
import Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64HelloByteOutP

open CoreLang CoreTerm TermRun
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.SrcSem Scc.Sem.SrcOutProto
open Spike.Lib
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloPrintSrcPub (loadCP nextCP elemW)

/-- **The byte step of the published `print` loop at byte `a`** in state `s`, from the source control `c1` into
`Q` (see the module docstring). -/
def ByteOutP {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (_s : I.State)
    (a : Nat) (c1 : Ctl) (Q : Ctl → Prop) : Prop :=
  ∃ (pw wn : Word) (l b m k : Nat), pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some b ∧ a = b + k ∧
    LocalRun p c1 (loadCP pw wn m k) ∧
    ∀ mw n, mw.val = .num n →
      ∃ c2, LocalRun p (nextCP pw wn m k (elemW pw l (k / 8)) mw (laneN .w8 n (k % 8))) c2 ∧ Q c2

/-- **`ByteOutP` is closed under local runs** before its control and after its landing. -/
theorem ByteOutP.closed {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {a : Nat} {c c' : Ctl} {Φ Ψ : Ctl → Prop} (hr : LocalRun p c c') (h : ByteOutP p lbl s a c' Φ)
    (hΦ : ∀ c1, Φ c1 → ∃ c2, LocalRun p c1 c2 ∧ Ψ c2) : ByteOutP p lbl s a c Ψ := by
  obtain ⟨pw, wn, l, b, m, k, hpw, hl, ha, hrun, hQ⟩ := h
  refine ⟨pw, wn, l, b, m, k, hpw, hl, ha, hr.trans hrun, fun mw n hmw => ?_⟩
  obtain ⟨c2, r2, h2⟩ := hQ mw n hmw
  obtain ⟨c3, r3, h3⟩ := hΦ c2 h2
  exact ⟨c3, r2.trans r3, h3⟩

/-- **`ByteOutP` at the published loop's element `idx`** of byte `k` of the location `l` placed at `b`: into the
controls after the byte's `emit`. -/
theorem ByteOutP.load {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {s : I.State} {pw wn : Word} {l b m k : Nat} (hpw : pw.val = .loc ⟨l, 0⟩ 0) (hl : lbl l = some b) :
    ByteOutP p lbl s (b + k) (loadCP pw wn m k) (fun c => ∃ mw v, c = nextCP pw wn m k (elemW pw l (k / 8)) mw v) :=
  ⟨pw, wn, l, b, m, k, hpw, hl, rfl, .refl _, fun mw _ _ => ⟨_, .refl _, mw, _, rfl⟩⟩

/-- **The worker's memory side with `print`'s byte step and the write abort's justification**: `helloMs` with
`bo := ByteOutP helloSrc lbl`, `we := WeAb abi AbW`. -/
def helloMsW (L : RuntimeLayout) (G : Loc → Val → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (lsize : WeakMem.AllocLabel → Nat) (AbW : isa.State → Prop) : MemSide isa :=
  (X64HelloMs.helloMs L G lbl lsize).withBW (ByteOutP X64HelloSrc.helloSrc lbl)
    (X64ConsumerA.WeAb Scc.Sem.X64.abi AbW)

end Spike.Lib.X64HelloByteOutP

/-- info: 'Spike.Lib.X64HelloByteOutP.ByteOutP.closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloByteOutP.ByteOutP.closed
