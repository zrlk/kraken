/-
**The memory side with allocation, the output's byte step and the write
abort's justification** on the canonical AArch64 target: `msOfA`
(`Spike/Lib/A64ConsumerA.lean`, unchanged) with `bo` and `we` set
(`MemSide.withBW`, `Spike/Lib/MemSideBW.lean`), for a consumer whose rows
include `print`'s `write(1, buf, n)` (`Out.emit`).

- `WeAb abi Ab` (in `Spike/Lib/A64ConsumerA.lean`): the abort justification
  tied to the write abort phase `Ab` (as `SFactsA`'s `abSys` sees it): every
  refused result of the call resumes the thread in `Ab`;
- `msOfAB` (there too): `msOfA` with `bo := ByteOut p lbl`
  (`Spike/Lib/ByteOut.lean`, the byte step `byteOut_emit` consumes) and
  `we := WeAb abi Ab`; `msOfAX … none` is `msOfA` (checked below);
- `msOfAB_bo`, `msOfAB_we`, `sysOk_msOfAB`: its fields, and the system calls
  it matches (`msOfA`'s);
- `Out.msOfAB`, `OutS.msOfAB`, `SegWS.msOfAB`: the rows and segments under
  `msOfA` (no `emit`) are ones under `msOfAB`; `NodesA.toAB`: so node
  obligations at `ab := none` hold at `some Ab`, for every `Ab`;
- `refused_ab_of_emit`: an `Out.emit` row under `msOfAB` at `s` resumes every
  refusal in `Ab` (`Out.we_of_emit`);
- `byteOut_emit_msOfAB`: its byte step is `ByteOut`, consumed by
  `byteOut_emit` (the source emits the kernel's byte).
-/
import Spike.Lib.A64ConsumerA
import Spike.Lib.ByteOut
import Spike.Lib.MemSideBW

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.ByteOut (ByteOut)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Arena} {I : InvS} {Ab : State → Prop} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}

theorem msOfAB_bo : (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs).bo = ByteOut p lbl := rfl

theorem msOfAB_we : (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs).we = WeAb abi Ab := rfl

/-- `msOfAB` matches the system calls `msOfA` does. -/
theorem sysOk_msOfAB {s : State} {c : Ctl} {call : Kernel.Call} :
    SysOk p (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs) s c call ↔
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs) s c call :=
  Iff.rfl

/-- **A row under `msOfA` is one under `msOfAB`** (`msOfA` has no byte step
and justifies no abort). -/
theorem Out.msOfAB {X : Frag isaLSE2} {s : State} {c : Ctl}
    (h : Out p lbl (msOfA Λ μ rd G own ar I lbl lsize fs) X s c) :
    Out p lbl (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs) X s c :=
  withBW_of_none h (fun _ _ _ _ h => h) fun _ _ h => h

/-- **A row at depth under `msOfA` is one under `msOfAB`.** -/
theorem OutS.msOfAB {X : FragS isaLSE2} {s : State} {c : Ctl}
    (h : OutS p lbl (msOfA Λ μ rd G own ar I lbl lsize) X s c fs) :
    OutS p lbl (msOfAB Λ μ p rd G own ar I Ab lbl lsize) X s c fs :=
  h.withBW (fun _ _ _ _ _ h => h.elim) fun _ _ _ h => h.elim

/-- At `none`, the rows' memory side is `msOfA`. -/
example : msOfAX Λ μ p rd G own ar I none = msOfA Λ μ rd G own ar I := rfl

/-- **Node obligations under `msOfA` are ones under `msOfAB`**, for every
write abort phase `Ab`: each row carries over (`OutS.msOfAB`), the rest is
unchanged. -/
theorem NodesA.toAB (h : NodesA Λ p μ rd G own ar I) (Ab : State → Prop) : NodesA Λ p μ rd G own ar I (some Ab) :=
  { h with out := fun lbl lsize s c fs hI ht hc => OutS.msOfAB (h.out lbl lsize s c fs hI ht hc) }

/-- **A segment at depth under `msOfA` is one under `msOfAB`.** -/
theorem SegWS.msOfAB {W : FragS isaLSE2} {K : State → State → Prop} {P Q : FragS isaLSE2}
    (h : SegWS W K p lbl (msOfA Λ μ rd G own ar I lbl lsize) P Q) :
    SegWS W K p lbl (msOfAB Λ μ p rd G own ar I Ab lbl lsize) P Q :=
  h.withBW (fun _ _ _ _ _ h => h.elim) fun _ _ _ h => h.elim

/-- **An output row under `msOfAB` resumes every refusal in `Ab`**: the row's
abort justification at the refusal with no byte out (`Out.we_of_emit`). -/
theorem refused_ab_of_emit {X : Frag isaLSE2} {s : State} {c : Ctl} (K : Kernel.Abi isaLSE2) (buf n : Nat)
    (Pw : Nat → Ctl → Prop) (Qw : Ctl → Prop) (h0 : ∃ c', LocalRun p c c' ∧ Pw 0 c')
    (hr : ∀ j ≤ n, ∀ c1, Pw j c1 → ∀ r ∈ Kernel.results (.write 1 buf n), WriteRetOk j r →
      X (K.ret s r) c1 ∧ (j = 0 → Kernel.writeRefused r = true → Qw c1))
    (hq : ∀ c1, Qw c1 → (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs).we s c1) :
    ∀ r, Kernel.writeRefused r = true → Ab (abi.ret s r) :=
  let ⟨_, h⟩ := Out.we_of_emit K buf n Pw Qw h0 hr hq
  h

/-- **The consumer's byte step under `msOfAB`**: an `Out.emit` row's byte
step (`ms.bo`) at byte `a` from `c1` is `ByteOut`, so `byteOut_emit` gives the
invariant after the kernel's read and the source's emit of that byte into
`Q` (its premises as there). -/
theorem byteOut_emit_msOfAB {P : SrcSem.SrcParams} {Λ' : Scc.Sem.Layout} {ts : Nat → Option Nat}
    {t t' : Thread isaLSE2} {tm : Memory} {A : Arch} {a rdx : Nat} {bt : Fin 256} {c1 : Ctl} {Q : Ctl → Prop}
    {s : TermRun.Cfg} {th : TermRun.TTh}
    (hP : SrcOutProto.UsesWc P p) (hbo : (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs).bo t.st a c1 Q)
    (hinv : Inv1 Λ' lbl lsize ts t tm s.mem) (hwf : Λ'.WF) (hrb : Kernel.readByte abi A t tm a rdx = some (bt, t'))
    (hpriv : ∀ x, (abi.dmem t.st).loadBytes (BitVec.ofNat 64 a) 1 ≠ some [x])
    (hi : s.ths[0]? = some th) (ht : th.term = c1.term) (he : th.env = c1.env) (hσ : th.σs = [])
    (hst : th.stack ≠ []) (hp : th.promises = []) (hx : ∀ x, TermRun.Event.exit x ∉ s.trace)
    (hnum : ∀ sa, wordAddr lbl sa = some (a - a % 8) →
      ∃ j msg n, MemRel.SLatest s.mem sa j ∧ s.mem[j]? = some msg ∧ msg.val = .num n) :
    Inv1 Λ' lbl lsize ts t' tm s.mem ∧
      ∃ th', (SrcSem.source P p).Run s [.out bt]
          { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out bt.val] } ∧
        Q ⟨th'.term, th'.env, none⟩ ∧ th'.σs = [] ∧ th'.stack = th.stack ∧ th'.promises = [] :=
  ByteOut.byteOut_emit hP hbo hinv hwf hrb hpriv hi ht he hσ hst hp hx hnum

end Spike.Lib.A64ConsumerA
