/-
**hello.w's worker at `print`'s call, at the source, on x86-64** (the twin of
`Spike/Lib/HelloWorkerCallSrc.lean`): the source facts that `wc_worker`'s segment asks of the call's control `Kc`
and `print`'s predicate `Pr`, at hello's own `print` (`X64HelloPrintSrcPub.printPD` on the published slice).

The worker's control at the call is `X64HelloSplit.wcP`; the call pushes `X64HelloW1.uFrame` (the frame
`X64HelloW1.PrintPh` keeps on the stack) and enters `print`'s body; `print`'s predicate is `PrintCP` up to a
pending local run (`PrW`), so it holds at the body's entry (through `printP_entry_run`); at `printN n m` bytes
`print` runs to `ret ()` and the return lands at `X64HelloSplit.wcR`, the `store rel c 1`.

The facts are generic in the abstract state: `Kc` asks the count register `%rsi` at `printN n m` (the bytes
`print` emits); the machine side (`Body.wkC_rsi`, the slice's words in the frame) discharges it.

- `PrWr`, `PrW`: `print`'s predicate, untightened and with the control's term among `print`'s or `printL`'s
  body's terms (`PrW.ext`, `printCP_term`, `PrW.of_printCP`); `KcW`: the call's control.
- `entryC`, `callI_wcP`, `callI_inv`: the call (`CallToI`) at `wcP`, and its only entry and frame.
- `kcW_callI`, `kcW_P0`, `kcW_done`, `kcW_call`: the segment's `hcallI`, `hP0`, `hdone`, `hcall` at
  `Kc := KcW`, `Pr := fun _ => PrW`.

## Differences from the AArch64 version

- The count register is `%rsi` (`(σ.regs.get64 .rsi).toNat`, as `PrintF.printF_callTCSX`'s `hlen`), A64's `x1`.
- Over x86-64's `X64HelloSrc`, `X64HelloSplit`, `X64HelloW1`, `X64HelloPrintSrcPub`, `X64HelloRodataSrc` and
  `CallToI` (`Spike/Lib/X64HelloCallTCS.lean`); the proofs are the original's.
- Only the live constants are twinned: the loop's `prW_load`, `prW_next`, `PrWr.pre` and the model-body facts
  `printBody_eq`, `printLBodyP_eq`, `printNext_eq`, `printBody_ext`, `printLBodyP_ext`, `printNext_ext`,
  `printNext_term`, `printCP_ext` are not.
-/
import Spike.Lib.X64HelloCallTCS
import Spike.Lib.X64HelloW1
import Spike.Lib.PrintTopExt

namespace Spike.Lib.X64HelloWorkerCallSrc

open CoreLang CoreTerm TermRun
open Spike.Lib
open Spike.Lib.X64 (AS)
open Spike.Lib.X64.Flow (CallToI)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (envP wcP wcR workerRestH workerCallH)
open Spike.Lib.X64HelloW1 (uFrame)
open Spike.Lib.X64HelloPrintSrcPub (PrintCP printPD printPD_find printLPD_find)
open Spike.Lib.PrintSrc (printN printBody)

/-! ## The predicates -/

/-- **`print`'s predicate, untightened** on the slice `pw` (`wn` holding
`n`) of `m` words, `k` bytes emitted: a local run to the top of `printL` at
`PrintCP k`. -/
def PrWr (pw wn : Word) (n m k : Nat) (c : Ctl) : Prop :=
  ∃ c1, LocalRunS helloSrc c c1 ∧ PrintCP pw wn n m k c1

/-- **`print`'s predicate**: `PrWr`, the control's term one of `print`'s or
`printL`'s published body's terms (`PrintSvc.printTerms`), so a frame at it
is an `ExternFrame` or reads no variable (`PrW.ext`). -/
def PrW (pw wn : Word) (n m k : Nat) (c : Ctl) : Prop :=
  PrWr pw wn n m k c ∧ (c.term ∈ PrintSvc.printTerms printBody ∨
    c.term ∈ PrintSvc.printTerms X64HelloPrintSrcPub.printLBodyP)

/-- **`PrW`'s term fact**: a term of `print`'s or `printL`'s body is a
model term of the output extern or `ret ()` (`PrintSvc.printTerms_model`). -/
theorem PrW.ext {pw wn : Word} {n m k : Nat} {c : Ctl} (h : PrW pw wn n m k c) :
    c.term ∈ Scc.Sem.externModelTerms ∨ Scc.Sem.exprFv c.term = [] := by
  have e1 : Scc.Frontend.printBody = printBody := rfl
  have e2 : Scc.Frontend.printLPubBody = X64HelloPrintSrcPub.printLBodyP := rfl
  rcases h.2 with h | h
  · rcases PrintSvc.printTerms_model X64HelloW1.printShape_printBody h with h' | h'
    · refine .inl ?_
      unfold Scc.Sem.externModelTerms
      rw [e1]
      simp [h']
    · rw [h']
      exact .inr rfl
  · rcases PrintSvc.printTerms_model X64HelloW1.printShape_printLBodyP h with h' | h'
    · refine .inl ?_
      unfold Scc.Sem.externModelTerms
      rw [e2]
      simp [h']
    · rw [h']
      exact .inr rfl

/-- `PrintCP`'s controls are at `printL`'s published body, one of its terms. -/
theorem printCP_term {pw wn : Word} {n m k : Nat} {c : Ctl} (h : PrintCP pw wn n m k c) :
    c.term ∈ PrintSvc.printTerms X64HelloPrintSrcPub.printLBodyP := by
  obtain ⟨_, _, ht, -⟩ := h
  exact ht ▸ PrintSvc.self_mem_printTerms _

/-- `PrW` at a `PrintCP` control. -/
theorem PrW.of_printCP {pw wn : Word} {n m k : Nat} {c : Ctl} (h : PrintCP pw wn n m k c) : PrW pw wn n m k c :=
  ⟨⟨c, .refl _, h⟩, .inr (printCP_term h)⟩

/-- **The worker's control at `print`'s call** on the packet's words
`w0 w1 w2` (the slice: `m` words, `n` bytes), `w3` (`c`), `w4` (`j`): the
source at `wcP`, the count register `%rsi` at `printN n m`. -/
def KcW (w0 w1 w2 w3 w4 : Word) (n m : Nat) (σ : AS) (c : Ctl) : Prop :=
  c = wcP w0 w1 w2 w3 w4 ∧ (σ.regs.get64 .rsi).toNat = printN n m

/-! ## The call -/

/-- `print`'s body entered on the slice's words. -/
abbrev entryC (w0 w1 w2 : Word) : Ctl := ⟨printBody, [("a", X64HelloRodataSrc.sliceTyP, [w0, w1, w2])], none⟩

/-- **The call at `wcP`**: `print`'s body on the slice's words, the frame
`uFrame`. -/
theorem callI_wcP (w0 w1 w2 w3 w4 : Word) :
    CallToI helloSrc (wcP w0 w1 w2 w3 w4) (entryC w0 w1 w2) (uFrame w0 w1 w2 w3 w4) :=
  ⟨"u", "print", ["q"], .var "sl", workerRestH, printPD, X64HelloRodataSrc.sliceTyP, [w0, w1, w2], rfl,
    printPD_find, rfl, rfl, rfl⟩

/-- **The call at `wcP` is that one**: its entry and frame. -/
theorem callI_inv {w0 w1 w2 w3 w4 : Word} {cE : Ctl} {fr : Frame}
    (h : CallToI helloSrc (wcP w0 w1 w2 w3 w4) cE fr) : cE = entryC w0 w1 w2 ∧ fr = uFrame w0 w1 w2 w3 w4 := by
  obtain ⟨x, f, is, a, e, d, t, ws, ht, hd, ha, rfl, rfl⟩ := h
  simp only [wcP, workerCallH, Expr.let_.injEq, Op.call.injEq] at ht
  obtain ⟨rfl, ⟨rfl, rfl, rfl, -⟩, rfl⟩ := ht
  rw [printPD_find, Option.some.injEq] at hd
  subst hd
  have hw : ws = [w0, w1, w2] := by
    rw [(X64HelloSplit.wcP_call w0 w1 w2 w3 w4).2.1, Option.some.injEq, Prod.mk.injEq] at ha
    exact ha.2.symm
  subst hw
  exact ⟨rfl, rfl⟩

/-! ## The segment's source premises -/

section Prem

variable {w0 w1 w2 w3 w4 : Word} {n m : Nat}

/-- **`hcallI`**: at `KcW` the source calls. -/
theorem kcW_callI {σ : AS} {c : Ctl} (h : KcW w0 w1 w2 w3 w4 n m σ c) : ∃ cE fr, CallToI helloSrc c cE fr :=
  ⟨_, _, h.1 ▸ callI_wcP w0 w1 w2 w3 w4⟩

/-- **`hP0`**: on a nonempty slice (`w1` holding `m ≠ 0`, `w2` holding
`n`), `print`'s predicate at 0 bytes holds at the callee's entry. -/
theorem kcW_P0 (hwm : w1.val = .num m) (hm0 : m ≠ 0) (hwn : w2.val = .num n) {σ : AS} {c cE : Ctl} {fr : Frame}
    (h : KcW w0 w1 w2 w3 w4 n m σ c) (hc : CallToI helloSrc c cE fr) : PrW w0 w2 n m 0 cE := by
  obtain ⟨rfl, -⟩ := h
  obtain ⟨rfl, -⟩ := callI_inv hc
  exact ⟨⟨_, X64HelloPrintSrcPub.printP_entry_run printLPD_find hwm hm0,
    X64HelloPrintSrcPub.printCP_entry hwn hm0⟩, .inl (PrintSvc.self_mem_printTerms _)⟩

/-- **`hdone`**: at the count register's bytes (`printN n m`), `print`
runs to `ret ()` and the return lands at `wcR` on no frames. -/
theorem kcW_done {σ : AS} {c cE c' : Ctl} {fr : Frame} (h : KcW w0 w1 w2 w3 w4 n m σ c)
    (hc : CallToI helloSrc c cE fr) (hP : PrW w0 w2 n m (σ.regs.get64 .rsi).toNat c') :
    FrameRun helloSrc (c', [fr]) (wcR w0 w1 w2 w3 w4, []) := by
  obtain ⟨rfl, hx⟩ := h
  obtain ⟨-, rfl⟩ := callI_inv hc
  rw [hx] at hP
  obtain ⟨⟨c1, r1, hp⟩, -⟩ := hP
  obtain ⟨env, r2⟩ := X64HelloPrintSrcPub.printP_done_run (p := helloSrc) hp
  exact (FrameRun.ofLocalS (r1.trans r2) _).trans (FrameRun.single (.ret rfl rfl rfl))

/-- **`hcall`**: the worker's segment entered at `wcP` (`c0`), the count
register after the `.entry` block (`g σ`) at `printN n m`, the call's
control is `c0` itself. -/
theorem kcW_call {J : AS → Ctl → Prop} {g : AS → AS} {c0 : Ctl} (hc0 : c0 = wcP w0 w1 w2 w3 w4)
    (hx : ∀ σ, J σ c0 → ((g σ).regs.get64 .rsi).toNat = printN n m) :
    ∀ σ, J σ c0 → ∃ c', LocalRun helloSrc c0 c' ∧ KcW w0 w1 w2 w3 w4 n m (g σ) c' :=
  fun σ hJ => ⟨c0, .refl _, hc0, hx σ hJ⟩

end Prem

/-! ## Non-vacuity -/

/-- `KcW`, `PrW` at 0 are realizable: on the two-word, ten-byte slice. -/
example (w0 w3 w4 : Word) (σ : AS) (hx : (σ.regs.get64 .rsi).toNat = 10) :
    KcW w0 (cst (.num 2)) (cst (.num 10)) w3 w4 10 2 σ (wcP w0 (cst (.num 2)) (cst (.num 10)) w3 w4) ∧
      PrW w0 (cst (.num 10)) 10 2 0 (entryC w0 (cst (.num 2)) (cst (.num 10))) := by
  have hk : KcW w0 (cst (.num 2)) (cst (.num 10)) w3 w4 10 2 σ (wcP w0 (cst (.num 2)) (cst (.num 10)) w3 w4) :=
    ⟨rfl, by rw [hx]; rfl⟩
  exact ⟨hk, kcW_P0 rfl (by decide) rfl hk (callI_wcP w0 _ _ w3 w4)⟩

end Spike.Lib.X64HelloWorkerCallSrc

/-- info: 'Spike.Lib.X64HelloWorkerCallSrc.kcW_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerCallSrc.kcW_done

/-- info: 'Spike.Lib.X64HelloWorkerCallSrc.kcW_P0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerCallSrc.kcW_P0

/-- info: 'Spike.Lib.X64HelloWorkerCallSrc.PrW.ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloWorkerCallSrc.PrW.ext
