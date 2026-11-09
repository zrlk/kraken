/-
**The two TCB self words at main's clone, from the clone's facts** (x86-64 only; the hello counterpart of
`X64WakeHandover.handover_clone`): at `X64HelloPreA.ClonePreH` (main's `syscall` at `.Lwc_main.x3 + 94` on the
first pool stack), the consumer's `OwnOk` of main's pre-spawn own map `ownGHXW L a` gives both self words'
`OwnVal` (`X64HelloSelfWords.SelfWordsAtClone` at `tcbM L`, `tcbWH L`), the `self` fact the start row consumes.

- `spPool_of_ownedH`: a stack `224` bytes below the top of an owned 16 KiB range is a pool stack
  (`ClonePreH`'s `%rsp`: `scc_rt_main`'s 80 bytes and `wc_main`'s 144).
- `selfWords_clonePre`: `SelfWordsAtClone` at main's thread of `ClonePreH` from `OwnOk (ownGHXW L a th.st)`
  (`X64HelloOwnSX.selfWords_clone`), the clone's state on `L`'s executable (`hX`).

## Differences from the AArch64 version

AArch64 has no counterpart (main owns no TCB word there). Against wake's `handover_clone`: hello's `ClonePreH`
puts `%rsp` `224` bytes below the stack's top (wake: `128`), the clone is at `.Lwc_main.x3 + 94` (wake:
`.x21 + 46`), and the conclusion is the bundled `SelfWordsAtClone` (both `OwnVal`s) rather than membership of the
two words in the own list.
-/
import Spike.Lib.X64HelloOwnSX
import Spike.Lib.X64HelloClonePreH

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (spPool tcbM)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib.X64HelloSelfWords (SelfWordsAtClone)
open Spike.Lib.X64HelloPreA (ClonePreH)
open SccCode (helloCells)

/-- **A stack `224` below the top of an owned 16 KiB range is a pool stack.** -/
theorem spPool_of_ownedH {L : RuntimeLayout} {r0 : Range} {st : State} (hO : X64Consumer.Owned L.Λ r0 st)
    (htop : (st.st.1.regs.get64 .rsp).toNat + 224 = r0.lo + r0.size) (hsz : r0.size = 16384) :
    spPool L st := by
  have hs := hO.1
  simp only [Range.Sub] at hs
  show L.Λ.stackPool.lo < (st.st.1.regs.get64 .rsp).toNat ∧
    (st.st.1.regs.get64 .rsp).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size
  omega

/-- **Both self words at the clone** (see the module doc): main's thread at `ClonePreH` (on `L`'s executable,
`hX`), whose own map `ownGHXW L a` is `OwnOk` (`hown`), has `SelfWordsAtClone` at `tcbM L`, `tcbWH L`. -/
theorem selfWords_clonePre {L : RuntimeLayout} {a : BitVec 64}
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {d : Spike.Lib.X64WakeA64.Cfg}
    {s : TermRun.Cfg} (h : ClonePreH L.Λ r0 r1 X lbl d s) (hX : ∀ st, X st → st.exe = L.exe)
    (hown : ∀ th : Thread isa, d.1.threads = #[th] → Spike.Lib.ExtRows.OwnOk (ownGHXW L a th.st) d.1.mem th.prom) :
    ∃ th : Thread isa, d.1.threads = #[th] ∧ SelfWordsAtClone d.1.mem th.prom (tcbM L) (tcbWH L) := by
  obtain ⟨th, -, -, -, -, -, -, -, -, -, -, -, hth, -, hpc, -, -, -, -, -, -, -, -, -, -, -, -, -, hO, -, hXs, -, -,
    htop, hsz, -⟩ := h
  have hpc' : th.st.st.2 = L.lab ".Lwc_main.x3" + 94 := by
    rw [hpc, Spike.Lib.X64HelloPreA.cloneAtH, hX _ hXs]
  exact ⟨th, hth, selfWords_clone hlab (spPool_of_ownedH hO htop hsz) hpc' (hown th hth)⟩

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.spPool_of_ownedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.spPool_of_ownedH

/-- info: 'Spike.Lib.X64.HelloPh.selfWords_clonePre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.selfWords_clonePre
