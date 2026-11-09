/-
**wake.w's owned words for the second thread's allocations** (x86-64; twin
of `Spike/Lib/A64WakeOwn2.lean`): the instances of `InstOk` at wake.w's
extended phase `phW` (`Spike/Lib/X64WakePh.lean`) for the owned words
around `wc_main`'s second `scc_rt_alloc_tcb` and `scc_rt_thread_init`
calls.

The four counters and `scc_rt_nthreads` take one value before and one after
their write, chosen by the phase index's bits (`X64PhRec.ownOf`'s): `ownV`.
Three instances, switched where both give the same list:

- `ownW` (`own1`): `scc_rt_start` and `wc_main` up to the second
  `call scc_rt_alloc_tcb`; `scc_rt_pinned_next` `0 → 112`,
  `scc_rt_stack_next` `0 → 16384`, `scc_rt_nthreads` `0 → 1` (`ownW_eq`).
- `own2a`: the second `scc_rt_alloc_tcb` call and `wc_main` up to the second
  `call scc_rt_thread_init`; `scc_rt_pinned_next` `112 → 240` (`112 + lenOf h`
  at `wc_main`'s header `h = 0x800903`, `pn2_eq`).
- `own2b`: the second `scc_rt_thread_init` call and after;
  `scc_rt_stack_next` `16384 → 32768`.

At each switch, a `call` from `wc_main` (phase `16`) to the callee's entry,
the instances agree on the list (`own1_own2a`, `own2a_own2b`, with the
phases decided in `allocTcb2_ph`, `threadInit2_ph`: the 5-byte `call`s at
`.x2 - 5` and `.x3 - 5`); the owned words change only at the writes.
`instOkV` is `instOkW` for any owned words by phase.
-/
import Spike.Lib.X64WakePh
import Spike.Lib.X64Ret0AllocTcbG

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (okPcOf)
open Scc.Sem.X64 (pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (InstOk RuntimeLayout)

/-- **The owned words at an extended phase index, by their values**:
`scc_rt_pinned_next` `pb` before its add (bit `0` set) and `pa` after,
`scc_rt_stack_lock` by bit `1`, `scc_rt_stack_free_n` `0`,
`scc_rt_stack_next` `xb` before its take (bit `2` set) and `xa` after,
`scc_rt_nthreads` (at `a`) `nb` before its add (bit `4` clear) and `na`
after. -/
def ownV (L : RuntimeLayout) (a : BitVec 64) (pb pa xb xa nb na : BitVec 64) (i : Nat) : List (Loc × Val) :=
  [(⟨L.pnA, 8⟩, (if i % 2 = 1 then pb else pa).setWidth 128),
    (⟨L.lockA, 8⟩, (if i / 2 % 2 = 1 then 1#64 else 0#64).setWidth 128),
    (⟨L.freeNA, 8⟩, (0#64).setWidth 128),
    (⟨L.nextA, 8⟩, (if i / 4 % 2 = 1 then xb else xa).setWidth 128),
    (⟨a, 8⟩, (if i / 16 % 2 = 1 then na else nb).setWidth 128)]

/-- **The first instance** is `ownV` at the first thread's values. -/
theorem ownW_eq (L : RuntimeLayout) (a : BitVec 64) :
    ownW L a = ownV L a 0#64 112#64 0#64 16384#64 0#64 1#64 := by
  funext i
  unfold ownW ownV Spike.Lib.X64.PhRec.ownOf
  rfl

/-- `wc_main`'s header for the second TCB (`movq $8391939, %rdi`). -/
abbrev hdr2 : BitVec 64 := 8391939#64

/-- The second TCB's bytes after the first's 112. -/
theorem pn2_eq : 112#64 + Spike.Lib.X64.Flow.Ret0.AllocTcb.lenOf hdr2 = 240#64 := by decide

/-- **The second `scc_rt_alloc_tcb` call's instance**: `scc_rt_pinned_next`
`112 → 240`, `scc_rt_stack_next` `16384`, `scc_rt_nthreads` `1`. -/
def own2a (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 112#64 240#64 16384#64 16384#64 1#64 1#64

/-- **The second `scc_rt_thread_init` call's instance**: `scc_rt_pinned_next`
`240`, `scc_rt_stack_next` `16384 → 32768`, `scc_rt_nthreads` `1`. -/
def own2b (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 240#64 240#64 16384#64 32768#64 1#64 1#64

/-- `wc_main`'s second `call scc_rt_alloc_tcb` and its return point `.x2`
are at phase `16`, the callee's entry at `13`. -/
theorem allocTcb2_ph : phC 4203405 = 16 ∧ phC 4203410 = 16 ∧ phC 4198992 = 13 := by decide +kernel

/-- `wc_main`'s second `call scc_rt_thread_init` and its return point
`.x3` are at phase `16`, the callee's entry at `12`. -/
theorem threadInit2_ph : phC 4203430 = 16 ∧ phC 4203435 = 16 ∧ phC 4199545 = 12 := by decide +kernel

/-- **The first switch**: past `wc_main`'s second `call scc_rt_alloc_tcb`
(phase `16`, the first instance) at the callee's entry (`13`, the second)
the lists agree. -/
theorem own1_own2a (L : RuntimeLayout) (a : BitVec 64) : ownW L a 16 = own2a L a 13 := by
  rw [ownW_eq]; unfold own2a ownV; simp

/-- **The second switch**: past `wc_main`'s second `call scc_rt_thread_init`
(phase `16`, the second instance) at the callee's entry (`12`, the third)
the lists agree. -/
theorem own2a_own2b (L : RuntimeLayout) (a : BitVec 64) : own2a L a 16 = own2b L a 12 := by
  unfold own2a own2b ownV; simp

/-- **The instance's facts at `phW` for any owned words by phase** `ownOf`
and take's phase `TkW` (`instOkW` at any `ownOf`). -/
theorem instOkV {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
    (ownOf : Nat → List (Loc × Val)) (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => ownOf (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) phW L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg ownOf h, by simp only [h]⟩
  off := (instOkW hp hlo 0#64 TkW hsite (rS := rS)).off

/-- **`own2a`'s instance**. -/
theorem instOk2a {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => own2a L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) phW L.pfx :=
  instOkV hp hlo (own2a L a) TkW hsite

/-- **`own2b`'s instance**. -/
theorem instOk2b {L : RuntimeLayout} (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.X64.PhRec.μ L) (fun s => own2b L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.X64.PhRec.K L rS) (okPcOf lo wakeCells L.Λ) phW L.pfx :=
  instOkV hp hlo (own2b L a) TkW hsite

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ownW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ownW_eq

/-- info: 'Spike.Lib.X64.WakePh.pn2_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.pn2_eq

/-- info: 'Spike.Lib.X64.WakePh.allocTcb2_ph' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.allocTcb2_ph

/-- info: 'Spike.Lib.X64.WakePh.threadInit2_ph' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.threadInit2_ph

/-- info: 'Spike.Lib.X64.WakePh.own1_own2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.own1_own2a

/-- info: 'Spike.Lib.X64.WakePh.own2a_own2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.own2a_own2b

/-- info: 'Spike.Lib.X64.WakePh.instOkV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOkV

/-- info: 'Spike.Lib.X64.WakePh.instOk2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOk2a

/-- info: 'Spike.Lib.X64.WakePh.instOk2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.instOk2b
