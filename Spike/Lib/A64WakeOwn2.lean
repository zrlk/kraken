/-
**wake.w's owned words for the second thread's allocations** (AArch64):
the instances of `InstOk` at wake.w's extended phase `phW`
(`Spike/Lib/A64WakePh.lean`) for the owned words around `wc_main`'s second
`scc_rt_alloc_tcb` and `scc_rt_thread_init` calls.

The four counters and `scc_rt_nthreads` take one value before and one after
their write, chosen by the phase index's bits (`A64PhRec.ownOf`'s): `ownV`.
Three instances, switched where both give the same list:

- `ownW` (`own1`): `scc_rt_start` and `wc_main` up to the second
  `bl scc_rt_alloc_tcb`; `scc_rt_pinned_next` `0 → 80`, `scc_rt_stack_next`
  `0 → 16384`, `scc_rt_nthreads` `0 → 1` (`ownW_eq`).
- `own2a`: the second `scc_rt_alloc_tcb` call and `wc_main` up to the second
  `bl scc_rt_thread_init`; `scc_rt_pinned_next` `80 → 176` (`80 + lenOf h`
  at `wc_main`'s header `h = 0x800903`, `pn2_eq`).
- `own2b`: the second `scc_rt_thread_init` call and after;
  `scc_rt_stack_next` `16384 → 32768`.

At each switch, a `bl` from `wc_main` (phase `16`) to the callee's entry,
the instances agree on the list (`own1_own2a`, `own2a_own2b`, with the
phases decided in `allocTcb2_ph`, `threadInit2_ph`); the owned words change
only at the writes. `instOkV` is
`instOkW` for any owned words by phase.
-/
import Spike.Lib.A64WakePh
import Spike.Lib.A64Ret0AllocTcbG

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (okPcOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout)

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
    ownW L a = ownV L a 0#64 80#64 0#64 16384#64 0#64 1#64 := by
  funext i
  unfold ownW ownV Spike.Lib.A64.PhRec.ownOf
  rfl

/-- `wc_main`'s header for the second TCB (`movz x0, #2307; movk x0, #128, lsl #16`). -/
abbrev hdr2 : BitVec 64 := 8390915#64

/-- The second TCB's bytes after the first's eighty. -/
theorem pn2_eq : 80#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.lenOf hdr2 = 176#64 := by decide

/-- **The second `scc_rt_alloc_tcb` call's instance**: `scc_rt_pinned_next`
`80 → 176`, `scc_rt_stack_next` `16384`, `scc_rt_nthreads` `1`. -/
def own2a (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 80#64 176#64 16384#64 16384#64 1#64 1#64

/-- **The second `scc_rt_thread_init` call's instance**: `scc_rt_pinned_next`
`176`, `scc_rt_stack_next` `16384 → 32768`, `scc_rt_nthreads` `1`. -/
def own2b (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 176#64 176#64 16384#64 32768#64 1#64 1#64

/-- `wc_main`'s second `bl scc_rt_alloc_tcb` and its return point are at
phase `16`, the callee's entry at `13`. -/
theorem allocTcb2_ph : phC 2169264 = 16 ∧ phC 2169268 = 16 ∧ phC 2164712 = 13 := by decide +kernel

/-- `wc_main`'s second `bl scc_rt_thread_init` and its return point are at
phase `16`, the callee's entry at `12`. -/
theorem threadInit2_ph : phC 2169288 = 16 ∧ phC 2169292 = 16 ∧ phC 2165244 = 12 := by decide +kernel

/-- **The first switch**: past `wc_main`'s second `bl scc_rt_alloc_tcb`
(phase `16`, the first instance) at the callee's entry (`13`, the second)
the lists agree. -/
theorem own1_own2a (L : RuntimeLayout) (a : BitVec 64) : ownW L a 16 = own2a L a 13 := by
  rw [ownW_eq]; unfold own2a ownV; simp

/-- **The second switch**: past `wc_main`'s second `bl scc_rt_thread_init`
(phase `16`, the second instance) at the callee's entry (`12`, the third)
the lists agree. -/
theorem own2a_own2b (L : RuntimeLayout) (a : BitVec 64) : own2a L a 16 = own2b L a 12 := by
  unfold own2a own2b ownV; simp

/-- **The instance's facts at `phW` for any owned words by phase** `ownOf`
and take's phase `TkW` (`instOkW` at any `ownOf`). -/
theorem instOkV {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
    (ownOf : Nat → List (Loc × Val)) (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => ownOf (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) phW L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg ownOf h, by simp only [h]⟩
  off := (instOkW hp hlo 0#64 TkW hsite (rS := rS)).off

/-- **`own2a`'s instance**. -/
theorem instOk2a {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2a L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) phW L.pfx :=
  instOkV hp hlo (own2a L a) TkW hsite

/-- **`own2b`'s instance**. -/
theorem instOk2b {L : RuntimeLayout} (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkW : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (phW (pcOf s)))
      (fun s => TkW (phW (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo wakeProg L.Λ) phW L.pfx :=
  instOkV hp hlo (own2b L a) TkW hsite

end Spike.Lib.A64.WakePh

/-- info: 'Spike.Lib.A64.WakePh.own1_own2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.own1_own2a

/-- info: 'Spike.Lib.A64.WakePh.instOk2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.instOk2a

/-- info: 'Spike.Lib.A64.WakePh.instOk2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.instOk2b
