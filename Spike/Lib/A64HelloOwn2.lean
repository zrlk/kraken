/-
**hello.w's owned words for the second thread's allocations** (AArch64): `Spike/Lib/A64WakeOwn2.lean` at hello.w's
extended phase
`phH` (`Spike/Lib/A64HelloPh.lean`) for the owned words around
`wc_main`'s second `scc_rt_alloc_tcb` and `scc_rt_thread_init` calls in
hello.w's listing (`SccCode.helloProg`).

The values are wake's (`WakePh.ownV`, ISA- and program-generic) except the
second TCB's length: hello's `wc_main` header is `0xC00C03`
(`movz x0, #4099; movk x0, #192, lsl #16`: twelve words of the thread's
record, three of its arguments), so `scc_rt_pinned_next` goes `112 → 272`
(wake's `112 → 240`).

- `hdr2H`, `pn2H_eq`: the header and the pinned counter after the second TCB.
- `own2aH` (the second `scc_rt_alloc_tcb` call: `scc_rt_pinned_next`
  `112 → 272`), `own2bH` (the second `scc_rt_thread_init` call:
  `scc_rt_stack_next` `16384 → 32768`).
- `ph2aH := phH % 4`, `ph2bH := phH % 16` (the instances' phase
  projections, wake's `WakeTcb2.ph2a` / `WakeTake2.ph2b`), their table
  forms `ph2aHC`, `ph2bHC` and `ph2aH_eq`, `ph2bH_eq`; `own2aH_mod4`,
  `own2bH_mod16`: the lists read only those bits.
- `allocTcb2H_ph`, `threadInit2H_ph`: `wc_main`'s two `bl`s and their return
  points are at phase `16`, the callees' entries at `13` and `12`.
- `own1_own2aH`, `own2a_own2bH` (at the phase indices) and
  `own1_own2aH_ph`, `own2a_own2bH_ph` (at the pcs, through `phH` and the
  projections): the switches agree on the list.
- `instOk2aH`, `instOk2bH`: the instances' facts at `phH`.
-/
import Spike.Lib.A64HelloPh
import Spike.Lib.A64WakeOwn2

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (okPcOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (InstOk RuntimeLayout)
open Spike.Lib.A64.WakePh (ownV ownW ownW_eq)

/-! ## The values -/

/-- `wc_main`'s header for the second TCB in hello.w (`movz x0, #4099; movk x0, #192, lsl #16`). -/
abbrev hdr2H : BitVec 64 := 12587011#64

/-- The second TCB's bytes after the first's 112. -/
theorem pn2H_eq : 112#64 + Spike.Lib.A64.Flow.Ret0.AllocTcb.lenOf hdr2H = 272#64 := by decide

/-- **The second `scc_rt_alloc_tcb` call's instance**: `scc_rt_pinned_next`
`112 → 272`, `scc_rt_stack_next` `16384`, `scc_rt_nthreads` `1`. -/
def own2aH (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 112#64 272#64 16384#64 16384#64 1#64 1#64

/-- **The second `scc_rt_thread_init` call's instance**: `scc_rt_pinned_next`
`272`, `scc_rt_stack_next` `16384 → 32768`, `scc_rt_nthreads` `1`. -/
def own2bH (L : RuntimeLayout) (a : BitVec 64) : Nat → List (Loc × Val) :=
  ownV L a 272#64 272#64 16384#64 32768#64 1#64 1#64

/-! ## The phase projections -/

/-- **The second `scc_rt_alloc_tcb` call's phase projection**: the canonical
bits `0` and `1` of `phH`. -/
def ph2aH (pc : Nat) : Nat := phH pc % 4

/-- The projection through the resolved tables. -/
def ph2aHC (pc : Nat) : Nat := phC pc % 4

theorem ph2aH_eq : ph2aH = ph2aHC := by
  funext pc; unfold ph2aH ph2aHC; rw [phH_eq]

/-- **The second `scc_rt_thread_init` call's phase projection**: the
canonical bits `0`-`3` of `phH`. -/
def ph2bH (pc : Nat) : Nat := phH pc % 16

/-- The projection through the resolved tables. -/
def ph2bHC (pc : Nat) : Nat := phC pc % 16

theorem ph2bH_eq : ph2bH = ph2bHC := by
  funext pc; unfold ph2bH ph2bHC; rw [phH_eq]

/-- **`own2aH` reads the phase's bits `0` and `1` only.** -/
theorem own2aH_mod4 (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : own2aH L a (i % 4) = own2aH L a i := by
  have h1 : i % 4 % 2 = i % 2 := by omega
  have h2 : i % 4 / 2 % 2 = i / 2 % 2 := by omega
  unfold own2aH ownV
  rw [h1, h2]
  simp

/-- **`own2bH` reads the phase's bits `0`-`3` only.** -/
theorem own2bH_mod16 (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : own2bH L a (i % 16) = own2bH L a i := by
  have h1 : i % 16 % 2 = i % 2 := by omega
  have h2 : i % 16 / 2 % 2 = i / 2 % 2 := by omega
  have h4 : i % 16 / 4 % 2 = i / 4 % 2 := by omega
  unfold own2bH ownV
  rw [h1, h2, h4]
  simp

/-! ## The switches -/

/-- `wc_main`'s second `bl scc_rt_alloc_tcb` (`.sp3 + 16`) and its return
point `.sp4` are at phase `16`, the callee's entry at `13`. -/
theorem allocTcb2H_ph : phC 2169744 = 16 ∧ phC 2169748 = 16 ∧ phC 2164748 = 13 := by decide +kernel

/-- `wc_main`'s second `bl scc_rt_thread_init` (`.sp4 + 20`) and its return
point `.sp6` are at phase `16`, the callee's entry at `12`. -/
theorem threadInit2H_ph : phC 2169768 = 16 ∧ phC 2169772 = 16 ∧ phC 2165284 = 12 := by decide +kernel

/-- The pcs above are the listing's (`.sp3`, `.sp4`, `.sp6`, the callees'
labels at the canonical base). -/
theorem switch_pcs :
    Scc.Cert.Link.A64.codeOf lo SccCode.helloProg ".L22_wc_main.sp3" = some (2169744 - 16) ∧
    Scc.Cert.Link.A64.codeOf lo SccCode.helloProg ".L22_wc_main.sp4" = some 2169748 ∧
    Scc.Cert.Link.A64.codeOf lo SccCode.helloProg ".L22_wc_main.sp6" = some 2169772 ∧
    Scc.Cert.Link.A64.codeOf lo SccCode.helloProg "scc_rt_alloc_tcb" = some 2164748 ∧
    Scc.Cert.Link.A64.codeOf lo SccCode.helloProg "scc_rt_thread_init" = some 2165284 := by
  rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- **The first switch**: past `wc_main`'s second `bl scc_rt_alloc_tcb`
(phase `16`, the first instance) at the callee's entry (`13`, the second)
the lists agree. -/
theorem own1_own2aH (L : RuntimeLayout) (a : BitVec 64) : ownW L a 16 = own2aH L a 13 := by
  rw [ownW_eq]; unfold own2aH ownV; simp

/-- **The second switch**: past `wc_main`'s second `bl scc_rt_thread_init`
(phase `16`, the second instance) at the callee's entry (`12`, the third)
the lists agree. -/
theorem own2a_own2bH (L : RuntimeLayout) (a : BitVec 64) : own2aH L a 16 = own2bH L a 12 := by
  unfold own2aH own2bH ownV; simp

/-- **The first switch at the two phase maps**: `ownH` through `phH` at the
`bl`, `own2aH` through `ph2aH` at the callee's entry. -/
theorem own1_own2aH_ph (L : RuntimeLayout) (a : BitVec 64) :
    ownH L a (phH 2169744) = own2aH L a (ph2aH 2164748) := by
  have h1 : phH 2169744 = 16 := by rw [phH_eq]; exact allocTcb2H_ph.1
  have h2 : ph2aH 2164748 = 1 := by rw [ph2aH_eq]; unfold ph2aHC; rw [allocTcb2H_ph.2.2]
  rw [h1, h2, ownH, ownW_eq]; unfold own2aH ownV; simp

/-- **The second switch at the two phase maps**: `own2aH` through `ph2aH` at
the `bl`, `own2bH` through `ph2bH` at the callee's entry. -/
theorem own2a_own2bH_ph (L : RuntimeLayout) (a : BitVec 64) :
    own2aH L a (ph2aH 2169768) = own2bH L a (ph2bH 2165284) := by
  have h1 : ph2aH 2169768 = 0 := by rw [ph2aH_eq]; unfold ph2aHC; rw [threadInit2H_ph.1]
  have h2 : ph2bH 2165284 = 12 := by rw [ph2bH_eq]; unfold ph2bHC; rw [threadInit2H_ph.2.2]
  rw [h1, h2]; unfold own2aH own2bH ownV; simp

/-! ## The instances -/

/-- **The instance's facts at `phH` for any owned words by phase** `ownOf`
and take's phase `TkH` (`instOkH` at any `ownOf`). -/
theorem instOkVH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
    (ownOf : Nat → List (Loc × Val)) (TkH : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => ownOf (phH (pcOf s)))
      (fun s => TkH (phH (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) phH L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg ownOf h, by simp only [h]⟩
  off := (instOkH hp hlo 0#64 TkH hsite (rS := rS)).off

/-- **`own2aH`'s instance**. -/
theorem instOk2aH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkH : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2aH L a (phH (pcOf s)))
      (fun s => TkH (phH (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) phH L.pfx :=
  instOkVH hp hlo (own2aH L a) TkH hsite

/-- **`own2bH`'s instance**. -/
theorem instOk2bH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkH : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => own2bH L a (phH (pcOf s)))
      (fun s => TkH (phH (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) phH L.pfx :=
  instOkVH hp hlo (own2bH L a) TkH hsite

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.own1_own2aH_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.own1_own2aH_ph

/-- info: 'Spike.Lib.A64.HelloPh.own2a_own2bH_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.own2a_own2bH_ph

/-- info: 'Spike.Lib.A64.HelloPh.instOk2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.instOk2aH

/-- info: 'Spike.Lib.A64.HelloPh.instOk2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.instOk2bH
