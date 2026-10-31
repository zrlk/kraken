/-
**What `wake_start_wc_segW`'s landing gives `wc_main`'s entry** (x86-64; the
x64 twin of `Spike/Lib/A64WakeStartFacts.lean`): read off its post (the heap
abort inside `wc_main`, reached from `wc_main`'s entry invariant
`wJ0 (wNC _ (JS _ _ _)).J σC`).

- `startPost_facts`: the base `v` of the new stack is the top of stack `k0`
  (`swFSL`). So `wc_main`'s region `wR (RS Lsw top) D` is based 56 below the
  top (b), and its depth is `D` (c). At every entry state of `wc_main`,
  `%rdi` is the first TCB's thread pointer `tpOf (pinA + 0 + 8)` (a):
  `scc_rt_main` saved its `%rdi` (`mainE0`) at slot `-16`, and `wNC` passes
  that slot in `%rdi`.
- `wcEntry_rdi`: (a) alone, for any caller state `σC`.
- `wcCallOff`, `allocD`, `reserveD`, `allocTcbD`, `tiD`, `waitD`: the
  frame constants of x86-64 wake.w (`Scc/Test/elf/wakex64/wake.s`):
  `wc_main`'s offset of a callee's region (`pushq %rbp`, `subq $64`, the
  call's return address: `80`) and its callees' depths (`scc_rt_alloc`
  `160`, `scc_rt_thread_reserve` `40`, `scc_rt_alloc_tcb` `184`,
  `scc_rt_thread_init` `248` with the take inside, the tail
  `wc_waitLoop` `88`).
- `wcD`, `wcLsw`: `wc_main`'s depth (`80 + 248 = 328`, its deepest callee
  `scc_rt_thread_init`) and the new stack's (`56 + 328 = 384`: the return
  address of `call scc_rt_main`, `scc_rt_main`'s frame `pushq %rbp`,
  `subq $32` and its call's return address).
- `wcD_callees`: every callee's region fits `wcD`; `wcD_ti`: `wcD` meets the
  second `thread_init`'s `R.lo ≤ -328` (`Ti2.stackM_r0`'s `hRs`).
- `dLsw_ok`: `wcD`, `wcLsw` meet `wake_start_wc_segW`'s depth premises, and
  the new stack's region fits stack `k0` (`16384`).

**Unlike AArch64** (forced by the x64 shape): `scc_rt_main` runs in
`call scc_rt_main`'s callee region `RS Lsw v` (`MainGlue.RS`, 8 below `v`
for the return address), so `wc_main`'s region is based `8 + 48 = 56`
below the top (AArch64: `48`), and `Lsw = 56 + D` (AArch64: `48 + D`).
`D` is computed from x86-64's frames, with the calls' return addresses
(`wcD = 328`, `wcLsw = 384`; AArch64: `336`, `384`). The TCB argument is `%rdi`, carried in
slot `-16` (AArch64: `x0`, slot `-48`), and is the thread pointer
`tpOf tcb` (AArch64: the TCB address). The thread pointer fact is
`TP (tpOf tcb)` (AArch64: `TP (UInt64.ofBitVec tcb)`). There is no alignment
conjunct in the depth facts (`MainGlue` takes `D % 8 = 0`; AArch64:
`D % 16 = 0`).
-/
import Spike.Lib.X64WakeMainGlue

namespace Spike.Lib.X64.WakePh.StartFacts

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (swR At)
open Spike.Lib.X64.Flow.Ret0 (pinA stacksA tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (wX)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS topS tcbS)

/-- **(a) `%rdi` at `wc_main`'s entry is the first TCB's thread pointer**,
for every entry state of `wJ0 (wNC _ (JS L k0 c0)).J σC`. -/
theorem wcEntry_rdi {L : RuntimeLayout} {k0 : BitVec 64} {c0 : Ctl} {σC σe : Spike.Lib.X64.AS} {c : Ctl}
    (h : wJ0 (wNC L.lab (JS L k0 c0)).J σC σe c) : σe.regs.rdi.toBitVec = (tpOf (tcbS L)).toBitVec := by
  obtain ⟨rfl, ⟨σm, hm, -, -, h16, -, -⟩, hrdi, -, -⟩ := h
  exact hrdi.trans (h16.trans hm.2)

/-- **The landing's facts**: at `wake_start_wc_segW`'s post, the new stack's
base is the top of stack `k0`. `wc_main`'s region is based 56 below it (b)
and is `D` deep (c). Every entry state of `wc_main` has `%rdi` the first
TCB's thread pointer (a). -/
theorem startPost_facts {L : RuntimeLayout} {rS : Scc.Sem.Range} {Lsw D : Int} {k0 : BitVec 64} {c0 : Ctl}
    {ms : Spike.Lib.MemSide isa} {s : State} {c : Ctl}
    (h : ∃ v m0 σC,
      At L.exe L.endPc (wR (RS Lsw v) D) (wF (RS Lsw v) D (FS L rS Lsw k0 v) m0 σC)
        (wX ms L.lab (wR (RS Lsw v) D) (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
      TP (tpOf (tcbS L)) s) :
    ∃ m0 σC,
      At L.exe L.endPc (wR (RS Lsw (topS L k0)) D) (wF (RS Lsw (topS L k0)) D (FS L rS Lsw k0 (topS L k0)) m0 σC)
        (wX ms L.lab (wR (RS Lsw (topS L k0)) D) (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
      TP (tpOf (tcbS L)) s ∧
      (∀ σe c', wJ0 (wNC L.lab (JS L k0 c0)).J σC σe c' → σe.regs.rdi.toBitVec = (tpOf (tcbS L)).toBitVec) ∧
      (wR (RS Lsw (topS L k0)) D).base + 56#64 = topS L k0 ∧
      (wR (RS Lsw (topS L k0)) D).lo = -D := by
  obtain ⟨v, m0, σC, hA, hT⟩ := h
  obtain ⟨σ, -, ⟨⟨⟨-, hsw⟩, -⟩, -, -⟩, -⟩ := hA.2.2.2.2
  have hv : v = topS L k0 := hsw.1.1
  subst hv
  refine ⟨m0, σC, hA, hT, fun _ _ h => wcEntry_rdi h, ?_, rfl⟩
  simp only [Spike.Lib.Region.callee, Spike.Lib.Region.addr, swR]
  bv_decide

/-- `wc_main`'s offset of a callee's region below its own region's base:
`pushq %rbp` (8), `subq $64, %rsp` (64), the call's return address (8)
(`wake.s` lines 1403, 1410, 1416). -/
def wcCallOff : Int := 8 + 64 + 8

/-- `scc_rt_alloc`'s region depth: `pushq %rbp`, `subq $144, %rsp`, its
abort call's return address (`wake.s` lines 92, 94, 130;
`X64WakeWcPre.wAR`'s `-160`). -/
def allocD : Int := 8 + 144 + 8

/-- `scc_rt_thread_reserve`'s region depth: `pushq %rbp`, `subq $32, %rsp`
(`wake.s` lines 303, 305; `X64WakeWcRes`'s `-40`). -/
def reserveD : Int := 8 + 32

/-- `scc_rt_alloc_tcb`'s region depth: `pushq %rbp`, `subq $176, %rsp`
(`wake.s` lines 192, 194; `AllocTcb.oI`'s `-184`). -/
def allocTcbD : Int := 8 + 176

/-- `scc_rt_thread_init`'s region depth: its frame to the take's region
(`pushq %rbp`, `subq $32, %rsp`, the call's return address: `48`), then
`scc_rt_stack_take`'s (`pushq %rbp`, `subq $192, %rsp`: `200`) (`wake.s`
lines 339, 343, 381, 383; `Ti2`'s `R.callee (-80) (-248) 8`). -/
def tiD : Int := (8 + 32 + 8) + (8 + 192)

/-- `wc_waitLoop`'s depth below `wc_main`'s base, its tail (`wc_main`'s
frame popped): `pushq %rbp`, `subq $16, %rsp`, the call's return address,
`scc_rt_park`'s `56` (`wake.s` lines 1358, 1375; `X64WaitLoop`'s
`R.lo ≤ -88`). -/
def waitD : Int := 8 + 16 + 8 + 56

/-- **`wc_main`'s depth**: its callee offset and its deepest callee,
`scc_rt_thread_init`. -/
def wcD : Int := wcCallOff + tiD

/-- **The new stack's depth**: `call scc_rt_main`'s return address (8),
`scc_rt_main`'s `pushq %rbp`, `subq $32, %rsp` and its call's return
address (48, `wake.s` lines 44, 51, 58, 62), then `wc_main`'s `wcD`. -/
def wcLsw : Int := 8 + (8 + 32 + 8) + wcD

theorem wcD_eq : wcD = 328 ∧ wcLsw = 384 := by decide

/-- **Every region `wc_main` reaches fits `wcD`**: its callees' at
`wcCallOff`, and its tail's. -/
theorem wcD_callees : wcCallOff + allocD ≤ wcD ∧ wcCallOff + reserveD ≤ wcD ∧ wcCallOff + allocTcbD ≤ wcD ∧
    wcCallOff + tiD ≤ wcD ∧ waitD ≤ wcD := by decide

/-- **`wcD` meets the second `thread_init`'s region bound** (`R.lo ≤ -328`
of `Ti2.stackM_r0`). -/
theorem wcD_ti : -wcD ≤ -328 := by decide

/-- **`wcD`, `wcLsw`** meet `wake_start_wc_segW`'s depth premises, and the
new stack's region fits stack `k0`. -/
theorem dLsw_ok : wcD % 8 = 0 ∧ 240 ≤ wcD ∧ 56 + wcD ≤ wcLsw ∧ wcLsw % 8 = 0 ∧ wcLsw ≤ 16384 := by decide

end Spike.Lib.X64.WakePh.StartFacts

/-- info: 'Spike.Lib.X64.WakePh.StartFacts.startPost_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartFacts.startPost_facts
