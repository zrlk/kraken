/-
**The second `scc_rt_thread_init` call's fence at hello** (x86-64; the twin of `Spike/Lib/A64HelloTi2HatG.lean`,
and the hello twin of `Spike/Lib/X64WakeTi2HatG.lean`): the per-state facts the second thread init's node
obligations carry inside hello's level, off hello's clone (`.Lwc_main.x3 + 94`, `X64HelloPreA.clonePcH`) and at
the take site with the child's stack `r1Of` the site's range, main's stack owned and the child's not yet in
private memory.

Reused from wake as is (layout generic, no hello copy): `Ti2.r0_owned` (main's stack owned from the frame's
`StackM`), `Ti2.takeOkA_tpX` (`TakeOkA` under `tpXa`), `Pz.pz_not_stackM`, `Pz.pz_fstable`.

Hello's copies (they read hello's labels or `wc_main`'s frame):

- `ne_clonePc_tiH`: the runtime functions' pcs are off hello's clone's.
- `X0TH`, `x0TH_ti`: the fence and its states in the runtime functions off the take site.
- `x0TH_sitePz`: `X0TH` at the take site from the site frame `Pz r1Of`.
- `pz_fstable_ti2H`: `Pz r1Of` kept by the frames of the thread init's region `R.callee (-136) (-248) 8`, `R`'s
  base `96` below `r1Of` (`BoxPureH`'s geometry, the call's return slot `-136`, `wcNIH`).

Unlike AArch64: the labels are resolved by `codeLabel lo helloCells` (A64 `codeOf lo helloProg`), read off
`HelloPh.labs_eqH`; the clone is the `syscall` at `.Lwc_main.x3 + 94` (A64's `svc` at `.L22_wc_main.sp6 + 100`),
past `scc_rt_stack_release`; the thread init's region is `R.callee (-136) (-248) 8`, its high end `8` the return
address (A64 `R.callee (-144) (-256) 0`), and `R`'s base is `96` below `r1Of` (A64 `80`).
-/
import Spike.Lib.X64WakeTi2HatG
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64HelloWcInv

namespace Spike.Lib.X64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (pcOf abi codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.X64HelloPreA (clonePcH)
open Spike.Lib.X64.WakePh (inPc)

variable {L : RuntimeLayout}

/-- **The runtime functions' pcs are off hello's clone's**: the clone's pc is `wc_main`'s, `.x25 + 94`, past
`scc_rt_stack_release`. Unlike AArch64 (`.L22_wc_main.sp6 + 100`), the addresses are `labs_eqH`'s. -/
theorem ne_clonePc_tiH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (h : inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) : pcOf s ≠ clonePcH L := by
  obtain ⟨-, -, -, hr, -, h25, -, -, -⟩ := labs_eqH hlab (L := L)
  have e : clonePcH L = (L.lab ".Lwc_main.x3").toBitVec.toNat + 94 := by
    show ((L.lab ".Lwc_main.x3").toBitVec + 94#64).toNat = _
    rw [BitVec.toNat_add, h25]; rfl
  rw [e, h25]; unfold inPc at h; rw [hr] at h; omega

/-- **The fence of the second `scc_rt_thread_init` call at hello**: off hello's clone's pc, and at the take pc
`a` the child's stack the site's range, main's stack owned, the child's not in private memory. Unlike AArch64,
the clone's pc is `X64HelloPreA.clonePcH`'s (`.Lwc_main.x3 + 94`). -/
def X0TH (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ clonePcH L ∧ (pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.X64.Flow.Ret0.StackM (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- `X0TH` holds at every state off the clone's pc and off the take pc (its site clause vacuous there). -/
example {a : Int64} {s : State} (hc : pcOf s ≠ clonePcH L) (ha : pcOf s ≠ a.toBitVec.toNat) : X0TH L a s :=
  ⟨hc, fun h => absurd h ha⟩

/-- **`X0TH` in the runtime functions off the take site**, the take pc `a` the site's. Unlike AArch64, the labels
are `helloCells`'. -/
theorem x0TH_ti (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {a : Int64}
    (ha : a = L.lab siteL) :
    ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab siteL).toBitVec.toNat → X0TH L a s :=
  fun _ hi hs => ⟨ne_clonePc_tiH hlab hi, fun h => absurd (ha ▸ h) hs⟩

/-- **`X0TH` at the take site from the site frame `Pz r1Of`**: from its range, main's stack owned there under the
frame and the site's extra facts `P` (`hOw`, e.g. `Ti2.r0_owned`), the child's stack not in private memory from
its first word unmapped (`Pz.pz_not_stackM`), the site off the clone's pc. Unlike AArch64, `Pz` and `StackM` are
x86-64's (`X64Consumer.Pz`, `X64.Flow.Ret0.StackM`). -/
theorem x0TH_sitePz {a : Int64} {F : MachineData → Prop} {P : State → Prop}
    (hc : (L.lab siteL).toBitVec.toNat ≠ clonePcH L)
    (hOw : ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab → F s.st.1 → P s →
      Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of L.lab) s) :
    ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.X64.Rt.PreChild.r1Of L.lab → F s.st.1 →
      Spike.Lib.X64Consumer.Pz (Spike.Lib.X64.Rt.PreChild.r1Of L.lab) s.st.1 → P s → X0TH L a s :=
  fun s hp hr hF hz hP => ⟨hp ▸ hc, fun _ => ⟨hr, hOw s hp hr hF hP,
    Spike.Lib.X64.WakePh.Pz.pz_not_stackM (Spike.Lib.X64.WakePh.Pz.r1Of_lo_al L)
      (by exact (by decide : 8 ≤ 16384)) hz⟩⟩

/-- **`Pz r1Of` is kept by the thread init's region's frames**: the region `R.callee (-136) (-248) 8` has its top
`128` below `R`'s base, itself `96` below `r1Of` (`hbase`, `BoxPureH`'s). Unlike AArch64 (`R.callee (-144)
(-256) 0`, base `80` below), the region's high end is `8`, the pushed return address. -/
theorem pz_fstable_ti2H {R : Spike.Lib.Region} (hbase : R.base.toNat + 96 = L.stacksA.toNat + 16384) :
    Spike.Lib.X64.FStable (R.callee (-136) (-248) 8)
      (Spike.Lib.X64Consumer.Pz (Spike.Lib.X64.Rt.PreChild.r1Of L.lab)) := by
  have hst := L.stacks_sub
  have hpf := L.pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hr1 : (Spike.Lib.X64.Rt.PreChild.r1Of L.lab).lo = L.stacksA.toNat + 16384 := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 16384#64).toNat = _
    rw [L.lab_stacks, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hx := R.base.isLt
  have hb : (R.callee (-136) (-248) 8).base.toNat = R.base.toNat - 136 := by
    show (R.base + BitVec.ofInt 64 (-136)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofInt]
    have : ((-(136 : Int)) % (2 ^ 64 : Nat) : Int).toNat = 2 ^ 64 - 136 := by omega
    rw [this]; omega
  refine Spike.Lib.X64.WakePh.Pz.pz_fstable (Spike.Lib.X64.WakePh.Pz.r1Of_fit L) ?_
  rw [hb, hr1]; show ((R.base.toNat - 136 : Nat) : Int) + 8 ≤ _; omega

end Spike.Lib.X64.HelloPh.Ti2

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.ne_clonePc_tiH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.ne_clonePc_tiH

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.x0TH_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.x0TH_ti

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.x0TH_sitePz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.x0TH_sitePz

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.pz_fstable_ti2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.pz_fstable_ti2H
