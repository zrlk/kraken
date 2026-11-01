/-
**The second `scc_rt_thread_init` call's fence at hello** (AArch64; the
hello twin of `Spike/Lib/A64WakeTi2HatG.lean`): the per-state facts the
second thread init's node obligations (`HelloPh.Ti2.ti2_WSH`'s `X0`) carry
inside hello's level, off hello's clone (`.L22_wc_main.sp6 + 100`) and at
the take site with the child's stack `r1Of` the site's range, main's stack
owned and the child's not yet in private memory.

Reused from wake as is (layout generic, no hello copy): `Ti2.r0_owned`
(main's stack owned from the frame's `StackM`), `Ti2.takeOkA_tpX`
(`TakeOkA` under `tpXa`), `Pz.pz_not_stackM`, `Pz.pz_fstable`.

Hello's copies (they read hello's labels or `wc_main`'s frame):

- `ne_clonePc_tiH`: the runtime functions' pcs are off hello's clone's.
- `X0TH`, `x0TH_ti`: the fence and its states in the runtime functions off
  the take site.
- `x0TH_sitePz`: `X0TH` at the take site from the site frame `Pz r1Of`.
- `pz_fstable_ti2H`: `Pz r1Of` kept by the frames of the thread init's
  region `R.callee (-144) (-256) 0`, `R`'s base `80` below `r1Of`
  (`HelloHMid.BoxPureH`'s).
-/
import Spike.Lib.A64WakeTi2HatG
import Spike.Lib.A64HelloStartH0Ti

namespace Spike.Lib.A64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)
open Spike.Lib.HelloPreA (clonePcH)
open Spike.Lib.A64.WakePh (lo inPc)

variable {L : RuntimeLayout}

open Spike.Lib.A64.HelloPh.WcW (cvH freeLabsH lab_cvH clone_inCvH) in
/-- **The runtime functions' pcs are off hello's clone's**: the clone's pc
is `wc_main`'s, `.sp6 + 100`, past `scc_rt_stack_release`. -/
theorem ne_clonePc_tiH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {s : State} (h : inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) : pcOf s ≠ clonePcH L := by
  have hl := fun {l : Label} hl => show (L.lab l).toBitVec.toNat = cvH l by
    have := List.all_eq_true.mp freeLabsH l hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact lab_cvH hlab this.1 this.2
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hc.1.1
  have ey : cvH ".L22_wc_main.sp6" = y := by simp [cvH, hy]
  have e : clonePcH L = y + 100 := by
    show (L.lab (".L22_wc_main" ++ ".sp6") + Int64.ofNat (4 * 25)).toBitVec.toNat = y + 100
    rw [show (".L22_wc_main" ++ ".sp6" : String) = ".L22_wc_main.sp6" from rfl, hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 100).toNat = y + 100
    have := hc.1.2; rw [ey] at this
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hd : decide (cvH "scc_rt_stack_release" ≤ cvH ".L22_wc_main.sp6") = true := by
    unfold cvH; rw [← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel
  simp only [decide_eq_true_eq] at hd
  unfold inPc at h
  rw [hl (by simp), hl (by simp)] at h
  rw [e]; omega

/-- **The fence of the second `scc_rt_thread_init` call at hello**: off
hello's clone's pc, and at the take pc `a` the child's stack the site's
range, main's stack owned, the child's not in private memory. -/
def X0TH (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ clonePcH L ∧ (pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- **`X0TH` in the runtime functions off the take site** (`ti2_WSH`'s
`hX0`), the take pc `a` the site's. -/
theorem x0TH_ti (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {a : Int64}
    (ha : a = L.lab siteL) :
    ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab siteL).toBitVec.toNat → X0TH L a s :=
  fun _ hi hs => ⟨ne_clonePc_tiH hlab hi, fun h => absurd (ha ▸ h) hs⟩

/-- **`X0TH` at the take site from the site frame `Pz r1Of`**: from its
range, main's stack owned there under the frame and the site's extra facts
`P` (`hOw`, e.g. `owned_r0H`), the child's stack not in private memory from
its first word unmapped (`Pz.pz_not_stackM`), the site off the clone's pc. -/
theorem x0TH_sitePz {a : Int64} {F : MachineData → Prop} {P : State → Prop}
    (hc : (L.lab siteL).toBitVec.toNat ≠ clonePcH L)
    (hOw : ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab → F s.st.1 → P s →
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s) :
    ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab → F s.st.1 →
      Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1 → P s → X0TH L a s :=
  fun s hp hr hF hz hP => ⟨hp ▸ hc, fun _ => ⟨hr, hOw s hp hr hF hP,
    Spike.Lib.A64.WakePh.Pz.pz_not_stackM (Spike.Lib.A64.WakePh.Pz.r1Of_lo_al L)
      (by exact (by decide : 8 ≤ 16384)) hz⟩⟩

/-- **`Pz r1Of` is kept by the thread init's region's frames**: the region
`R.callee (-144) (-256) 0` has its top `144` below `R`'s base, itself `80`
below `r1Of` (`hbase`). -/
theorem pz_fstable_ti2H {R : Spike.Lib.Region} (hbase : R.base.toNat + 80 = L.stacksA.toNat + 16384) :
    Spike.Lib.A64.Flow.FStable (R.callee (-144) (-256) 0)
      (Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.PreChild.r1Of L.lab)) := by
  have hst := L.stacks_sub
  have hpf := L.pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hr1 : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo = L.stacksA.toNat + 16384 := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 16384#64).toNat = _
    rw [L.lab_stacks, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hx := R.base.isLt
  have hb : (R.callee (-144) (-256) 0).base.toNat = R.base.toNat - 144 := by
    show (R.base + BitVec.ofInt 64 (-144)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofInt]
    have : ((-(144 : Int)) % (2 ^ 64 : Nat) : Int).toNat = 2 ^ 64 - 144 := by omega
    rw [this]; omega
  refine Spike.Lib.A64.WakePh.Pz.pz_fstable (Spike.Lib.A64.WakePh.Pz.r1Of_fit L) ?_
  rw [hb, hr1]; show ((R.base.toNat - 144 : Nat) : Int) + 0 ≤ _; omega

end Spike.Lib.A64.HelloPh.Ti2

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.ne_clonePc_tiH' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.ne_clonePc_tiH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.x0TH_ti' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.x0TH_ti

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.x0TH_sitePz' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.x0TH_sitePz

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.pz_fstable_ti2H' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.pz_fstable_ti2H
