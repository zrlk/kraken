/-
**The second `scc_rt_thread_init` call's level facts** (AArch64; towards
`HMidP.ti`): the fence `X0` the call's `StartWf.WS` runs at (`X0T`: off the
clone's pc, at the take site the site's range the child's stack, main's
stack owned and the child's not in private memory (`¬ StackM`), `X1W`'s
second clause), from the pc range of the runtime functions (`x0T_ti`) and
at the site from main's stack owned (`hOw`) and the site frame `Pz r1Of`
(`x0T_sitePz`); the take's facts across `tpXa` (`takeOkA_tpX`).

- `r0_owned`: main's stack owned from the frame's `StackM`.
- `ne_clonePc_ti`: the runtime functions' pcs are off the clone's.
- `X0T`, `x0T_ti`, `x1W_of_x0T`.
- `takeOkA_tpX`: `TakeOkA` under `tpXa`.
- `x0T_sitePz`: `X0T` at the take site from the site frame `Pz r1Of`
  (`¬ StackM` by `Pz.pz_not_stackM`).
- `pz_fstable_ti2`: `Pz r1Of` kept by the frames of the thread init's
  region below `wc_main`'s (`R.callee (-80) (-256) 0`, `R`'s base `48`
  below `r1Of`).
-/
import Spike.Lib.A64WakeOwnGEq
import Spike.Lib.A64WakeWcPreWI
import Spike.Lib.A64WakeH1Inv
import Spike.Lib.Rt.A64RtTi2
import Spike.Lib.A64OwnedStackM
import Spike.Lib.A64WakePz

namespace Spike.Lib.A64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib.A64.Flow.WakeWc (clonePc)
open Spike.Lib.A64.Flow.Ret0.StackTake (siteL)

variable {L : RuntimeLayout}

/-- **Main's stack owned** where the frame keeps it in private memory
(main's first take: `StackM` of `r0Of`), the stack inside the pool. -/
theorem r0_owned {F : MachineData → Prop}
    (hF0 : ∀ m, F m → Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) m) {s : State}
    (hF : F s.st.1) : Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s := by
  refine Spike.Lib.A64Consumer.owned_of_stackM ?_ (hF0 _ hF)
  show (⟨(Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 0#64).toNat, 16384⟩ : Scc.Sem.Range).Sub _
  rw [L.lab_stacks, BitVec.add_zero]
  exact L.stacks_sub

/-- **The runtime functions' pcs are off the clone's**: the clone's pc is
`wc_main`'s, after `.sp6`. -/
theorem ne_clonePc_ti (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (h : inPc L "scc_rt_thread_init" "scc_rt_stack_release" s) : pcOf s ≠ clonePc L := by
  obtain ⟨-, -, -, hr, -, h6, -, -, -⟩ := labs_eq hlab (L := L)
  have e : clonePc L = (L.lab ".L21_wc_main.sp6").toBitVec.toNat + 52 := by
    show (L.lab (".L21_wc_main" ++ ".sp6") + Int64.ofNat (4 * 13)).toBitVec.toNat = _
    rw [show (".L21_wc_main" ++ ".sp6" : String) = ".L21_wc_main.sp6" from rfl]
    show ((L.lab ".L21_wc_main.sp6").toBitVec + 52#64).toNat = _
    rw [BitVec.toNat_add, h6]; rfl
  rw [e, h6]; unfold inPc at h; rw [hr] at h; omega

/-- **The fence of the second `scc_rt_thread_init` call's `WS`**: off the
clone's pc, and at the take pc `a` `X1W`'s site clause. -/
def X0T (L : RuntimeLayout) (a : Int64) (s : State) : Prop :=
  pcOf s ≠ clonePc L ∧ (pcOf s = a.toBitVec.toNat →
    Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab ∧
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s ∧
      ¬ Spike.Lib.A64.Flow.Ret0.StackM (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1)

/-- **`X0T` in the runtime functions off the take site** (`ti2_WS`'s `hX0`),
the take pc `a` the site's. -/
theorem x0T_ti (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {a : Int64}
    (ha : a = L.lab siteL) :
    ∀ s, inPc L "scc_rt_thread_init" "scc_rt_stack_release" s →
      pcOf s ≠ (L.lab siteL).toBitVec.toNat → X0T L a s :=
  fun _ hi hs => ⟨ne_clonePc_ti hlab hi, fun h => absurd (ha ▸ h) hs⟩

/-- **`X0T` at the take site from the site frame `Pz r1Of`**: from its
range, main's stack owned there under the frame and the site's extra facts
`P` (`hOw`, e.g. `owned_r0`), the child's stack not in private memory from
its first word unmapped (`Pz.pz_not_stackM`), the site off the clone's pc
(at any take pc `a`: the site clause is the site's facts). -/
theorem x0T_sitePz {a : Int64} {F : MachineData → Prop} {P : State → Prop}
    (hc : (L.lab siteL).toBitVec.toNat ≠ clonePc L)
    (hOw : ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab → F s.st.1 → P s →
      Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of L.lab) s) :
    ∀ s, pcOf s = (L.lab siteL).toBitVec.toNat →
      Scc.Sem.Kernel.siteRange abi s = Spike.Lib.A64.Rt.PreChild.r1Of L.lab → F s.st.1 →
      Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s.st.1 → P s → X0T L a s :=
  fun s hp hr hF hz hP => ⟨hp ▸ hc, fun _ => ⟨hr, hOw s hp hr hF hP,
    Spike.Lib.A64.WakePh.Pz.pz_not_stackM (Spike.Lib.A64.WakePh.Pz.r1Of_lo_al L)
      (by exact (by decide : 8 ≤ 16384)) hz⟩⟩

/-- **`Pz r1Of` is kept by the thread init's region's frames**: the region
`R.callee (-80) (-256) 0` has its top `80` below `R`'s base, itself `48`
below `r1Of` (`hbase`). -/
theorem pz_fstable_ti2 {R : Spike.Lib.Region} (hbase : R.base.toNat + 48 = L.stacksA.toNat + 16384) :
    Spike.Lib.A64.Flow.FStable (R.callee (-80) (-256) 0)
      (Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.PreChild.r1Of L.lab)) := by
  have hst := L.stacks_sub
  have hpf := L.pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  have hr1 : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo = L.stacksA.toNat + 16384 := by
    show (Spike.Lib.A64.Flow.Ret0.stacksA L.lab + 16384#64).toNat = _
    rw [L.lab_stacks, BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hx := R.base.isLt
  have hb : (R.callee (-80) (-256) 0).base.toNat = R.base.toNat - 80 := by
    show (R.base + BitVec.ofInt 64 (-80)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofInt]
    have : ((-(80 : Int)) % (2 ^ 64 : Nat) : Int).toNat = 2 ^ 64 - 80 := by omega
    rw [this]; omega
  refine Spike.Lib.A64.WakePh.Pz.pz_fstable (Spike.Lib.A64.WakePh.Pz.r1Of_fit L) ?_
  rw [hb, hr1]; show ((R.base.toNat - 80 : Nat) : Int) + 0 ≤ _; omega

/-- **`X1W` from `X0T`**: the clone's clause vacuous, the site's `X0T`'s. -/
theorem x1W_of_x0T {a endPc : Int64} {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Spike.Lib.A64Consumer.Lsize}
    {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame} (h : X0T L a s) :
    Spike.Lib.WakeH1Inv.X1W L a endPc lbl lsize s c fs :=
  ⟨fun hc => absurd hc h.1, h.2⟩

/-- **`TakeOkA` under `tpXa`**: none of its facts reads `xa`. -/
theorem takeOkA_tpX {ms : Spike.Lib.MemSide isaLSE2} {t : UInt64} {F0 F : MachineData → Prop}
    {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {q : Spike.Lib.A64.Flow.Ret0.TakeG}
    (h : Spike.Lib.A64.Rt.TakeOkA ms F0 exe endPc R F q) : Spike.Lib.A64.Rt.TakeOkA (tpXa ms t) F0 exe endPc R F q :=
  ⟨{ h.lock1 with }, { h.freeN with }, { h.lock0 with }, { h.next with }, h.ownLock, h.ownFreeN, h.ownNext⟩

end Spike.Lib.A64.WakePh.Ti2

/-- info: 'Spike.Lib.A64.WakePh.Ti2.ne_clonePc_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.ne_clonePc_ti

/-- info: 'Spike.Lib.A64.WakePh.Ti2.x0T_ti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.x0T_ti

/-- info: 'Spike.Lib.A64.WakePh.Ti2.r0_owned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.r0_owned

/-- info: 'Spike.Lib.A64.WakePh.Ti2.x1W_of_x0T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.x1W_of_x0T

/-- info: 'Spike.Lib.A64.WakePh.Ti2.takeOkA_tpX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.takeOkA_tpX

/-- info: 'Spike.Lib.A64.WakePh.Ti2.x0T_sitePz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.x0T_sitePz

/-- info: 'Spike.Lib.A64.WakePh.Ti2.pz_fstable_ti2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.pz_fstable_ti2
