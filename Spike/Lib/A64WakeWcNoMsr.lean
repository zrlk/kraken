/-
**wake.w's `wc_main` obligations at cells other than an `MSR`** (AArch64,
the pre-spawn consumer): every node obligation of `wc_main`'s chain up to
its `clone`'s `svc` (`WcPreW`, `WcSp0W`, `WcMidW`) inside `W` is one inside
`NoMsrW W K` in any valid layout of `wakeProg`, the form
`A64WakeWcMain.wake_wc_entry_segW` and `A64WakeWcHat.wake_wc_mid_hatW` ask.
None of these blocks is an `MSR` (wakeProg's only `MSR` is in the start
code); a node obligation already has `K` not moving its states, so no
premise on `K` is needed.

- `blk_nm`, `node_nm`: `BlkW.noMsr`, `NodeW.noMsr` at a `blockAt` check;
- `WcPreW.noMsr`, `WcSp0W.noMsr`: up to the box's store;
- `reserveW_noMsr`, `WcResW.noMsr`: the reserve and its caller's blocks;
- `tcbWG_noMsr`, `WcSp3W.noMsr`: the second TCB's call;
- `WcSp4W.noMsr`, `WcMidW.noMsr`: to the `svc`;
- `wake_tiPro`, `wcNI_code`: `scc_rt_thread_init`'s first block (the call
  node `wcNI`).
-/
import Spike.Lib.A64WakeWcMain

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.KeepTP (NoMsrAt dNoMsr)
open Spike.Lib.A64.WakePh.WcSp4 (wcNI wcSp4In wake_wcSp4In)
open Spike.Lib.A64.Rt (TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResG ReserveW)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

section NoMsr

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
  {kp : Nat}

/-- **A block node at a checked block with no `MSR`** is inside `NoMsrW W K`. -/
theorem blk_nm {prog : List Directive} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {n : ND} {b : List Directive} {l : Label} {k : Nat} (h : BlkW W K exe endPc R F n b)
    (hb : blockAt prog l k b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hds : b.all dNoMsr = true) : BlkW (NoMsrW W K) K exe endPc R F n b :=
  BlkW.noMsr h (code_of hp hend hb e) hds

/-- **A node at a checked one-instruction block with no `MSR`** is inside
`NoMsrW W K`. -/
theorem node_nm {prog : List Directive} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {n : ND} {d : Directive} {l : Label} {k : Nat} (h : NodeW W K exe endPc R F n)
    (hb : blockAt prog l k [d] = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hds : [d].all dNoMsr = true) : NodeW (NoMsrW W K) K exe endPc R F n :=
  NodeW.noMsr h (code_of hp hend hb e) (by simp) hds

variable (hp : Lays exe SccCode.wakeProg kp) (hend : endPc = endOf exe SccCode.wakeProg kp)
include hp hend

/-- **`wc_main` up to the allocator's return is inside `NoMsrW W K`**. -/
theorem WcPreW.noMsr {ms : MemSide isaLSE2} {J0 Jc : AS → Ctl → Prop}
    (h : WcPreW W K exe endPc R F ms J0 Jc) : WcPreW (NoMsrW W K) K exe endPc R F ms J0 Jc := by
  have hin := wake_wcPro
  simp only [wcPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have he := wake_wcEIn
  simp only [wcEIn, Bool.and_eq_true] at he
  refine ⟨ProW.noMsr h.pro (code_of hp hend b0 ?_) (code_of hp hend b1 ?_) (code_of hp hend b2 ?_)
    (code_of hp hend b3 ?_) (by decide) (by decide) (by decide) (by decide),
    BlkW.noMsr h.e (code_of hp hend he.1 (ofNat4_zero _)) (by decide),
    fun q hok hq => AllocW.noMsr (h.alloc q hok hq) (alloc_code_of hp hend wake_alloc)⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]

/-- **`.sp0` is inside `NoMsrW W K`**. -/
theorem WcSp0W.noMsr {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    (h : WcSp0W W K exe endPc R F ms J0) : WcSp0W (NoMsrW W K) K exe endPc R F ms J0 := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  exact ⟨blk_nm hp hend h.b hin.1 (ofNat4_zero _) (by decide),
    node_nm hp hend h.st (boxSt_eq ▸ hin.2) rfl (by decide)⟩

/-- **`scc_rt_thread_reserve` is inside `NoMsrW W K`**. -/
theorem reserveW_noMsr {q : ResG} (h : ∀ i, ReserveW W K exe endPc R F q i) :
    ∀ i, ReserveW (NoMsrW W K) K exe endPc R F q i := by
  have hin := wake_reserveIn
  simp only [Flow.Reserve.reserveIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨-, r0, r1, r2, r3, r4, r5, r6, r7⟩ := hin
  intro i
  cases i
  · exact blk_nm hp hend (h .e) r0 (ofNat4_zero _) (by decide)
  · exact node_nm hp hend (h .entry) r1 (ofNat4_zero _) (by decide)
  · exact node_nm hp hend (h .add) r2 rfl (by decide)
  · exact blk_nm hp hend (h .arg) r3 rfl (by decide)
  · exact node_nm hp hend (h .rmw) r4 rfl (by decide)
  · exact blk_nm hp hend (h .bnd) r5 rfl (by decide)
  · exact blk_nm hp hend (h .j) r6 rfl (by decide)
  · exact blk_nm hp hend (h .ok) r7 (ofNat4_zero _) (by decide)

/-- **From the fence to `.sp3` is inside `NoMsrW W K`**. -/
theorem WcResW.noMsr {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResW W K exe endPc R F ms J0 S Q) : WcResW (NoMsrW W K) K exe endPc R F ms J0 S Q := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, h5⟩, -⟩ := hin
  exact ⟨node_nm hp hend h.f (pubF_eq ▸ h4) rfl (by decide), blk_nm hp hend h.bl h5 rfl (by decide),
    fun g hg => reserveW_noMsr hp hend (h.res g hg)⟩

/-- **`scc_rt_alloc_tcb` is inside `NoMsrW W K`**. -/
theorem tcbWG_noMsr {q : TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i) :
    ∀ i, TcbWG (NoMsrW W K) K exe endPc R F q i := by
  have hin := Spike.Lib.A64.WakePh.Tcb2W.wake_allocTcbIn
  simp only [Ret0.AllocTcb.allocTcbIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨-, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14⟩ := hin
  intro i
  cases i
  · exact blk_nm hp hend (h .e) t0 (ofNat4_zero _) (by decide)
  · exact blk_nm hp hend (h .entry) t1 (ofNat4_zero _) (by decide)
  · exact blk_nm hp hend (h .j1) t2 rfl (by decide)
  · exact blk_nm hp hend (h .len) t3 (ofNat4_zero _) (by decide)
  · exact node_nm hp hend (h .adrp) t4 rfl (by decide)
  · exact node_nm hp hend (h .add) t5 rfl (by decide)
  · exact blk_nm hp hend (h .arg) t6 rfl (by decide)
  · exact node_nm hp hend (h .rmw) t7 rfl (by decide)
  · exact blk_nm hp hend (h .bnd) t8 rfl (by decide)
  · exact blk_nm hp hend (h .j2) t9 rfl (by decide)
  · exact node_nm hp hend (h .ok) t10 (ofNat4_zero _) (by decide)
  · exact node_nm hp hend (h .ok1) t11 rfl (by decide)
  · exact blk_nm hp hend (h .ok2) t12 rfl (by decide)
  · exact node_nm hp hend (h .hdr) t13 rfl (by decide)
  · exact blk_nm hp hend (h .ret) t14 rfl (by decide)

/-- **From `.sp3` to `.sp4` is inside `NoMsrW W K`**. -/
theorem WcSp3W.noMsr {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp3W W K exe endPc R F c0 cA m fr) : WcSp3W (NoMsrW W K) K exe endPc R F c0 cA m fr := by
  have hin := Spike.Lib.A64.WakePh.Tcb2Call.wake_tcb2CallIn
  simp only [Spike.Lib.A64.WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at hin
  exact ⟨blk_nm hp hend h.blk hin.1 (ofNat4_zero _) (by decide),
    fun g hg => tcbWG_noMsr hp hend (h.tcb g hg)⟩

omit hp hend in
/-- `scc_rt_thread_init`'s first block in `wakeProg`. -/
theorem wake_tiPro : blockAt SccCode.wakeProg Ret0.ThreadInit.fnL 0 Ret0.ThreadInit.tiPro = true := by
  decide +kernel

/-- **From `.sp4` to the `svc` is inside `NoMsrW W K`**. -/
theorem WcSp4W.noMsr {F₂ : MachineData → Prop} {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp4W W K exe endPc R F F₂ c0 t cA m fr) : WcSp4W (NoMsrW W K) K exe endPc R F F₂ c0 t cA m fr := by
  have hin := wake_wcSp4In
  simp only [wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b4, b4s⟩, b5⟩, -⟩, b6⟩, b6f⟩, b6a⟩ := hin
  exact ⟨blk_nm hp hend h.n4 b4 (ofNat4_zero _) (by decide),
    node_nm hp hend h.n4s (tidSt_eq ▸ b4s) rfl (by decide),
    blk_nm hp hend h.n5 b5 rfl (by decide),
    NodeW.noMsr h.nI (code_of hp hend wake_tiPro (ofNat4_zero _)) (by decide) (by decide),
    blk_nm hp hend h.n6 b6 (ofNat4_zero _) (by decide),
    node_nm hp hend h.n6f (fenceB_eq ▸ b6f) rfl (by decide),
    blk_nm hp hend h.n6a b6a rfl (by decide)⟩

/-- **From the box's store to the `svc` is inside `NoMsrW W K`**. -/
theorem WcMidW.noMsr {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J0 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidW W K exe endPc R F F₂ ms J0 S Q) :
    WcMidW (NoMsrW W K) K exe endPc R F F₂ ms J0 S Q :=
  ⟨WcResW.noMsr hp hend h.res, fun c0 cA m fr hM => WcSp3W.noMsr hp hend (h.sp3 c0 cA m fr hM),
    fun c0 cA m fr hM => WcSp4W.noMsr hp hend (h.sp4 c0 cA m fr hM)⟩

end NoMsr

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcPreW.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcPreW.noMsr

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcSp0W.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcSp0W.noMsr

/-- info: 'Spike.Lib.A64.Flow.WakeWc.WcMidW.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.WcMidW.noMsr
