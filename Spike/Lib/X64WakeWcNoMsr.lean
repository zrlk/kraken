/-
**wake.w's `wc_main` obligations at cells other than a `syscall`**
(x86-64, the pre-spawn consumer): every node obligation of `wc_main`'s
chain up to its `clone`'s `syscall` (`WcPreW`, `WcSp0W`, `WcMidW`) inside
`W` is one inside `NoSetFsW W K` in any valid layout of `wakeCells`, the
form `X64WakeWcMain.wake_wc_entry_segW` and `X64WakeWcHat.wake_wc_mid_hatW`
ask. None of these blocks is a `syscall` (the `clone`'s `syscall` is past
the last node); a node obligation already has `K` not moving its states, so
no premise on `K` is needed.

- `blk_ns`, `node_ns`: `BlkW.noSetFs`, `NodeW.noSetFs` at a `blockAtB`
  check;
- `WcPreW.noSetFs`, `WcSp0W.noSetFs`: up to the box's store;
- `blkI_ns`, `nodeI_ns`: the same at an indexed `blockAt` check;
- `reserveW_noSetFs`, `WcResW.noSetFs`: the reserve and its caller's call;
- `wake_allocTcbInW`, `tcbWG_noSetFs`, `WcSp3W.noSetFs`: the second TCB's
  call;
- `wake_tiPro`, `WcSp4PreW.noSetFs`: `.x20` up to `scc_rt_thread_init`'s
  call node (`wcNI`);
- `WcCloneW.noSetFs`, `WcClonePW.noSetFs`, `WcSp4W.noSetFs`,
  `WcSp4PW.noSetFs`, `WcMidW.noSetFs`: to the `syscall`.

x86-64 twin of `Spike/Lib/A64WakeWcNoMsr.lean` (namespace
`Spike.Lib.X64.Flow.WakeWc`). **Where this differs from AArch64**: the
thread pointer is `fsBase`, set only by `arch_prctl`, so `NoMsrW` is
`NoSetFsW` (`X64KeepTPW`) and the per-block check is `cNoSys` (no `syscall`;
A64 `dNoMsr`); the names are `*.noSetFs` (A64 `*.noMsr`). The cells are
`wakeCells` with byte offsets (A64 `wakeProg`, `4 * k`). The x86-64
`WcResW` has no fence node (A64 `f`), and the x86-64 reserve has no `add`
node (its `nthreads` address is one `leaq`, the `entry` node). The x86-64
`WcMidW`'s last part is `WcSp4PW` (`.x20` and the clone past the
publication, `WcClonePW`); `WcSp4W`/`WcCloneW` are covered as well.
-/
import Spike.Lib.X64WakeWcMain
import Spike.Lib.X64KeepTPW
import Spike.Lib.X64WakeCloneIn

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.X64.WakePh.WcClone (WcCloneW)
open Scc.Cert.Rt.X64 (Lays endOf blockAt blockAtB code_field label_labelGapB codeAt_blockAt_lays)

section NoSetFs

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
  {kp : Nat}

/-- **A block node at a checked block with no `syscall`** is inside
`NoSetFsW W K`. -/
theorem blk_ns {cells : List (Directive × Nat)} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {b : List (Directive × Nat)} {l : Label} {k : Nat} (h : BlkW W K exe endPc R F n b)
    (hb : blockAtB cells l k b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hds : cNoSys b = true) : BlkW (NoSetFsW W K) K exe endPc R F n b :=
  BlkW.noSetFs h (code_field hp hend hb e) hds

/-- **A node at a checked one-instruction block with no `syscall`** is
inside `NoSetFsW W K`. -/
theorem node_ns {cells : List (Directive × Nat)} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {d : Directive × Nat} {l : Label} {k : Nat} (h : NodeW W K exe endPc R F n)
    (hb : blockAtB cells l k [d] = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hds : cNoSys [d] = true) : NodeW (NoSetFsW W K) K exe endPc R F n :=
  NodeW.noSetFs h (code_field hp hend hb e) (by simp) hds

/-- `blk_ns` at an indexed `blockAt` check (the instruction index `k`, the
byte offset `off`). -/
theorem blkI_ns {cells : List (Directive × Nat)} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {b : List (Directive × Nat)} {l : Label} {k off : Nat} (h : BlkW W K exe endPc R F n b)
    (hb : blockAt cells l k off b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat off = n.pc)
    (hds : cNoSys b = true) : BlkW (NoSetFsW W K) K exe endPc R F n b :=
  BlkW.noSetFs h (fun _ he hn => e ▸ codeAt_blockAt_lays hp he (hn.trans hend) hb) hds

/-- `node_ns` at an indexed `blockAt` check. -/
theorem nodeI_ns {cells : List (Directive × Nat)} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {d : Directive × Nat} {l : Label} {k off : Nat} (h : NodeW W K exe endPc R F n)
    (hb : blockAt cells l k off [d] = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat off = n.pc)
    (hds : cNoSys [d] = true) : NodeW (NoSetFsW W K) K exe endPc R F n :=
  NodeW.noSetFs h (fun _ he hn => e ▸ codeAt_blockAt_lays hp he (hn.trans hend) hb) (by simp) hds

variable (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
include hp hend

/-- **`wc_main` up to the allocator's return is inside `NoSetFsW W K`**. -/
theorem WcPreW.noSetFs {ms : MemSide isa} {J0 Jc : AS → Ctl → Prop}
    (h : WcPreW W K exe endPc R F ms J0 Jc) : WcPreW (NoSetFsW W K) K exe endPc R F ms J0 Jc := by
  have hin := wake_wcPro
  simp only [wcPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label "wc_main" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_main.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have he := wake_wcEIn
  simp only [wcEIn, Bool.and_eq_true] at he
  refine ⟨XProW.noSetFs h.pro (code_field hp hend b0 (ofNat_zero' _)) (code_field hp hend b1 ?_)
    (code_field hp hend b2 ?_) (code_field hp hend b3 ?_) (code_field hp hend b4 ?_),
    BlkW.noSetFs h.e (code_field hp hend he.1 (ofNat_zero' _)) (by decide),
    fun q hok hq => Alloc.AllocW.noSetFs hp hend wake_alloc (h.alloc q hok hq)⟩
  · rw [h4, ofNat_zero']
  · rw [h4]
  · rw [h4, ofNat_add']
  · rw [h4, ofNat_add', ofNat_add', ofNat_add']

/-- **`.x18`'s block and the box's store are inside `NoSetFsW W K`**. -/
theorem WcSp0W.noSetFs {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    (h : WcSp0W W K exe endPc R F ms J0) : WcSp0W (NoSetFsW W K) K exe endPc R F ms J0 := by
  have hin := wake_wcS0In
  simp only [wcS0In, Bool.and_eq_true] at hin
  exact ⟨blk_ns hp hend h.b hin.1 (ofNat_zero' _) (by decide),
    node_ns hp hend h.st hin.2 rfl (by decide)⟩

/-- **`scc_rt_thread_reserve` is inside `NoSetFsW W K`**. -/
theorem reserveW_noSetFs {q : ResG} (h : ∀ i, ReserveW W K exe endPc R F q i) :
    ∀ i, ReserveW (NoSetFsW W K) K exe endPc R F q i := by
  have hin := wake_reserveIn
  simp only [Flow.Reserve.reserveIn, Ret0.AllocTcb.siAt, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨-, r0⟩, r1⟩, r2⟩, r3⟩, r4⟩, r5⟩, r6⟩ := hin
  intro i
  cases i
  · exact blk_ns hp hend (h .e) r0 (ofNat_zero' _) (by decide)
  · exact node_ns hp hend (h .entry) r1 (ofNat_zero' _) (by decide)
  · exact blk_ns hp hend (h .arg) r2 rfl (by decide)
  · exact node_ns hp hend (h .rmw) r3 rfl (by decide)
  · exact blk_ns hp hend (h .bnd) r4 rfl (by decide)
  · exact blk_ns hp hend (h .j) r5 rfl (by decide)
  · exact BlkW.noSetFs (h .ok)
      (Spike.Lib.X64.code_field_blockAcrossB hp hend r6 (List.take_append_drop 3 _) (ofNat_zero' _)) (by decide)

/-- **The reserve's call and the reserve are inside `NoSetFsW W K`**. -/
theorem WcResW.noSetFs {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResW W K exe endPc R F ms J0 Q) : WcResW (NoSetFsW W K) K exe endPc R F ms J0 Q := by
  have hin := wake_wcResIn
  simp only [wcResIn, Bool.and_eq_true] at hin
  exact ⟨blk_ns hp hend h.bl hin.1 rfl (by decide), fun g hg => reserveW_noSetFs hp hend (h.res g hg)⟩

omit hp hend in
/-- `scc_rt_alloc_tcb`'s code in `wakeCells`. -/
theorem wake_allocTcbInW : Ret0.AllocTcb.allocTcbIn SccCode.wakeCells = true := by decide +kernel

/-- **`scc_rt_alloc_tcb` is inside `NoSetFsW W K`**. -/
theorem tcbWG_noSetFs {q : TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i) :
    ∀ i, TcbWG (NoSetFsW W K) K exe endPc R F q i := by
  have hin := wake_allocTcbInW
  simp only [Ret0.AllocTcb.allocTcbIn, Ret0.AllocTcb.fiAt, Ret0.AllocTcb.siAt, Bool.and_eq_true,
    and_assoc] at hin
  obtain ⟨-, t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19,
    t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32⟩ := hin
  intro i
  cases i
  · exact blk_ns hp hend (h .e) t0 (ofNat_zero' _) (by decide)
  · exact blk_ns hp hend (h .entry) t1 (ofNat_zero' _) (by decide)
  · exact blk_ns hp hend (h .j1) t2 rfl (by decide)
  · exact blk_ns hp hend (h .len) t3 (ofNat_zero' _) (by decide)
  · exact node_ns hp hend (h .shr1) t4 rfl (by decide)
  · exact blk_ns hp hend (h .l1) t5 rfl (by decide)
  · exact node_ns hp hend (h .and1) t6 rfl (by decide)
  · exact blk_ns hp hend (h .l2) t7 rfl (by decide)
  · exact node_ns hp hend (h .shr2) t8 rfl (by decide)
  · exact blk_ns hp hend (h .l3) t9 rfl (by decide)
  · exact node_ns hp hend (h .and2) t10 rfl (by decide)
  · exact blk_ns hp hend (h .l4) t11 rfl (by decide)
  · exact node_ns hp hend (h .imul1) t12 rfl (by decide)
  · exact blk_ns hp hend (h .l5) t13 rfl (by decide)
  · exact node_ns hp hend (h .shl1) t14 rfl (by decide)
  · exact blk_ns hp hend (h .l6) t15 rfl (by decide)
  · exact node_ns hp hend (h .lea1) t16 rfl (by decide)
  · exact blk_ns hp hend (h .arg) t17 rfl (by decide)
  · exact node_ns hp hend (h .rmw) t18 rfl (by decide)
  · exact blk_ns hp hend (h .bnd) t19 rfl (by decide)
  · exact blk_ns hp hend (h .j2) t20 rfl (by decide)
  · exact node_ns hp hend (h .ok) t21 (ofNat_zero' _) (by decide)
  · exact blk_ns hp hend (h .o1) t22 rfl (by decide)
  · exact node_ns hp hend (h .imul2) t23 rfl (by decide)
  · exact blk_ns hp hend (h .o2) t24 rfl (by decide)
  · exact node_ns hp hend (h .shl2) t25 rfl (by decide)
  · exact blk_ns hp hend (h .o3) t26 rfl (by decide)
  · exact node_ns hp hend (h .shl3) t27 rfl (by decide)
  · exact blk_ns hp hend (h .o4) t28 rfl (by decide)
  · exact node_ns hp hend (h .or1) t29 rfl (by decide)
  · exact blk_ns hp hend (h .o5) t30 rfl (by decide)
  · exact node_ns hp hend (h .hdr) t31 rfl (by decide)
  · exact BlkW.noSetFs (h .ret)
      (Spike.Lib.X64.code_field_blockAcrossB hp hend t32 (List.take_append_drop 11 _) rfl) (by decide)

/-- **From `.x19` to `.x20` is inside `NoSetFsW W K`**: the call block and
`scc_rt_alloc_tcb`. -/
theorem WcSp3W.noSetFs {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp3W W K exe endPc R F c0 cA m fr) : WcSp3W (NoSetFsW W K) K exe endPc R F c0 cA m fr := by
  have hin := WakePh.Tcb2Call.wake_tcb2CallIn
  simp only [WakePh.Tcb2Call.tcb2CallIn, Bool.and_eq_true] at hin
  exact ⟨blk_ns hp hend h.blk hin.1 (ofNat_zero' _) (by decide),
    fun g hg => tcbWG_noSetFs hp hend (h.tcb g hg)⟩

omit hp hend in
/-- `scc_rt_thread_init`'s first block in `wakeCells`. -/
theorem wake_tiPro : blockAtB SccCode.wakeCells Ret0.ThreadInit.fnL 0 Ret0.ThreadInit.tiPro = true := by
  decide +kernel

/-- **`.x20`'s states up to the call are inside `NoSetFsW W K`**. -/
theorem WcSp4PreW.noSetFs {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp4PreW W K exe endPc R F c0 t cA m fr) : WcSp4PreW (NoSetFsW W K) K exe endPc R F c0 t cA m fr := by
  have hin := WakePh.WcSp4.wake_wcSp4In
  simp only [WakePh.WcSp4.wcSp4In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨b0, bs⟩, bp⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n20 b0 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.n20s bs rfl (by decide),
    blkI_ns hp hend h.n20p bp rfl (by decide),
    NodeW.noSetFs h.nI (code_field hp hend wake_tiPro (ofNat_zero' _)) (by decide) (by decide)⟩

/-- **`.x21`'s states to the `syscall` are inside `NoSetFsW W K`** (the
`syscall` itself is past `nrB`). -/
theorem WcCloneW.noSetFs {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcCloneW W K exe endPc R F c0 t k cA m fr) : WcCloneW (NoSetFsW W K) K exe endPc R F c0 t k cA m fr := by
  have hin := WakePh.wake_wcCloneIn
  simp only [WakePh.WcClone.wcCloneIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, ba⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n21 b0 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.nf bf rfl (by decide),
    blkI_ns hp hend h.na ba rfl (by decide), nodeI_ns hp hend h.nd bd rfl (by decide),
    nodeI_ns hp hend h.n10 b10 rfl (by decide), blkI_ns hp hend h.nr br rfl (by decide)⟩

/-- **`.x21`'s states to the `syscall`, past the publication, are inside
`NoSetFsW W K`**. -/
theorem WcClonePW.noSetFs {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t k cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcClonePW W K exe endPc R F c0 ty l t k cA m fr) :
    WcClonePW (NoSetFsW W K) K exe endPc R F c0 ty l t k cA m fr := by
  have hin := WakePh.wake_wcCloneIn
  simp only [WakePh.WcClone.wcCloneIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, ba⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n21 b0 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.nf bf rfl (by decide),
    blkI_ns hp hend h.na ba rfl (by decide), nodeI_ns hp hend h.nd bd rfl (by decide),
    nodeI_ns hp hend h.n10 b10 rfl (by decide), blkI_ns hp hend h.nr br rfl (by decide)⟩

/-- **From `.x20` to the `syscall` is inside `NoSetFsW W K`**. -/
theorem WcSp4W.noSetFs {F₂ : MachineData → Prop} {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp4W W K exe endPc R F F₂ c0 t cA m fr) : WcSp4W (NoSetFsW W K) K exe endPc R F F₂ c0 t cA m fr :=
  ⟨WcSp4PreW.noSetFs hp hend h.toWcSp4PreW, WcCloneW.noSetFs hp hend h.clone⟩

/-- **From `.x20` to the `syscall`, past the publication, is inside
`NoSetFsW W K`**. -/
theorem WcSp4PW.noSetFs {F₂ : MachineData → Prop} {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel}
    {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4PW W K exe endPc R F F₂ c0 ty l t cA m fr) :
    WcSp4PW (NoSetFsW W K) K exe endPc R F F₂ c0 ty l t cA m fr :=
  ⟨WcSp4PreW.noSetFs hp hend h.toWcSp4PreW, WcClonePW.noSetFs hp hend h.clone⟩

/-- **From the box's store to the `syscall` is inside `NoSetFsW W K`**. -/
theorem WcMidW.noSetFs {F₂ : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidW W K exe endPc R F F₂ ms J0 Q) :
    WcMidW (NoSetFsW W K) K exe endPc R F F₂ ms J0 Q :=
  ⟨WcResW.noSetFs hp hend h.res, fun c0 cA m fr hM => WcSp3W.noSetFs hp hend (h.sp3 c0 cA m fr hM),
    fun c0 ty l cA m fr hM => WcSp4PW.noSetFs hp hend (h.sp4 c0 ty l cA m fr hM)⟩

end NoSetFs

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcPreW.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcPreW.noSetFs

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcSp0W.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcSp0W.noSetFs

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcResW.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcResW.noSetFs

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcSp4W.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcSp4W.noSetFs

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcMidW.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcMidW.noSetFs
