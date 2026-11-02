/-
**hello.w's `wc_main` obligations at cells other than a `syscall`** (x86-64; the twin of
`Spike/Lib/A64HelloWcNoMsr.lean`): every node obligation of hello's `wc_main` chain up to its `clone`'s `syscall`
(`WcPreWH`, `WcSp0WH`, `WcMidWH`) inside `W` is one inside `NoSetFsW W K` in any valid layout of `helloCells`.
None of these blocks is a `syscall` (the `clone`'s `syscall` is past the last node); a node obligation already has
`K` not moving its states, so no premise on `K` is needed. Wake's x86-64 `X64WakeWcNoMsr` at hello's blocks
(`blk_ns`, `node_ns`, `blkI_ns`, `nodeI_ns` reused).

- `WcPreWH.noSetFs`, `WcSp0WH.noSetFs`: up to the box's store;
- `reserveW_noSetFsH`, `WcResWH.noSetFs`: the reserve and its caller's call;
- `tcbWG_noSetFsH`, `WcSp3WH.noSetFs`: the second TCB's call;
- `WcSp4WH.noSetFs`, `wcSp6W_noSetFs`, `wcSp6PW_noSetFs`, `WcMidWH.noSetFs`: to the `syscall`.

## Differences from the AArch64 version

- The thread pointer is `fsBase`, set only by `arch_prctl`, so `NoMsrW` is `NoSetFsW` (`X64KeepTPW`) and the
  per-block check is `cNoSys` (no `syscall`; AArch64 `dNoMsr`). The names follow wake's x86-64 twin: `*.noSetFs`,
  `reserveW_noSetFsH`, `tcbWG_noSetFsH`, `wcSp6W_noSetFs` (AArch64 `*.noMsr`, `reserveW_noMsrH`, `tcbWG_noMsrH`,
  `wcSp6W_noMsr`).
- The cells are `helloCells` with byte offsets (AArch64 `helloProg`, `4 * k`); `.x23`'s to `.x25`'s blocks are
  checked by the indexed `blockAt` (`wcSp3InH`, `wcSp6InH`).
- x86-64's `WcResWH` has no fence node (AArch64 `f`) and the reserve no `add` node; `scc_rt_alloc_tcb` has
  x86-64's 33 nodes; `WcSp6W` has six nodes (AArch64 three).
-/
import Spike.Lib.X64HelloWcMid
import Spike.Lib.X64WakeWcNoMsr

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (blk_ns node_ns blkI_ns nodeI_ns)
open Spike.Lib.X64.Flow.HelloRd (hello_alloc)
open Spike.Lib.X64.HelloPh.WcSp6 (WcSp6W WcSp6PW wcSp6InH hello_wcSp6InH)
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResG ReserveW)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

section NoSetFs

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
  {kp : Nat}

variable (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
include hp hend

/-- **`wc_main` up to the allocator's return is inside `NoSetFsW W K`**. -/
theorem WcPreWH.noSetFs {ms : MemSide isa} {J0 J1 : AS → Ctl → Prop}
    (h : WcPreWH W K exe endPc R F ms J0 J1) : WcPreWH (NoSetFsW W K) K exe endPc R F ms J0 J1 := by
  have hin := hello_wcPro
  simp only [hWcPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label "wc_main" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_main.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have he := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at he
  refine ⟨XProW.noSetFs h.pro (code_field hp hend b0 (ofNat_zero' _)) (code_field hp hend b1 ?_)
    (code_field hp hend b2 ?_) (code_field hp hend b3 ?_) (code_field hp hend b4 ?_),
    BlkW.noSetFs h.e (code_field hp hend he.1 (ofNat_zero' _)) (by decide),
    fun q hok hq => Alloc.AllocW.noSetFs hp hend hello_alloc (h.alloc q hok hq)⟩
  · rw [h4, ofNat_zero']
  · rw [h4]
  · rw [h4, ofNat_add']
  · rw [h4, ofNat_add', ofNat_add', ofNat_add']

/-- **`.x22`'s block and the box's store are inside `NoSetFsW W K`**. -/
theorem WcSp0WH.noSetFs {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    (h : WcSp0WH W K exe endPc R F ms J1) : WcSp0WH (NoSetFsW W K) K exe endPc R F ms J1 := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  exact ⟨blk_ns hp hend h.b hin.1 (ofNat_zero' _) (by decide),
    node_ns hp hend h.st hin.2 rfl (by decide)⟩

/-- **`scc_rt_thread_reserve` is inside `NoSetFsW W K`**. -/
theorem reserveW_noSetFsH {q : ResG} (h : ∀ i, ReserveW W K exe endPc R F q i) :
    ∀ i, ReserveW (NoSetFsW W K) K exe endPc R F q i := by
  have hin := hello_reserveIn
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
  · exact blk_ns hp hend (h .ok) r6 (ofNat_zero' _) (by decide)

/-- **The reserve's call and the reserve are inside `NoSetFsW W K`**. -/
theorem WcResWH.noSetFs {ms : MemSide isa} {J1 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResWH W K exe endPc R F ms J1 Q) : WcResWH (NoSetFsW W K) K exe endPc R F ms J1 Q := by
  have hin := hello_wcResInH
  simp only [wcResInH, Bool.and_eq_true] at hin
  exact ⟨blk_ns hp hend h.bl hin.1 rfl (by decide), fun g hg => reserveW_noSetFsH hp hend (h.res g hg)⟩

/-- **`scc_rt_alloc_tcb` is inside `NoSetFsW W K`**. -/
theorem tcbWG_noSetFsH {q : TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i) :
    ∀ i, TcbWG (NoSetFsW W K) K exe endPc R F q i := by
  have hin := hello_allocTcbIn
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
  · exact blk_ns hp hend (h .ret) t32 rfl (by decide)

/-- **From `.x23` to `.x24` is inside `NoSetFsW W K`**: the call block and `scc_rt_alloc_tcb`. -/
theorem WcSp3WH.noSetFs {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcSp3WH W K exe endPc R F c0 sl me cA fr) :
    WcSp3WH (NoSetFsW W K) K exe endPc R F c0 sl me cA fr := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  exact ⟨blkI_ns hp hend h.blk hin.1.1.1.1.1 (ofNat_zero' _) (by decide),
    fun g hg => tcbWG_noSetFsH hp hend (h.tcb g hg)⟩

/-- **From `.x24` to the call of `scc_rt_thread_init` is inside `NoSetFsW W K`**. -/
theorem WcSp4WH.noSetFs {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4WH W K exe endPc R F c0 t sl me cA fr) :
    WcSp4WH (NoSetFsW W K) K exe endPc R F c0 t sl me cA fr := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, b4⟩, b4s⟩, b5⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n4 b4 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.n4s b4s rfl (by decide),
    blkI_ns hp hend h.n5 b5 rfl (by decide)⟩

/-- **From `.x25` to the `syscall` is inside `NoSetFsW W K`** (the `syscall` itself is past `nrB`). -/
theorem wcSp6W_noSetFs {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    WcSp6W (NoSetFsW W K) K exe endPc R F c0 t k sl me cA fr := by
  have hin := hello_wcSp6InH
  simp only [wcSp6InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, ba⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n6 b0 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.n6f bf rfl (by decide),
    blkI_ns hp hend h.n6a ba rfl (by decide), nodeI_ns hp hend h.nd bd rfl (by decide),
    nodeI_ns hp hend h.n10 b10 rfl (by decide), blkI_ns hp hend h.nr br rfl (by decide)⟩

/-- **From `.x25` to the `syscall`, publishing at the `mfence`, is inside `NoSetFsW W K`** (`wcSp6W_noSetFs` at
`X64HelloWcPub`'s nodes). -/
theorem wcSp6PW_noSetFs {c0 c1 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6PW W K exe endPc R F c0 c1 t k sl me cA fr) :
    WcSp6PW (NoSetFsW W K) K exe endPc R F c0 c1 t k sl me cA fr := by
  have hin := hello_wcSp6InH
  simp only [wcSp6InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨b0, bf⟩, ba⟩, bd⟩, b10⟩, br⟩, -⟩ := hin
  exact ⟨blkI_ns hp hend h.n6 b0 (ofNat_zero' _) (by decide), nodeI_ns hp hend h.n6f bf rfl (by decide),
    blkI_ns hp hend h.n6a ba rfl (by decide), nodeI_ns hp hend h.nd bd rfl (by decide),
    nodeI_ns hp hend h.n10 b10 rfl (by decide), blkI_ns hp hend h.nr br rfl (by decide)⟩

/-- **From the box's store to the `syscall` is inside `NoSetFsW W K`**. -/
theorem WcMidWH.noSetFs {F₂ : MachineData → Prop} {ms : MemSide isa} {J1 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidWH W K exe endPc R F F₂ ms J1 Q) :
    WcMidWH (NoSetFsW W K) K exe endPc R F F₂ ms J1 Q :=
  ⟨WcResWH.noSetFs hp hend h.res, fun c0 sl me cA fr hM => WcSp3WH.noSetFs hp hend (h.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.noSetFs hp hend (h.sp4 c0 sl me cA fr hM),
    fun c0 ty l sl me cA fr hM => wcSp6PW_noSetFs hp hend (h.sp6 c0 ty l sl me cA fr hM)⟩

end NoSetFs

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcPreWH.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcPreWH.noSetFs

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcSp0WH.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcSp0WH.noSetFs

/-- info: 'Spike.Lib.X64.Flow.HelloWc.WcMidWH.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.WcMidWH.noSetFs

/-- info: 'Spike.Lib.X64.Flow.HelloWc.wcSp6PW_noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.wcSp6PW_noSetFs
