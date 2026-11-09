/-
**hello.w's `wc_main` obligations at cells other than an `MSR`** (AArch64,
hTop; the twin of `Spike/Lib/A64WakeWcNoMsr.lean` at
helloProg): every node obligation of `wc_main`'s chain up to its `clone`'s
`svc` (`WcPreWH`, `WcSp0WH`, `WcMidWH`) inside `W` is one inside `NoMsrW W K`
in any valid layout of `helloProg`, the form `A64HelloWcHat.hello_wc_mid_hatW`
and the start's chain ask. None of these blocks is an `MSR` (helloProg's only
`MSR` is in the start code); a node obligation already has `K` not moving its
states, so no premise on `K` is needed. Wake's `blk_nm`, `node_nm` are program
independent and reused as is.

- `WcPreWH.noMsr`, `WcSp0WH.noMsr`: up to the box's store;
- `reserveW_noMsrH`, `WcResWH.noMsr`: the reserve and its caller's blocks;
- `tcbWG_noMsrH`, `WcSp3WH.noMsr`: the second TCB's call;
- `WcSp4WH.noMsr`, `wcSp6W_noMsr`, `WcMidWH.noMsr`: to the `svc`.
-/
import Spike.Lib.A64HelloWcMid
import Spike.Lib.A64WakeWcNoMsr

namespace Spike.Lib.A64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.KeepTP (NoMsrAt dNoMsr)
open Spike.Lib.A64.Flow.WakeWc (blk_nm node_nm boxSt_eq pubF_eq tidSt_eq fenceB_eq)
open Spike.Lib.A64.Flow.HelloRd (hello_alloc)
open Spike.Lib.A64.HelloPh.WcSp6 (WcSp6W wcSp6In hello_wcSp6In)
open Spike.Lib.A64.Rt (TcbGG TcbWG)
open Spike.Lib.A64.Rt.Reserve (ResG ReserveW)
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)

section NoMsr

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
  {kp : Nat}

variable (hp : Lays exe SccCode.helloProg kp) (hend : endPc = endOf exe SccCode.helloProg kp)
include hp hend

/-- **`wc_main` up to the allocator's return is inside `NoMsrW W K`**. -/
theorem WcPreWH.noMsr {ms : MemSide isaLSE2} {J0 J1 : AS → Ctl → Prop}
    (h : WcPreWH W K exe endPc R F ms J0 J1) : WcPreWH (NoMsrW W K) K exe endPc R F ms J0 J1 := by
  have hin := hello_wcPro
  simp only [hWcPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have he := hello_wcEInH
  simp only [wcEInH, Bool.and_eq_true] at he
  refine ⟨ProW.noMsr h.pro (code_of hp hend b0 ?_) (code_of hp hend b1 ?_) (code_of hp hend b2 ?_)
    (code_of hp hend b3 ?_) (by decide) (by decide) (by decide) (by decide),
    BlkW.noMsr h.e (code_of hp hend he.1 (ofNat4_zero _)) (by decide),
    fun q hok hq => AllocW.noMsr (h.alloc q hok hq) (alloc_code_of hp hend hello_alloc)⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]

/-- **`.sp0` is inside `NoMsrW W K`**. -/
theorem WcSp0WH.noMsr {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    (h : WcSp0WH W K exe endPc R F ms J1) : WcSp0WH (NoMsrW W K) K exe endPc R F ms J1 := by
  have hin := hello_wcS0InH
  simp only [wcS0InH, Bool.and_eq_true] at hin
  exact ⟨blk_nm hp hend h.b hin.1 (ofNat4_zero _) (by decide),
    node_nm hp hend h.st (boxSt_eq ▸ hin.2) rfl (by decide)⟩

/-- **`scc_rt_thread_reserve` is inside `NoMsrW W K`**. -/
theorem reserveW_noMsrH {q : ResG} (h : ∀ i, ReserveW W K exe endPc R F q i) :
    ∀ i, ReserveW (NoMsrW W K) K exe endPc R F q i := by
  have hin := hello_reserveIn
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
  · exact BlkW.noMsr (h .ok)
      (Spike.Lib.A64.code_field_blockAcross hp hend r7 (List.take_append_drop 4 _) (ofNat4_zero _)) (by decide)

/-- **From the fence to `.sp3` is inside `NoMsrW W K`**. -/
theorem WcResWH.noMsr {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop} {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResWH W K exe endPc R F ms J1 S Q) : WcResWH (NoMsrW W K) K exe endPc R F ms J1 S Q := by
  have hin := hello_wcResInH
  simp only [wcResInH, Bool.and_eq_true] at hin
  obtain ⟨⟨h4, h5⟩, -⟩ := hin
  exact ⟨node_nm hp hend h.f (pubF_eq ▸ h4) rfl (by decide), blk_nm hp hend h.bl h5 rfl (by decide),
    fun g hg => reserveW_noMsrH hp hend (h.res g hg)⟩

/-- **`scc_rt_alloc_tcb` is inside `NoMsrW W K`**. -/
theorem tcbWG_noMsrH {q : TcbGG} (h : ∀ i, TcbWG W K exe endPc R F q i) :
    ∀ i, TcbWG (NoMsrW W K) K exe endPc R F q i := by
  have hin := hello_allocTcbIn
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
  · exact BlkW.noMsr (h .ret)
      (Spike.Lib.A64.code_field_blockAcross hp hend t14 (List.take_append_drop 12 _) rfl) (by decide)

/-- **From `.sp3` to `.sp4` is inside `NoMsrW W K`**. -/
theorem WcSp3WH.noMsr {c0 : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcSp3WH W K exe endPc R F c0 sl me cA fr) :
    WcSp3WH (NoMsrW W K) K exe endPc R F c0 sl me cA fr := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  exact ⟨blk_nm hp hend h.blk hin.1.1.1.1.1 (ofNat4_zero _) (by decide),
    fun g hg => tcbWG_noMsrH hp hend (h.tcb g hg)⟩

/-- **From `.sp4` to the call of `scc_rt_thread_init` is inside `NoMsrW W K`**. -/
theorem WcSp4WH.noMsr {c0 : Ctl} {t : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4WH W K exe endPc R F c0 t sl me cA fr) :
    WcSp4WH (NoMsrW W K) K exe endPc R F c0 t sl me cA fr := by
  have hin := hello_wcSp3InH
  simp only [wcSp3InH, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, b4⟩, b4s⟩, b5⟩, -⟩ := hin
  exact ⟨blk_nm hp hend h.n4 b4 (ofNat4_zero _) (by decide),
    node_nm hp hend h.n4s (tidSt_eq ▸ b4s) rfl (by decide),
    blk_nm hp hend h.n5 b5 rfl (by decide)⟩

/-- **From `.sp6` to the `svc` is inside `NoMsrW W K`**. -/
theorem wcSp6W_noMsr {c0 : Ctl} {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
    {me cA : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp6W W K exe endPc R F c0 t k sl me cA fr) :
    WcSp6W (NoMsrW W K) K exe endPc R F c0 t k sl me cA fr := by
  have hin := hello_wcSp6In
  simp only [wcSp6In, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨b6, b6f⟩, b6a⟩, -⟩ := hin
  exact ⟨blk_nm hp hend h.n6 b6 (ofNat4_zero _) (by decide),
    node_nm hp hend h.n6f (fenceB_eq ▸ b6f) rfl (by decide),
    blk_nm hp hend h.n6a b6a rfl (by decide)⟩

/-- **From the box's store to the `svc` is inside `NoMsrW W K`**. -/
theorem WcMidWH.noMsr {F₂ : MachineData → Prop} {ms : MemSide isaLSE2} {J1 : AS → Ctl → Prop}
    {S Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidWH W K exe endPc R F F₂ ms J1 S Q) :
    WcMidWH (NoMsrW W K) K exe endPc R F F₂ ms J1 S Q :=
  ⟨WcResWH.noMsr hp hend h.res, fun c0 sl me cA fr hM => WcSp3WH.noMsr hp hend (h.sp3 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => WcSp4WH.noMsr hp hend (h.sp4 c0 sl me cA fr hM),
    fun c0 sl me cA fr hM => wcSp6W_noMsr hp hend (h.sp6 c0 sl me cA fr hM)⟩

end NoMsr

end Spike.Lib.A64.Flow.HelloWc

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcPreWH.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcPreWH.noMsr

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcSp0WH.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcSp0WH.noMsr

/-- info: 'Spike.Lib.A64.Flow.HelloWc.WcMidWH.noMsr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.HelloWc.WcMidWH.noMsr
