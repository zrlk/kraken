/-
**The generic runtime block and node lemmas at `ret0.x`'s instance**
(`Spike/Lib/Rt/X64RtW.lean`): `ret0.x`'s facts are an `InstOk`, the hand
block and node lemmas of `Spike/Lib/X64Ret0I.lean` follow from the generic
ones with the hand premises, and a row of `ret0.x`'s runtime table is inside
`Wr` with its phase check from `ret0_rtNodesOk` (`Spike/Test/X64RtNodes.lean`).
The twin of `Spike/Test/A64RtW.lean`.
-/
import Spike.Lib.Rt.X64RtW
import Spike.Test.X64RtNodes

namespace Spike.Lib.X64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Rt Spike.Lib.X64.Flow.Ret0.Inst
open Spike.Lib.X64.Flow.Ret0 (StackM StackOff)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0_lays)
open Scc.Cert.Rt.X64 (blockAtB)
open SccCode (ret0Λ ret0Cells)

variable {rS : Range}

/-- **`ret0.x`'s instance facts.** -/
theorem ret0_instOk : InstOk ret0Exe ret0End ret0Cells labT μ0 own Tk (Kr rS) okPc ph :=
  ⟨ret0_lays, rfl, ret0_labT, ph_same, pcOff_of_okPc⟩

section Hand

variable {R : Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
  {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}

/-- The hand `blkW_pre` from the generic one. -/
example (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat off).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk :=
  Rt.blkW_pre ret0_instOk hb he hok hR hlo hhi hC hph hret hdead fun _ hs => not_tk (by rw [hs]; exact hT)

/-- The hand `blkW_post` from the generic one. -/
example (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n blk :=
  Rt.blkW_post ret0_instOk hb he hok hR hlo hhi hC hph hret hdead hsub hSM

/-- The hand `blkW_postO` from the generic one. -/
example (hb : blockAtB ret0Cells l off blk = true) (he : labT l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk :=
  Rt.blkW_postO ret0_instOk hb he hok hR hlo hhi hR8 hl hh hC hph hret hdead hsub hfit hFO

end Hand

/-! ## A row of the table -/

/-- `scc_rt_alloc_tcb`'s first row, its prologue. -/
def tcbG : Scc.Cert.Rt.X64.OGrp := ret0RtRows[9]'(by decide +kernel)
def tcbB : Scc.Cert.Rt.X64.OBlk := tcbG.bs[0]'(by decide +kernel)

example : tcbG.l = "scc_rt_alloc_tcb" := by decide +kernel
theorem tcbG_mem : tcbG ∈ ret0RtRows := List.getElem_mem _
theorem tcbB_mem : tcbB ∈ tcbG.bs := List.getElem_mem _

/-- **The prologue row is inside `Wr`** for every node at it, its code from
the cells, its phase check from `ret0_rtNodesOk`; the node's facts left as
premises. -/
example {R : Region} {F : MachineData → Prop} {n : ND} (he : labT tcbG.l + Int64.ofNat tcbB.off = n.pc)
    (ho : n.o = tcbB.o) (hok : okBlk tcbB.lo tcbB.hi tcbB.o tcbB.blk = true)
    (hR : R.OK) (hlo : R.lo ≤ tcbB.lo) (hhi : tcbB.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hdead : ∀ σ c, n.J σ c →
      ret0Dead tcbG.l tcbB.k (arun labT tcbB.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n tcbB.blk :=
  blkW_pre_row ret0_instOk ret0_rtNodesOk tcbG_mem tcbB_mem (by decide +kernel) (by decide +kernel) he ho hok hR hlo hhi hC
    (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim) hdead
    (fun _ hs => not_tk (by rw [hs]; decide +kernel))

/-! ## The node lemmas -/

section Node

open Spike.Lib.X64.Flow.Ret0.Mem (ret0Words ret0F ret0Words_mapped)

variable {R : Region} {F : MachineData → Prop}

/-- `ret0.x`'s owned words factor through its phase. -/
theorem ret0_own : ∀ s, own s = ownOf (ph (Scc.Sem.X64.pcOf s)) := fun _ => rfl

/-- The hand `nodeW_si_pre` from the generic one. -/
example {n : ND} {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(si.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_si_pre ret0_instOk hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT)) hph

/-- The hand `nodeW_fi_pre` from the generic one. -/
example {n : ND} {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(fi.toDir, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_fi_pre ret0_instOk hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT)) hph

/-- The hand `nodeW_and_pre` from the generic one. -/
example {n : ND} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(andRsp k, z)] = true) (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_and_pre ret0_instOk hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT)) hph

/-- The hand `nodeW_st_pre` from the generic one. -/
example {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_st_pre ret0_instOk ret0_own hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT)) hph ha
    (ret0Words_mapped hw).1 (fun m hm => hFr m hm a hw) hno

/-- The hand `nodeW_xadd_pre` from the generic one. -/
example {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(xaddDir b k r, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → Rt.ownUpdB (ownOf (ph p.toBitVec.toNat))
      (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (old.setWidth 64 + σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_xadd_pre ret0_instOk ret0_own hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT))
    (fun _ hs => not_tk (by rw [hs]; exact hT')) ha (ret0Words_mapped hw).1 (fun m hm => hFr m hm a hw) hin hupd

/-- The hand `nodeW_xchg_pre` from the generic one. -/
example {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(xchgDir b k r, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT' : bT (p + Int64.ofNat z).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → Rt.ownUpdB (ownOf (ph p.toBitVec.toNat))
      (ownOf (ph (p + Int64.ofNat z).toBitVec.toNat))
      ⟨a, 8⟩ (fun _ => (σ.regs.get64 r).setWidth 128) = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_xchg_pre ret0_instOk ret0_own hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT))
    (fun _ hs => not_tk (by rw [hs]; exact hT')) ha (ret0Words_mapped hw).1 (fun m hm => hFr m hm a hw) hin hupd

/-- The hand `nodeW_st_post` from the generic one. -/
example {n : ND} {b r : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(stDir b k r, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → bAddr σ.regs b k = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  Rt.nodeW_st_post ret0_instOk ret0_own hb he hp hC hok hph ha (ret0Words_mapped hw).1
    (fun m hm => hFr m hm a hw) hno hsub

/-- The hand `nodeW_fsld_postO` from the generic one. -/
example {n : ND} {d : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAtB ret0Cells l off [(fsDir d k, z)] = true) (he : labT l + Int64.ofNat off = p)
    (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → σ.regs.fsBase.toBitVec + k.toBitVec = a) (hw : a ∈ ret0Words)
    (hun : ∀ m, F m → Mem.loadInt m.dmem a 8 = none) (hR : R.OK) (hR8 : R.base.toNat % 8 = 0)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_fsld_postO ret0_instOk hb he hp hC hok hph ha (ret0Words_mapped hw).2.1 hun hR hR8 hl hh hsub hFO

/-- The hand `nodeW_syscall_postO` from the generic one. -/
example {n : ND} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB ret0Cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, z)] = true)
    (he : labT l + Int64.ofNat off = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.rax.toNat ≠ 1) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_syscall_postO ret0_instOk hb he hp hC hok hph hR hR8 hl hh hsub hFO hnr

end Node

/-- **Code at a loaded thread with data symbols below the code**: the
generic code lemmas take the prefix (`belowLen`) of the canonical loader's
thread, from `lays_threadAt_below` and `endPc_threadAt_below`. -/
example (E : Scc.Sem.Entry) (base : Nat) (syms : List (String × Nat))
    (hlab : ∀ p ∈ Scc.Sem.symsBelow base syms, ∀ c ∈ ret0Cells, c.1 ≠ .label p.1)
    [Kraken.Executable.ValidLayout (Scc.Sem.X64.threadAt E base ret0Cells syms).exe] {st : State}
    (he : st.exe = (Scc.Sem.X64.threadAt E base ret0Cells syms).exe)
    (hend : st.endPc = (Scc.Sem.X64.threadAt E base ret0Cells syms).endPc) {l : Label} {off : Nat}
    {b : List (Directive × Nat)} (h : blockAtB ret0Cells l off b = true) :
    CodeAt st ((_root_.Executable.labels (Scc.Sem.X64.threadAt E base ret0Cells syms).exe).label l
      + Int64.ofNat off) b :=
  Scc.Cert.Rt.X64.codeAt_blockAtB (Scc.Cert.Link.X64.lays_threadAt_below E base ret0Cells syms hlab) he
    (hend.trans (Scc.Cert.Link.X64.endPc_threadAt_below E base ret0Cells syms)) h

end Spike.Lib.X64.Rt.Test
