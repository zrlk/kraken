/-
**The generic runtime block and node lemmas at `ret0.w`'s instance**
(`Spike/Lib/Rt/A64RtW.lean`): `ret0.w`'s facts are an `InstOk`, the hand
block and node lemmas of `Spike/Lib/A64Ret0I.lean` follow from the generic
ones with the hand premises, and a row of `ret0.w`'s runtime table is inside `Wr`
with its phase check from `ret0_rtNodesOk` (`Spike/Test/A64RtNodes.lean`).
-/
import Spike.Lib.Rt.A64RtW
import Spike.Test.A64RtNodes

namespace Spike.Lib.A64.Rt.Test

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (ND BlkW)
open Spike.Lib.A64.Rt Spike.Lib.A64.Flow.Ret0.Inst
open Spike.Lib.A64.Flow.Ret0 (StackM StackOff)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0_lays)
open Scc.Cert.Rt.A64 (blockAt)
open SccCode (ret0Λ ret0Prog)

variable {rS : Range}

/-- **`ret0.w`'s instance facts.** -/
theorem ret0_instOk : InstOk ret0Exe ret0End ret0Prog labT μ0 own Tk (Kr rS) okPc ph :=
  ⟨ret0_lays, rfl, ret0_labT, ph_same, pcOff_of_okPc⟩

section Hand

open Spike.Lib.A64.Flow

variable {R : Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool}
  {ra : Int64} {l : Label} {k : Nat}

/-- The hand `blkW_pre` from the generic one. -/
example (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hT : bT (labT l + Int64.ofNat (4 * k)).toBitVec.toNat = true) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk :=
  Rt.blkW_pre ret0_instOk hb he hok hR hal hlo hhi hC hph hret hdead fun _ hs => not_tk (by rw [hs]; exact hT)

/-- The hand `blkW_post` from the generic one. -/
example (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hSM : FStable R (StackM rS)) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n blk :=
  Rt.blkW_post ret0_instOk hb he hok hR hal hlo hhi hC hph hret hdead hsub hSM

/-- The hand `blkW_postO` from the generic one. -/
example (hb : blockAt ret0Prog l k blk = true) (he : labT l + Int64.ofNat (4 * k) = n.pc)
    (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hph : blkPh okPc ph dead labT (labT l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun labT (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Flow.arun labT blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n blk :=
  Rt.blkW_postO ret0_instOk hb he hok hR hal hlo hhi hC hph hret hdead hl hh hsub hfit hFO

end Hand

/-! ## A row of the table -/

/-- `scc_rt_alloc_tcb`'s first row, its prologue. -/
def tcbG : Scc.Cert.Rt.A64.OGrp := ret0RtRows[8]'(by decide +kernel)
def tcbB : Scc.Cert.Rt.A64.OBlk := tcbG.bs[0]'(by decide +kernel)

example : tcbG.l = "scc_rt_alloc_tcb" := by decide +kernel
theorem tcbG_mem : tcbG ∈ ret0RtRows := List.getElem_mem _
theorem tcbB_mem : tcbB ∈ tcbG.bs := List.getElem_mem _

/-- **The prologue row is inside `Wr`** for every node at it, its code from
`allocTcbIn`, its phase check from `ret0_rtNodesOk`; the node's facts left
as premises. -/
example {R : Region} {F : MachineData → Prop} {n : ND} (he : labT tcbG.l + Int64.ofNat (4 * tcbB.k) = n.pc)
    (ho : n.o = tcbB.o) (hok : Spike.Lib.A64.Flow.okBlk tcbB.lo tcbB.hi tcbB.o tcbB.blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ tcbB.lo) (hhi : tcbB.hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c)
    (hdead : ∀ σ c, n.J σ c →
      ret0Dead tcbG.l tcbB.k (Spike.Lib.A64.Flow.arun labT tcbB.blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false) :
    BlkW (Wr rS) (Kr rS) ret0Exe ret0End R F n tcbB.blk :=
  blkW_pre_row ret0_instOk ret0_rtNodesOk tcbG_mem tcbB_mem (by decide +kernel) he ho hok hR hal hlo hhi hC
    (fun _ _ _ k hk r hr => (noRet_false (by decide +kernel) k hk r hr).elim) hdead
    (fun _ hs => not_tk (by rw [hs]; decide +kernel))

/-! ## The node lemmas -/

section Node

open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Words ret0F ret0Words_mapped)

variable {R : Region} {F : MachineData → Prop}

/-- `ret0.w`'s owned words factor through its phase. -/
theorem ret0_own : ∀ s, own s = ownOf (ph (Scc.Sem.A64.pcOf s)) := fun _ => rfl

/-- The hand `nodeW_si_pre` from the generic one. -/
example {n : ND} {si : SI} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [si.toDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_si_pre ret0_instOk hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT)) hph

/-- The hand `nodeW_ldop_pre` from the generic one. -/
example {n : ND} {op : AtomicOp} {kk : RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    {a : BitVec 64} (hb : blockAt ret0Prog l k [ldopDir op kk rs rt b] = true)
    (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hT : bT p.toBitVec.toNat = true) (hT4 : bT (p + Int64.ofNat 4).toBitVec.toNat = true)
    (ha : ∀ σ c, n.J σ c → (σ.regs.getXReg b).toBitVec = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hin : ∃ v, (⟨a, 8⟩, v) ∈ ownOf (ph p.toBitVec.toNat))
    (hupd : ∀ σ c, n.J σ c → Rt.ownUpdB (ownOf (ph p.toBitVec.toNat))
      (ownOf (ph (p + Int64.ofNat 4).toBitVec.toNat))
      ⟨a, 8⟩ (fun old => (op.apply (old.setWidth 64) (σ.regs.getRegOrZr (.low (.reg rs) .W64))).setWidth 128)
      = true) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_ldop_pre ret0_instOk ret0_own hb he hp hC hok (fun _ hs => not_tk (by rw [hs]; exact hT))
    (fun _ hs => not_tk (by rw [hs]; exact hT4)) ha (ret0Words_mapped hw).1 (fun m hm => hFr m hm a hw) hin hupd

/-- The hand `nodeW_st_post` from the generic one. -/
example {n : ND} {t b : XReg} {i : Int64} {l : Label} {k : Nat} {p : Int64} {a : BitVec 64}
    (hb : blockAt ret0Prog l k [strDir t b i] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (ha : ∀ σ c, n.J σ c → rAddr σ.regs b i = a) (hw : a ∈ ret0Words) (hFr : ∀ m, F m → ret0F m)
    (hno : ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) (hsub : rS.Sub ret0Λ.stackPool) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R (fun m => F m ∧ StackM rS m) n :=
  Rt.nodeW_st_post ret0_instOk ret0_own hb he hp hC hok hph ha (ret0Words_mapped hw).1 (fun m hm => hFr m hm a hw)
    hno hsub

/-- The hand `nodeW_svc_postO` from the generic one. -/
example {n : ND} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt ret0Prog l k [svcDir] = true) (he : labT l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hC : ∀ σ c, n.J σ c → CFacts ret0Λ ret0Λ.static c) (hok : okPc p.toBitVec.toNat = true)
    (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub ret0Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hnr : ∀ σ c, n.J σ c → σ.regs.X8.toNat ≠ 64) :
    NodeW (Wr rS) (Kr rS) ret0Exe ret0End R F n :=
  Rt.nodeW_svc_postO ret0_instOk hb he hp hC hok hph hR hR8 hl hh hsub hFO hnr

end Node

end Spike.Lib.A64.Rt.Test
