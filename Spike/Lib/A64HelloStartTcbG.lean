/-
**hello.w's first `scc_rt_alloc_tcb` call at `ownGH`** (AArch64;
twin of `Spike/Lib/A64WakeStartTcbG.lean` at helloProg):
the call from `scc_rt_start` (on the start's stack, off the pool) where
`ownGH` picks `ownH` (`GoodWH`'s first case: the callee's pcs off a pool
stack), so a node's `SFacts` at the first instance (`ownH` at `phH`) move to
`SFactsSt2` at `ownGH`. The frame band `StartTcb.BandT` and `sp_of_abs` are
wake's, program independent.

- `PcTH`: the callee's pcs at hello's canonical base.
- `inTH_of`, `goodWTH_of`: `inPc` and `GoodWH` by the pc and `sp`.
- `finTH`: `GoodWH` where a block's run ends inside the callee.
- `blkT_ownH`, `nodeT_ownH`: a block's (a node's) `SFacts` at `ownH` as
  `SFactsSt2` at `ownGH`.
-/
import Spike.Lib.A64HelloStartTiG
import Spike.Lib.A64WakeStartTcbG

namespace Spike.Lib.A64.HelloPh.StartTcb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl SFacts)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakePh (inPc spPool Keep)
open Spike.Lib.A64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.A64.WakePh.StartTcb (BandT sp_of_abs)

/-- **`scc_rt_alloc_tcb`'s pcs** at hello's canonical base (`labs_eqH`'s
`scc_rt_alloc_tcb` up to `scc_rt_thread_reserve`). -/
def PcTH (p : Int64) : Prop := 2164748 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2165172

instance (p : Int64) : Decidable (PcTH p) := by unfold PcTH; infer_instance

variable {L : RuntimeLayout}

/-- **`inPc` of `scc_rt_alloc_tcb`** by the pc. -/
theorem inTH_of (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcTH s.st.2) : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s := by
  obtain ⟨e1, e2, -⟩ := labs_eqH hlab (L := L)
  unfold inPc pcOf; rw [e1, e2]; exact hp

/-- **`GoodWH` by the pc and `sp`**: inside the callee, off the pool. -/
theorem goodWTH_of (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {R : Spike.Lib.Region} (hb : BandT L R) {s : State} (hp : PcTH s.st.2) (hsp : SpAt R (-192) 0 s) :
    GoodWH L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨.inl (inTH_of hlab hp), ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi : Int}
  {Dt : State → Prop}

/-- **`GoodWH` where a block's run ends inside the callee**: there its pc
(`h2`) and its static `sp` offsets in `[-192, 0]` (`hso`). -/
theorem finTH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (h2 : ∀ σ c, n.J σ c →
      PcTH (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine goodWTH_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the call at `ownGH`** from its `SFacts` at the first
instance: its pcs in `PcTH` (`h1`), its static `sp` offsets in `[-192, 0]`
(`hso`), `GoodWH` where its run ends (`hfin`). -/
theorem blkT_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandT L R)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165980)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcTH (n.pc + Int64.ofNat (4 * k)))
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → GoodWH L s := by
    intro σ c _ k hk s m hA _ _ hs
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine goodWTH_of hlab hb (by rw [hs]; exact h1 k hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hagWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by have := h1 k hk; unfold PcTH at this; rw [hsite x hx]; omega) hQ
    (fun σ c hJ k hk s m hA he hn hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ s m hA he hn hs)
  have hst := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.blkW_toSt2 hS) hag
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
    let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

/-- **A node of the call at `ownGH`** from its `SFacts` at the first
instance: its successors keeping `sp` and `x30` 4 bytes on (`hk`), its pc
and the next in `PcTH` (`hpc`), its static `sp` offset in `[-192, 0]`
(`hso`). -/
theorem nodeT_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandT L R)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => GoodWH L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodWH L s')
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hAt
    obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
    have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
    refine ⟨⟨goodWTH_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
    obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
    exact goodWTH_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS)
    (Spike.Lib.A64.WakePh.NodeW.agree_of hag fun _ hs => ownGH_W hlab hs)
  exact fun s c hA =>
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

end Own

end Spike.Lib.A64.HelloPh.StartTcb

/-- info: 'Spike.Lib.A64.HelloPh.StartTcb.inTH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTcb.inTH_of

/-- info: 'Spike.Lib.A64.HelloPh.StartTcb.goodWTH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTcb.goodWTH_of

/-- info: 'Spike.Lib.A64.HelloPh.StartTcb.finTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTcb.finTH

/-- info: 'Spike.Lib.A64.HelloPh.StartTcb.blkT_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTcb.blkT_ownH

/-- info: 'Spike.Lib.A64.HelloPh.StartTcb.nodeT_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTcb.nodeT_ownH
