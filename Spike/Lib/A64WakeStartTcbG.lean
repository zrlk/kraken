/-
**wake.w's first `scc_rt_alloc_tcb` call at `ownG`** (AArch64): the call
from `scc_rt_start` (on the start's stack, off the pool) where `ownG` picks
`ownW` (`GoodW`'s first case: the callee's pcs off a pool stack), so a
node's `SFacts` at the first instance (`ownW` at `phW`) move to
`SFactsSt2` at `ownG`.

- `PcT`, `BandT`: the callee's pcs at the canonical base; its frame
  `[-192, 0]` off the pool.
- `inT_of`, `goodWT_of`, `siteT`: `inPc` and `GoodW` by the pc and `sp`; the
  take site's pc.
- `finT`: `GoodW` where a block's run ends inside the callee.
- `blkT_own`, `nodeT_own`: a block's (a node's) `SFacts` at `ownW` as
  `SFactsSt2` at `ownG`.
-/
import Spike.Lib.A64WakeStartWf
import Spike.Lib.A64WakeTcb2W
import Spike.Lib.A64WakeWfW

namespace Spike.Lib.A64.WakePh.StartTcb

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl SFacts)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakePh.Tcb2W (soRun arun_so)

/-- **`scc_rt_alloc_tcb`'s pcs** at the canonical base. The bounds are
checked against the labels only by `inT_of` (`labs_eq`, decided from `hlab`),
and every `PcT` fact is decided on pcs from `Tcb2W.tcb_labs`, so a `.text`
shift fails those decisions loudly. -/
def PcT (p : Int64) : Prop := 2164712 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2165132

instance (p : Int64) : Decidable (PcT p) := by unfold PcT; infer_instance

/-- **`scc_rt_alloc_tcb`'s frame off the pool**: no address of `[-192, 0]`
of `R` in `(pool.lo, pool.lo + pool.size]`. -/
def BandT (L : RuntimeLayout) (R : Spike.Lib.Region) : Prop :=
  ∀ k, -192 ≤ k → k ≤ 0 → ¬ (L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)

variable {L : RuntimeLayout}

/-- **`inPc` of `scc_rt_alloc_tcb`** by the pc. -/
theorem inT_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcT s.st.2) : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s := by
  obtain ⟨e1, e2, -⟩ := labs_eq hlab (L := L)
  unfold inPc pcOf; rw [e1, e2]; exact hp

/-- **`GoodW` by the pc and `sp`**: inside the callee, off the pool. -/
theorem goodWT_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {R : Spike.Lib.Region}
    (hb : BandT L R) {s : State} (hp : PcT s.st.2) (hsp : SpAt R (-192) 0 s) : GoodW L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨.inl (inT_of hlab hp), ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- The take site's pc at the canonical base. -/
theorem siteT (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165940 := by
  intro x hx
  rw [hsite, show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 from
    (Tcb2W.tcb_labs hlab).2.2.2.2.2] at hx
  cases hx; rfl

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi : Int}
  {Dt : State → Prop}

theorem sp_of_abs {o : Spike.Lib.A64.Flow.SO} {m : MachineData} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R o m σ) : m.regs.SP.toBitVec = R.addr o.sp := by
  rw [hA.regs]; exact hA.so .SP _ rfl

/-- **`GoodW` where a block's run ends inside the callee**: there its pc
(`h2`) and its static `sp` offsets in `[-192, 0]` (`hso`). -/
theorem finT (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (h2 : ∀ σ c, n.J σ c → PcT (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine goodWT_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the call at `ownG`** from its `SFacts` at the first
instance: its pcs in `PcT` (`h1`), its static `sp` offsets in `[-192, 0]`
(`hso`), `GoodW` where its run ends (`hfin`). -/
theorem blkT_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165940)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcT (n.pc + Int64.ofNat (4 * k)))
    (hso : ∀ k ≤ blk.length, -192 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → GoodW L s := by
    intro σ c _ k hk s m hA _ _ hs
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine goodWT_of hlab hb (by rw [hs]; exact h1 k hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hagW (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by have := h1 k hk; unfold PcT at this; rw [hsite x hx]; omega) hQ
    (fun σ c hJ k hk s m hA he hn hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ s m hA he hn hs)
  have hst := Spike.Lib.A64ConsumerA.BlkW.ownCongr2 (Tcb2W.blkW_toSt2 hS) hag
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
    let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

/-- **A node of the call at `ownG`** from its `SFacts` at the first
instance: its successors keeping `sp` and `x30` 4 bytes on (`hk`), its pc
and the next in `PcT` (`hpc`), its static `sp` offset in `[-192, 0]`
(`hso`). -/
theorem nodeT_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcT n.pc ∧ PcT (n.pc + 4)) (hso : -192 ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => GoodW L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodW L s')
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hAt
    obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
    have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
    refine ⟨⟨goodWT_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
    obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
    exact goodWT_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩
  have hst := Tcb2W.nodeW_ownCongr2 (Tcb2W.nodeW_toSt2 hS) (NodeW.agree_of hag fun _ hs => ownG_W hlab hs)
  exact fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

end Own

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.goodWT_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms goodWT_of

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.siteT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms siteT

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.finT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finT

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.blkT_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkT_own

/-- info: 'Spike.Lib.A64.WakePh.StartTcb.nodeT_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeT_own

end Spike.Lib.A64.WakePh.StartTcb
