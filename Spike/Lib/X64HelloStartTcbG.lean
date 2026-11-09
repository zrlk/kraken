/-
**hello.w's first `scc_rt_alloc_tcb` call at `ownGH`, on x86-64** (the twin of
`Spike/Lib/A64HelloStartTcbG.lean`; wake's `Spike/Lib/X64WakeStartTcbG.lean` at `SccCode.helloCells`): the call
from `scc_rt_start` (on the start's stack, off the pool) where `ownGH` picks `ownH` (`GoodWH`'s first case: the
callee's pcs off a pool stack), so a node's `SFacts` at the first instance (`ownH` at `phH`) move to `SFactsSt2`
at `ownGH`. The frame band `StartTcb.BandT` and `rsp_of_abs` are wake's, program independent.

- `PcTH`: the callee's pcs at hello's canonical base (`scc_rt_alloc_tcb` at `4199029` up to
  `scc_rt_thread_reserve` at `4199484`).
- `inTH_of`, `goodWTH_of`: `inPc` and `GoodWH` by the pc and `%rsp`.
- `finTH`: `GoodWH` where a block's run ends inside the callee.
- `blkT_ownH`, `nodeT_ownH`: a block's (a node's) `SFacts` at `ownH` as `SFactsSt2` at `ownGH`.

## Differences from the AArch64 version

- hello's x86-64 addresses (`X64HelloOwnGEq.labs_eqH`; AArch64: `2164748 .. 2165172`), the take site `4200314`
  (`StartTi.siteTH`); labels by `codeLabel lo helloCells`.
- As wake's x86-64 `StartTcb`: no `hal`; the band is `[-184, 8]` (AArch64's `[-192, 0]`); a block's pcs are its
  pc plus `cellOff`; a node's successor is `sz` bytes on; `Keep` is `%rsp`/`%rbp`.
-/
import Spike.Lib.X64HelloStartTiG
import Spike.Lib.X64WakeStartTcbG

namespace Spike.Lib.X64.HelloPh.StartTcb

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl SFacts)
open Spike.Lib.X64ConsumerA (StSucc SpAt SFactsSt2 rsp_of_abs)
open Spike.Lib.X64 (ND BlkW NodeW At Abs arun cellOff okBlk CodeAt)
open Spike.Lib.X64.WakePh (inPc spPool Keep)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64.WakePh.StartTcb (BandT)
open Spike.Lib.X64.HelloPh (GoodWH ownGH ownGH_W ownH phH hagWH labs_eqH)

/-- **`scc_rt_alloc_tcb`'s pcs** at hello's canonical base (`labs_eqH`'s `scc_rt_alloc_tcb` up to
`scc_rt_thread_reserve`). -/
def PcTH (p : Int64) : Prop := 4199029 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 4199484

instance (p : Int64) : Decidable (PcTH p) := by unfold PcTH; infer_instance

variable {L : RuntimeLayout}

/-- **`inPc` of `scc_rt_alloc_tcb`** by the pc. -/
theorem inTH_of (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcTH s.st.2) : inPc L "scc_rt_alloc_tcb" "scc_rt_thread_reserve" s := by
  obtain ⟨e1, e2, -⟩ := labs_eqH hlab (L := L)
  unfold inPc pcOf; rw [e1, e2]; exact hp

/-- **`GoodWH` by the pc and `%rsp`**: inside the callee, off the pool. -/
theorem goodWTH_of (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    {R : Spike.Lib.Region} (hb : BandT L R) {s : State} (hp : PcTH s.st.2) (hsp : SpAt R (-184) 8 s) :
    GoodWH L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨.inl (inTH_of hlab hp), ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}
  {Dt : State → Prop}

/-- **`GoodWH` where a block's run ends inside the callee**: there its pc
(`h2`) and its static `%rsp` offsets in `[-184, 8]` (`hso`). -/
theorem finTH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (h2 : ∀ σ c, n.J σ c → PcTH (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine goodWTH_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact rsp_of_abs hA

/-- **A block of the call at `ownGH`** from its `SFacts` at the first
instance: its pcs in `PcTH` (`h1`), its static `%rsp` offsets in `[-184, 8]`
(`hso`), `GoodWH` where its run ends (`hfin`). -/
theorem blkT_ownH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) (hb : BandT L R)
    (hsite : ∀ x, (Spike.Lib.X64.PhRec.μ L).site .take = some x → x = 4200314)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcTH (n.pc + Int64.ofNat (cellOff blk k)))
    (hso : ∀ k ≤ blk.length, -184 ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 8)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → GoodWH L s := by
    intro σ c _ k hk s m hA _ _ hs
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine goodWTH_of hlab hb (by rw [hs]; exact h1 k hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact rsp_of_abs hA
  have hag := hagWH (a := a) (μ := Spike.Lib.X64.PhRec.μ L) (F := F) hlab hcode hok hR hlo hhi
    (fun x hx k hk => by have := h1 k hk; unfold PcTH at this; rw [hsite x hx]; omega) hQ
    (fun σ c hJ k hk s m hA he hn hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.X64.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ s m hA he hn hs)
  have hst := Spike.Lib.X64ConsumerA.BlkW.ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.blkW_toSt2 hS) hag
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
    let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

/-- **A node of the call at `ownGH`** from its `SFacts` at the first
instance: its successors keeping `%rsp` and `%rbp` `sz` bytes on (`hk`),
its pc and the next in `PcTH` (`hpc`), its static `%rsp` offset in
`[-184, 8]` (`hso`). -/
theorem nodeT_ownH {sz : Nat} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hb : BandT L R)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : PcTH n.pc ∧ PcTH (n.pc + Int64.ofNat sz)) (hso : -184 ≤ n.o.sp ∧ n.o.sp ≤ 8) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n := by
  have hag : NodeW (fun s _ => GoodWH L s ∧ ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' → GoodWH L s')
      (fun _ _ => False) L.exe L.endPc R F n := by
    intro s c hAt
    obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
    have hsp : s.st.1.regs.rsp.toBitVec = R.addr n.o.sp := rsp_of_abs hA
    refine ⟨⟨goodWTH_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩, fun _ h => h⟩
    obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
    exact goodWTH_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩
  have hst := Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.X64.WakePh.Tcb2W.nodeW_toSt2 hS)
    (Spike.Lib.X64.WakePh.NodeW.agree_of hag fun _ hs => ownGH_W hlab hs)
  exact fun s c hA => ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

end Own

end Spike.Lib.X64.HelloPh.StartTcb

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.inTH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.inTH_of

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.goodWTH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.goodWTH_of

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.finTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.finTH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.blkT_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.blkT_ownH

/-- info: 'Spike.Lib.X64.HelloPh.StartTcb.nodeT_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartTcb.nodeT_ownH
