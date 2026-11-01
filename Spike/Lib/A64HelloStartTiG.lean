/-
**hello.w's `scc_rt_thread_init` call at `ownGH`** (AArch64,
the `hti` chain; twin of `Spike/Lib/A64WakeStartTiG.lean` at helloProg): the
call from `scc_rt_start` (on the start's stack, off the pool) and its nested
`scc_rt_stack_take` call, where `ownGH` picks `ownH` (`GoodWH`'s first case:
the callees' pcs off a pool stack), so a node's `SFacts` at the first
instance (`ownH` at `phH`) move to `SFactsSt2` at `ownGH`. The callees' pcs
are `Ti2.PcIH` / `PcNH` (hello's canonical base), the frame band
`StartTi.BandI` (and `bandI_callee`) is wake's, program independent.

- `siteTH`: the marks' take site is `2165976`.
- `goodWIH_of`: `GoodWH` by the pc and `sp`.
- `finIH`: `GoodWH` where a block's run ends inside the callees.
- `blkI_ownH`, `nodeI_ownH`, `siteI_ownH`: a block's (a node's, the take
  site's) `SFacts` at `ownH` as `SFactsSt2` at `ownGH`.
-/
import Spike.Lib.A64HelloTi2G
import Spike.Lib.A64HelloTcb2W

namespace Spike.Lib.A64.HelloPh.StartTi

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
open Spike.Lib.A64.WakePh.StartTcb (sp_of_abs)
open Spike.Lib.A64.WakePh.StartTi (BandI)
open Spike.Lib.A64.HelloPh.Ti2 (PcIH PcNH inIH_of)

variable {L : RuntimeLayout}

/-- **The marks' take site is hello's `2165976`** (`Tcb2W.tcb_labsH`). -/
theorem siteTH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165976 := by
  intro x hx
  rw [hsite, show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165976 from
    (Spike.Lib.A64.HelloPh.Tcb2W.tcb_labsH hlab).2.2.2.2.2] at hx
  cases hx; rfl

/-- **The take site's label is `2165976`** (`Tcb2W.tcb_labsH`). -/
theorem siteLabH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) :
    (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 2165976 := by
  rw [show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165976 from
    (Spike.Lib.A64.HelloPh.Tcb2W.tcb_labsH hlab).2.2.2.2.2]; rfl

/-- **`GoodWH` by the pc and `sp`**: inside the callees, off the pool. -/
theorem goodWIH_of (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {R : Spike.Lib.Region} {klo : Int} (hb : BandI L R klo) {s : State} (hp : PcIH s.st.2) (hsp : SpAt R klo 0 s) :
    GoodWH L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨.inr (inIH_of hlab hp), ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi klo : Int}
  {Dt : State → Prop}

/-- **`GoodWH` where a block's run ends inside the callees**: there its pc
(`h2`) and its static `sp` offsets in `[klo, 0]` (`hso`). -/
theorem finIH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (h2 : ∀ σ c, n.J σ c →
      PcIH (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine goodWIH_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the callees at `ownGH`** from its `SFacts` at the first
instance: its pcs in `PcNH` (`h1`), its static `sp` offsets in `[klo, 0]`
(`hso`), `GoodWH` where its run ends (`hfin`). -/
theorem blkI_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandI L R klo)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165976)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcNH (n.pc + Int64.ofNat (4 * k)))
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0)
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
    refine goodWIH_of hlab hb (by rw [hs]; exact (h1 k hk).1) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hagWH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by rw [hsite x hx]; exact (h1 k hk).2) hQ
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

/-- **`GoodWH` at a node of the callees** and at its successors, which keep
`sp` and `x30` 4 bytes on (`hk`): its pc and the next in `PcIH` (`hpc`), its
static `sp` offset in `[klo, 0]` (`hso`). -/
theorem goodWIH_node (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandI L R klo)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c →
      GoodWH L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodWH L s' := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
  refine ⟨goodWIH_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact goodWIH_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

/-- **A node of the callees at `ownGH`** from its `SFacts` at the first
instance (as `goodWIH_node`). -/
theorem nodeI_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandI L R klo)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n := by
  have hg := goodWIH_node hlab hb hk hpc hso
  have hag : NodeW (fun s _ => GoodWH L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodWH L s')
      (fun _ _ => False) L.exe L.endPc R F n := fun s c hA => ⟨hg s c hA, fun _ h => h⟩
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (Spike.Lib.A64.WakePh.Tcb2W.nodeW_toSt2 hS)
    (Spike.Lib.A64.WakePh.NodeW.agree_of hag fun _ hs => ownGH_W hlab hs)
  exact fun s c hA =>
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

/-- **The take site's states at `ownGH`** from their `SFacts` at the first
instance (as `goodWIH_node`; the site's successors are the `nop`'s and the
take's). -/
theorem siteI_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandI L R klo)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) rS Tk lbl' s c)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c → SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt := by
  intro s c hA
  have hg := goodWIH_node hlab hb hk hpc hso s c hA
  exact Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt ((hS s c hA).toSt.toSt2.congr (ownGH_W hlab hg.1)
    fun s' h => ownGH_W hlab (hg.2 s' h)) (fun h => h.elim)

end Own

end Spike.Lib.A64.HelloPh.StartTi

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.siteTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.siteTH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.siteLabH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.siteLabH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.goodWIH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.goodWIH_of

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.finIH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.finIH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.blkI_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.blkI_ownH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.nodeI_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.nodeI_ownH

/-- info: 'Spike.Lib.A64.HelloPh.StartTi.siteI_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartTi.siteI_ownH
