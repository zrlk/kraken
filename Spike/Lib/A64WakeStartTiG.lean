/-
**wake.w's `scc_rt_thread_init` call at `ownG`** (AArch64): the call from
`scc_rt_start` (on the start's stack, off the pool) and its nested
`scc_rt_stack_take` call, where `ownG` picks `ownW` (`GoodW`'s first case:
the callee's pcs off a pool stack), so a node's `SFacts` at the first
instance (`ownW` at `phW`) move to `SFactsSt2` at `ownG`. As
`StartTcb.blkT_own` / `nodeT_own`, the frame's low end `lo` a parameter
(`-48` for `scc_rt_thread_init`, `-208` for `scc_rt_stack_take`).

- `PcI`, `PcN`, `BandI`: the callees' pcs at the canonical base (`PcN` off
  the take site); a frame `[lo, 0]` off the pool.
- `inI_of`, `goodWI_of`: `inPc` and `GoodW` by the pc and `sp`.
- `finI`: `GoodW` where a block's run ends inside the callees.
- `blkI_own`, `nodeI_own`, `siteI_own`: a block's (a node's, the take
  site's) `SFacts` at `ownW` as `SFactsSt2` at `ownG`.
-/
import Spike.Lib.A64WakeStartTcbG

namespace Spike.Lib.A64.WakePh.StartTi

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
open Spike.Lib.A64.WakePh.StartTcb (sp_of_abs)

/-- **`scc_rt_thread_init`'s and `scc_rt_stack_take`'s pcs** at the
canonical base (up to `scc_rt_stack_release`). The bounds are checked
against the labels only by `inI_of` (`labs_eq`, decided from `hlab`), and
every `PcI` fact is decided on pcs from the label lemmas `ti_labs` /
`take_labs`, so a `.text` shift fails those decisions loudly. -/
def PcI (p : Int64) : Prop := 2165244 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2165964

instance (p : Int64) : Decidable (PcI p) := by unfold PcI; infer_instance

/-- **`PcI` off the take site.** The site's literal is tied to the label by
`StartTcb.siteT` (`Tcb2W.tcb_labs`, decided), the only producer of `hsite`. -/
def PcN (p : Int64) : Prop := PcI p ∧ p.toBitVec.toNat ≠ 2165940

instance (p : Int64) : Decidable (PcN p) := by unfold PcN; infer_instance

/-- **A callee's frame off the pool**: no address of `[lo, 0]` of `R` in
`(pool.lo, pool.lo + pool.size]`. -/
def BandI (L : RuntimeLayout) (R : Spike.Lib.Region) (lo : Int) : Prop :=
  ∀ k, lo ≤ k → k ≤ 0 → ¬ (L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)

variable {L : RuntimeLayout}

/-- **A callee's frame off the pool** from its caller's: `[lo', 0]` of the
callee at `kc` is `[kc + lo', kc]` of `R`. -/
theorem bandI_callee {R : Spike.Lib.Region} {klo kc lo' lo'' hi'' : Int} (hb : BandI L R klo)
    (h1 : klo ≤ kc + lo') (h2 : kc ≤ 0) : BandI L (R.callee kc lo'' hi'') lo' := by
  intro k hk1 hk2
  have he : (R.callee kc lo'' hi'').addr k = R.addr (kc + k) := by
    simp only [Spike.Lib.Region.callee, Spike.Lib.Region.addr_add]; rfl
  rw [he]; exact hb _ (by omega) (by omega)

/-- **`inPc` of `scc_rt_thread_init`** by the pc. -/
theorem inI_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcI s.st.2) : inPc L "scc_rt_thread_init" "scc_rt_stack_release" s := by
  obtain ⟨-, -, e3, e4, -⟩ := labs_eq hlab (L := L)
  unfold inPc pcOf; rw [e3, e4]; exact hp

/-- **A pc of the callees off the take site is off its label** (`PcN`'s
literal tied by `Tcb2W.tcb_labs`). -/
theorem offSite (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcN s.st.2) : pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  rw [show L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat 2165940 from
    (Tcb2W.tcb_labs hlab).2.2.2.2.2]
  exact fun e => hp.2 (e.trans (by decide))

/-- **`GoodW` by the pc and `sp`**: inside the callees, off the pool. -/
theorem goodWI_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {R : Spike.Lib.Region}
    {klo : Int} (hb : BandI L R klo) {s : State} (hp : PcI s.st.2) (hsp : SpAt R klo 0 s) : GoodW L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨.inr (inI_of hlab hp), ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi klo : Int}
  {Dt : State → Prop}

/-- **`GoodW` where a block's run ends inside the callees**: there its pc
(`h2`) and its static `sp` offsets in `[klo, 0]` (`hso`). -/
theorem finI (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (h2 : ∀ σ c, n.J σ c → PcI (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine goodWI_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the callees at `ownG`** from its `SFacts` at the first
instance: its pcs in `PcN` (`h1`), its static `sp` offsets in `[klo, 0]`
(`hso`), `GoodW` where its run ends (`hfin`). -/
theorem blkI_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165940)
    (hS : BlkW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcN (n.pc + Int64.ofNat (4 * k)))
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0)
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
    refine goodWI_of hlab hb (by rw [hs]; exact (h1 k hk).1) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hagW (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by rw [hsite x hx]; exact (h1 k hk).2) hQ
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

/-- **`GoodW` at a node of the callees** and at its successors, which keep
`sp` and `x30` 4 bytes on (`hk`): its pc and the next in `PcI` (`hpc`), its
static `sp` offset in `[klo, 0]` (`hso`). -/
theorem goodWI_node (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c →
      GoodW L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodW L s' := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
  refine ⟨goodWI_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact goodWI_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

/-- **A node of the callees at `ownG`** from its `SFacts` at the first
instance (as `goodWI_node`). -/
theorem nodeI_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (hS : NodeW (fun s c => SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n := by
  have hg := goodWI_node hlab hb hk hpc hso
  have hag : NodeW (fun s _ => GoodW L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → GoodW L s')
      (fun _ _ => False) L.exe L.endPc R F n := fun s c hA => ⟨hg s c hA, fun _ h => h⟩
  have hst := Tcb2W.nodeW_ownCongr2 (Tcb2W.nodeW_toSt2 hS) (NodeW.agree_of hag fun _ hs => ownG_W hlab hs)
  exact fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

/-- **The take site's states at `ownG`** from their `SFacts` at the first
instance (as `goodWI_node`; the site's successors are the `nop`'s and the
take's). -/
theorem siteI_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandI L R klo)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      SFacts L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) rS Tk lbl' s c)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c → SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt := by
  intro s c hA
  have hg := goodWI_node hlab hb hk hpc hso s c hA
  exact Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt ((hS s c hA).toSt.toSt2.congr (ownG_W hlab hg.1)
    fun s' h => ownG_W hlab (hg.2 s' h)) (fun h => h.elim)

end Own

/-- info: 'Spike.Lib.A64.WakePh.StartTi.bandI_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms bandI_callee

/-- info: 'Spike.Lib.A64.WakePh.StartTi.goodWI_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms goodWI_of

/-- info: 'Spike.Lib.A64.WakePh.StartTi.offSite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms offSite

/-- info: 'Spike.Lib.A64.WakePh.StartTi.finI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms finI

/-- info: 'Spike.Lib.A64.WakePh.StartTi.blkI_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkI_own

/-- info: 'Spike.Lib.A64.WakePh.StartTi.nodeI_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeI_own

/-- info: 'Spike.Lib.A64.WakePh.StartTi.siteI_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms siteI_own

end Spike.Lib.A64.WakePh.StartTi
