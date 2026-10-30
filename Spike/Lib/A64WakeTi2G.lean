/-
**wake.w's second `scc_rt_thread_init` call at `ownG`** (AArch64; the
`hatA` ti discharger): the call from `wc_main` (on stack 0, a pool stack)
and its nested `scc_rt_stack_take` call, where `ownG` picks `own2b`
(`Good2b`'s first case: the callees' pcs on a pool stack), so a node's
`SFactsSt` at the second instance (`own2b` at `ph2b`, `instOk2bP`) move to
`SFactsSt2` at `ownG`. As `StartTi.blkI_own` / `nodeI_own` / `siteI_own`
with the frame on the pool instead of off it.

- `BandP`: a callee's frame `[lo, 0]` on the pool; `bandP_callee`.
- `good2bI_of`: `Good2b` by the pc and `sp`.
- `fin2`: `Good2b` where a block's run ends inside the callees.
- `blk2_own`, `node2_own`, `site2_own`: a block's (a node's, the take
  site's) `SFactsSt` at `own2b` as `SFactsSt2` at `ownG`.

The callees' pcs are `StartTi.PcI` / `PcN` (decided at the canonical base,
tied to the labels by `labs_eq`).
-/
import Spike.Lib.A64WakeStartTiG
import Spike.Lib.A64WakeTake2

namespace Spike.Lib.A64.WakePh.Ti2

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
open Spike.Lib.A64.WakePh.StartTi (PcI PcN inI_of)

/-- **A callee's frame on the pool**: every address of `[lo, 0]` of `R`
in `(pool.lo, pool.lo + pool.size]`. -/
def BandP (L : RuntimeLayout) (R : Spike.Lib.Region) (lo : Int) : Prop :=
  ∀ k, lo ≤ k → k ≤ 0 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

variable {L : RuntimeLayout}

/-- **A callee's frame on the pool** from its caller's: `[lo', 0]` of the
callee at `kc` is `[kc + lo', kc]` of `R`. -/
theorem bandP_callee {R : Spike.Lib.Region} {klo kc lo' lo'' hi'' : Int} (hb : BandP L R klo)
    (h1 : klo ≤ kc + lo') (h2 : kc ≤ 0) : BandP L (R.callee kc lo'' hi'') lo' := by
  intro k hk1 hk2
  have he : (R.callee kc lo'' hi'').addr k = R.addr (kc + k) := by
    simp only [Spike.Lib.Region.callee, Spike.Lib.Region.addr_add]; rfl
  rw [he]; exact hb _ (by omega) (by omega)

/-- A frame on the pool, its low end raised. -/
theorem bandP_mono {R : Spike.Lib.Region} {lo lo' : Int} (hb : BandP L R lo) (h : lo ≤ lo') : BandP L R lo' :=
  fun k h1 h2 => hb k (by omega) h2

/-- **`Good2b` by the pc and `sp`**: inside the callees, on the pool. -/
theorem good2bI_of (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) {R : Spike.Lib.Region}
    {klo : Int} (hb : BandP L R klo) {s : State} (hp : PcI s.st.2) (hsp : SpAt R klo 0 s) : Good2b L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨inI_of hlab hp, ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {lbl' : Lbl} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi klo : Int}
  {Dt : State → Prop}

/-- **`Good2b` where a block's run ends inside the callees**: there its pc
(`h2`) and its static `sp` offsets in `[klo, 0]` (`hso`). -/
theorem fin2 (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (h2 : ∀ σ c, n.J σ c → PcI (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine good2bI_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the callees at `ownG`** from its `SFactsSt` at the second
instance: its pcs in `PcN` (`h1`), its static `sp` offsets in `[klo, 0]`
(`hso`), `Good2b` where its run ends (`hfin`). -/
theorem blk2_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165940)
    (hS : BlkW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n blk)
    (hcode : ∀ s : State, s.exe = L.exe → s.endPc = L.endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (h1 : ∀ k < blk.length, PcN (n.pc + Int64.ofNat (4 * k)))
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → Good2b L s := by
    intro σ c _ k hk s m hA _ _ hs
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2bI_of hlab hb (by rw [hs]; exact (h1 k hk).1) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hag2b (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by rw [hsite x hx]; exact (h1 k hk).2) hQ
    (fun σ c hJ k hk s m hA he hn hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ s m hA he hn hs)
  have hst := Spike.Lib.A64ConsumerA.BlkW.ownCongr2
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 => let r := hS s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9; ⟨r.1.toSt2, r.2⟩) hag
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
    let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

/-- **`Good2b` at a node of the callees** and at its successors, which keep
`sp` and `x30` 4 bytes on (`hk`): its pc and the next in `PcI` (`hpc`), its
static `sp` offset in `[klo, 0]` (`hso`). -/
theorem good2bI_node (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c →
      Good2b L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → Good2b L s' := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
  refine ⟨good2bI_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact good2bI_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

/-- **A node of the callees at `ownG`** from its `SFactsSt` at the second
instance (as `good2bI_node`). -/
theorem node2_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt) K L.exe L.endPc R F n := by
  have hg := good2bI_node hlab hb hk hpc hso
  have hag : NodeW (fun s _ => Good2b L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → Good2b L s')
      (fun _ _ => False) L.exe L.endPc R F n := fun s c hA => ⟨hg s c hA, fun _ h => h⟩
  have hst := Tcb2W.nodeW_ownCongr2 (fun s c hA => let r := hS s c hA; ⟨r.1.toSt2, r.2⟩) (NodeW.agree_of hag fun _ hs => ownG_2b hlab hs)
  exact fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

/-- **The take site's states at `ownG`** from their `SFactsSt` at the second
instance (as `good2bI_node`). -/
theorem site2_own (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2b L a (ph2b (pcOf s))) rS Tk s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcI n.pc ∧ PcI (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c → SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownG L a) s Dt := by
  intro s c hA
  have hg := good2bI_node hlab hb hk hpc hso s c hA
  exact Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt ((hS s c hA).toSt2.congr (ownG_2b hlab hg.1)
    fun s' h => ownG_2b hlab (hg.2 s' h)) (fun h => h.elim)

end Own

end Spike.Lib.A64.WakePh.Ti2

/-- info: 'Spike.Lib.A64.WakePh.Ti2.bandP_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.bandP_callee

/-- info: 'Spike.Lib.A64.WakePh.Ti2.good2bI_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.good2bI_of

/-- info: 'Spike.Lib.A64.WakePh.Ti2.fin2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.fin2

/-- info: 'Spike.Lib.A64.WakePh.Ti2.blk2_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.blk2_own

/-- info: 'Spike.Lib.A64.WakePh.Ti2.node2_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.node2_own

/-- info: 'Spike.Lib.A64.WakePh.Ti2.site2_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.site2_own

/-- info: 'Spike.Lib.A64.WakePh.Ti2.bandP_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.bandP_mono

/-- info: 'Spike.Lib.A64.WakePh.Ti2.good2bI_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.good2bI_node
