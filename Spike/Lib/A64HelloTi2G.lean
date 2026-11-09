/-
**hello.w's second `scc_rt_thread_init` call at `ownGH`** (AArch64, hello
plan B3, the `hti` chain; twin of `Spike/Lib/A64WakeTi2G.lean` at
helloProg): the call from `wc_main` (on stack 0, a pool stack) and its
nested `scc_rt_stack_take` call, where `ownGH` picks `own2bH` (`Good2bH`'s
first case: the callees' pcs on a pool stack), so a node's `SFactsSt` at the
second instance (`own2bH` at `ph2bH`, `instOk2bPH`) move to `SFactsSt2` at
`ownGH`. The frame band `Ti2.BandP` (and `bandP_callee`, `bandP_mono`) is
wake's, program independent.

- `PcIH`, `PcNH`: the callees' pcs at hello's canonical base (`PcNH` off
  the take site `2165980`); `inIH_of`, `offSiteH`.
- `good2bIH_of`: `Good2bH` by the pc and `sp`.
- `fin2H`: `Good2bH` where a block's run ends inside the callees.
- `blk2_ownH`, `node2_ownH`, `site2_ownH`: a block's (a node's, the take
  site's) `SFactsSt` at `own2bH` as `SFactsSt2` at `ownGH`.
-/
import Spike.Lib.A64HelloTake2
import Spike.Lib.A64HelloOwnGAgree
import Spike.Lib.A64WakeTi2G

namespace Spike.Lib.A64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl)
open Spike.Lib.A64ConsumerA (StSucc SpAt SFactsSt2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At)
open Spike.Lib.A64.WakePh (inPc spPool Keep)
open Spike.Lib.A64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.A64.WakePh.StartTcb (sp_of_abs)
open Spike.Lib.A64.WakePh.Ti2 (BandP)

/-- **`scc_rt_thread_init`'s and `scc_rt_stack_take`'s pcs** at hello's
canonical base (up to `scc_rt_stack_release`), tied to the labels by
`inIH_of` (`labs_eqH`). -/
def PcIH (p : Int64) : Prop := 2165284 ≤ p.toBitVec.toNat ∧ p.toBitVec.toNat < 2166004

instance (p : Int64) : Decidable (PcIH p) := by unfold PcIH; infer_instance

/-- **`PcIH` off the take site** (`2165980`). -/
def PcNH (p : Int64) : Prop := PcIH p ∧ p.toBitVec.toNat ≠ 2165980

instance (p : Int64) : Decidable (PcNH p) := by unfold PcNH; infer_instance

variable {L : RuntimeLayout}

/-- **`inPc` of `scc_rt_thread_init`** by the pc. -/
theorem inIH_of (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {s : State}
    (hp : PcIH s.st.2) : inPc L "scc_rt_thread_init" "scc_rt_stack_release" s := by
  obtain ⟨-, -, e3, e4, -⟩ := labs_eqH hlab (L := L)
  unfold inPc pcOf; rw [e3, e4]; exact hp

/-- **A pc of the callees off the take site is off its label** (hello's take
site at `2165980`, `hsite`). -/
theorem offSiteH (hsite : (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat = 2165980) {s : State}
    (hp : PcNH s.st.2) : pcOf s ≠ (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  rw [hsite]; exact hp.2

/-- **`Good2bH` by the pc and `sp`**: inside the callees, on the pool. -/
theorem good2bIH_of (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    {R : Spike.Lib.Region} {klo : Int} (hb : BandP L R klo) {s : State} (hp : PcIH s.st.2) (hsp : SpAt R klo 0 s) :
    Good2bH L s := by
  obtain ⟨k, h1, h2, hk⟩ := hsp
  refine .inl ⟨inIH_of hlab hp, ?_⟩
  unfold spPool; rw [hk]; exact hb k h1 h2

section Own

variable {a : BitVec 64} {rS : Range} {Tk : State → Prop} {K : State → State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {n : ND} {blk : List Directive} {blo bhi klo : Int}
  {Dt : State → Prop}

/-- **`Good2bH` where a block's run ends inside the callees**: there its pc
(`h2`) and its static `sp` offsets in `[klo, 0]` (`hso`). -/
theorem fin2H (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) (hb : BandP L R klo)
    (h2 : ∀ σ c, n.J σ c →
      PcIH (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hso : ∀ k ≤ blk.length, klo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ 0) :
    ∀ σ c, n.J σ c → ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Good2bH L s := by
  intro σ c hJ s m hA _ _ hs
  have ho := hso blk.length (Nat.le_refl _)
  rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
  refine good2bIH_of hlab hb (by rw [hs]; exact h2 σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
  rw [hs]; exact sp_of_abs hA

/-- **A block of the callees at `ownGH`** from its `SFactsSt` at the second
instance: its pcs in `PcNH` (`h1`), its static `sp` offsets in `[klo, 0]`
(`hso`), `Good2bH` where its run ends (`hfin`). -/
theorem blk2_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandP L R klo)
    (hsite : ∀ x, (Spike.Lib.A64.PhRec.μ L).site .take = some x → x = 2165980)
    (hS : BlkW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
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
      Good2bH L s) :
    BlkW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels L.exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = L.exe → s.endPc = L.endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → Good2bH L s := by
    intro σ c _ k hk s m hA _ _ hs
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine good2bIH_of hlab hb (by rw [hs]; exact (h1 k hk).1) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs]; exact sp_of_abs hA
  have hag := hag2bH (a := a) (μ := Spike.Lib.A64.PhRec.μ L) (F := F) hlab hcode hok hR hal hlo hhi
    (fun x hx k hk => by rw [hsite x hx]; exact (h1 k hk).2) hQ
    (fun σ c hJ k hk s m hA he hn hs => by
      rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
      · rw [Spike.Lib.A64.Flow.arun_pc _ hok hk1] at hs
        exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs
      · rw [List.take_of_length_le (by omega)] at hA hs
        exact hfin σ c hJ s m hA he hn hs)
  have hst := Spike.Lib.A64ConsumerA.BlkW.ownCongr2
    (fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 =>
      let r := hS s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9; ⟨r.1.toSt2, r.2⟩) hag
  exact fun s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9 =>
    let r := hst s σ c a1 a2 a3 a4 a5 a6 a7 j hj m a8 a9
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt r.1 (fun h => h.elim), r.2⟩

/-- **`Good2bH` at a node of the callees** and at its successors, which keep
`sp` and `x30` 4 bytes on (`hk`): its pc and the next in `PcIH` (`hpc`), its
static `sp` offset in `[klo, 0]` (`hso`). -/
theorem good2bIH_node (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandP L R klo)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c →
      Good2bH L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → Good2bH L s' := by
  intro s c hAt
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.SP.toBitVec = R.addr n.o.sp := sp_of_abs hA
  refine ⟨good2bIH_of hlab hb (by rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact good2bIH_of hlab hb (by rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

/-- **A node of the callees at `ownGH`** from its `SFactsSt` at the second
instance (as `good2bIH_node`). -/
theorem node2_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandP L R klo)
    (hS : NodeW (fun s c => Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L)
        (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
      K L.exe L.endPc R F n)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    NodeW (fun s _ => SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt) K L.exe L.endPc R F n := by
  have hg := good2bIH_node hlab hb hk hpc hso
  have hag : NodeW (fun s _ => Good2bH L s ∧ ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' → Good2bH L s')
      (fun _ _ => False) L.exe L.endPc R F n := fun s c hA => ⟨hg s c hA, fun _ h => h⟩
  have hst := Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 (fun s c hA => let r := hS s c hA; ⟨r.1.toSt2, r.2⟩)
    (Spike.Lib.A64.WakePh.NodeW.agree_of hag fun _ hs => ownGH_2b hlab hs)
  exact fun s c hA =>
    ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hst s c hA).1 (fun h => h.elim), (hst s c hA).2⟩

/-- **The take site's states at `ownGH`** from their `SFactsSt` at the second
instance (as `good2bIH_node`). -/
theorem site2_ownH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hb : BandP L R klo)
    (hS : ∀ s c, At L.exe L.endPc R F n s c →
      Spike.Lib.A64ConsumerA.SFactsSt L.Λ (Spike.Lib.A64.PhRec.μ L) (fun s => own2bH L a (ph2bH (pcOf s))) rS Tk s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.A64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + 4)
    (hpc : PcIH n.pc ∧ PcIH (n.pc + 4)) (hso : klo ≤ n.o.sp ∧ n.o.sp ≤ 0) :
    ∀ s c, At L.exe L.endPc R F n s c → SFactsSt2 L.Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s Dt := by
  intro s c hA
  have hg := good2bIH_node hlab hb hk hpc hso s c hA
  exact Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt ((hS s c hA).toSt2.congr (ownGH_2b hlab hg.1)
    fun s' h => ownGH_2b hlab (hg.2 s' h)) (fun h => h.elim)

end Own

end Spike.Lib.A64.HelloPh.Ti2

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.inIH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.inIH_of

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.offSiteH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.offSiteH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.good2bIH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.good2bIH_of

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.fin2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.fin2H

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.blk2_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.blk2_ownH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.good2bIH_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.good2bIH_node

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.node2_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.node2_ownH

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.site2_ownH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.site2_ownH
