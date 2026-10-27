/-
**The runtime's own states' remaining `W2` facts** (AArch64): the world
`RtX` of the facts `W2` asks at a runtime state beyond the phase table's
`SFacts` (`Spike/Lib/LowerA64/RtW2.lean`): the write abort's phase kept
(`AbSt` at `WriteAb.Ab lab`), the source start's control `c0` placed at no
frame, no write to the arena's heap nor its counter (`WrOff`), and the
control `c0` itself; and its producers at the runtime's covered blocks.

A covered block's instructions are silent (`blkW_noWr`), so `WrOff` holds;
its targets are positions of runs of labels off the write abort's
(`PosOff`, `blkW_abSt_pos`): the fall-through positions of its own run, and
its branch labels' (`htgt_posOff`).

- `aiFalls`, `lastFalls`: a covered instruction falls through; a block's
  last instruction does (the branch labels: `aiLab`, `blkLabs`,
  `Spike/Lib/LowerA64/PhCheck.lean`);
- `aiTgts_cases`: a target of a non-`ret` instruction is its fall-through
  or one of its labels;
- `htgt_posOff`: `blkW_abSt_pos`'s targets at a block of a run of a label
  off the write abort's, the position after it off the write abort when its
  last instruction falls through, its branch labels positions off the write
  abort;
- `RtX`, `rtX_w2`: the world, and `W2` from `SFacts` at `c0` and `RtX`;
- `blkW_rtX`: a covered block inside `RtX`.
- `nodeW_rtX_si`, `nodeW_rtX_st`, `nodeW_rtX_ldop`, `nodeW_rtX_svc`: a single
  instruction's node inside `RtX`, a store's and an RMW's word off the
  arena's counter and heap.
- `blkW_abSt_tg`, `htgt_offR`, `blkW_rtXG`: a covered block with a `ret`
  (to a return address off the write abort's pcs) or calls of the abort's
  entry (at `x0 ≠ 4`) inside `RtX`.
- `nodeW_rtX_ldr`, `nodeW_rtX_swp`, `nodeW_rtX_stlr`: a load's, a swap's
  and a release store's node inside `RtX`;
- `site_rtX`: a take site's nop inside `RtX`;
- `nodeW_rtX_reg`: a register operation's node inside `RtX`.
-/
import Spike.Lib.LowerA64.RtW2
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.LowerA64.PhCheck
import Spike.Lib.A64AllocGAb

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (ofNat4_succ')
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.A64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.A64 (blockAt InRun inRun_of_blockAt Lays)
open Scc.Sem.A64 (abi pcOf atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)

/-! ## A block's targets -/

/-- A covered instruction falls through (neither `b`, `bl` nor `ret`). -/
def aiFalls : AI → Bool
  | .b _ | .bl _ | .ret _ => false
  | _ => true

/-- A block's last instruction falls through. -/
def lastFalls (blk : List Directive) : Bool :=
  match blk.getLast? with
  | some d => ((classify d).map aiFalls).getD false
  | none => false

/-- **A target of a non-`ret` instruction** is its fall-through (when it
falls through) or one of its labels. -/
theorem aiTgts_cases {lab : Label → Int64} {fall ra t : Int64} {a : AI} (hr : ∀ r, a ≠ .ret r)
    (ht : t ∈ aiTgts lab fall ra a) : (t = fall ∧ aiFalls a = true) ∨ ∃ L, aiLab a = some L ∧ t = lab L := by
  cases a <;> simp_all [aiTgts, aiFalls, aiLab] <;> exact ht.symm

/-- **A block's targets are positions off the write abort** (`blkW_abSt_pos`'s
`htgt`): at a block of the run of a label `l` off the write abort's, with no
`ret`, the position after it off the write abort when its last instruction
falls through (`hnext`), and its branch labels positions off the write abort
(`hlabs`). -/
theorem htgt_posOff {prog : List Directive} {lab : Label → Int64} {n : ND} {blk : List Directive} {l : Label}
    {k : Nat} {ra : Int64} (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hl : l ∉ abLabs) (hnr : noRetBlk blk = true)
    (hnext : lastFalls blk = true → PosOff prog lab (lab l + Int64.ofNat (4 * (k + blk.length))))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff prog lab (lab L)) :
    ∀ σ c, n.J σ c → ∀ k' (hk : k' < blk.length) a, classify blk[k'] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k') + Int64.ofNat 4) ra a,
        PosOff prog lab t ∨
          (a = .bl "scc_rt_abort" ∧
            (Spike.Lib.A64.Flow.arun lab (blk.take k') ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4) := by
  intro σ c _ k' hk a ha t ht
  left
  rcases aiTgts_cases (fun r hr => noRet_false hnr k' hk r (hr ▸ ha)) ht with ⟨rfl, hf⟩ | ⟨L, hL, rfl⟩
  · rw [← he, ofNat4_succ', ← ofNat4_add]
    by_cases hlt : k' + 1 < blk.length
    · exact ⟨l, k + (k' + 1), inRun_of_blockAt hb hlt, hl, rfl⟩
    · have hk1 : k' = blk.length - 1 := by omega
      have hlast : blk.getLast? = some blk[k'] := by
        rw [List.getLast?_eq_getElem?]; simp [hk1]
      have := hnext (by simp only [lastFalls, hlast, ha, Option.map_some, Option.getD_some, hf])
      rwa [show k + (k' + 1) = k + blk.length by omega]
  · refine hlabs L (List.mem_filterMap.mpr ⟨blk[k'], List.getElem_mem hk, ?_⟩)
    simp only [ha, Option.bind_some]
    exact hL

/-! ## The world -/

/-- **The runtime's remaining facts at a state**: the write abort's phase
kept, the control placed at no frame, no write to the arena's heap nor its
counter, the control the source start's `c0`. -/
def RtX (Λ : Scc.Sem.Layout) (μ : Marks) (ar : Arena) (lbl : Lbl) (lab : Label → Int64) (c0 : Ctl) :
    Frag isaLSE2 := fun s c =>
  AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c [] ∧ WrOff ar s ∧ c = c0

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {lab : Label → Int64} {c0 : Ctl}

/-- **`W2` at a runtime state at no frame**: `SFacts` at the source start's
control `c0` (`A64Consumer.c0`, free of `ZBad`) and `RtX`. -/
theorem rtX_w2 (hp : ProgNoS ZBad p) (hf0 : FrOk2 A64Consumer.c0 []) {s : State} {c : Ctl}
    (hS : SFacts Λ μ own rS Tk lbl0 s A64Consumer.c0) (hX : RtX Λ μ ar lbl lab A64Consumer.c0 s c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c [] := by
  obtain ⟨hab, hpl, hwr, rfl⟩ := hX
  exact w2_of_parts hp hS (w2Part_of_wrOff hab hpl hwr hS) (fun _ => hS.noRet) hf0

/-! ## Covered blocks -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered runtime block inside `RtX`**: a block of the code (`hb`,
`he`) covered at its node's offsets (`hok`) passing its phase check
(`hph`), with no `ret`, in the run of a label off the write abort's, the
position after it off the write abort when its last instruction falls
through (`hnext`), its branch labels positions off the write abort
(`hlabs`), at a node whose controls are `c0` (`hc0`), placed at no frame (`hpl0`), in a
layout of a program with the runtime's code (`hI`, `hpr`, `hab`). -/
theorem blkW_rtX {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hnr : noRetBlk blk = true) (hl : l ∉ abLabs)
    (hnext : lastFalls blk = true → PosOff prog lab (lab l + Int64.ofNat (4 * (k + blk.length))))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff prog lab (lab L))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    BlkW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n blk := by
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hA := blkW_abSt_pos hI hpr hab (F := F) (dead := dead) (ra := ra) hcode hok hR hal hlo hhi hph hnr
    (htgt_posOff hb he hl hnr hnext hlabs)
  have hW := Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi (F := F)
  intro s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h1 := hA s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h2 := hW s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-! ## Single-instruction nodes -/

/-- **A runtime node at a single instruction without an event inside
`RtX`** (`nodeW_ab_si`, `nodeW_noWr_si`): its pc off the sites, its next pc
off the write abort's pcs, its controls `c0` (`hc0`), placed at no frame
(`hpl0`). -/
theorem nodeW_rtX_si {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.A64.AllocG.nodeW_ab_si hI hb he hp hok hnx s c hA
  have h2 := Spike.Lib.A64.AllocG.nodeW_noWr_si hI hb he hp s c hA
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-- **A runtime node at a store inside `RtX`** (`nodeW_ab_st`,
`nodeW_wr_st`): as `nodeW_rtX_si`, the stored word unmapped in private
memory (`ha`), off the arena's counter and heap (`hoff`). -/
theorem nodeW_rtX_st {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {i : Int64} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat ∧
        (Spike.Lib.A64.Flow.rAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.A64.AllocG.nodeW_ab_st hI hb he hp hok hnx ha s c hA
  obtain ⟨⟨σ, hJ, -, hw⟩, -⟩ := Spike.Lib.A64.AllocG.nodeW_wr_st hI hb he hp ha s c hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => hw L hL ▸ hoff σ _ hJ, rfl⟩, fun _ h => h⟩

/-- **A runtime node at an RMW inside `RtX`** (`nodeW_ab_ldop`,
`nodeW_wr_ldop`): as `nodeW_rtX_st`. -/
theorem nodeW_rtX_ldop {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧
        (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.A64.AllocG.nodeW_ab_ldop hI hb he hp hok hnx ha s c hA
  obtain ⟨⟨σ, hJ, hw⟩, -⟩ := Spike.Lib.A64.AllocG.nodeW_wr_ldop hI hb he hp ha s c hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => hw L hL ▸ hoff σ _ hJ, rfl⟩, fun _ h => h⟩

/-- **A runtime node at `svc #0` inside `RtX`**: as `nodeW_rtX_si`, the
system call's returns at the next pc, off the write abort's pcs; a fault
writes nothing. -/
theorem nodeW_rtX_svc {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hsys : abi.atSys s = true := atSvc_of_cellAt hc
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨⟨fun _ h => (by rw [hsys] at h; cases h), fun _ _ call hd s' hs' hAb => ?_,
    fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩, hpl0 _, fun L hL => ?_, rfl⟩, fun _ h => h⟩
  · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
    exact (Spike.Lib.A64.AllocG.not_ab_after hpc hnx hAb).elim
  · rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
      rw [Kraken.Promising.Lower.A64.exec_svc hc] at h <;> cases h

/-! ## Blocks with a `ret` or an abort call -/

/-- **A covered block's states keep the write abort's phase**, a `ret`
allowed: as `blkW_abSt_pos`, every `ret` returning to `ra` (`hret`), every
target off the write abort's pcs or the abort's entry called at `x0 ≠ 4`
(`htgt`), the last instruction's the block run's end. -/
theorem blkW_abSt_tg {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k] = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a,
        (k + 1 = blk.length → t = (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc) →
        t ∉ Spike.Lib.A64.WriteAb.abPcs lab ∨
          (a = .bl "scc_rt_abort" ∧
            (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  obtain ⟨hlays, -, rfl, -, hoff⟩ := hI
  refine Spike.Lib.A64ConsumerA.blkW_abSt hcode hok hR hal hlo hhi (fun k hk s _ _ hs => (hoff s ?_).1) ?_
  · have := List.all_eq_true.mp hph k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at this
    show okPc s.st.2.toBitVec.toNat = true
    rw [hs]
    exact this.1.1
  · intro σ c hJ k hk a ha s' _ _ hpc' hA
    have hmem := aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (fall := n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (ra := ra)
      (σ := (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      (fun r hr => hret σ c hJ k hk r (hr ▸ ha))
    have hd : k + 1 = blk.length → a.tgt (_root_.Executable.labels exe).label
        (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ =
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc := fun he => by
      have hrun := arun_take_succ (_root_.Executable.labels exe).label hk ⟨n.pc, n.o, σ⟩
      rw [he, List.take_length] at hrun
      have hpk := arun_pc (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
      rw [hrun]
      simp only [dstep, ha, hpk]
    rcases htgt σ c hJ k hk a ha _ hmem hd with hp | ⟨rfl, hx⟩
    · exact Spike.Lib.A64.WriteAb.not_ab_of_pc (hpc' ▸ hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_bl_X0]
      exact hx

/-- **`blkW_abSt_tg`'s targets from the block's place**: at a block of the
run of a label `l` off the write abort's, the fall-through positions (the
one after the block when its last instruction falls through, `hnext`) and
its branch labels but the abort's entry (`hlabs`) positions off the write
abort, or the block's run ending at such a position (a branch is the
block's last instruction, its target or fall-through the run's end),
its `ret`'s return address off the write abort's pcs (`hra`, needed only
with a `ret`), the abort's entry only called (`bl`), at `x0 ≠ 4`
(`habt`). -/
theorem htgt_offR {kp : Nat} (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {n : ND} {blk : List Directive} {l : Label} {k : Nat}
    {ra : Int64} {lo hi : Int} (hb : blockAt prog l k blk = true)
    (hok : okBlk lo hi n.o blk = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc) (hl : l ∉ abLabs)
    (hnext : lastFalls blk = true → PosOff prog (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * (k + blk.length))) ∨
        ∀ σ c, n.J σ c → PosOff prog (_root_.Executable.labels exe).label
          (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hlabs : ∀ L ∈ blkLabs blk, L ≠ "scc_rt_abort" →
      PosOff prog (_root_.Executable.labels exe).label ((_root_.Executable.labels exe).label L) ∨
        ∀ σ c, n.J σ c → PosOff prog (_root_.Executable.labels exe).label
          (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hra : noRetBlk blk = false → ra ∉ Spike.Lib.A64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (habt : ∀ σ c, n.J σ c → ∀ k' (hk : k' < blk.length) a, classify blk[k'] = some a →
      aiLab a = some "scc_rt_abort" → a = .bl "scc_rt_abort" ∧
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k') ⟨n.pc, n.o, σ⟩).σ.regs.X0
          ≠ 4) :
    ∀ σ c, n.J σ c → ∀ k' (hk : k' < blk.length) a, classify blk[k'] = some a →
      ∀ t ∈ aiTgts (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k') + Int64.ofNat 4) ra a,
        (k' + 1 = blk.length → t = (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label blk
          ⟨n.pc, n.o, σ⟩).pc) →
        t ∉ Spike.Lib.A64.WriteAb.abPcs (_root_.Executable.labels exe).label ∨
          (a = .bl "scc_rt_abort" ∧
            (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k') ⟨n.pc, n.o, σ⟩).σ.regs.X0
              ≠ 4) := by
  intro σ c hJ k' hk a ha t ht hdt
  by_cases hr : ∃ r, a = .ret r
  · obtain ⟨r, rfl⟩ := hr
    left
    simp only [aiTgts, List.mem_singleton] at ht
    cases hnr : noRetBlk blk
    · exact ht ▸ hra hnr
    · exact (noRet_false hnr k' hk r ha).elim
  · have hr' : ∀ r, a ≠ .ret r := fun r h => hr ⟨r, h⟩
    rcases aiTgts_cases hr' ht with ⟨rfl, hf⟩ | ⟨L, hL, rfl⟩
    · left
      by_cases hlt : k' + 1 < blk.length
      · refine notAbPc_of_posOff hp hpr hab ?_
        rw [← he, ofNat4_succ', ← ofNat4_add]
        exact ⟨l, k + (k' + 1), inRun_of_blockAt hb hlt, hl, rfl⟩
      · have hk1 : k' = blk.length - 1 := by omega
        have hlast : blk.getLast? = some blk[k'] := by
          rw [List.getLast?_eq_getElem?]; simp [hk1]
        rcases hnext (by simp only [lastFalls, hlast, ha, Option.map_some, Option.getD_some, hf]) with hn' | hend
        · refine notAbPc_of_posOff hp hpr hab ?_
          rw [← he, ofNat4_succ', ← ofNat4_add]
          rwa [show k + (k' + 1) = k + blk.length by omega]
        · exact hdt (by omega) ▸ notAbPc_of_posOff hp hpr hab (hend σ c hJ)
    · have hmem : L ∈ blkLabs blk := List.mem_filterMap.mpr ⟨blk[k'], List.getElem_mem hk, by
        simp only [ha, Option.bind_some]; exact hL⟩
      by_cases hab' : L = "scc_rt_abort"
      · exact .inr (habt σ c hJ k' hk a ha (hab' ▸ hL))
      · -- a branch is the block's last instruction
        obtain ⟨a', ha', -, hterm⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
        rw [ha] at ha'
        cases ha'
        have hlast : k' + 1 = blk.length := by
          refine Classical.byContradiction fun hne => ?_
          have := hterm (by omega)
          cases a <;> simp_all [aiLab, AI.isTerm]
        rcases hlabs L hmem hab' with hL' | hend
        · exact .inl (notAbPc_of_posOff hp hpr hab hL')
        · exact .inl (hdt hlast ▸ notAbPc_of_posOff hp hpr hab (hend σ c hJ))

/-- **A covered runtime block inside `RtX`**, a `ret` and abort calls
allowed: as `blkW_rtX`, every `ret` returning to `ra` (`hret`) off the write
abort's pcs (`hra`), the abort's entry only called, at `x0 ≠ 4` (`habt`),
a branch label, and the position after a last instruction falling through,
positioned off the write abort or the block's run ending at such a position
(`hlabs`, `hnext`). -/
theorem blkW_rtXG {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hl : l ∉ abLabs)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hra : noRetBlk blk = false → ra ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hnext : lastFalls blk = true → PosOff prog lab (lab l + Int64.ofNat (4 * (k + blk.length))) ∨
      ∀ σ c, n.J σ c → PosOff prog lab (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (hlabs : ∀ L ∈ blkLabs blk, L ≠ "scc_rt_abort" → PosOff prog lab (lab L) ∨
      ∀ σ c, n.J σ c → PosOff prog lab (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (habt : ∀ σ c, n.J σ c → ∀ k' (hk : k' < blk.length) a, classify blk[k'] = some a →
      aiLab a = some "scc_rt_abort" → a = .bl "scc_rt_abort" ∧
        (Spike.Lib.A64.Flow.arun lab (blk.take k') ⟨n.pc, n.o, σ⟩).σ.regs.X0 ≠ 4)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    BlkW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n blk := by
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  have hW := Spike.Lib.A64.AllocG.blkW_noWr hI hb he hok hR hal hlo hhi (F := F)
  have hlays := hI.lays
  have hA : BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
    obtain ⟨-, -, hlab, -, -⟩ := id hI
    subst hlab
    exact blkW_abSt_tg hI hpr hab hcode hok hR hal hlo hhi hph hret
      (htgt_offR hlays hpr hab hb hok he hl hnext hlabs hra habt)
  intro s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h1 := hA s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h2 := hW s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-! ## Loads, swaps and release stores -/

/-- **A runtime node at a load** `ldr Xt, [Xn, #i]` of a word unmapped in
private memory (`ha`) inside `RtX`: as `nodeW_rtX_si`; a load writes
nothing. -/
theorem nodeW_rtX_ldr {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {i : Int64} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldrDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
  have hex := Kraken.Promising.Lower.A64.exec_ldr_agrees hc ha' (ha σ c s.st.1 hJ hD)
    (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h))
    fun tr ht => ?_, hpl0 _, fun L hL => (noWr_load hex L hL).elim, rfl⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => Spike.Lib.A64.AllocG.not_ab_after hpc hnx

/-- **A runtime node at a swap** `swp Xs, Xt, [Xn]` of a word unmapped in
private memory (`ha`) inside `RtX`: as `nodeW_rtX_ldop`. -/
theorem nodeW_rtX_swp {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k
      [.instr ⟨.W64, .SWP kk .W64 (.low (.reg rs) .W64) (.low (.reg rt) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧
        (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
  have hex := Kraken.Promising.Lower.A64.exec_swp hc (by rw [ha']; exact ha σ c s.st.1 hJ hD)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h))
    fun tr ht => ?_, hpl0 _, fun L hL => ?_, rfl⟩, fun _ h => h⟩
  · rw [hex] at ht
    cases ht
    unfold EvTree.access
    split
    · exact fun _ _ => ⟨fun _ _ => trivial, Spike.Lib.A64.AllocG.not_ab_after hpc hnx⟩
    · trivial
  · rw [hdc, ha'] at hex
    exact (wrAt_rmw hex hL) ▸ hoff σ _ hJ

/-- **A runtime node at a release store** `stlr Xt, [Xn]` of a word
unmapped in private memory (`ha`) inside `RtX`: as `nodeW_rtX_st`. -/
theorem nodeW_rtX_stlr {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [.instr ⟨.W64, .STLR .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨(σ.regs.getXReg b).toBitVec, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (σ.regs.getXReg b).toBitVec.toNat ∧
        (σ.regs.getXReg b).toBitVec.toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
  have hex := Kraken.Promising.Lower.A64.exec_stlr_agrees hc (by rw [ha']; exact ha σ c s.st.1 hJ hD)
    (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
  rw [ha'] at hex
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h))
    fun tr ht => ?_, hpl0 _, fun L hL => (wrAt_store hex hL) ▸ hoff σ _ hJ, rfl⟩,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact ⟨trivial, fun _ _ => Spike.Lib.A64.AllocG.not_ab_after hpc hnx⟩

/-- **The take site inside `RtX`**: a `nop` (at the marks' take site or
not), its next pc off the write abort's pcs; the take lands there too, and
a `nop` writes nothing. -/
theorem site_rtX {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {k : Nat} {p : Int64} (hb : blockAt prog l k [.instr ⟨.W64, .NOP⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    ∀ s c, At exe endPc R F n s c → RtX Λ μ ar lbl lab c0 s c := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hex := Kraken.Promising.Lower.A64.exec_nop hc
  have hsys : abi.atSys s = false := atSvc_false_of_cellAt hc (by intro imm h; cases h)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h), fun _ a _ _ m => ?_⟩, hpl0 _,
    fun L hL => (noWr_done hex L hL).elim, rfl⟩
  · rw [hex] at ht
    cases ht
    exact Spike.Lib.A64.AllocG.not_ab_after hpc hnx
  · have hc' : Kraken.Promising.Lower.A64.CellAt (abi.setDmem s m) (.instr ⟨.W64, .NOP⟩) 4 :=
      ⟨hc.valid, hc.ne, hc.code⟩
    rw [Scc.Sem.A64.abi_skip_of_cellAt hc']
    exact Spike.Lib.A64.AllocG.not_ab_after (s := abi.setDmem s m) hpc hnx

/-- **A runtime node at a register operation inside `RtX`** (`RegOnly`, as
`add sp, x9, #0`): as `nodeW_rtX_si`. -/
theorem nodeW_rtX_reg {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {w : RegWidth}
    {op : Operation w} {l : Label} {k : Nat} {p : Int64} (hop : RegOnly op = true)
    (hb : blockAt prog l k [.instr ⟨w, op⟩] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hex := exec_reg hop hc
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc fun imm h => by cases h; simp [RegOnly] at hop)
    fun t ht => ?_, hpl0 _, fun L hL => (noWr_done hex L hL).elim, rfl⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact Spike.Lib.A64.AllocG.not_ab_after hpc hnx

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.blkW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtX

/-- info: 'Spike.Lib.LowerA64.site_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms site_rtX

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_reg

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_ldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_ldr

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_swp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_swp

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_stlr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_stlr

/-- info: 'Spike.Lib.LowerA64.blkW_abSt_tg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_tg

/-- info: 'Spike.Lib.LowerA64.htgt_offR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htgt_offR

/-- info: 'Spike.Lib.LowerA64.blkW_rtXG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtXG

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_svc

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_si' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_si

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_st

/-- info: 'Spike.Lib.LowerA64.nodeW_rtX_ldop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_ldop

/-- info: 'Spike.Lib.LowerA64.rtX_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtX_w2

end Spike.Lib.LowerA64
