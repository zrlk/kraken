/-
**The runtime's own states' remaining `W2` facts** (x86-64; the twin of
`Spike/Lib/LowerA64/RtStartX.lean`): the world `RtX` of the facts `W2`
asks at a runtime state beyond the phase table's `SFacts`
(`Spike/Lib/LowerX64/RtW2.lean`): the write abort's phase kept (`AbSt` at
`WriteAb.Ab lab`), the source start's control `c0` placed at no frame, no
write to the arena's heap nor its counter (`WrOff`), and the control `c0`
itself; and its producers at the runtime's covered blocks.

A covered block's instructions are silent (`AllocG.blkW_noWr`), so `WrOff`
holds; its targets are positions of runs of labels off the write abort's
(`PosOff`, `blkW_abSt_pos`): the fall-through positions of its own run, and
its branch labels' (`htgt_posOff`). Positions are byte offsets
(`cellOff`).

- `aiFalls`, `lastFalls`: a covered instruction falls through; a block's
  last instruction does (the branch labels: `aiLab`, `blkLabs`,
  `Spike/Lib/LowerX64/PhCheck.lean`);
- `aiTgts_cases`: a target of a non-`ret` instruction is its fall-through
  or one of its labels;
- `htgt_posOff`: `blkW_abSt_pos`'s targets at a block of a run of a label
  off the write abort's, the position after it off the write abort when its
  last instruction falls through, its branch labels positions off the write
  abort;
- `RtX`, `rtX_w2`: the world, and `W2` from `SFacts` at `c0` and `RtX`;
- `blkW_rtX`: a covered block inside `RtX`;
- `nodeW_rtX_si`, `nodeW_rtX_fi`, `nodeW_rtX_st`, `nodeW_rtX_xadd`,
  `nodeW_rtX_sys`: single-instruction runtime nodes inside `RtX`;
- `blkW_abSt_tg`, `htgt_offR`, `blkW_rtXG`: a covered block with a `ret`
  (to a return address off the write abort's pcs) or calls of the abort's
  entry (at `%rdi ≠ 4`) inside `RtX`;
- `nodeW_rtX_ld`, `nodeW_rtX_xchg`, `site_rtX`: a load, an exchange and the
  take site's `nop` inside `RtX`;
- `nodeW_rtX_and`, `nodeW_rtX_reg`: `andq $k, %rsp` and a register
  operation (the switch) inside `RtX`;
- `RtM`, `rtX_iff`, `RtX.toM`: the world inside `scc_rt_main` (`RtX`
  without the control's facts);
- `blkW_rtMG`, `nodeW_rtM_fs`, `nodeW_rtM_sys`, `nodeW_rtM_exit`: a
  covered block, a thread-pointer load, a `syscall` and an `exit_group`
  inside `RtM`.
-/
import Spike.Lib.LowerX64.RtW2
import Spike.Lib.LowerX64.StubAbW2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At AI okBlk arun classify cellOff)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.X64.AllocG (abLabs)
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Scc.Cert.Rt.X64 (blockAtB)

/-! ## A block's targets -/

/-- A covered instruction falls through (neither `jmp`, `call` nor `ret`). -/
def aiFalls : AI → Bool
  | .jmp _ | .call _ | .ret => false
  | _ => true

/-- A block's last instruction falls through. -/
def lastFalls (blk : List (Directive × Nat)) : Bool :=
  match blk.getLast? with
  | some dz => ((classify dz.1).map aiFalls).getD false
  | none => false

/-- **A target of a non-`ret` instruction** is its fall-through (when it
falls through) or one of its labels. -/
theorem aiTgts_cases {lab : Label → Int64} {fall ra t : Int64} {a : AI} (hr : a ≠ .ret)
    (ht : t ∈ aiTgts lab fall ra a) : (t = fall ∧ aiFalls a = true) ∨ ∃ L, aiLab a = some L ∧ t = lab L := by
  cases a <;> simp_all [aiTgts, aiFalls, aiLab] <;> exact ht.symm

/-- **A block's targets are positions off the write abort** (`blkW_abSt_pos`'s
`htgt`): at a block of the run of a label `l` off the write abort's, with no
`ret`, the position after it off the write abort when its last instruction
falls through (`hnext`), and its branch labels positions off the write abort
(`hlabs`). -/
theorem htgt_posOff {cells : List (Directive × Nat)} {lab : Label → Int64} {n : ND}
    {blk : List (Directive × Nat)} {l : Label} {off : Nat} {ra : Int64} (hb : blockAtB cells l off blk = true)
    (he : lab l + Int64.ofNat off = n.pc) (hl : l ∉ abLabs) (hnr : noRetBlk blk = true)
    (hnext : lastFalls blk = true → PosOff cells lab (lab l + Int64.ofNat (off + cellOff blk blk.length)))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff cells lab (lab L)) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        PosOff cells lab t ∨
          (a = .call "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64) := by
  intro σ c _ k hk a ha t ht
  left
  rcases aiTgts_cases (fun hr => noRet_false hnr k hk (hr ▸ ha)) ht with ⟨rfl, hf⟩ | ⟨L, hL, rfl⟩
  · have hpos : n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
        lab l + Int64.ofNat (off + cellOff blk (k + 1)) := by
      rw [← he, cellOff_succ hk, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc]
    rw [hpos]
    by_cases hlt : k + 1 < blk.length
    · exact ⟨l, off + cellOff blk (k + 1), inRunB_of_blockAtB hb hlt, hl, rfl⟩
    · have hk1 : k = blk.length - 1 := by omega
      have hlast : blk.getLast? = some blk[k] := by
        rw [List.getLast?_eq_getElem?]; simp [hk1]
      have := hnext (by simp only [lastFalls, hlast, ha, Option.map_some, Option.getD_some, hf])
      rwa [show k + 1 = blk.length by omega]
  · refine hlabs L (List.mem_filterMap.mpr ⟨blk[k], List.getElem_mem hk, ?_⟩)
    simp only [ha, Option.bind_some]
    exact hL

/-! ## The world -/

/-- **The runtime's remaining facts at a state**: the write abort's phase
kept, the control placed at no frame, no write to the arena's heap nor its
counter, the control the source start's `c0`. -/
def RtX (Λ : Scc.Sem.Layout) (μ : Marks) (ar : Arena) (lbl : Lbl) (lab : Label → Int64) (c0 : Ctl) :
    Frag isa := fun s c =>
  AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c [] ∧ WrOff ar s ∧ c = c0

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {lab : Label → Int64} {c0 : Ctl}

/-- **`W2` at a runtime state at no frame**: `SFacts` at the source start's
control `c0` (`X64Consumer.c0`, free of `ZBad`) and `RtX`. -/
theorem rtX_w2 (hp : ProgNoS ZBad p) (hf0 : FrOk2 X64Consumer.c0 []) {s : State} {c : Ctl}
    (hS : SFacts Λ μ own rS Tk lbl0 s X64Consumer.c0) (hX : RtX Λ μ ar lbl lab X64Consumer.c0 s c) :
    W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c [] := by
  obtain ⟨hab, hpl, hwr, rfl⟩ := hX
  exact w2_of_parts hp hS (w2Part_of_wrOff hab hpl hwr hS) (fun _ => hS.noRet) hf0

/-! ## Covered blocks -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat}
  {R : Region} {F : MachineData → Prop}

/-- **A covered runtime block inside `RtX`**: a block of the code (`hb`,
`he`) covered at its node's offsets (`hok`) passing its phase check
(`hph`), with no `ret`, in the run of a label off the write abort's, the
position after it off the write abort when its last instruction falls
through (`hnext`), its branch labels positions off the write abort
(`hlabs`), at a node whose controls are `c0` (`hc0`), placed at no frame
(`hpl0`), in a layout of cells with the runtime's code (`hI`, `hpr`,
`hab`). -/
theorem blkW_rtX {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hnr : noRetBlk blk = true) (hl : l ∉ abLabs)
    (hnext : lastFalls blk = true → PosOff cells lab (lab l + Int64.ofNat (off + cellOff blk blk.length)))
    (hlabs : ∀ L ∈ blkLabs blk, PosOff cells lab (lab L))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    BlkW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  have hA := blkW_abSt_pos hI hpr hab (F := F) (dead := dead) (ra := ra) hcode hok hR hlo hhi hph hnr
    (htgt_posOff hb he hl hnr hnext hlabs)
  have hW := Spike.Lib.X64.AllocG.blkW_noWr hI hb he hok hR hlo hhi (F := F)
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
theorem nodeW_rtX_si {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.X64.SI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(si.toDir, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.X64.AllocG.nodeW_ab_si hI hb he hp hok hnx s c hA
  have h2 := Spike.Lib.X64.AllocG.nodeW_noWr_si hI hb he hp s c hA
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-- **A runtime node at an instruction with undefined flags inside `RtX`**
(`nodeW_ab_fi`, `nodeW_noWr_fi`): as `nodeW_rtX_si`. -/
theorem nodeW_rtX_fi {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {fi : Spike.Lib.X64.FI} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(fi.toDir, z)] = true) (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hok : okPc p.toBitVec.toNat = true) (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.X64.AllocG.nodeW_ab_fi hI hb he hp hok hnx s c hA
  have h2 := Spike.Lib.X64.AllocG.nodeW_noWr_fi hI hb he hp s c hA
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-- **A runtime node at a store inside `RtX`** (`nodeW_ab_st`,
`nodeW_wr_st`): as `nodeW_rtX_si`, the stored word unmapped in private
memory (`ha`), off the arena's counter and heap (`hoff`). -/
theorem nodeW_rtX_st {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {i : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.stDir b i r, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.X64.bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨Spike.Lib.X64.bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (Spike.Lib.X64.bAddr σ.regs b i).toNat ∧
        (Spike.Lib.X64.bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.X64.AllocG.nodeW_ab_st hI hb he hp hok hnx ha s c hA
  obtain ⟨⟨σ, hJ, -, hw⟩, -⟩ := Spike.Lib.X64.AllocG.nodeW_wr_st hI hb he hp ha s c hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => hw L hL ▸ hoff σ _ hJ, rfl⟩, fun _ h => h⟩

/-- **A runtime node at a `lock xaddq` inside `RtX`** (`nodeW_ab_xadd`,
`nodeW_wr_xadd`): as `nodeW_rtX_st`. -/
theorem nodeW_rtX_xadd {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {i : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.xaddDir b i r, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.X64.bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨Spike.Lib.X64.bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (Spike.Lib.X64.bAddr σ.regs b i).toNat ∧
        (Spike.Lib.X64.bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := Spike.Lib.X64.AllocG.nodeW_ab_xadd hI hb he hp hok hnx ha s c hA
  obtain ⟨⟨σ, hJ, -, hw⟩, -⟩ := Spike.Lib.X64.AllocG.nodeW_wr_xadd hI hb he hp ha s c hA
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => hw L hL ▸ hoff σ _ hJ, rfl⟩, fun _ h => h⟩

/-- **A runtime node at `syscall` inside `RtX`** (`nodeW_ab_sys`): as
`nodeW_rtX_si`, the system call's returns at the next pc, off the write
abort's pcs; the instruction itself (a fault to the kernel) writes
nothing. -/
theorem nodeW_rtX_sys {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, 2)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 2 ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := nodeW_ab_sys hI hb he hp hok hnx s c hA
  obtain ⟨hs, hn, -, hpc, σ, -, -, hJ⟩ := hA
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨h1.1, hpl0 _, fun L hL => ?_, rfl⟩, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
    rw [Kraken.Promising.Lower.X64.exec_syscall hc] at h <;> cases h

/-! ## Blocks with a `ret` or an abort call -/

/-- **A covered block's states keep the write abort's phase**, a `ret`
allowed: as `blkW_abSt_pos`, every `ret` returning to `ra` (`hret`), every
target off the write abort's pcs or the abort's entry called at
`%rdi ≠ 4` (`htgt`). -/
theorem blkW_abSt_tg {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts lab (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        (k + 1 = blk.length → t = (arun lab blk ⟨n.pc, n.o, σ⟩).pc) →
        t ∉ Spike.Lib.X64.WriteAb.abPcs lab ∨
          (a = .call "scc_rt_abort" ∧ (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  obtain ⟨hlays, -, rfl, -, hoff⟩ := hI
  refine blkW_abSt hcode hok hR hlo hhi (fun k hk s _ _ hs => (hoff s ?_).1) ?_
  · have := List.all_eq_true.mp hph k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true] at this
    show okPc s.st.2.toBitVec.toNat = true
    rw [hs]
    exact this.1.1
  · intro σ c hJ k hk a ha s' _ _ hpc' hA
    have hmem := aiTgt_mem (lab := (_root_.Executable.labels exe).label)
      (o := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so)
      (fall := n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (ra := ra)
      (σ := (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) a
      (fun hr => hret σ c hJ k hk (hr ▸ ha))
    have hd : k + 1 = blk.length → a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ =
        (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc := fun he => by
      have hrun := Spike.Lib.X64.arun_take_succ (_root_.Executable.labels exe).label hk ⟨n.pc, n.o, σ⟩
      rw [he, List.take_length] at hrun
      have hpk := Spike.Lib.X64.arun_pc (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
      rw [hrun]
      simp only [Spike.Lib.X64.dstep, ha, hpk]
    rcases htgt σ c hJ k hk a ha _ hmem hd with hp | ⟨rfl, hx⟩
    · exact Spike.Lib.X64.WriteAb.not_ab_of_pc (hpc' ▸ hp)
    · refine not_ab_abortEntry hlays hpr hab hpc' ?_
      rw [hA.regs, step_call_rdi]
      exact hx

/-- **`blkW_abSt_tg`'s targets from the block's place**: at a block of the
run of a label `l` off the write abort's, the fall-through positions (the
one after the block when its last instruction falls through, `hnext`) and
its branch labels but the abort's entry (`hlabs`) positions off the write
abort, or the block's run ending at such a position (a branch is the
block's last instruction, its target or fall-through the run's end), its
`ret`'s return address off the write abort's pcs (`hra`, needed only with a `ret`), the
abort's entry only called, at `%rdi ≠ 4` (`habt`). -/
theorem htgt_offR {kp : Nat} (hp : Scc.Cert.Rt.X64.Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {l : Label} {off : Nat} {ra : Int64} {lo hi : Int}
    (hb : blockAtB cells l off blk = true) (hok : okBlk lo hi n.o blk = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat off = n.pc) (hl : l ∉ abLabs)
    (hnext : lastFalls blk = true → PosOff cells (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (off + cellOff blk blk.length)) ∨
        ∀ σ c, n.J σ c → PosOff cells (_root_.Executable.labels exe).label
          (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hlabs : ∀ L ∈ blkLabs blk, L ≠ "scc_rt_abort" →
      PosOff cells (_root_.Executable.labels exe).label ((_root_.Executable.labels exe).label L) ∨
        ∀ σ c, n.J σ c → PosOff cells (_root_.Executable.labels exe).label
          (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc)
    (hra : noRetBlk blk = false → ra ∉ Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label)
    (habt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      aiLab a = some "scc_rt_abort" → a = .call "scc_rt_abort" ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      ∀ t ∈ aiTgts (_root_.Executable.labels exe).label
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) ra a,
        (k + 1 = blk.length → t = (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
        t ∉ Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label ∨
          (a = .call "scc_rt_abort" ∧
            (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64) := by
  intro σ c hJ k hk a ha t ht hdt
  by_cases hr : a = .ret
  · subst hr
    left
    simp only [aiTgts, List.mem_singleton] at ht
    cases hnr : noRetBlk blk
    · exact ht ▸ hra hnr
    · exact (noRet_false hnr k hk ha).elim
  · rcases aiTgts_cases hr ht with ⟨rfl, hf⟩ | ⟨L, hL, rfl⟩
    · left
      have hpos : n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
          (_root_.Executable.labels exe).label l + Int64.ofNat (off + cellOff blk (k + 1)) := by
        rw [← he, cellOff_succ hk, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc]
      by_cases hlt : k + 1 < blk.length
      · refine notAbPc_of_posOff hp hpr hab ?_
        rw [hpos]
        exact ⟨l, off + cellOff blk (k + 1), inRunB_of_blockAtB hb hlt, hl, rfl⟩
      · have hk1 : k = blk.length - 1 := by omega
        have hlast : blk.getLast? = some blk[k] := by
          rw [List.getLast?_eq_getElem?]; simp [hk1]
        rcases hnext (by simp only [lastFalls, hlast, ha, Option.map_some, Option.getD_some, hf]) with hn' | hend
        · refine notAbPc_of_posOff hp hpr hab ?_
          rw [hpos]
          rwa [show k + 1 = blk.length by omega]
        · exact hdt (by omega) ▸ notAbPc_of_posOff hp hpr hab (hend σ c hJ)
    · have hmem : L ∈ blkLabs blk := List.mem_filterMap.mpr ⟨blk[k], List.getElem_mem hk, by
        simp only [ha, Option.bind_some]; exact hL⟩
      by_cases hab' : L = "scc_rt_abort"
      · exact .inr (habt σ c hJ k hk a ha (hab' ▸ hL))
      · -- a branch is the block's last instruction
        obtain ⟨a', ha', -, hterm⟩ :=
          Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
        rw [ha] at ha'
        cases ha'
        have hlast : k + 1 = blk.length := by
          refine Classical.byContradiction fun hne => ?_
          have := hterm (by omega)
          cases a <;> simp_all [aiLab, Spike.Lib.X64.AI.isTerm]
        rcases hlabs L hmem hab' with hL' | hend
        · exact .inl (notAbPc_of_posOff hp hpr hab hL')
        · exact .inl (hdt hlast ▸ notAbPc_of_posOff hp hpr hab (hend σ c hJ))

/-- **A covered runtime block inside `RtX`**, a `ret` and abort calls
allowed: as `blkW_rtX`, every `ret` returning to `ra` (`hret`) off the write
abort's pcs (`hra`), the abort's entry only called, at `%rdi ≠ 4`
(`habt`), a branch label, and the position after a last instruction falling
through, positioned off the write abort or the block's run ending at such a
position (`hlabs`, `hnext`). -/
theorem blkW_rtXG {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hl : l ∉ abLabs)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hra : noRetBlk blk = false → ra ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hnext : lastFalls blk = true → PosOff cells lab (lab l + Int64.ofNat (off + cellOff blk blk.length)) ∨
      ∀ σ c, n.J σ c → PosOff cells lab (arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (hlabs : ∀ L ∈ blkLabs blk, L ≠ "scc_rt_abort" → PosOff cells lab (lab L) ∨
      ∀ σ c, n.J σ c → PosOff cells lab (arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (habt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      aiLab a = some "scc_rt_abort" → a = .call "scc_rt_abort" ∧
        (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    BlkW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  have hW := Spike.Lib.X64.AllocG.blkW_noWr hI hb he hok hR hlo hhi (F := F)
  have hlays := hI.lays
  have hA : BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
    obtain ⟨-, -, hlab, -, -⟩ := id hI
    subst hlab
    exact blkW_abSt_tg hI hpr hab hcode hok hR hlo hhi hph hret
      (htgt_offR hlays hpr hab hb hok he hl hnext hlabs hra habt)
  intro s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h1 := hA s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h2 := hW s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  obtain rfl := hc0 σ c hJ
  exact ⟨⟨h1.1, hpl0 _, fun L hL => (h2.1 L hL).elim, rfl⟩, fun _ h => h⟩

/-! ## Loads, exchanges and the take site -/

/-- **A runtime node at a load** `movq k(%b), %r` of a word unmapped in
private memory (`ha`) inside `RtX`: as `nodeW_rtX_si`; a load writes
nothing. -/
theorem nodeW_rtX_ld {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {i : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.ldDir b i r, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.X64.bAddr σ.regs b i) 8 = none)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have ha' : Kraken.Promising.Lower.X64.eaddr s z (Spike.Lib.X64.mB b i) = Spike.Lib.X64.bAddr σ.regs b i :=
    (Spike.Lib.X64.eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  have hex := Kraken.Promising.Lower.X64.exec_load_agrees hc ha' (ha σ c s.st.1 hJ hD)
    (Spike.Lib.X64.agrees_of_decls hdc _ _)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    hpl0 _, fun L hL => (noWr_load hex L hL).elim, rfl⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => Spike.Lib.X64.AllocG.not_ab_after hpc hnx

/-- **A runtime node at an exchange** `xchgq %r, k(%b)` of a word unmapped
in private memory (`ha`) inside `RtX`: as `nodeW_rtX_xadd`. -/
theorem nodeW_rtX_xchg {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {i : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.xchgDir b i r, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.X64.bAddr σ.regs b i) 8 = none)
    (hoff : ∀ σ c, n.J σ c → (⟨Spike.Lib.X64.bAddr σ.regs b i, 8⟩ : Loc) ≠ ar.ctrLoc ∧
      ¬ (ar.heap ≤ (Spike.Lib.X64.bAddr σ.regs b i).toNat ∧
        (Spike.Lib.X64.bAddr σ.regs b i).toNat < ar.heap + 16 * ar.cells))
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have ha' : Kraken.Promising.Lower.X64.eaddr s z (Spike.Lib.X64.mB b i) = Spike.Lib.X64.bAddr σ.regs b i :=
    (Spike.Lib.X64.eaddr_mB s z b i).trans (by rw [hA.regs]; rfl)
  have hex := Kraken.Promising.Lower.X64.exec_xchgG_agrees (w := .W64) hc ha' (ha σ c s.st.1 hJ hD)
    (Spike.Lib.X64.agrees_of_decls hdc _ _)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    hpl0 _, fun L hL => (wrAt_rmw hex hL) ▸ hoff σ _ hJ, rfl⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => ⟨fun _ _ => trivial, Spike.Lib.X64.AllocG.not_ab_after hpc hnx⟩

/-- **The take site inside `RtX`**: a `nop` (at the marks' take site or
not), its next pc off the write abort's pcs; the take lands there too, and
a `nop` writes nothing. -/
theorem site_rtX {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 (.nop 1), 1)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (hnx : p + Int64.ofNat 1 ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    ∀ s c, At exe endPc R F n s c → RtX Λ μ ar lbl lab c0 s c := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hex := Kraken.Promising.Lower.X64.exec_nop hc
  have hsys : abi.atSys s = false := atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨fun _ _ tr ht => ?_, fun _ h => (by rw [hsys] at h; cases h), fun _ a _ _ m => ?_⟩, hpl0 _,
    fun L hL => (noWr_done hex L hL).elim, rfl⟩
  · rw [hex] at ht
    cases ht
    exact Spike.Lib.X64.AllocG.not_ab_after hpc hnx
  · have hc' : Kraken.Promising.Lower.X64.CellAt (abi.setDmem s m) (Kraken.Promising.Lower.X64.op64 (.nop 1)) 1 :=
      ⟨hc.valid, hc.ne, hc.code⟩
    rw [Scc.Sem.X64.abi_skip_of_cellAt hc']
    exact Spike.Lib.X64.AllocG.not_ab_after (s := abi.setDmem s m) hpc hnx

/-- **A runtime node at `andq $k, %rsp` inside `RtX`** (`_start`'s
alignment): as `nodeW_rtX_fi`; its tree is silent (`exec_andRsp`). -/
theorem nodeW_rtX_and {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.andRsp k, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  obtain ⟨t0, hex, hst⟩ := Spike.Lib.X64.exec_andRsp hc
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    hpl0 _, fun L hL => ?_, rfl⟩, fun _ h => h⟩
  · rw [hex] at ht
    cases ht
    exact (silent_facts (p := fun _ _ => True) (G := fun _ _ => True) (G' := fun _ _ => True)
      (fun _ ⟨_, h⟩ => h ▸ Spike.Lib.X64.AllocG.not_ab_after hpc hnx) hst).2.1
  · exfalso
    rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hex] at h <;> cases h <;> exact hst.elim

/-- **A runtime node at a register operation inside `RtX`** (`RegOnly`;
the switch `movq %rax, %rsp`): as `nodeW_rtX_si`; its step is a leaf
(`exec_reg`). -/
theorem nodeW_rtX_reg {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {w : Width} {op : Operation w} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hop : Spike.Lib.X64.RegOnly op = true)
    (hb : blockAtB cells l off [(.instr (.regular .W64 w op), z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc0 : ∀ σ c, n.J σ c → c = c0) (hpl0 : ∀ s, PlacedS Λ lbl s c0 []) :
    NodeW (RtX Λ μ ar lbl lab c0) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, -, -, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hex := Spike.Lib.X64.exec_reg hop hc
  obtain rfl := hc0 σ c hJ
  refine ⟨⟨AbSt.ofLeaves hP.noTake
    (atSyscall_false_of_cellAt hc (fun w w' h => by cases h; simp [Spike.Lib.X64.RegOnly] at hop)) fun t ht => ?_,
    hpl0 _, fun L hL => (noWr_done hex L hL).elim, rfl⟩, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact Spike.Lib.X64.AllocG.not_ab_after hpc hnx

/-! ## `scc_rt_main`'s world -/

/-- **The runtime's remaining facts inside `scc_rt_main`**: `RtX` without
the control's facts (`scc_rt_main` runs at the source's controls after
`c0`, its frames placed): the write abort's phase kept and no write to the
arena's heap nor its counter. -/
def RtM (μ : Marks) (ar : Arena) (lab : Label → Int64) : Frag isa := fun s _ =>
  AbSt μ (Ab lab) s ∧ WrOff ar s

/-- `RtX` is `RtM` with the control `c0` placed at no frame. -/
theorem rtX_iff {s : State} {c : Ctl} :
    RtX Λ μ ar lbl lab c0 s c ↔ RtM μ ar lab s c ∧ PlacedS Λ lbl s c [] ∧ c = c0 :=
  ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h3⟩, h2, h4⟩, fun ⟨⟨h1, h3⟩, h2, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- `RtX` gives `RtM`. -/
theorem RtX.toM {s : State} {c : Ctl} (h : RtX Λ μ ar lbl lab c0 s c) : RtM μ ar lab s c :=
  (rtX_iff.mp h).1

/-- **A covered block inside `RtM`**: `blkW_rtXG` without the control's
facts. -/
theorem blkW_rtMG {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label}
    {off : Nat} (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true) (hl : l ∉ abLabs)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hra : noRetBlk blk = false → ra ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hnext : lastFalls blk = true → PosOff cells lab (lab l + Int64.ofNat (off + cellOff blk blk.length)) ∨
      ∀ σ c, n.J σ c → PosOff cells lab (arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (hlabs : ∀ L ∈ blkLabs blk, L ≠ "scc_rt_abort" → PosOff cells lab (lab L) ∨
      ∀ σ c, n.J σ c → PosOff cells lab (arun lab blk ⟨n.pc, n.o, σ⟩).pc)
    (habt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a →
      aiLab a = some "scc_rt_abort" → a = .call "scc_rt_abort" ∧
        (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64) :
    BlkW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn
  have hW := Spike.Lib.X64.AllocG.blkW_noWr hI hb he hok hR hlo hhi (F := F)
  have hlays := hI.lays
  have hA : BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
    obtain ⟨-, -, hlab, -, -⟩ := id hI
    subst hlab
    exact blkW_abSt_tg hI hpr hab hcode hok hR hlo hhi hph hret
      (htgt_offR hlays hpr hab hb hok he hl hnext hlabs hra habt)
  intro s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h1 := hA s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  have h2 := hW s σ c hs hn hd hpc hAb hF hJ k' hk m hA' hD
  exact ⟨⟨h1.1, fun L hL => (h2.1 L hL).elim⟩, fun _ h => h⟩

/-- **A thread-pointer load `movq %fs:k, %d` inside `RtM`**: its pc off the
sites, its next pc off the write abort's pcs; mapped in private memory or
not, a load writes nothing. -/
theorem nodeW_rtM_fs {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {d : Reg64} {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Spike.Lib.X64.fsDir d k, z)] = true) (he : lab l + Int64.ofNat off = p)
    (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab) :
    NodeW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hsys := atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  cases hm : Mem.loadInt s.st.1.dmem (Kraken.Promising.Lower.X64.fsAddr s z
    { base := none, idx := none, disp := .int64 k }) 8 with
  | none =>
    have hex := Kraken.Promising.Lower.X64.exec_movfs_load_agrees hc rfl hm
      (Spike.Lib.X64.agrees_of_decls hdc _ _)
    refine ⟨⟨AbSt.ofLeaves hP.noTake hsys fun t ht => ?_, fun L hL => (noWr_load hex L hL).elim⟩,
      fun _ h => h⟩
    rw [hex] at ht
    cases ht
    exact fun _ _ => Spike.Lib.X64.AllocG.not_ab_after hpc hnx
  | some j =>
    have hex := Kraken.Promising.Lower.X64.exec_movfs_load_mapped hc rfl hm
    refine ⟨⟨AbSt.ofLeaves hP.noTake hsys fun t ht => ?_, fun L hL => (noWr_done hex L hL).elim⟩,
      fun _ h => h⟩
    rw [hex] at ht
    cases ht
    exact Spike.Lib.X64.AllocG.not_ab_after hpc hnx

/-- **A `syscall` inside `RtM`** (`nodeW_ab_sys`): as `nodeW_rtX_sys`
without the control's facts. -/
theorem nodeW_rtM_sys {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, 2)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 2 ∉ Spike.Lib.X64.WriteAb.abPcs lab) :
    NodeW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  have h1 := nodeW_ab_sys hI hb he hp hok hnx s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := hA
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨h1.1, fun L hL => ?_⟩, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
    rw [Kraken.Promising.Lower.X64.exec_syscall hc] at h <;> cases h

/-- **An `exit_group` `syscall` inside `RtM`** (`nodeW_ab_exit`): at
`%rax = 231` (`hx`) the call resumes in no state; its pc off the sites. -/
theorem nodeW_rtM_exit {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {l : Label} {off : Nat} {p : Int64}
    (hb : blockAtB cells l off [(Kraken.Promising.Lower.X64.op64 .syscall, 2)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rax = 231#64) :
    NodeW (RtM μ ar lab) (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨hs, hn, -, hpc, -⟩ := id hA
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a := fun a ha h =>
    hP.noTake a ha (by unfold pcOf; rw [hpc]; exact h)
  have h1 := nodeW_ab_exit hI hb he hp htk hx s c hA
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨h1.1, fun L hL => ?_⟩, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;>
    rw [Kraken.Promising.Lower.X64.exec_syscall hc] at h <;> cases h

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.htgt_posOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htgt_posOff

/-- info: 'Spike.Lib.LowerX64.blkW_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtX

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_ld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_ld

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_xchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_xchg

/-- info: 'Spike.Lib.LowerX64.site_rtX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms site_rtX

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_and

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_reg

/-- info: 'Spike.Lib.LowerX64.blkW_rtMG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtMG

/-- info: 'Spike.Lib.LowerX64.nodeW_rtM_fs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtM_fs

/-- info: 'Spike.Lib.LowerX64.nodeW_rtM_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtM_sys

/-- info: 'Spike.Lib.LowerX64.nodeW_rtM_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtM_exit

/-- info: 'Spike.Lib.LowerX64.rtX_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtX_w2

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_si' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_si

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_fi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_fi

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_st

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_xadd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_xadd

/-- info: 'Spike.Lib.LowerX64.nodeW_rtX_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_rtX_sys

/-- info: 'Spike.Lib.LowerX64.blkW_abSt_tg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abSt_tg

/-- info: 'Spike.Lib.LowerX64.htgt_offR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htgt_offR

/-- info: 'Spike.Lib.LowerX64.blkW_rtXG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_rtXG

end Spike.Lib.LowerX64
