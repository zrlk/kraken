/-
**`scc_rt_alloc`'s node obligations at any instance** (x86-64): the
allocator's `AllocW` (`Spike/Lib/X64Alloc.lean`) inside the components of
`W0` (`Spike/Lib/X64W0G.lean`) for any executable laid out with labels
`lab` (`InstOk`) whose cells hold the allocator's code (`Alloc.allocIn`,
A7), no layout constant: `hello1.x`'s instances
(`Spike/Test/X64Hello1Alloc{Arena,Ctr}.lean`) with `hello1_instOk`'s facts
and the kernel's decisions at `labT` replaced by `InstOk` and `allocIn`.
The twin of `Spike/Lib/A64AllocG.lean`, name for name.

- `NodeW.imp`, `BlkW.imp`, `AllocW.imp`: two obligations into one
  (`Spike/Lib/X64Hello1WImp.lean`'s, here so the generic path imports no
  `hello1` module).
- `blkW_noWr`, `nodeW_noWr_si`, `nodeW_noWr_fi`, `nodeW_wr_st`,
  `nodeW_wr_xadd`, `arenaWr0_of_noWr`: `hello1.x`'s generic node lemmas
  (`Spike/Test/X64Hello1AllocArena.lean`; AArch64 has no `nodeW_noWr_fi`,
  and its RMW is `nodeW_wr_ldop`).
- `allocIn_spec`: `allocIn`'s facts.
- `hdr_addr`, `ctr_addr`: the header store's and the counter add's
  addresses at any labels.
- `allocArena`: every node allows `ArenaWr0` at every frame list.
- `allocCtr`: only the counter's add writes the counter.
-/
import Spike.Lib.X64W0G
import Spike.Lib.Rt.X64RtW
import Spike.Lib.LowerX64.NodeTp
import Spike.Lib.X64Alloc

namespace Spike.Lib.X64.AllocG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FrameRun FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND At SI FI bAddr xaddDir stDir mB eaddr_mB cellOff)
open Spike.Lib.X64.Rt (InstOk cellOf codeOf)
open Scc.Cert.Rt.X64 (blockAtB labelGapB)
open Kraken.Promising.Lower.X64 (CellAt exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (WrAt noWr_done wrAt_store wrAt_rmw)
open Spike.Lib.X64.W0G (ArenaWr0)

/-! ## Two node obligations into one -/

section Imp

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W1 W2 : Frag isa} {K : State → State → Prop}

/-- **A node inside `W`** from one inside `W1` not moved by `K` and one
inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem NodeW.imp {n : ND} (h1 : NodeW W1 K exe endPc R F n) (h2 : NodeW W2 (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : NodeW W K exe endPc R F n := fun s c hA =>
  ⟨hw s c (h1 s c hA).1 (h2 s c hA).1, (h1 s c hA).2⟩

/-- **A block node inside `W`** from one inside `W1` not moved by `K` and
one inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem BlkW.imp {n : ND} {blk : List (Directive × Nat)} (h1 : BlkW W1 K exe endPc R F n blk)
    (h2 : BlkW W2 (fun _ _ => False) exe endPc R F n blk) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    BlkW W K exe endPc R F n blk := fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
  ⟨hw _ c (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1 (h2 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
    (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

/-- **`scc_rt_alloc` inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem AllocW.imp {ms : MemSide isa} {q : Spike.Lib.X64.Alloc.Call}
    (h1 : Spike.Lib.X64.Alloc.AllocW ms q W1 K exe endPc R F)
    (h2 : Spike.Lib.X64.Alloc.AllocW ms q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Alloc.AllocW ms q W K exe endPc R F :=
  ⟨BlkW.imp h1.e h2.e hw, BlkW.imp h1.entry h2.entry hw, BlkW.imp h1.j1 h2.j1 hw, NodeW.imp h1.cnt h2.cnt hw,
    BlkW.imp h1.c1 h2.c1 hw, NodeW.imp h1.rmw h2.rmw hw, BlkW.imp h1.c2 h2.c2 hw, BlkW.imp h1.j2 h2.j2 hw,
    BlkW.imp h1.slow h2.slow hw, BlkW.imp h1.j3 h2.j3 hw, BlkW.imp h1.full h2.full hw, BlkW.imp h1.ok h2.ok hw,
    NodeW.imp h1.f1 h2.f1 hw, BlkW.imp h1.o1 h2.o1 hw, NodeW.imp h1.f2 h2.f2 hw, BlkW.imp h1.o2 h2.o2 hw,
    NodeW.imp h1.s2 h2.s2 hw, BlkW.imp h1.o3 h2.o3 hw, NodeW.imp h1.f3 h2.f3 hw, BlkW.imp h1.o4 h2.o4 hw,
    NodeW.imp h1.f4 h2.f4 hw, BlkW.imp h1.o5 h2.o5 hw, NodeW.imp h1.f5 h2.f5 hw, BlkW.imp h1.o6 h2.o6 hw,
    NodeW.imp h1.f6 h2.f6 hw, BlkW.imp h1.o7 h2.o7 hw, NodeW.imp h1.f7 h2.f7 hw, BlkW.imp h1.o8 h2.o8 hw,
    NodeW.imp h1.hdr h2.hdr hw, BlkW.imp h1.o9 h2.o9 hw, NodeW.imp h1.ret h2.ret hw⟩

end Imp

/-! ## Generic nodes' writes -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block's states write nothing**: every instruction of the
block is a silent step (`exec_ai`). -/
theorem blkW_noWr {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {off : Nat}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) :
    BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk := by
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  intro s σ c hs hn _ _ _ _ _ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s hs hn).cell hd rfl rfl rfl
  obtain ⟨m', hex, -⟩ := Spike.Lib.X64.exec_ai haok hR hlo hhi hc hreg hA'
  exact noWr_done hex

/-- **A single instruction without an event** (`SI`) writes nothing. -/
theorem nodeW_noWr_si {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  exact ⟨noWr_done (Spike.Lib.X64.exec_si (cellOf hI hb he hs hn hpc)), fun _ h => h⟩

/-- **An instruction with undefined flags** (`FI`) writes nothing: its tree
is silent (`exec_fi`). -/
theorem nodeW_noWr_fi {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {fi : FI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(fi.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  obtain ⟨t, hex, hst⟩ := Spike.Lib.X64.exec_fi (cellOf hI hb he hs hn hpc)
  refine ⟨fun L hL => ?_, fun _ h => h⟩
  rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hex] at h <;> cases h <;> exact hst.elim

/-- **A store** `movq %r, k(%b)` of a word unmapped in private memory
(`ha`) writes only the word at the abstract state's address. -/
theorem nodeW_wr_st {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s c => ∃ σ, n.J σ c ∧ F s.st.1 ∧ ∀ L, WrAt s L → L = ⟨bAddr σ.regs b k, 8⟩)
      (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  exact ⟨⟨σ, hJ, hD, fun L hL => wrAt_store hex hL⟩, fun _ h => h⟩

/-- **A `lock xaddq %r, k(%b)`** of a word unmapped in private memory
(`ha`) writes only the word at the abstract state's address. -/
theorem nodeW_wr_xadd {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {b r : Reg64}
    {k : Int64} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s c => ∃ σ, n.J σ c ∧ F s.st.1 ∧ ∀ L, WrAt s L → L = ⟨bAddr σ.regs b k, 8⟩)
      (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hc := cellOf hI hb he hs hn hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_xaddG_agrees (w := .W64) hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  exact ⟨⟨σ, hJ, hD, fun L hL => wrAt_rmw hex hL⟩, fun _ h => h⟩

end Gen

/-- A state writing nothing allows `ArenaWr0` at every frame list. -/
theorem arenaWr0_of_noWr {ar : Arena} {lbl : Lbl} {p : Prog} {s : State} {c : Spike.Lib.Ctl}
    (h : ∀ L, ¬ WrAt s L) : ∀ fs, ArenaWr0 ar lbl p s c fs :=
  fun _ _ _ _ L hL => (h L hL).elim

/-! ## The allocator's code -/

section Code

open Spike.Lib.X64.Alloc

/-- **`allocIn`'s facts**: the prologue's fall-through, and every block and
single instruction of `scc_rt_alloc` at its label and byte offset, in
`AllocW`'s order. -/
theorem allocIn_spec {cells : List (Directive × Nat)} (h : allocIn cells = true) :
    labelGapB cells fnL entryL 23 = true ∧ blockAtB cells fnL 0 bPro = true ∧
    blockAtB cells entryL 0 bChk = true ∧ blockAtB cells entryL 16 bJ1 = true ∧
    blockAtB cells cntL 0 [(iCtr.toDir, 7)] = true ∧ blockAtB cells cntL 7 bC1 = true ∧
    blockAtB cells cntL 19 [(iRmw, 5)] = true ∧ blockAtB cells cntL 24 bC2 = true ∧
    blockAtB cells cntL 59 bJ2 = true ∧ blockAtB cells slowL 0 bSlow = true ∧
    blockAtB cells slowL 16 bJ3 = true ∧ blockAtB cells fullL 0 bFull = true ∧
    blockAtB cells okL 0 bO0 = true ∧ blockAtB cells okL 11 [((FI.shr_cl .rax).toDir, 3)] = true ∧
    blockAtB cells okL 14 bO1 = true ∧ blockAtB cells okL 29 [((FI.and_rr .rax .rcx).toDir, 3)] = true ∧
    blockAtB cells okL 32 bO2 = true ∧ blockAtB cells okL 36 [(iHeap.toDir, 7)] = true ∧
    blockAtB cells okL 43 bO3 = true ∧ blockAtB cells okL 58 [((FI.shl_cl .rax).toDir, 3)] = true ∧
    blockAtB cells okL 61 bO4 = true ∧ blockAtB cells okL 88 [((FI.imul_rr .rax .rcx).toDir, 4)] = true ∧
    blockAtB cells okL 92 bO5 = true ∧ blockAtB cells okL 107 [((FI.shl_cl .rax).toDir, 3)] = true ∧
    blockAtB cells okL 110 bO6 = true ∧ blockAtB cells okL 125 [((FI.shl_cl .rax).toDir, 3)] = true ∧
    blockAtB cells okL 128 bO7 = true ∧ blockAtB cells okL 140 [((FI.or_rr .rax .rcx).toDir, 3)] = true ∧
    blockAtB cells okL 143 bO8 = true ∧ blockAtB cells okL 170 [(iHdr, 3)] = true ∧
    blockAtB cells okL 173 bO9 = true ∧ blockAtB cells okL 226 [(iRet.toDir, 1)] = true := by
  simpa only [allocIn, fiAt, Bool.and_eq_true, and_assoc] using h

end Code

/-- **A node's pc at its label and offset**: `N`'s pcs are `lab l` plus
bytes (the goal `lab l + off = (N lab ms q i).pc`, or its mirror). -/
macro "pc_tac" : tactic =>
  `(tactic| first | rfl | exact Spike.Lib.X64.Flow.ofNat_zero' _ | exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm)

/-! ## The counter's and the header's addresses -/

section Addr

variable {lab : Label → Int64} {ms : MemSide isa} {q : Spike.Lib.X64.Alloc.Call}

/-- **The counter's address** at the counter's add. -/
theorem ctr_addr {σ : Spike.Lib.X64.AS} (hq : q.OK ms lab)
    (hcx : σ.regs.rcx.toBitVec = (lab "scc_rt_heap_use").toBitVec) :
    bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
  rw [← hq.ctr, ← hcx]; simp [bAddr, Reg64s.get64]

/-- **The header's address** at the header's store, the counter's old
value `o`. -/
theorem hdr_addr {σ : Spike.Lib.X64.AS} {o : BitVec 64} (hq : q.OK ms lab)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (hcx : σ.regs.rcx.toBitVec = Spike.Lib.X64.Alloc.H lab + o <<< 4 +
      (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3) :
    (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
  have hk := Spike.Lib.X64.Alloc.Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hra : bAddr σ.regs .rcx 0 =
      Spike.Lib.X64.Alloc.H lab + o <<< 4 + (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3 := by
    rw [← hcx]; simp [bAddr, Reg64s.get64]
  rw [hra, Spike.Lib.X64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.X64.Alloc.mOf_lt _)
    (by rw [hq.heap]; exact hq.room), hq.heap, hk]
  rfl

end Addr

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok
  bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call} {ar : Arena}

set_option hygiene false in
/-- A block of `scc_rt_alloc` writing nothing, as `W`'s component `C`. -/
local macro "nab " hb:term:max ok:term:max C:term : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR (by omega) (by omega)) Spike.Lib.X64.BlkW.triv $C)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event, as `W`'s
component `C`. -/
local macro "nsi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac)) Spike.Lib.X64.NodeW.triv $C)

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags, as `W`'s
component `C`. -/
local macro "nfi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_fi hI $hb rfl (by pc_tac)) Spike.Lib.X64.NodeW.triv $C)

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list and
any placement `lbl`, for a memory side with the arena's counter, base and
offsets (`hctr`, `hheap`, `hoff`), the counter and every header the code
may store unmapped in private memory (`hmem`, `hq`): the counter's add
writes the counter, the header's store a header below the held count's
object (no frame run leaves the held allocation, `FrameRun.eq_of_newBuf`),
every other step nothing. -/
theorem allocArena (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) {lbl : Lbl} {p : Prog}
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 ar lbl p s c fs) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → ∀ fs, ArenaWr0 ar lbl p s c fs :=
    fun _ _ h _ => arenaWr0_of_noWr h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 bPro_ok C
  · nab h1 bChk_ok C
  · nab h2 bJ1_ok C
  · nsi h3 C
  · nab h4 bC1_ok C
  · refine NodeW.imp (nodeW_wr_xadd hI (b := .rcx) (k := 0) (r := .rax) h5 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨-, hcx, -⟩ := hJ
      rw [ctr_addr (hq m hF) hcx]
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, hcx, -⟩, hF, hL⟩ - fs c' fs' - L hW hne
      exact (hne (by rw [hL L hW, ctr_addr (hq _ hF) hcx, hctr]; rfl)).elim
  · nab h6 bC2_ok C
  · nab h7 bJ2_ok C
  · nab h8 bSlow_ok C
  · nab h9 bJ3_ok C
  · nab h10 bFull_ok C
  · nab h11 bO0_ok C
  · nfi h12 C
  · nab h13 bO1_ok C
  · nfi h14 C
  · nab h15 bO2_ok C
  · nsi h16 C
  · nab h17 bO3_ok C
  · nfi h18 C
  · nab h19 bO4_ok C
  · nfi h20 C
  · nab h21 bO5_ok C
  · nfi h22 C
  · nab h23 bO6_ok C
  · nfi h24 C
  · nab h25 bO7_ok C
  · nfi h26 C
  · nab h27 bO8_ok C
  · refine NodeW.imp (nodeW_wr_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 hcx⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Spike.Lib.X64ConsumerA.FrameRun.eq_of_newBuf hr
        (show (Spike.Lib.X64.holdCtr ms q.c0 o).term = _ from hq'.term) hq'.ev hq'.num)
      rw [hL L hW]
      refine .inr (.inr (.inr ⟨o.toNat, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, by rw [← hctr]; rfl, hq'.term,
        hq'.ev, hq'.num, ?_⟩))
      show (bAddr σ.regs .rcx 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
      rw [hdr_addr hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
      omega
  · nab h29 bO9_ok C
  · exact NodeW.imp (Spike.Lib.LowerX64.BlkW.nodeW (blkW_noWr hI (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8)
      h30 rfl (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv C

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`**, for a
memory side with the arena's base (`hheap`), the counter below the heap
(`hlt`, `h64`), the counter add's states in `Ctx` (`hctx`), every header
the code may store unmapped in private memory (`hmem`, `hq`): the header's
store writes a word of the heap, every other step but the add nothing. -/
theorem allocCtr (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) {Ctx : Frag isa}
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, -, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → WrAt s ar.ctrLoc → Ctx s c :=
    fun _ _ h _ hW => (h _ hW).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c (by rw [← hI.labOk]; exact hA), fun _ h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hI.labOk]
  · nab h0 bPro_ok C
  · nab h1 bChk_ok C
  · nab h2 bJ1_ok C
  · nsi h3 C
  · nab h4 bC1_ok C
  · nab h6 bC2_ok C
  · nab h7 bJ2_ok C
  · nab h8 bSlow_ok C
  · nab h9 bJ3_ok C
  · nab h10 bFull_ok C
  · nab h11 bO0_ok C
  · nfi h12 C
  · nab h13 bO1_ok C
  · nfi h14 C
  · nab h15 bO2_ok C
  · nsi h16 C
  · nab h17 bO3_ok C
  · nfi h18 C
  · nab h19 bO4_ok C
  · nfi h20 C
  · nab h21 bO5_ok C
  · nfi h22 C
  · nab h23 bO6_ok C
  · nfi h24 C
  · nab h25 bO7_ok C
  · nfi h26 C
  · nab h27 bO8_ok C
  · refine NodeW.imp (nodeW_wr_st hI (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 hcx⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addr hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, hheap] at ha
      have : ar.ctrLoc.addr.toNat = ar.ctr := by
        simp only [Arena.ctrLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
      omega
  · nab h29 bO9_ok C
  · exact NodeW.imp (Spike.Lib.LowerX64.BlkW.nodeW (blkW_noWr hI (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8)
      h30 rfl (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv C

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.allocIn_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocIn_spec

/-- info: 'Spike.Lib.X64.AllocG.hdr_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hdr_addr

/-- info: 'Spike.Lib.X64.AllocG.allocArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocArena

/-- info: 'Spike.Lib.X64.AllocG.allocCtr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtr

end Spike.Lib.X64.AllocG
