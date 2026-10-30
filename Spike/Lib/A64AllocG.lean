/-
**`scc_rt_alloc`'s node obligations at any instance** (AArch64): the
allocator's `AllocW` (`Spike/Lib/A64Alloc.lean`) inside the components of
`W0` (`Spike/Lib/A64W0G.lean`) for any executable laid out with labels
`lab` (`InstOk`) whose program holds the allocator's code (`Flow.allocIn`,
A7), no layout constant: `hello1.w`'s instances
(`Spike/Test/A64Hello1Alloc{Arena,Ctr,W,Ab}.lean`) with `hello1_instOk`'s
facts and the kernel's decisions at `labT` replaced by `InstOk`, `allocIn`
and the node pcs' equations at any `lab` (`pc_tac`).

- `NodeW.imp`, `BlkW.imp`, `AllocW.imp`: two obligations into one
  (`Spike/Test/A64Hello1W0N.lean`'s).
- `blkW_noWr`, `nodeW_noWr_si`, `nodeW_wr_st`, `nodeW_wr_ldop`,
  `arenaWr0_of_noWr`: `hello1.w`'s generic node lemmas
  (`Spike/Test/A64Hello1AllocArena.lean`), here so the generic path imports
  no test module.
- `allocIn_spec`: `allocIn`'s facts.
- `hdr_addr`: the header store's address at any labels.
- `allocArena`: every node allows `ArenaWr0` at every frame list.
- `allocCtr`: only the counter's add writes the counter.
-/
import Spike.Lib.A64W0G
import Spike.Lib.Rt.A64RtW
import Spike.Lib.LowerA64.NodeTp
import Scc.Cert.Rt.A64AllocIn

namespace Spike.Lib.A64.AllocG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide FrameRun FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk cellOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt exec_str_agrees exec_ldop)
open Spike.Lib.A64ConsumerA (WrAt noWr_done wrAt_store wrAt_rmw FrameRun.eq_of_newBuf)
open Spike.Lib.A64.W0G (ArenaWr0)

/-! ## Two node obligations into one -/

section Imp

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W W1 W2 : Frag isaLSE2} {K : State → State → Prop}

/-- **A node inside `W`** from one inside `W1` not moved by `K` and one
inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem NodeW.imp {n : ND} (h1 : NodeW W1 K exe endPc R F n) (h2 : NodeW W2 (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : NodeW W K exe endPc R F n := fun s c hA =>
  ⟨hw s c (h1 s c hA).1 (h2 s c hA).1, (h1 s c hA).2⟩

/-- **A block node inside `W`** from one inside `W1` not moved by `K` and
one inside `W2`, `W1 ∧ W2` inside `W`. -/
theorem BlkW.imp {n : ND} {blk : List Directive} (h1 : BlkW W1 K exe endPc R F n blk)
    (h2 : BlkW W2 (fun _ _ => False) exe endPc R F n blk) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    BlkW W K exe endPc R F n blk := fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
  ⟨hw _ c (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1 (h2 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
    (h1 s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2⟩

/-- **`scc_rt_alloc` inside `W`** from two (`NodeW.imp`, `BlkW.imp`). -/
theorem AllocW.imp {ms : MemSide isaLSE2} {q : Spike.Lib.A64.Alloc.Call}
    (h1 : Spike.Lib.A64.Alloc.AllocW ms q W1 K exe endPc R F)
    (h2 : Spike.Lib.A64.Alloc.AllocW ms q W2 (fun _ _ => False) exe endPc R F)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.A64.Alloc.AllocW ms q W K exe endPc R F :=
  ⟨BlkW.imp h1.e h2.e hw, BlkW.imp h1.entry h2.entry hw, BlkW.imp h1.n2 h2.n2 hw, NodeW.imp h1.cnt h2.cnt hw,
    NodeW.imp h1.cnt1 h2.cnt1 hw, BlkW.imp h1.cnt2 h2.cnt2 hw, NodeW.imp h1.rmw h2.rmw hw,
    BlkW.imp h1.n4 h2.n4 hw, BlkW.imp h1.n5 h2.n5 hw, BlkW.imp h1.slow h2.slow hw, BlkW.imp h1.n7 h2.n7 hw,
    BlkW.imp h1.full h2.full hw, BlkW.imp h1.ok h2.ok hw, NodeW.imp h1.ok1 h2.ok1 hw,
    NodeW.imp h1.ok2 h2.ok2 hw, BlkW.imp h1.n12 h2.n12 hw, NodeW.imp h1.hdr h2.hdr hw,
    BlkW.imp h1.n13 h2.n13 hw, NodeW.imp h1.ret h2.ret hw⟩

end Imp

/-! ## Generic nodes' writes -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block's states write nothing**: every instruction of the
block is a silent step (`exec_ai`). -/
theorem blkW_noWr {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) :
    BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk := by
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  intro s σ c he hn _ _ _ _ _ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ := Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label
    (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  obtain ⟨m', hex, -⟩ := Spike.Lib.A64.Flow.exec_ai haok hR hal hlo hhi hc hreg hA'
  exact noWr_done hex

/-- **A single instruction without an event** (`SI`) writes nothing. -/
theorem nodeW_noWr_si {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) :
    NodeW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  exact ⟨noWr_done (Spike.Lib.A64.Flow.exec_si (cellOf hI hb he hs hn hpc)), fun _ h => h⟩

/-- **A store** `str Xt, [Xn, #i]` of a word unmapped in private memory
(`ha`) writes only the word at the abstract state's address. -/
theorem nodeW_wr_st {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {i : Int64} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    NodeW (fun s c => ∃ σ, n.J σ c ∧ F s.st.1 ∧
        ∀ L, WrAt s L → L = ⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩)
      (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hc := cellOf hI hb he hs hn hpc
  have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
  exact ⟨⟨σ, hJ, hD, fun L hL => wrAt_store hex hL⟩, fun _ h => h⟩

/-- **An RMW** `ld<op><k> Xs, Xt, [Xn]` (`Xt` a register) of a word
unmapped in private memory (`ha`) writes only the word at the abstract
state's address. -/
theorem nodeW_wr_ldop {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none) :
    NodeW (fun s c => ∃ σ, n.J σ c ∧ ∀ L, WrAt s L → L = ⟨(σ.regs.getXReg b).toBitVec, 8⟩)
      (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hc := cellOf hI hb he hs hn hpc
  have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
  have hex := exec_ldop hc (by rw [ha']; exact ha σ c s.st.1 hJ hD)
  rw [hdc, ha'] at hex
  exact ⟨⟨σ, hJ, fun L hL => wrAt_rmw hex hL⟩, fun _ h => h⟩

end Gen

/-- A state writing nothing allows `ArenaWr0` at every frame list. -/
theorem arenaWr0_of_noWr {ar : Arena} {lbl : Lbl} {p : Prog} {s : State} {c : Spike.Lib.Ctl}
    (h : ∀ L, ¬ WrAt s L) : ∀ fs, ArenaWr0 ar lbl p s c fs :=
  fun _ _ _ _ L hL => (h L hL).elim

/-! ## The allocator's code -/

section Code

open Spike.Lib.A64.Alloc

/-- **`allocIn`'s facts**: every block and single instruction of
`scc_rt_alloc` at its label and offset, and the prologue's fall-through. -/
theorem allocIn_spec {prog : List Directive} (h : Spike.Lib.A64.Flow.allocIn prog = true) :
    blockAt prog "scc_rt_alloc" 0 b0 = true ∧
    blockAt prog ".L2_scc_rt_alloc.0_entry" 0 b1 = true ∧
    blockAt prog ".L2_scc_rt_alloc.0_entry" 4 b2 = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 0 [iAdrpC.toDir] = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 1 [iAddC.toDir] = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 2 b3 = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 5 [iRmw] = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 6 b4 = true ∧
    blockAt prog ".L2_scc_rt_alloc.1_cnt" 15 b5 = true ∧
    blockAt prog ".L2_scc_rt_alloc.2_slow" 0 b6 = true ∧
    blockAt prog ".L2_scc_rt_alloc.2_slow" 4 b7 = true ∧
    blockAt prog ".L2_scc_rt_alloc.4_full" 0 b9 = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 0 b11 = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 8 [iAdrpH.toDir] = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 9 [iAddH.toDir] = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 10 b12 = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 41 [iHdr] = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 42 b13 = true ∧
    blockAt prog ".L2_scc_rt_alloc.5_ok" 54 [iRet.toDir] = true ∧
    Scc.Cert.Rt.A64.labelGap prog "scc_rt_alloc" ".L2_scc_rt_alloc.0_entry" 7 = true := by
  simpa only [Spike.Lib.A64.Flow.allocIn, Bool.and_eq_true, and_assoc] using h

end Code

/-- **A node's pc at its label and offset**: `N`'s pcs are `lab l` plus
fours (the goal `lab l + 4 k = (N lab ms q i).pc`). -/
macro "pc_tac" : tactic =>
  `(tactic| (dsimp only [Spike.Lib.A64.Alloc.N]; first | (simp only [Int64.add_assoc]; rfl) | simp))

/-! ## The header's address -/

section Hdr

variable {lab : Label → Int64} {ms : MemSide isaLSE2} {q : Spike.Lib.A64.Alloc.Call}

/-- **The header's address** at the header's store, the counter's old
value `o`, at any allocation site (`Call.OKS`). -/
theorem hdr_addrS {σ : Spike.Lib.A64.Flow.AS} {o : BitVec 64} (hq : q.OKS ms lab)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (h10 : σ.regs.X10.toBitVec = Spike.Lib.A64.Alloc.H lab + o <<< 4 +
      (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3) :
    (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
  have hk := Spike.Lib.A64.Alloc.Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hra : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 =
      Spike.Lib.A64.Alloc.H lab + o <<< 4 + (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3 := by
    rw [← h10]; simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg]
  rw [hra, Spike.Lib.A64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.A64.Alloc.mOf_lt _)
    (by rw [hq.heap]; exact hq.room), hq.heap, hk]
  rfl

/-- **The header's address** at the header's store, the counter's old
value `o`. -/
theorem hdr_addr {σ : Spike.Lib.A64.Flow.AS} {o : BitVec 64} (hq : q.OK ms lab)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (h10 : σ.regs.X10.toBitVec = Spike.Lib.A64.Alloc.H lab + o <<< 4 +
      (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3) :
    (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat :=
  hdr_addrS hq.toS hle hn28 h10

end Hdr

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call} {ar : Arena}

set_option hygiene false in
/-- A block of `scc_rt_alloc` writing nothing, as `W`'s component `C`. -/
local macro "nab " hb:term:max ok:term:max C:term : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr hI $hb (by pc_tac) $ok hR hal (by omega) (by omega))
    Spike.Lib.A64.Flow.BlkW.triv $C)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event, as `W`'s
component `C`. -/
local macro "nsi " hb:term:max C:term : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si hI $hb rfl (by pc_tac)) Spike.Lib.A64.Flow.NodeW.triv $C)

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list and
any placement `lbl`, for a memory side with the arena's counter, base and
offsets (`hctr`, `hheap`, `hoff`), the counter and every header the code
may store unmapped in private memory (`hmem`, `hq`): the counter's add
writes the counter, the header's store a header below the held count's
object. -/
theorem allocArena (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) {lbl : Lbl} {p : Prog}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 ar lbl p s c fs) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → ∀ fs, ArenaWr0 ar lbl p s c fs :=
    fun _ _ h _ => arenaWr0_of_noWr h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 b0_ok C
  · nab h1 b1_ok C
  · nab h2 b2_ok C
  · nsi h3 C
  · nsi h4 C
  · nab h5 b3_ok C
  · refine NodeW.imp (nodeW_wr_ldop hI (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) h6 rfl
      (by pc_tac) fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨-, h10, -⟩ := hJ
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      rw [h10']
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, h10, -⟩, hL⟩ - fs c' fs' - L hW hne
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      exact (hne (by rw [hL L hW, h10', hctr]; rfl)).elim
  · nab h7 b4_ok C
  · nab h8 b5_ok C
  · nab h9 b6_ok C
  · nab h10 b7_ok C
  · nab h11 b9_ok C
  · nab h12 b11_ok C
  · nsi h13 C
  · nsi h14 C
  · nab h15 b12_ok C
  · refine NodeW.imp (nodeW_wr_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pc_tac)
      fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 h10⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -, -⟩, -, -, h10⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf hr hq'.term hq'.ev hq'.num)
      rw [hL L hW]
      refine .inr (.inr (.inr (.inl ⟨o.toNat, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, by rw [← hctr]; rfl, hq'.term,
        hq'.ev, hq'.num, ?_⟩)))
      show (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
      rw [hdr_addr hq' hle hn28 h10, Spike.Lib.A64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
      omega
  · nab h17 b13_ok C
  · exact NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr hI (blk := [iRet.toDir]) (lo := -160) (hi := 0) h18
      (by pc_tac) (by dsimp only [N]; decide) hR hal (by omega) (by omega)) (List.cons_ne_nil _ _))
      Spike.Lib.A64.Flow.NodeW.triv C

/-- **`scc_rt_alloc`'s states write the counter only in `Ctx`**, for a
memory side with the arena's base (`hheap`), the counter below the heap
(`hlt`, `h64`), the counter add's states in `Ctx` (`hctx`), every header
the code may store unmapped in private memory (`hmem`, `hq`): the header's
store writes a word of the heap, every other step but the add nothing. -/
theorem allocCtr (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) {Ctx : Frag isaLSE2}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hmem : ∀ a : BitVec 64, (∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hheap : ms.heap = ar.heap) (hlt : ar.ctr + 8 ≤ ar.heap) (h64 : ar.ctr < 2 ^ 64)
    (hctx : ∀ s c, At exe endPc R F (N lab ms q .rmw) s c → Ctx s c) :
    AllocW ms q (fun s c => WrAt s ar.ctrLoc → Ctx s c) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  have C : ∀ s (c : Spike.Lib.Ctl), (∀ L, ¬ WrAt s L) → True → WrAt s ar.ctrLoc → Ctx s c :=
    fun _ _ h _ hW => (h _ hW).elim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun s c hA => ⟨fun _ => hctx s c (by rw [← hI.labOk]; exact hA), fun _ h => h⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · nab h0 b0_ok C
  · nab h1 b1_ok C
  · nab h2 b2_ok C
  · nsi h3 C
  · nsi h4 C
  · nab h5 b3_ok C
  · nab h7 b4_ok C
  · nab h8 b5_ok C
  · nab h9 b6_ok C
  · nab h10 b7_ok C
  · nab h11 b9_ok C
  · nab h12 b11_ok C
  · nsi h13 C
  · nsi h14 C
  · nab h15 b12_ok C
  · refine NodeW.imp (nodeW_wr_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pc_tac)
      fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
      exact hmem _ ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 h10⟩ m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -, -⟩, -, -, h10⟩, hF, hL⟩ - hW
      have hq' := hq _ hF
      have ha := congrArg (fun L : Loc => L.addr.toNat) (hL _ hW)
      simp only at ha
      rw [hdr_addr hq' hle hn28 h10, Spike.Lib.A64.Alloc.Call.hdrAt, hheap] at ha
      have : ar.ctrLoc.addr.toNat = ar.ctr := by
        simp only [Arena.ctrLoc, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
      omega
  · nab h17 b13_ok C
  · exact NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr hI (blk := [iRet.toDir]) (lo := -160) (hi := 0) h18
      (by pc_tac) (by dsimp only [N]; decide) hR hal (by omega) (by omega)) (List.cons_ne_nil _ _))
      Spike.Lib.A64.Flow.NodeW.triv C

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.AllocG.allocIn_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms allocIn_spec

/-- info: 'Spike.Lib.A64.AllocG.hdr_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hdr_addr

/-- info: 'Spike.Lib.A64.AllocG.allocArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocArena

/-- info: 'Spike.Lib.A64.AllocG.allocCtr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocCtr

end Spike.Lib.A64.AllocG
