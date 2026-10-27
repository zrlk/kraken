/-
**`scc_rt_alloc`'s arena writes at `hello1.w`'s instance** (AArch64): the
allocator's node obligations (`AllocW`, `Spike/Lib/A64Alloc.lean`) inside
`W0`'s arena component (`ArenaWr0`, `Spike/Test/A64Hello1W0.lean`) at every
frame list.

- `blkW_noWr`, `nodeW_noWr_si`: a covered block's and a single
  instruction's states write no location (their steps are silent: the
  stack is private memory).
- `nodeW_wr_ldop`, `nodeW_wr_st`: an RMW and a store of a word unmapped in
  private memory write only the word at the abstract state's address.
- `hdr_addr`: the header store's address, `Call.hdrAt` of the old count.
- `allocArena`: every node of `scc_rt_alloc`, for a memory side with the
  arena's counter, base and offsets: the counter's add writes the counter
  (excluded by `ArenaWr0`), the header's store a word below the held
  count's object (`ArenaW`'s header case; no frame run leaves the held
  allocation, `FrameRun.eq_of_newBuf`), every other step nothing.
- `w0_of_stA`: `W0` from the state's facts with the arena component given
  as `ArenaWr0` (for states writing the arena, `w0_of_st`'s off-arena
  premise too weak).
-/
import Spike.Test.A64Hello1AllocAb

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide FrameRun FragS)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND)
open Spike.Lib.A64.Rt (InstOk cellOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt exec_str_agrees exec_ldop)
open Spike.Lib.A64ConsumerA (AbSt WrAt ArenaW SFactsSt noWr_done wrAt_store wrAt_rmw FrameRun.eq_of_newBuf)
open Spike.Test.A64ArenaHello1 (ar)
open Spike.Lib.A64ConsumerS (PlacedS)
open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.SFactsN (RunOk)
open SccCode (hello1Λ)

/-! ## Generic nodes' writes -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block's states write nothing**: every instruction of the
block is a silent step (`exec_ai`). -/
theorem blkW_noWr {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {l : Label} {k : Nat}
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

/-! ## `W0` with the arena component -/

variable {p : Prog} {rS : Range} {Dt : State → Prop} {Ctx : FragS isaLSE2} {s : State} {c : Spike.Lib.Ctl}
  {fs : List TermRun.Frame}

/-- **`W0` from the state's facts** as `w0_of_st`, the arena component
given as `ArenaWr0`. -/
theorem w0_of_stA (h : SFactsSt hello1Λ μ0 own rS Tk s) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hpl : PlacedS hello1Λ hello1Λ.static s c fs) (hab : AbSt μ0 (Spike.Lib.A64.WriteAb.Ab labT) s)
    (hrun : RunOk p c fs) (hn : ArenaWr0 p s c fs) (hcx : WrAt s ar.ctrLoc → Ctx s c fs)
    (hao : AbortW μ0 s c fs) : W0 p rS Dt Ctx s c fs :=
  ⟨{ h with wrTail := fun h1 _ _ _ h2 => (h.wrTail h1 _ _ _ h2).elim }, hab, hnr, hpl, hn, hcx, hrun, hao⟩

/-- A state writing nothing allows `ArenaWr0` at every frame list. -/
theorem arenaWr0_of_noWr (h : ∀ L, ¬ WrAt s L) : ∀ fs, ArenaWr0 p s c fs :=
  fun _ _ _ _ L hL => (h L hL).elim

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Test.A64Hello1RtW (hello1_instOk)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc`: it writes nothing. -/
local macro "nab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact BlkW.imp (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (k := $k) (by decide +kernel)
    (by dsimp only [N]; decide +kernel) $ok hR hal (by omega) (by omega)) Spike.Lib.A64.Flow.BlkW.triv
    (fun _ _ h _ => arenaWr0_of_noWr h))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "nsi " si:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact NodeW.imp (nodeW_noWr_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (l := $l) (k := $k)
    (p := labT $l + Int64.ofNat (4 * $k)) (by decide +kernel) rfl (by dsimp only [N]; decide +kernel))
    Spike.Lib.A64.Flow.NodeW.triv (fun _ _ h _ => arenaWr0_of_noWr h))

/-- **The header's address** at the header's store, the counter's old
value `o`. -/
theorem hdr_addr {σ : Spike.Lib.A64.Flow.AS} {o : BitVec 64} (hq : q.OK ms labT)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (h10 : σ.regs.X10.toBitVec = Spike.Lib.A64.Alloc.H labT + o <<< 4 +
      (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3) :
    (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
  have hk := Spike.Lib.A64.Alloc.Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hra : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 =
      Spike.Lib.A64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3 := by
    rw [← h10]; simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg]
  rw [hra, Spike.Lib.A64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.A64.Alloc.mOf_lt _)
    (by rw [hq.heap]; exact hq.room), hq.heap, hk]
  rfl

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list, for a
memory side with the arena's counter, base and offsets (`hctr`, `hheap`,
`hoff`), the counter and every header the code may store unmapped in
private memory (`hmem`, `hq`): the counter's add writes the counter, the
header's store a header below the held count's object. -/
theorem allocArena (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 p s c fs) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · nab "scc_rt_alloc" 0 b0_ok
  · nab ".L2_scc_rt_alloc.0_entry" 0 b1_ok
  · nab ".L2_scc_rt_alloc.0_entry" 4 b2_ok
  · nsi iAdrpC ".L2_scc_rt_alloc.1_cnt" 0
  · nsi iAddC ".L2_scc_rt_alloc.1_cnt" 1
  · nab ".L2_scc_rt_alloc.1_cnt" 2 b3_ok
  · refine NodeW.imp (nodeW_wr_ldop (hello1_instOk (rS := ⟨0, 0⟩)) (op := .ADD) (kk := .acqRel) (rs := .X9)
      (rt := .X11) (b := .X10) (l := ".L2_scc_rt_alloc.1_cnt") (k := 5)
      (p := labT ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5)) (by decide +kernel) rfl
      (by dsimp only [N]; decide +kernel) fun σ c m hJ hF => ?_) Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨-, h10, -⟩ := hJ
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      rw [h10']
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, h10, -⟩, hL⟩ - fs c' fs' - L hW hne
      have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
      exact (hne (by rw [hL L hW, h10', hctr]; rfl)).elim
  · nab ".L2_scc_rt_alloc.1_cnt" 6 b4_ok
  · nab ".L2_scc_rt_alloc.1_cnt" 15 b5_ok
  · nab ".L2_scc_rt_alloc.2_slow" 0 b6_ok
  · nab ".L2_scc_rt_alloc.2_slow" 4 b7_ok
  · nab ".L2_scc_rt_alloc.4_full" 0 b9_ok
  · nab ".L2_scc_rt_alloc.5_ok" 0 b11_ok
  · nsi iAdrpH ".L2_scc_rt_alloc.5_ok" 8
  · nsi iAddH ".L2_scc_rt_alloc.5_ok" 9
  · nab ".L2_scc_rt_alloc.5_ok" 10 b12_ok
  · refine NodeW.imp (nodeW_wr_st (hello1_instOk (rS := ⟨0, 0⟩)) (t := .X9) (b := .X10) (i := 0)
      (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (p := labT ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41))
      (by decide +kernel) rfl (by dsimp only [N]; decide +kernel) fun σ c m hJ hF => ?_)
      Spike.Lib.A64.Flow.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, h10⟩ := hJ
      have hq' := hq m hF
      rw [hello1_labT] at hq'
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr hq' hle hn28 h10⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, h10⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      rw [hello1_labT] at hq'
      obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf hr hq'.term hq'.ev hq'.num)
      rw [hL L hW]
      refine .inr (.inr (.inr ⟨o.toNat, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, by rw [← hctr]; rfl, hq'.term,
        hq'.ev, hq'.num, ?_⟩))
      show (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
      rw [hdr_addr hq' hle hn28 h10, Spike.Lib.A64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
      omega
  · nab ".L2_scc_rt_alloc.5_ok" 42 b13_ok
  · exact NodeW.imp (Spike.Lib.LowerA64.BlkW.nodeW (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩))
      (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (blk := [iRet.toDir]) (lo := -160) (hi := 0) (by decide +kernel)
      (by dsimp only [N]; decide +kernel) (by dsimp only [N]; decide) hR hal (by omega) (by omega))
      (List.cons_ne_nil _ _)) Spike.Lib.A64.Flow.NodeW.triv (fun _ _ h _ => arenaWr0_of_noWr h)

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.A64Hello1W0.blkW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_noWr

/-- info: 'Spike.Test.A64Hello1W0.nodeW_noWr_si' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_noWr_si

/-- info: 'Spike.Test.A64Hello1W0.nodeW_wr_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_wr_st

/-- info: 'Spike.Test.A64Hello1W0.nodeW_wr_ldop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_wr_ldop

/-- info: 'Spike.Test.A64Hello1W0.w0_of_stA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms w0_of_stA

/-- info: 'Spike.Test.A64Hello1W0.hdr_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hdr_addr

/-- info: 'Spike.Test.A64Hello1W0.allocArena' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocArena

end Spike.Test.A64Hello1W0
