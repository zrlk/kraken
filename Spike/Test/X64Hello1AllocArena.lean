/-
**`scc_rt_alloc`'s arena writes at `hello1.x`'s instance** (x86-64): the
allocator's node obligations (`AllocW`, `Spike/Lib/X64Alloc.lean`) inside
`W0`'s arena component (`ArenaWr0`, `Spike/Test/X64Hello1W0.lean`) at every
frame list. The twin of `Spike/Test/A64Hello1AllocArena.lean`.

- `blkW_noWr`, `nodeW_noWr_si`, `nodeW_noWr_fi`: a covered block's, a
  single instruction's and one with undefined flags' states write no
  location (their steps are silent: the stack is private memory; AArch64
  has no `nodeW_noWr_fi`).
- `nodeW_wr_xadd`, `nodeW_wr_st`: a `lock xadd` and a store of a word
  unmapped in private memory write only the word at the abstract state's
  address (AArch64's RMW is `nodeW_wr_ldop`; both carry the frame condition,
  the counter's address a label's here).
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
import Spike.Test.X64Hello1AllocAb
import Spike.Test.X64Hello1Ctr
import Spike.Lib.X64Hello1WImp

namespace Spike.Test.X64Hello1W0

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FrameRun FragS)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND SI FI bAddr xaddDir stDir mB eaddr_mB cellOff)
open Spike.Lib.X64.Rt (InstOk cellOf codeOf)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (AbSt WrAt ArenaW SFactsSt noWr_done wrAt_store wrAt_rmw)
open Spike.Test.X64Hello1Ctr (FrameRun.eq_of_newBuf)
open Spike.Test.X64ArenaHello1 (ar)
open Spike.Lib.X64ConsumerS (PlacedS)
open Spike.Lib.X64.Flow.Hello1.Inst
open Spike.Lib.X64.Flow.Hello1.SFactsN (RunOk)
open SccCode (hello1Λ)

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

/-! ## `W0` with the arena component -/

variable {p : Prog} {rS : Range} {Dt : State → Prop} {Ctx : FragS isa} {s : State} {c : Spike.Lib.Ctl}
  {fs : List TermRun.Frame}

/-- **`W0` from the state's facts** as `w0_of_st`, the arena component
given as `ArenaWr0`. -/
theorem w0_of_stA (h : SFactsSt hello1Λ μ0 own rS Tk s) (hnr : fs = [] → ∀ a, c.term ≠ .ret a)
    (hpl : PlacedS hello1Λ hello1Λ.static s c fs) (hab : AbSt μ0 (Spike.Lib.X64.WriteAb.Ab labT) s)
    (hrun : RunOk p c fs) (hn : ArenaWr0 p s c fs) (hcx : WrAt s ar.ctrLoc → Ctx s c fs)
    (hao : AbortW μ0 s c fs) : W0 p rS Dt Ctx s c fs :=
  ⟨{ h with wrTail := fun h1 _ _ _ h2 => (h.wrTail h1 _ _ _ h2).elim }, hab, hnr, hpl, hn, hcx, hrun, hao⟩

/-- A state writing nothing allows `ArenaWr0` at every frame list. -/
theorem arenaWr0_of_noWr (h : ∀ L, ¬ WrAt s L) : ∀ fs, ArenaWr0 p s c fs :=
  fun _ _ _ _ L hL => (h L hL).elim

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL entryL cntL slowL fullL okL bPro_ok bChk_ok
  bJ1_ok bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok
  bO9_ok)
open Spike.Test.X64Hello1RtW (hello1_instOk)
open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End)

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc`: it writes nothing. -/
local macro "nab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.BlkW.imp (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (off := $k)
    (by decide +kernel) (by first | rfl | exact Spike.Lib.X64.Flow.ofNat_zero' _) $ok hR (by omega) (by omega))
    Spike.Lib.X64.BlkW.triv (fun _ _ h _ => arenaWr0_of_noWr h))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "nsi " si:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.NodeW.imp (nodeW_noWr_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (z := $z)
    (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl
    (by first | rfl | exact (Spike.Lib.X64.Flow.ofNat_zero' _).symm))
    Spike.Lib.X64.NodeW.triv (fun _ _ h _ => arenaWr0_of_noWr h))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "nfi " fi:term:max z:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact Spike.Lib.X64.NodeW.imp (nodeW_noWr_fi (hello1_instOk (rS := ⟨0, 0⟩)) (fi := $fi) (z := $z)
    (l := $l) (off := $k) (p := labT $l + Int64.ofNat $k) (by decide +kernel) rfl rfl)
    Spike.Lib.X64.NodeW.triv (fun _ _ h _ => arenaWr0_of_noWr h))

/-- **The header's address** at the header's store, the counter's old
value `o`. -/
theorem hdr_addr {σ : Spike.Lib.X64.AS} {o : BitVec 64} (hq : q.OK ms labT)
    (hle : o.toNat + ms.units q.n q.τ ≤ ms.cells) (hn28 : q.n < 2 ^ 28)
    (hcx : σ.regs.rcx.toBitVec = Spike.Lib.X64.Alloc.H labT + o <<< 4 +
      (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3) :
    (bAddr σ.regs .rcx 0).toNat = q.hdrAt ms o.toNat := by
  have hk := Spike.Lib.X64.Alloc.Call.k_toNat hq.n_lt
  have hcl := hq.cells
  have hra : bAddr σ.regs .rcx 0 =
      Spike.Lib.X64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.X64.Alloc.mOf q.h) <<< 3 := by
    rw [← hcx]; simp [bAddr, Reg64s.get64]
  rw [hra, Spike.Lib.X64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.X64.Alloc.mOf_lt _)
    (by rw [hq.heap]; exact hq.room), hq.heap, hk]
  rfl

/-- **`scc_rt_alloc`'s states allow `ArenaWr0`** at every frame list, for a
memory side with the arena's counter, base and offsets (`hctr`, `hheap`,
`hoff`), the counter and every header the code may store unmapped in
private memory (`hmem`, `hq`): the counter's add writes the counter, the
header's store a header below the held count's object. -/
theorem allocArena (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hctr : ms.ctr = ar.ctr) (hheap : ms.heap = ar.heap) (hoff : ∀ k τ, ms.off k τ = ar.off k τ) :
    AllocW ms q (fun s c => ∀ fs, ArenaWr0 p s c fs) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · nab fnL 0 bPro_ok
  · nab entryL 0 bChk_ok
  · nab entryL 16 bJ1_ok
  · nsi iCtr 7 cntL 0
  · nab cntL 7 bC1_ok
  · refine Spike.Lib.X64.NodeW.imp (nodeW_wr_xadd (hello1_instOk (rS := ⟨0, 0⟩)) (b := .rcx) (k := 0) (r := .rax)
      (z := 5) (l := cntL) (off := 19) (p := labT cntL + Int64.ofNat 19) (by decide +kernel) rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨-, hcx, -⟩ := hJ
      have hq' := hq m hF
      rw [hello1_labT] at hq'
      have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
        rw [← hq'.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
      rw [hb]
      exact hmem _ (.inl rfl) m hF
    · rintro s c ⟨σ, ⟨-, hcx, -⟩, hF, hL⟩ - fs c' fs' - L hW hne
      have hq' := hq _ hF
      rw [hello1_labT] at hq'
      have hb : bAddr σ.regs .rcx 0 = BitVec.ofNat 64 ms.ctr := by
        rw [← hq'.ctr, ← hcx]; simp [bAddr, Reg64s.get64]
      exact (hne (by rw [hL L hW, hb, hctr]; rfl)).elim
  · nab cntL 24 bC2_ok
  · nab cntL 59 bJ2_ok
  · nab slowL 0 bSlow_ok
  · nab slowL 16 bJ3_ok
  · nab fullL 0 bFull_ok
  · nab okL 0 bO0_ok
  · nfi (.shr_cl .rax) 3 okL 11
  · nab okL 14 bO1_ok
  · nfi (.and_rr .rax .rcx) 3 okL 29
  · nab okL 32 bO2_ok
  · nsi iHeap 7 okL 36
  · nab okL 43 bO3_ok
  · nfi (.shl_cl .rax) 3 okL 58
  · nab okL 61 bO4_ok
  · nfi (.imul_rr .rax .rcx) 4 okL 88
  · nab okL 92 bO5_ok
  · nfi (.shl_cl .rax) 3 okL 107
  · nab okL 110 bO6_ok
  · nfi (.shl_cl .rax) 3 okL 125
  · nab okL 128 bO7_ok
  · nfi (.or_rr .rax .rcx) 3 okL 140
  · nab okL 143 bO8_ok
  · refine Spike.Lib.X64.NodeW.imp (nodeW_wr_st (hello1_instOk (rS := ⟨0, 0⟩)) (b := .rcx) (k := 0) (r := .rax)
      (z := 3) (l := okL) (off := 170) (p := labT okL + Int64.ofNat 170) (by decide +kernel) rfl rfl
      fun σ c m hJ hF => ?_) Spike.Lib.X64.NodeW.triv ?_
    · obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
      have hq' := hq m hF
      rw [hello1_labT] at hq'
      exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr hq' hle hn28 hcx⟩) m hF
    · rintro s c ⟨σ, ⟨o, ⟨rfl, hle, -, hn28, -⟩, -, -, hcx⟩, hF, hL⟩ - fs c' fs' hr L hW - lsize
      have hq' := hq _ hF
      rw [hello1_labT] at hq'
      obtain ⟨rfl, -⟩ := Prod.mk.inj (FrameRun.eq_of_newBuf
        (show (Spike.Lib.X64.holdCtr ms q.c0 o).term = _ from hq'.term) hr)
      rw [hL L hW]
      refine .inr (.inr (.inr ⟨o.toNat, q.x, q.a, q.τ, q.e, q.ta, q.ws, q.n, by rw [← hctr]; rfl, hq'.term,
        hq'.ev, hq'.num, ?_⟩))
      show (bAddr σ.regs .rcx 0).toNat < ar.heap + 16 * o.toNat + ar.off q.n q.τ
      rw [hdr_addr hq' hle hn28 hcx, Spike.Lib.X64.Alloc.Call.hdrAt, ← hheap, ← hoff, hq'.off]
      omega
  · nab okL 173 bO9_ok
  · exact Spike.Lib.X64.NodeW.imp (BlkW.nodeW (blkW_noWr (hello1_instOk (rS := ⟨0, 0⟩))
      (l := okL) (off := 226) (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8) (by decide +kernel) rfl
      (show Spike.Lib.X64.okBlk (-160) 8 Spike.Lib.X64.Alloc.oE [(iRet.toDir, 1)] = true by decide) hR
      (by omega) (by omega)) (List.cons_ne_nil _ _)) Spike.Lib.X64.NodeW.triv (fun _ _ h _ => arenaWr0_of_noWr h)

end Alloc

-- No axioms beyond Lean's.

/--
info: 'Spike.Test.X64Hello1W0.blkW_noWr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkW_noWr

/--
info: 'Spike.Test.X64Hello1W0.nodeW_noWr_si' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_noWr_si

/--
info: 'Spike.Test.X64Hello1W0.nodeW_noWr_fi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_noWr_fi

/--
info: 'Spike.Test.X64Hello1W0.nodeW_wr_st' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_wr_st

/--
info: 'Spike.Test.X64Hello1W0.nodeW_wr_xadd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodeW_wr_xadd

/--
info: 'Spike.Test.X64Hello1W0.w0_of_stA' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms w0_of_stA

/--
info: 'Spike.Test.X64Hello1W0.hdr_addr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hdr_addr

/--
info: 'Spike.Test.X64Hello1W0.allocArena' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms allocArena

end Spike.Test.X64Hello1W0
