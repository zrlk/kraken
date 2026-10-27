/-
**A lane store's nodes inside `W2`** (x86-64): `LaneW`
(`Spike/Lib/LowerX64/LaneC2.lean`) at `W2` (`Spike/Lib/LowerX64/SFactsA2.lean`)
for the code predicate `CdC`.

The heap access instructions `movq disp(%rcx), %rax` (the exchange's load)
and `movq %rax, disp(%rcx)` (its store) are not covered blocks; their
nodes' facts come from their events at the element's word, which is mapped,
owned at no state, in a placed label's range and not the arena's counter.

- `nodeW_sfacts_ldH`, `nodeW_sfacts_stH`: `SFacts` at a load or store of a
  heap word at the code's pc (`nodeW_st_postA`'s pattern at `CodeAt`);
- `nodeW_ab_ldH`, `nodeW_ab_stH`: the write abort's phase kept there;
- `nodeW_noWr_ldH`, `nodeW_wr_stH`: the load writes nothing and is off a
  system call; the store writes only its word;
- `codeAt_cdC`, `blkPh_append`, `blkW_abC`: the code predicate's chunks in
  the code, phase checks of consecutive blocks, the write abort's phase
  kept along a covered block;
- `lane_code`, `lane_ph`: a lane store's blocks and instructions in the
  code and their phase checks, from its two chunks;
- `HeapW`: the element's word (mapped, owned at no state, in a placed
  label's range, not the arena's counter, unmapped in private memory);
- `laneW_w2E`: `LaneW` at `W2` for a code predicate inside `CdC` whose
  chunks' pcs are off the write abort's, and the pc after a lane store's
  chunk too (`hend`);
- `laneW_w2`: `LaneW` at `W2` for `CdC`, its pcs and the pc after each of
  its chunks off the write abort's.
-/
import Spike.Lib.LowerX64.LaneC2
import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.UserAb
import Spike.Lib.X64AllocGAb
import Spike.Lib.LowerX64.NoSlotWr
import Spike.Lib.LowerX64.CallNodes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At cellOff okBlk CodeAt FStable bAddr mB eaddr_mB)
open Spike.Lib.X64.Rt (InstOk next_same nodeW_postO)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc)
open Spike.Lib.X64.AllocG (not_ab_after)

section Node

variable {exe : _root_.Executable} {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **`SFacts` at a heap word's load** `movq k(%b), %r` at the code's pc
(`hcode`), off the sites (`hok`), its next pc in its phase (`hph`), after
the switch: the word at the abstract state's address mapped for reading
and unmapped in private memory (`ha`). -/
theorem nodeW_sfacts_ldH {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.ldDir b k r, z)])
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc n.pc.toBitVec.toNat = true)
    (hph : ph (n.pc + Int64.ofNat z).toBitVec.toNat = ph n.pc.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) false ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI rfl hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc : CellAt s (X64.ldDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
    obtain ⟨hmr, hun⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_load_agrees hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s) (z := z)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.set (.low r .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown htk hO

/-- **`SFacts` at a heap word's store** `movq %r, k(%b)` at the code's pc,
as `nodeW_sfacts_ldH`: the word mapped for writing, unmapped in private
memory and owned at no state (`ha`). -/
theorem nodeW_sfacts_stH {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.stDir b k r, z)])
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc n.pc.toBitVec.toNat = true)
    (hph : ph (n.pc + Int64.ofNat z).toBitVec.toNat = ph n.pc.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧ ∀ (s : State) w, (⟨bAddr σ.regs b k, 8⟩, w) ∉ own s) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI rfl hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc : CellAt s (X64.stDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_store_agrees hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2 (.inl ⟨(next_same hI hpc hph _).1, hno s⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A heap word's load keeps the write abort's phase**: its pc off the
sites (`hok`), its next pc off the write abort's pcs (`hnx`). -/
theorem nodeW_ab_ldH {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.ldDir b k r, z)])
    (hok : okPc n.pc.toBitVec.toNat = true) (hnx : n.pc + Int64.ofNat z ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc : CellAt s (X64.ldDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_load_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => not_ab_after hpc hnx

/-- **A heap word's store keeps the write abort's phase**, as
`nodeW_ab_ldH`. -/
theorem nodeW_ab_stH {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.stDir b k r, z)])
    (hok : okPc n.pc.toBitVec.toNat = true) (hnx : n.pc + Int64.ofNat z ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc : CellAt s (X64.stDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSyscall_false_of_cellAt hc (by intro w w' h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact ⟨trivial, fun _ _ => not_ab_after hpc hnx⟩

/-- **A heap word's load writes nothing and is off a system call.** -/
theorem nodeW_noWr_ldH {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.ldDir b k r, z)])
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hc : CellAt s (X64.ldDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_load_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  exact ⟨⟨noWr_load hex, atSyscall_false_of_cellAt hc (by intro w w' h; cases h)⟩, fun _ h => h⟩

/-- **A heap word's store writes only its word and is off a system
call.** -/
theorem nodeW_wr_stH {n : ND} {b r : Reg64} {k : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(X64.stDir b k r, z)])
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none) :
    NodeW (fun s c => (∃ σ, n.J σ c ∧ F s.st.1 ∧ ∀ L, WrAt s L → L = ⟨bAddr σ.regs b k, 8⟩) ∧
      abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hc : CellAt s (X64.stDir b k r) z := (hcode s hs hn).cell0 rfl rfl hpc
  have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.X64.agrees_of_decls hdc _ _)
  exact ⟨⟨⟨σ, hJ, hD, fun L hL => wrAt_store hex hL⟩, atSyscall_false_of_cellAt hc (by intro w w' h; cases h)⟩,
    fun _ h => h⟩

end Node

/-! ## Blocks of the code predicate -/

section Blk

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A chunk of the code predicate is in the code.** -/
theorem codeAt_cdC {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {ra pc : Int64}
    {blk : List (Directive × Nat)} (h : CdC cells okPc ph lab ra pc blk) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc blk := by
  obtain ⟨-, L, j, off, hpc, hb, -⟩ := h
  intro s hs hn
  have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
  rwa [hI.labOk, hpc] at this

omit [Kraken.Executable.ValidLayout exe] in
/-- **The phase check of two blocks in a row**, the second's start in the
first's phase. -/
theorem blkPh_append {dd : Nat → Bool} {pc ra : Int64} {a b : List (Directive × Nat)}
    (ha : blkPh okPc ph dd lab pc ra a = true)
    (hb : blkPh okPc ph dd lab (pc + Int64.ofNat (a.map (·.2)).sum) ra b = true)
    (he : ph (pc + Int64.ofNat (a.map (·.2)).sum).toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · have hoff : cellOff (a ++ b) k = cellOff a k := by
      unfold cellOff; rw [List.take_append_of_le_length (by omega)]
    rw [hoff, List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have hoff : cellOff (a ++ b) (a.length + j) = (a.map (·.2)).sum + cellOff b j := by
      unfold cellOff
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.map_append,
        List.sum_append]
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [hoff, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Int64.ofNat_add, ← Int64.add_assoc]
    exact this

omit [Kraken.Executable.ValidLayout exe] in
/-- **A covered block without a branch keeps the write abort's phase**:
its code (`hcode`) passing the phase check (`hph`), none of its
instructions a branch (`hnt`), every next pc off the write abort's pcs
(`hnx`). -/
theorem blkW_abC {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true)
    (hnt : ∀ k (hk : k < blk.length) a, Spike.Lib.X64.classify blk[k].1 = some a → a.isTerm = false)
    (hnx : ∀ k < blk.length, n.pc + Int64.ofNat (cellOff blk (k + 1)) ∉ abPcs lab) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [← hI.labOk] at hph hnx ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) (n := n) hI.same hI.off hok hph
    (fun _ _ _ k hk h => absurd (hnt k hk _ h) (by decide)) (fun _ _ _ => rfl)
  refine blkW_abSt hcode hok hR hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) ?_
  intro σ c _ k hk a ha s' _ _ hpc' _
  rw [Spike.Lib.X64.AI.tgt_of_not_term (hnt k hk a ha)] at hpc'
  refine not_ab_of_pc ?_
  rw [hpc', Int64.add_assoc, ← Int64.ofNat_add, ← Spike.Lib.X64.cellOff_succ hk]
  exact hnx k hk

/-- No operand's load is a branch. -/
theorem getOp_noTerm {fr : Scc.Emit.X64.Frame} {t : Reg64} {o : Scc.IR.Operand} {l : List Scc.Emit.X64.Item}
    (hw : getOp fr t o = .ok l) {d : Directive} (hd : dirs l = [d]) :
    ∀ a, Spike.Lib.X64.classify d = some a → a.isTerm = false := by
  rcases getOp_cases hw with ⟨r, off, -, -, hl⟩ | ⟨v, -, hl⟩ <;> rw [hl] at hd <;>
    cases (List.cons.inj hd).1 <;> intro a ha
  · rw [show Spike.Lib.X64.classify (Spike.Lib.X64.AI.ld t .rbp (Int64.ofInt off)).toDir =
      some (Spike.Lib.X64.AI.ld t .rbp (Int64.ofInt off)) from rfl] at ha
    cases ha; rfl
  · simp [Scc.Emit.X64.i64, Scc.Emit.X64.op, Scc.Emit.X64.xr, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly] at ha
    subst ha; rfl

/-- A block none of whose instructions is a branch has no `ret`. -/
theorem noRet_of_noTerm {blk : List (Directive × Nat)}
    (h : ∀ k (hk : k < blk.length) a, Spike.Lib.X64.classify blk[k].1 = some a → a.isTerm = false) :
    noRetBlk blk = true := by
  unfold noRetBlk
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  split
  · rename_i heq
    exact absurd (h k hk _ heq) (by decide)
  · rfl

end Blk

/-! ## A lane store's two chunks -/

section Chunks

open Scc.Cert.Ph1X64 (runPhB runPhB_get blkPh_of_runPhB)

/-- **A lane store's code from its two chunks**: `B1`, the load, `B2` and
the store, each at its pc. -/
theorem lane_code {exe : _root_.Executable} {endPc pc i : Int64} {db dw : Directive} {off : Int}
    {z0 zL zt z1 z2 zS : Nat} (c1 : CdOf exe endPc pc [(db, z0), (X64.ldDir .rcx i .rax, zL), (stDir off, zt)])
    (c2 : CdOf exe endPc (pc + Int64.ofNat (z0 + zL + zt)) [(db, z1), (dw, z2), (X64.stDir .rcx i .rax, zS)]) :
    CdOf exe endPc pc [(db, z0)] ∧ CdOf exe endPc (pc + Int64.ofNat z0) [(X64.ldDir .rcx i .rax, zL)] ∧
      CdOf exe endPc (pc + Int64.ofNat z0 + Int64.ofNat zL) [(stDir off, zt), (db, z1), (dw, z2)] ∧
      CdOf exe endPc (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2))
        [(X64.stDir .rcx i .rax, zS)] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := cdOf_sub (pre := []) (blk := [(db, z0)]) (post := [_, _]) c1
    simp only [List.map_nil, List.sum_nil] at e
    simpa [Int64.add_zero] using e
  · have e := cdOf_sub (pre := [(db, z0)]) (blk := [_]) (post := [_]) c1
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at e
    exact e
  · have e1 := cdOf_sub (pre := [(db, z0), (_, zL)]) (blk := [_]) (post := []) c1
    have e2 := cdOf_sub (pre := []) (blk := [(db, z1), (dw, z2)]) (post := [_]) c2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at e1 e2
    have e := cdOf_append e1 (B := [(db, z1), (dw, z2)]) (by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] at e2 ⊢
      simpa [Int64.add_zero, Int64.add_assoc] using e2)
    simp only [Int64.ofNat_add, Int64.add_assoc, List.cons_append, List.nil_append] at e ⊢
    exact e
  · have e := cdOf_sub (pre := [(db, z1), (dw, z2)]) (blk := [_]) (post := []) c2
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
      Int64.add_assoc] at e ⊢
    exact e

/-- **A lane store's phases from its two chunks' run checks**: `B1`'s and
`B2`'s phase checks, the load's and the store's pcs off the sites with
their next pcs in their phases. -/
theorem lane_ph {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {pc ra i : Int64}
    {db dw : Directive} {off : Int} {z0 zL zt z1 z2 zS : Nat}
    (hr1 : runPhB okPc ph lab pc ra [(db, z0), (X64.ldDir .rcx i .rax, zL), (stDir off, zt)] = true)
    (hr2 : runPhB okPc ph lab (pc + Int64.ofNat (z0 + zL + zt)) ra
      [(db, z1), (dw, z2), (X64.stDir .rcx i .rax, zS)] = true)
    (hcb : (Spike.Lib.X64.classify db).isSome = true) (hcw : (Spike.Lib.X64.classify dw).isSome = true) :
    blkPh okPc ph (fun _ => false) lab pc ra [(db, z0)] = true ∧
      okPc (pc + Int64.ofNat z0).toBitVec.toNat = true ∧
      ph (pc + Int64.ofNat z0 + Int64.ofNat zL).toBitVec.toNat = ph (pc + Int64.ofNat z0).toBitVec.toNat ∧
      blkPh okPc ph (fun _ => false) lab (pc + Int64.ofNat z0 + Int64.ofNat zL) ra
        [(stDir off, zt), (db, z1), (dw, z2)] = true ∧
      okPc (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)).toBitVec.toNat = true ∧
      ph (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2) + Int64.ofNat zS).toBitVec.toNat =
        ph (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)).toBitVec.toNat := by
  have b1 := blkPh_of_runPhB (xs := []) (ys := [(db, z0)]) (zs := [_, _]) hr1 (by simpa using hcb)
  have bs := blkPh_of_runPhB (xs := [(db, z0), (_, zL)]) (ys := [(stDir off, zt)]) (zs := []) hr1
    (by simp; rfl)
  have br := blkPh_of_runPhB (xs := []) (ys := [(db, z1), (dw, z2)]) (zs := [_]) hr2 (by simp [hcb, hcw])
  obtain ⟨o1, p1, t1⟩ := runPhB_get hr1 (k := 1) (by simp)
  obtain ⟨-, p2, t2⟩ := runPhB_get hr1 (k := 2) (by simp)
  obtain ⟨o3, p3, t3⟩ := runPhB_get hr2 (k := 2) (by simp)
  have t1' := t1 _ (List.mem_singleton_self _)
  have t2' := t2 _ (List.mem_singleton_self _)
  have t3' := t3 _ (List.mem_singleton_self _)
  simp only [cellOff, List.take, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    List.length_nil, List.length_cons, List.take_succ_cons, List.take_zero, List.getElem_cons_succ,
    List.getElem_cons_zero, List.cons_append, List.nil_append, List.append_nil] at b1 bs br o1 p1 t1' p2 t2' o3 p3 t3'
  simp only [Int64.ofNat_add, Int64.add_assoc] at *
  refine ⟨by simpa [Int64.add_zero] using b1, o1, by rw [t1', p1], ?_, o3, by rw [t3', p3]⟩
  have := blkPh_append (a := [(stDir off, zt)]) (b := [(db, z1), (dw, z2)]) bs
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.add_assoc]
        simpa [Int64.add_zero, Int64.add_assoc] using br)
    (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.add_assoc]
        rw [t2', p2])
  simpa using this

end Chunks

/-! ## A lane store's states inside `W2` -/

/-- **The element's word at a lane store** `A`: mapped for reading and
writing in the loaded kernel state, owned at no state, a word of a placed
label (an arena write `ArenaW` allows), not the arena's counter, and
unmapped in the private memory of the frame condition's states. -/
def HeapW (Λ : Scc.Sem.Layout) (own : Own) (ar : Spike.Lib.Arena) (lbl : Lbl) (lsize : Lsize)
    (F : MachineData → Prop) (A : BitVec 64) : Prop :=
  Kernel.mapped (K0 Λ) false ⟨A, 8⟩ = true ∧ Kernel.mapped (K0 Λ) true ⟨A, 8⟩ = true ∧
    (∀ (s : State) w, (⟨A, 8⟩, w) ∉ own s) ∧ (∃ l b, lbl l = some b ∧ (lrange lsize l b).contains A.toNat) ∧
    (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc ∧ ∀ m, F m → Mem.loadInt m.dmem A 8 = none

section Lane

open Spike.Lib.X64 (arun ownStep)
open Spike.Lib.X64.Flow.XchgSeg (xsNL xsNH xsNS)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Spike.Lib.X64.AllocG (dumN)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.Form (opdVal)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Spike.Lib.Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A lane store's nodes inside `W2`** at the frames `fs` (`LaneW` at
`W2` for a code predicate `Cd` inside `CdC`, `hcd`): as `laneW_w2`, the pcs
of `Cd`'s chunks off the write abort's (`hnab`) and the pc right after a
chunk ending with a lane store's `movq %rax, disp(%rcx)` too (`hend`). -/
theorem laneW_w2E {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hcd : ∀ pc' blk, Cd pc' blk → CdC cells okPc ph lab ra pc' blk)
    (hnab : ∀ pc' blk, Cd pc' blk → ∀ k < blk.length, pc' + Int64.ofNat (cellOff blk k) ∉ abPcs lab)
    (hend : ∀ pc' blk (i : Int64) z, Cd pc' (blk ++ [(X64.stDir .rcx i .rax, z)]) →
      pc' + Int64.ofNat (cellOff blk blk.length + z) ∉ abPcs lab)
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (ms : Spike.Lib.MemSide isa) {pc : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand}
    {J : Spike.Lib.X64.AS → Ctl → Prop} {P : Spike.Lib.X64.AS → Ctl → Ctl → Prop}
    (hJp : ∀ σ c, J σ c → SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c)
    (hJ : ∀ σ c, J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs)
    (hP1 : ∀ σ c c1, J σ c → P σ c c1 → SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c1 ∧
      (∀ off, rsOf fr d = some off → ∀ v, SlotRepAt Λ.imms lbl (rsOf fr) (Spike.Lib.upd σ.slot off v) c1) ∧
      (fs = [] → ∀ a, c1.term ≠ .ret a) ∧ FrOk2 c1 fs)
    (hadr : ∀ σ c c1, J σ c → P σ c c1 → (-(2 ^ 62) ≤ a.disp ∧ a.disp ≤ 2 ^ 62) ∧
      (∀ off, rsOf fr d = some off → ∀ r, opdVal (rsOf fr) (Spike.Lib.upd σ.slot off r) (.reg a.base) =
        opdVal (rsOf fr) σ.slot (.reg a.base)) ∧
      ∀ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg a.base) = some vb.toNat →
        HeapW Λ own ar lbl lsize F (vb + BitVec.ofInt 64 a.disp)) :
    LaneW Cd (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
      K exe endPc R F ms lbl fr pc d a w J P := by
  intro lb lw off z0 zL zt z1 z2 zS hb hw hoff hC1 hC2
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  obtain ⟨dw, hdw⟩ := dirs_getOp hw
  have hz0 : [z0].length = (dirs lb).length := by rw [hdb]; rfl
  have hz1 : [z1].length = (dirs lb).length := by rw [hdb]; rfl
  have hz2 : [z2].length = (dirs lw).length := by rw [hdw]; rfl
  have hoK : (oB fr).kill .rax = oB fr := by simp [oB, Spike.Lib.X64.SO.kill, Spike.Lib.rm]
  let L := (_root_.Executable.labels exe).label
  let i := Int64.ofInt a.disp
  obtain ⟨hok1, hB1⟩ := xchg_b1 hf h1 hb L pc hz0
  obtain ⟨hok2, hB2⟩ := xchg_b2 hf h1 hoff hb hw L (pc + Int64.ofNat z0 + Int64.ofNat zL) (zt := zt) hz1 hz2
  have e1 : (dirs lb).zip [z0] = [(db, z0)] := by rw [hdb]; rfl
  have e2 : (stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2]) =
      [(stDir off, zt), (db, z1), (dw, z2)] := by rw [hdb, hdw]; rfl
  rw [e1] at hok1 hB1 ⊢
  rw [e2] at hok2 hB2 ⊢
  rw [hdb] at hC1
  rw [hdb, hdw] at hC2
  simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right] at hC1 hC2
  have hn1 := hnab _ _ hC1
  have hn2 := hnab _ _ hC2
  have hnS := hend _ [(db, z1), (dw, z2)] _ zS hC2
  replace hC1 := hcd _ _ hC1
  replace hC2 := hcd _ _ hC2
  obtain ⟨hcB1, hcL, hcB2, hcS⟩ := lane_code (codeAt_cdC hI hC1) (codeAt_cdC hI hC2)
  have hcb : (Spike.Lib.X64.classify db).isSome = true := classify_of_okBlk hok1 _ (List.mem_singleton_self _)
  have hcw : (Spike.Lib.X64.classify dw).isSome = true := classify_of_okBlk hok2 (dw, z2) (by simp)
  have hr1 := hC1.2.choose_spec.choose_spec.choose_spec.2.2
  have hr2 := hC2.2.choose_spec.choose_spec.choose_spec.2.2
  obtain ⟨hph1, hokL, hphL, hph2, hokS, hphS⟩ := lane_ph hr1 hr2 hcb hcw
  have nxB1 : ∀ k < [(db, z0)].length, pc + Int64.ofNat (cellOff [(db, z0)] (k + 1)) ∉ abPcs lab := by
    intro k hk
    obtain rfl : k = 0 := by simp at hk; omega
    simpa [cellOff] using hn1 1 (by simp)
  have nxL : pc + Int64.ofNat z0 + Int64.ofNat zL ∉ abPcs lab := by
    simpa [cellOff, Int64.ofNat_add, Int64.add_assoc] using hn1 2 (by simp)
  have nxB2 : ∀ k < [(stDir off, zt), (db, z1), (dw, z2)].length,
      pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (cellOff [(stDir off, zt), (db, z1), (dw, z2)] (k + 1)) ∉
        abPcs lab := by
    intro k hk
    have hk3 : k < 3 := by simpa using hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
    · simpa [cellOff, Int64.ofNat_add, Int64.add_assoc] using hn2 0 (by simp)
    · simpa [cellOff, Int64.ofNat_add, Int64.add_assoc] using hn2 1 (by simp)
    · simpa [cellOff, Int64.ofNat_add, Int64.add_assoc] using hn2 2 (by simp)
  have nxS : pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2) + Int64.ofNat zS ∉ abPcs lab := by
    simpa [cellOff, Int64.ofNat_add, Int64.add_assoc] using hnS
  -- the element's word at the load
  have hA1 : ∀ σ0 c0 c1, J σ0 c0 → P σ0 c0 c1 →
      HeapW Λ own ar lbl lsize F (bAddr (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ.regs .rcx i) := by
    intro σ0 c0 c1 hJ0 hP0
    obtain ⟨hdisp, -, hk⟩ := hadr σ0 c0 c1 hJ0 hP0
    have hdi : (Int64.ofInt a.disp).toInt = a.disp := toInt_ofInt_small hdisp.1 hdisp.2
    obtain ⟨vb, hvb, he1⟩ := hB1 σ0
    have hr1 : (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ.regs.get64 .rcx = vb := by
      rw [he1]; simp
    have hbA : bAddr (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ.regs .rcx i = vb + BitVec.ofInt 64 a.disp := by
      simp only [bAddr, i, hdi, hr1]
    rw [hbA]
    exact hk vb hvb
  -- the store's address and slots after `B2`
  have hAS : ∀ σ0 c0 c1 (r : BitVec 64), J σ0 c0 → P σ0 c0 c1 →
      bAddr (arun L [(stDir off, zt), (db, z1), (dw, z2)] ⟨pc + Int64.ofNat z0 + Int64.ofNat zL, (oB fr).kill .rax,
        ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ⟩).σ.regs .rcx i =
        bAddr (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ.regs .rcx i ∧
      (arun L [(stDir off, zt), (db, z1), (dw, z2)] ⟨pc + Int64.ofNat z0 + Int64.ofNat zL, (oB fr).kill .rax,
        ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ⟩).σ.slot = Spike.Lib.upd σ0.slot off r := by
    intro σ0 c0 c1 r hJ0 hP0
    obtain ⟨hdisp, hbase, -⟩ := hadr σ0 c0 c1 hJ0 hP0
    have hdi : (Int64.ofInt a.disp).toInt = a.disp := toInt_ofInt_small hdisp.1 hdisp.2
    obtain ⟨vb, hvb, he1⟩ := hB1 σ0
    have hr1 : (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ.regs.get64 .rcx = vb := by
      rw [he1]; simp
    rw [hoK]
    obtain ⟨vb', vw, hvb', -, he2⟩ := hB2 (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ)
    have hsl1 : (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ).slot = σ0.slot := by rw [he1]; rfl
    have hra : (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ).regs.get64 .rax = r := by
      simp [ownStep]
    rw [hsl1, hra] at hvb' he2
    have hvv : vb' = vb :=
      BitVec.eq_of_toNat_eq (Option.some.inj (hvb'.symm.trans ((hbase off hoff r).trans hvb)))
    rw [hvv] at he2
    rw [he2]
    refine ⟨?_, rfl⟩
    simp only [bAddr, i, hdi, hr1, Reg64s.get64_set64]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `B1`
    have hnt1 : ∀ k (hk : k < [(db, z0)].length) a, Spike.Lib.X64.classify [(db, z0)][k].1 = some a →
        a.isTerm = false := by
      intro k hk a ha
      obtain rfl : k = 0 := by simp at hk; omega
      exact getOp_noTerm hb hdb a ha
    exact blkW_w2BP (n := ⟨pc, oB fr, J⟩) hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcB1 hph1 hok1
      (noRet_of_noTerm hnt1) (blkW_abC hI hcB1 hok1 hR hlo hhi hph1 hnt1 nxB1) (blkW_placedS hFS hJp hrs hfp rfl) hJ
  · -- the load's node
    have haL : ∀ σ c m, (Spike.Lib.X64.Flow.XchgSeg.xsNL L [(db, z0)] pc (pc + Int64.ofNat z0) (oB fr) (oB fr)
        J P).J σ c → F m → HeapW Λ own ar lbl lsize F (bAddr σ.regs .rcx i) := by
      rintro σ c m ⟨σ0, c0, hJ0, hP0, rfl⟩ -
      exact hA1 σ0 c0 c hJ0 hP0
    have hS := nodeW_sfacts_ldH (n := dumN (Spike.Lib.X64.Flow.XchgSeg.xsNL L [(db, z0)] pc (pc + Int64.ofNat z0)
      (oB fr) (oB fr) J P)) (Λ := Λ) (rS := rS) (lbl := lbl) hI hcL (fun _ _ h => h.1 ▸ cfacts_c0) hokL hphL
      hR hR8 hl hh hsub hFO (by
        rintro σ c m ⟨-, c', hJ'⟩ hm
        have h := haL σ c' m hJ' hm
        exact ⟨h.1, h.2.2.2.2.2 m hm⟩)
    have hab := nodeW_ab_ldH (R := R) (F := F)
      (n := Spike.Lib.X64.Flow.XchgSeg.xsNL L [(db, z0)] pc (pc + Int64.ofNat z0) (oB fr) (oB fr) J P) hI hcL hokL nxL
      fun σ c m h hm => (haL σ c m h hm).2.2.2.2.2 m hm
    have hpl := nodeW_placedS (exe := exe) (endPc := endPc) (R := R) (F := F) (Λ := Λ) (lbl := lbl) (fs := fs)
      (n := Spike.Lib.X64.Flow.XchgSeg.xsNL L [(db, z0)] pc (pc + Int64.ofNat z0) (oB fr) (oB fr) J P)
      (by
        rintro σ c ⟨σ0, c0, hJ0, hP0, rfl⟩
        obtain ⟨_, _, he1⟩ := hB1 σ0
        rw [he1]
        exact (hP1 σ0 c0 c hJ0 hP0).1) hrs hfp
    have hnw := nodeW_noWr_ldH (R := R) (F := F)
      (n := Spike.Lib.X64.Flow.XchgSeg.xsNL L [(db, z0)] pc (pc + Int64.ofNat z0) (oB fr) (oB fr) J P) hcL
      fun σ c m h hm => (haL σ c m h hm).2.2.2.2.2 m hm
    refine NodeW.w2 hp hS (Spike.Lib.X64.AllocG.NodeW.imp (Spike.Lib.X64.AllocG.NodeW.imp
      (W := fun s c => AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c fs) hab hpl fun _ _ h1 h2 => ⟨h1, h2⟩) hnw
      fun s c h1 h2 =>
        ⟨h1.1, h1.2, fun _ _ _ _ => wrOkA_of_noWr h2.1, fun h => absurd h (by rw [h2.2]; decide)⟩) ?_
    rintro σ c ⟨σ0, c0, hJ0, hP0, -⟩
    exact (hP1 σ0 c0 c hJ0 hP0).2.2
  · -- `B2`
    have hok : okBlk (-(fr.size : Int)) 16 ((oB fr).kill .rax) [(stDir off, zt), (db, z1), (dw, z2)] = true := by
      rw [hoK]; exact hok2
    have hnt2 : ∀ k (hk : k < [(stDir off, zt), (db, z1), (dw, z2)].length) a,
        Spike.Lib.X64.classify [(stDir off, zt), (db, z1), (dw, z2)][k].1 = some a → a.isTerm = false := by
      intro k hk a ha
      have hk3 : k < 3 := by simpa using hk
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl
      · change Spike.Lib.X64.classify (stDir off) = some a at ha
        rw [show Spike.Lib.X64.classify (stDir off) =
          some (Spike.Lib.X64.AI.st .rbp (Int64.ofInt off) .rax) from rfl] at ha
        cases ha; rfl
      · exact getOp_noTerm hb hdb a ha
      · exact getOp_noTerm hw hdw a ha
    have hnw2 : noSlotWr [(db, z1), (dw, z2)] = true := by
      have a1 := noSlotWrD_getOp hb
      have a2 := noSlotWrD_getOp hw
      rw [hdb] at a1
      rw [hdw] at a2
      rw [noSlotWr_eq]
      show noSlotWrD ([db] ++ [dw]) = true
      rw [noSlotWrD_append, a1, a2]; rfl
    have hpl : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F
        (Spike.Lib.X64.Flow.XchgSeg.xsNH ms lbl L [(db, z0)] pc (pc + Int64.ofNat z0) zL (oB fr) (oB fr) .rax .rcx i
          J P) [(stDir off, zt), (db, z1), (dw, z2)] := by
      rintro s σ c - - - - - hF ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, rfl⟩ k hk m hA' hD
      refine ⟨placedS_of_abs (s := { s with st := (m, _) }) hA' ?_ hrs (hfp _ (hFS _ _ hF hD)).choose_spec,
        fun _ h => h⟩
      obtain ⟨_, _, he1⟩ := hB1 σ0
      have hsl1 : (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ).slot = σ0.slot := by rw [he1]; rfl
      have hra : (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ).regs.get64 .rax = r := by
        simp [ownStep]
      obtain ⟨hs1, hs2, -, -⟩ := hP1 σ0 c0 c1 hJ0 hP0
      cases k with
      | zero =>
        show SlotRepAt _ _ _ (ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ).slot _
        rw [hsl1]; exact hs1
      | succ k =>
        show SlotRepAt _ _ _ (arun L (List.take (k + 1) [(stDir off, zt), (db, z1), (dw, z2)])
          ⟨pc + Int64.ofNat z0 + Int64.ofNat zL, (oB fr).kill .rax,
            ownStep .rax r (arun L [(db, z0)] ⟨pc, oB fr, σ0⟩).σ⟩).σ.slot _
        have htk : noSlotWr (List.take k [(db, z1), (dw, z2)]) = true := by
          simp only [noSlotWr, List.all_eq_true] at hnw2 ⊢
          exact fun x hx => hnw2 x (List.mem_of_mem_take hx)
        rw [hoK, List.take_succ_cons, show ∀ l : List (Directive × Nat), (stDir off, zt) :: l = [(stDir off, zt)] ++ l
          from fun _ => rfl, arun_append, arun_stDir hf h1 hoff, arun_slot_noSlotWr L htk]
        simp only
        rw [hsl1, hra]
        exact hs2 off hoff r
    exact blkW_w2BP hI hR hR8 hlo hhi hl hh hsub hfit hFO hp hcB2 hph2 hok (noRet_of_noTerm hnt2)
      (blkW_abC hI hcB2 hok hR hlo hhi hph2 hnt2 nxB2) hpl
      (by rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, -, rfl⟩; exact (hP1 σ0 c0 c1 hJ0 hP0).2.2)
  · -- the store's node
    have haS : ∀ σ c m, (Spike.Lib.X64.Flow.XchgSeg.xsNS ms lbl L [(db, z0)] [(stDir off, zt), (db, z1), (dw, z2)]
        pc (pc + Int64.ofNat z0) (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr)
        (oB fr) (oB fr) .rax .rcx i J P).J σ c → F m → HeapW Λ own ar lbl lsize F (bAddr σ.regs .rcx i) := by
      rintro σ c m ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, -⟩ -
      rw [(hAS σ0 c0 c1 r hJ0 hP0).1]
      exact hA1 σ0 c0 c1 hJ0 hP0
    have hS := nodeW_sfacts_stH (n := dumN (Spike.Lib.X64.Flow.XchgSeg.xsNS ms lbl L [(db, z0)]
      [(stDir off, zt), (db, z1), (dw, z2)] pc (pc + Int64.ofNat z0)
      (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx i J P))
      (Λ := Λ) (rS := rS) (lbl := lbl) hI hcS (fun _ _ h => h.1 ▸ cfacts_c0) hokS hphS
      hR hR8 hl hh hsub hFO (by
        rintro σ c m ⟨-, c', hJ'⟩ hm
        have h := haS σ c' m hJ' hm
        exact ⟨h.2.1, h.2.2.2.2.2 m hm, h.2.2.1⟩)
    have hab := nodeW_ab_stH (R := R) (F := F) (n := Spike.Lib.X64.Flow.XchgSeg.xsNS ms lbl L [(db, z0)]
      [(stDir off, zt), (db, z1), (dw, z2)] pc (pc + Int64.ofNat z0)
      (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx i J P)
      hI hcS hokS nxS fun σ c m h hm => (haS σ c m h hm).2.2.2.2.2 m hm
    have hpl := nodeW_placedS (exe := exe) (endPc := endPc) (R := R) (F := F) (Λ := Λ) (lbl := lbl) (fs := fs)
      (n := Spike.Lib.X64.Flow.XchgSeg.xsNS ms lbl L [(db, z0)]
      [(stDir off, zt), (db, z1), (dw, z2)] pc (pc + Int64.ofNat z0)
      (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx i J P)
      (by
        rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, rfl⟩
        rw [(hAS σ0 c0 c1 r hJ0 hP0).2]
        exact (hP1 σ0 c0 c1 hJ0 hP0).2.1 off hoff r) hrs hfp
    have hwr := nodeW_wr_stH (R := R) (F := F) (n := Spike.Lib.X64.Flow.XchgSeg.xsNS ms lbl L [(db, z0)]
      [(stDir off, zt), (db, z1), (dw, z2)] pc (pc + Int64.ofNat z0)
      (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx i J P)
      hcS fun σ c m h hm => (haS σ c m h hm).2.2.2.2.2 m hm
    refine NodeW.w2 hp hS (Spike.Lib.X64.AllocG.NodeW.imp (Spike.Lib.X64.AllocG.NodeW.imp
      (W := fun s c => AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c fs) hab hpl fun _ _ h1 h2 => ⟨h1, h2⟩) hwr
      fun s c h1 h2 => ⟨h1.1, h1.2, fun _ _ _ _ => ?_, fun h => absurd h (by rw [h2.2]; decide)⟩) ?_
    · obtain ⟨σ, hJn, hFm, hw⟩ := h2.1
      have hh := haS σ c s.st.1 hJn hFm
      exact ⟨fun L hL => by rw [hw L hL]; exact .inr (.inr (.inl hh.2.2.2.1)),
        fun hL => (hh.2.2.2.2.1 (hw _ hL).symm).elim⟩
    · rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, -, rfl⟩
      exact (hP1 σ0 c0 c1 hJ0 hP0).2.2

/-- **A lane store's nodes inside `W2`** at the frames `fs` (`LaneW` at
`W2` for the code predicate `CdC`): at the lane's node `⟨pc, oB fr, J⟩`,
whose controls are placed in the slot file (`hJp`) and exclude `main`'s
`ret` and `ZBad` (`hJ`); at its source relation `P` the exchange site's
control placed in the slot file, also with `d`'s slot updated, and
excluding `main`'s `ret` and `ZBad` (`hP1`), the displacement small, the
base's value not moved by `d`'s slot and the element's word a heap word
(`HeapW`, `hadr`); the code predicate's pcs off the write abort's
(`hnab`); the phase `WriteAb.Ab`. -/
theorem laneW_w2 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra : Int64}
    (hnab : ∀ pc' blk, CdC cells okPc ph lab ra pc' blk → ∀ k ≤ blk.length,
      pc' + Int64.ofNat (cellOff blk k) ∉ abPcs lab)
    (hrs : ∀ r k, rsOf fr r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (ms : Spike.Lib.MemSide isa) {pc : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand}
    {J : Spike.Lib.X64.AS → Ctl → Prop} {P : Spike.Lib.X64.AS → Ctl → Ctl → Prop}
    (hJp : ∀ σ c, J σ c → SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c)
    (hJ : ∀ σ c, J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs)
    (hP1 : ∀ σ c c1, J σ c → P σ c c1 → SlotRepAt Λ.imms lbl (rsOf fr) σ.slot c1 ∧
      (∀ off, rsOf fr d = some off → ∀ v, SlotRepAt Λ.imms lbl (rsOf fr) (Spike.Lib.upd σ.slot off v) c1) ∧
      (fs = [] → ∀ a, c1.term ≠ .ret a) ∧ FrOk2 c1 fs)
    (hadr : ∀ σ c c1, J σ c → P σ c c1 → (-(2 ^ 62) ≤ a.disp ∧ a.disp ≤ 2 ^ 62) ∧
      (∀ off, rsOf fr d = some off → ∀ r, opdVal (rsOf fr) (Spike.Lib.upd σ.slot off r) (.reg a.base) =
        opdVal (rsOf fr) σ.slot (.reg a.base)) ∧
      ∀ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg a.base) = some vb.toNat →
        HeapW Λ own ar lbl lsize F (vb + BitVec.ofInt 64 a.disp)) :
    LaneW (CdC cells okPc ph lab ra) (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
      K exe endPc R F ms lbl fr pc d a w J P :=
  laneW_w2E hI hf h1 hR hR8 hlo hhi hl hh hsub hfit hFO hFS hp (fun _ _ h => h)
    (fun pc' blk h k hk => hnab pc' blk h k (Nat.le_of_lt hk))
    (fun pc' blk i z h => by
      have := hnab _ _ h (blk.length + 1) (by simp)
      rwa [show cellOff (blk ++ [(X64.stDir .rcx i .rax, z)]) (blk.length + 1) = cellOff blk blk.length + z by
        simp [cellOff, List.take_of_length_le]] at this)
    hrs hfp ms hJp hJ hP1 hadr

end Lane

/--
info: 'Spike.Lib.LowerX64.laneW_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneW_w2

/--
info: 'Spike.Lib.LowerX64.laneW_w2E' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneW_w2E

/--
info: 'Spike.Lib.LowerX64.lane_ph' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms lane_ph

end Spike.Lib.LowerX64
