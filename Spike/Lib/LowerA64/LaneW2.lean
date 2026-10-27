/-
**A lane store's nodes inside `W2`** (AArch64): `LaneW`
(`Spike/Lib/LowerA64/LaneSeg.lean`) at `W2` (`Spike/Lib/LowerA64/SFactsA2.lean`)
for the code predicate `CdC`, as `Spike/Lib/LowerX64/LaneW2.lean`.

The exchange's load (`LdAt`) and store (`StAt`) of the element's word are
not covered blocks; their nodes' facts come from their events at the
element's word, which is mapped, owned at no state, in a placed label's
range and not the arena's counter. The blocks `B1` and `B2` are at their
code (`B2` spans both of the lane's chunks), so their facts come from
`CodeAt` (`blkW_postO'`, `blkW_noWr'`, `blkW_noSys'`, `blkW_w2BP'`).

- `nodeW_sfacts_ldH`, `nodeW_sfacts_stH`: `SFacts` at a load or store of a
  heap word at the code's pc;
- `nodeW_ab_ldH`, `nodeW_ab_stH`: the write abort's phase kept there;
- `nodeW_noWr_ldH`, `nodeW_wr_stH`: the load writes nothing and is off a
  system call; the store writes only its word;
- `blkW_postO'`, `blkW_noWr'`, `blkW_noSys'`, `blkW_w2BP'`: the covered
  block facts at a block's code;
- `blkPh_append`, `blkW_abC`, `noTerm_of_okBlk_snoc`: phase checks of
  consecutive blocks, the write abort's phase kept along a covered block, a
  covered block's instructions before a covered one not branches;
- `ldrOff_acc`, `strOff_acc`, `aiTgts_noTerm`, `okBlk_pre_bl`: the
  exchange's accesses neither covered nor system calls, a covered
  non-branch's target, an access's prefix covered before a call;
- `nab_snoc`: a chunk's pcs off the write abort's, and the pc right after it;
- `laneW_w2E`: `LaneW` at `W2` for a code predicate inside `CdC` whose
  chunks' pcs are off the write abort's, and the pc after a lane store's
  chunk too (`hend`);
- `laneW_w2`: `LaneW` at `W2` for `CdC`, the element's word a `HeapW`
  (`Spike/Lib/LowerA64/HeapW.lean`).
-/
import Spike.Lib.LowerA64.LaneSeg
import Spike.Lib.LowerA64.W2Body
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.A64AllocGAb
import Spike.Lib.LowerA64.NoSlotWr
import Spike.Lib.LowerA64.HeapW

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable LdAt StAt agrees_of_decls)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk next_same nodeW_postO)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.WriteAb (Ab abPcs not_ab_of_pc)
open Spike.Lib.A64.AllocG (not_ab_after)

section Node

variable {exe : _root_.Executable} {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **`SFacts` at a heap word's load** `d` into `Xt` at `ad` (`LdAt`, not a
system call) at the code's pc (`hcode`), off the sites (`hok`), its next
pc in its phase (`hph`), after the take: the word at the abstract state's
address mapped for reading and unmapped in private memory (`ha`). -/
theorem nodeW_sfacts_ldH {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : LdAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc n.pc.toBitVec.toNat = true)
    (hph : ph (n.pc + Int64.ofNat 4).toBitVec.toNat = ph n.pc.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) false ⟨ad σ.regs, 8⟩ = true ∧
      Mem.loadInt m.dmem (ad σ.regs) 8 = none) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI rfl hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    obtain ⟨hmr, hun⟩ := ha σ c s.st.1 hJ hD
    have hex := hd s _ hc (by rw [hA.regs]) hun (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown, htk⟩ := load_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := fun v => { s.st.1 with regs := s.st.1.regs.setRegOrZr (.low (.reg t) .W64) (v.setWidth 64) })
      hmr (fun _ => (next_same hI hpc hph _).2) (fun _ => (next_same hI hpc hph _).1)
    exact sfacts_ev (hC σ c hJ) hP hc hns hex hT' hown htk hO

/-- **`SFacts` at a heap word's store** `d` of `Xt` at `ad` (`StAt`), as
`nodeW_sfacts_ldH`: the word mapped for writing, unmapped in private memory
and owned at no state (`ha`). -/
theorem nodeW_sfacts_stH {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : StAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c) (hok : okPc n.pc.toBitVec.toNat = true)
    (hph : ph (n.pc + Int64.ofNat 4).toBitVec.toNat = ph n.pc.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨ad σ.regs, 8⟩ = true ∧
      Mem.loadInt m.dmem (ad σ.regs) 8 = none ∧ ∀ (s : State) w, (⟨ad σ.regs, 8⟩, w) ∉ own s) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI rfl hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have hex := hd s _ hc (by rw [hA.regs]) hun (agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2 (.inl ⟨(next_same hI hpc hph _).1, hno s⟩)
    exact sfacts_ev (hC σ c hJ) hP hc hns hex hT' hown' htk hO

/-- **A heap word's load keeps the write abort's phase**: its pc off the
sites (`hok`), its next pc off the write abort's pcs (`hnx`). -/
theorem nodeW_ab_ldH {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : LdAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hok : okPc n.pc.toBitVec.toNat = true) (hnx : n.pc + Int64.ofNat 4 ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (ad σ.regs) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hex := hd s _ hc (by rw [hA.regs]) (ha σ c s.st.1 hJ hD) (agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc hns) fun t ht => ?_, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact fun _ _ => not_ab_after hpc hnx

/-- **A heap word's store keeps the write abort's phase**, as
`nodeW_ab_ldH`. -/
theorem nodeW_ab_stH {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : StAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hok : okPc n.pc.toBitVec.toNat = true) (hnx : n.pc + Int64.ofNat 4 ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (ad σ.regs) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hex := hd s _ hc (by rw [hA.regs]) (ha σ c s.st.1 hJ hD) (agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc hns) fun t ht => ?_, fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact ⟨trivial, fun _ _ => not_ab_after hpc hnx⟩

/-- **A heap word's load writes nothing and is off a system call.** -/
theorem nodeW_noWr_ldH {n : ND} {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : LdAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (ad σ.regs) 8 = none) :
    NodeW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hex := hd s _ hc (by rw [hA.regs]) (ha σ c s.st.1 hJ hD) (agrees_of_decls hdc _ _)
  exact ⟨⟨noWr_load hex, atSvc_false_of_cellAt hc hns⟩, fun _ h => h⟩

/-- **A heap word's store writes only its word and is off a system
call.** -/
theorem nodeW_wr_stH {n : ND} {d : Directive} {t : XReg} {ad : Reg64s → BitVec 64} (hd : StAt d t ad)
    (hns : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (ad σ.regs) 8 = none) :
    NodeW (fun s c => (∃ σ, n.J σ c ∧ F s.st.1 ∧ ∀ L, WrAt s L → L = ⟨ad σ.regs, 8⟩) ∧
      abi.atSys s = false) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  have hc : CellAt s d 4 := (hcode s hs hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  have hex := hd s _ hc (by rw [hA.regs]) (ha σ c s.st.1 hJ hD) (agrees_of_decls hdc _ _)
  exact ⟨⟨⟨σ, hJ, hD, fun L hL => wrAt_store hex hL⟩, atSvc_false_of_cellAt hc hns⟩, fun _ h => h⟩

end Node

/-! ## Covered blocks at their code -/

section Blk

variable {exe : _root_.Executable} {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **`blkW_postO` at a block's code** (`hcode`) rather than its
`blockAt` placement. -/
theorem blkW_postO' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hph : blkPh okPc ph dead lab n.pc ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, Spike.Lib.A64.Flow.classify blk[k] =
      some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n blk := by
  rw [← hI.labOk] at hph hret hdead
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  refine blkW_sfacts hcode hok hR hal hlo hhi hC hpc hph' fun s m hF hD hc k hk s' hm _ _ => ?_
  subst hm
  exact Spike.Lib.A64.Rt.owned_off hR (by omega) hl hh hsub
    (Spike.Lib.A64.Flow.Ret0.stackOff_stable hfit _ _ (hFO _ hF) hD) hc

/-- **A covered block's states write nothing** (`blkW_noWr` at the block's
code `hcode`). -/
theorem blkW_noWr' {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) :
    BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk := by
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

/-- **A covered block's states are off a system call** (`blkW_noSys` at
the block's code `hcode`). -/
theorem blkW_noSys' {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) :
    BlkW (fun s _ => abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m _ _
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨a, hca, -, -⟩ := Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label
    (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  refine Scc.Sem.A64.atSvc_false_of_cellAt hc fun imm h => ?_
  cases a <;> (try simp only [Spike.Lib.A64.Flow.AI.toDir] at h) <;> (try cases h)
  exact absurd (hreg _ _ rfl) (by simp [Spike.Lib.A64.Flow.RegOnly])

variable {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt Ab' : State → Prop} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A covered block at its code without a `ret` is inside `W2`** at the
frames `fs`, its states placed (`hP`): `blkW_w2BP` at the block's code
(`hcode`) rather than its `blockAt` placement. -/
theorem blkW_w2BP' {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {lo hi : Int}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS Spike.Lib.LowerNode.ZBad p) {n : ND}
    {ra : Int64} {blk : List Directive}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true) (hok : okBlk lo hi n.o blk = true)
    (hnr : noRetBlk blk = true)
    (hab : BlkW (fun s _ => AbSt μ Ab' s) (fun _ _ => False) exe endPc R F n blk)
    (hP : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F n blk)
    (hJ : ∀ σ c, n.J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ Spike.Lib.LowerNode.FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab' lbl lsize s c fs) K exe endPc R F n blk := by
  have hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (Spike.Lib.A64.AllocG.dumN n) blk :=
    blkW_postO' (n := Spike.Lib.A64.AllocG.dumN n) (dead := fun _ => false) (ra := ra) hI hcode hok hR
      hal hlo hhi (fun _ _ h => h.1 ▸ Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0) hph
      (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO
  have hW : BlkW (fun s _ => ∀ L, ¬ WrAt s L) (fun _ _ => False) exe endPc R F n blk :=
    blkW_noWr' hcode hok hR hal hlo hhi
  have hWN : BlkW (fun s _ => (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false) (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hW (blkW_noSys' hcode hok) fun _ _ h1 h2 => ⟨h1, h2⟩
  have hPW : BlkW (fun s c => PlacedS Λ lbl s c fs ∧ (∀ L, ¬ WrAt s L) ∧ abi.atSys s = false)
      (fun _ _ => False) exe endPc R F n blk :=
    Spike.Lib.A64.AllocG.BlkW.imp hP hWN fun _ _ h1 h2 => ⟨h1, h2⟩
  refine BlkW.w2 hp hS ?_ hJ
  exact Spike.Lib.A64.AllocG.BlkW.imp hab hPW fun s c h1 h2 =>
    ⟨h1, h2.1, fun _ _ _ _ => wrOkA_of_noWr h2.2.1, fun h => absurd h (by rw [h2.2.2]; decide)⟩

/-- **The phase check of two blocks in a row**, the second's start in the
first's phase. -/
theorem blkPh_append {dd : Nat → Bool} {pc ra : Int64} {a b : List Directive}
    (ha : blkPh okPc ph dd lab pc ra a = true)
    (hb : blkPh okPc ph dd lab (pc + Int64.ofNat (4 * a.length)) ra b = true)
    (he : ph (pc + Int64.ofNat (4 * a.length)).toBitVec.toNat = ph pc.toBitVec.toNat) :
    blkPh okPc ph dd lab pc ra (a ++ b) = true := by
  unfold blkPh at ha hb ⊢
  rw [List.all_eq_true] at ha hb ⊢
  intro k hk
  have hk' := List.mem_range.mp hk
  rw [List.length_append] at hk'
  rcases Nat.lt_or_ge k a.length with h' | h'
  · rw [List.getElem?_append_left h']
    exact ha k (List.mem_range.mpr h')
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hb j (List.mem_range.mpr (by omega))
    rw [he] at this
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Nat.mul_add, Int64.ofNat_add,
      ← Int64.add_assoc]
    exact this

/-- **A covered block's instructions before a last one are not
branches**: a block with one more covered instruction after it. -/
theorem noTerm_of_okBlk_snoc {lo hi : Int} {x : Directive} :
    ∀ {o : Spike.Lib.A64.Flow.SO} {blk : List Directive}, okBlk lo hi o (blk ++ [x]) = true →
    ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a → a.isTerm = false
  | _, [], _, k, hk, _, _ => absurd hk (by simp)
  | o, d :: ds, h, k, hk, a, ha => by
    rw [List.cons_append] at h
    unfold okBlk at h
    split at h
    · rename_i a' ha'
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.isEmpty_iff] at h
      obtain ⟨⟨-, hne⟩, hrest⟩ := h
      cases k with
      | zero =>
        simp only [List.getElem_cons_zero] at ha
        rw [ha'] at ha
        cases ha
        rcases hne with hne | hne
        · simp at hne
        · simpa using hne
      | succ k => exact noTerm_of_okBlk_snoc hrest k (by simp at hk; omega) a ha
    · cases h

/-- **A covered block without a branch keeps the write abort's phase**:
its code (`hcode`) passing the phase check (`hph`), none of its
instructions a branch (`hnt`), every next pc off the write abort's pcs
(`hnx`). -/
theorem blkW_abC {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} {ra : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc ra blk = true)
    (hnt : ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a → a.isTerm = false)
    (hnx : ∀ k < blk.length, n.pc + Int64.ofNat (4 * (k + 1)) ∉ abPcs lab) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [← hI.labOk] at hph hnx ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) (n := n) hI.same hI.off hok hph
    (fun _ _ _ k hk r h => by have := hnt k hk _ h; simp [Spike.Lib.A64.Flow.AI.isTerm] at this) (fun _ _ _ => rfl)
  refine Spike.Lib.A64ConsumerA.blkW_abSt hcode hok hR hal hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) ?_
  intro σ c _ k hk a ha s' _ _ hpc' _
  rw [Spike.Lib.A64.Flow.AI.tgt_of_not_term (hnt k hk a ha)] at hpc'
  refine not_ab_of_pc ?_
  rw [hpc', Int64.add_assoc, ← Int64.ofNat_add, show 4 * k + 4 = 4 * (k + 1) by omega]
  exact hnx k hk

/-- A block none of whose instructions is a branch has no `ret`. -/
theorem noRet_of_noTerm {blk : List Directive}
    (h : ∀ k (hk : k < blk.length) a, Spike.Lib.A64.Flow.classify blk[k] = some a → a.isTerm = false) :
    noRetBlk blk = true := by
  unfold noRetBlk
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  split
  · rename_i r heq
    have := h k hk _ heq
    simp [Spike.Lib.A64.Flow.AI.isTerm] at this
  · rfl

end Blk

/-! ## The exchange's accesses -/

section Acc

open Scc.Emit.A64
open Spike.Lib.A64.Flow (ldrDir ldurDir ldrXDir strDir sturDir strXDir classify AI SO)

/-- **A word load's access**: `ldrOff`'s last directive, a plain `ldr`,
`ldur` or register-offset `ldr`. -/
theorem ldrOff_last {t b : XReg} {disp : Int} {pre : List Item} {dL : Directive}
    (h : directives (ldrOff .W64 t (xs b) disp) = directives pre ++ [dL]) :
    dL = ldrDir t b (Int64.ofInt disp) ∨ dL = ldurDir t b (Int64.ofInt disp) ∨ dL = ldrXDir t b scratch0 := by
  have h' := congrArg List.getLast? h
  rw [List.getLast?_concat] at h'
  unfold ldrOff at h'
  split at h'
  · left; simp [directives, ins] at h'; exact h'.symm
  · split at h'
    · right; left; simp [directives, ins] at h'; exact h'.symm
    · right; right; simp [directives, ins] at h'; exact h'.symm

/-- **A word store's access**: `strOff`'s last directive, a plain `str`,
`stur` or register-offset `str`. -/
theorem strOff_last {t b : XReg} {disp : Int} {pre : List Item} {dS : Directive}
    (h : directives (strOff .W64 t (xs b) disp) = directives pre ++ [dS]) :
    dS = strDir t b (Int64.ofInt disp) ∨ dS = sturDir t b (Int64.ofInt disp) ∨ dS = strXDir t b scratch0 := by
  have h' := congrArg List.getLast? h
  rw [List.getLast?_concat] at h'
  unfold strOff at h'
  split at h'
  · left; simp [directives, ins] at h'; exact h'.symm
  · split at h'
    · right; left; simp [directives, ins] at h'; exact h'.symm
    · right; right; simp [directives, ins] at h'; exact h'.symm

/-- **A word load's access is neither covered nor a system call.** -/
theorem ldrOff_acc {t b : XReg} {disp : Int} {pre : List Item} {dL : Directive}
    (h : directives (ldrOff .W64 t (xs b) disp) = directives pre ++ [dL]) :
    classify dL = none ∧ ∀ imm, dL ≠ .instr ⟨.W64, .SVC imm⟩ := by
  rcases ldrOff_last h with rfl | rfl | rfl <;>
    exact ⟨by simp [ldrDir, ldurDir, ldrXDir, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly],
      fun _ h => by cases h⟩

/-- **A word store's access is neither covered nor a system call.** -/
theorem strOff_acc {t b : XReg} {disp : Int} {pre : List Item} {dS : Directive}
    (h : directives (strOff .W64 t (xs b) disp) = directives pre ++ [dS]) :
    classify dS = none ∧ ∀ imm, dS ≠ .instr ⟨.W64, .SVC imm⟩ := by
  rcases strOff_last h with rfl | rfl | rfl <;>
    exact ⟨by simp [strDir, sturDir, strXDir, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly],
      fun _ h => by cases h⟩

/-- A covered instruction that is not a branch targets its next pc. -/
theorem aiTgts_noTerm {lab : Label → Int64} {fall ra : Int64} {a : AI} (h : a.isTerm = false) :
    aiTgts lab fall ra a = [fall] := by
  cases a <;> simp_all [AI.isTerm, aiTgts]

/-- **An access's prefix then a call is covered.** -/
theorem okBlk_pre_bl {pre : List Item} {disp : Int} (hp : pre = [] ∨ pre = movImm scratch0 disp) (lo hi : Int)
    (o : SO) (fn : Label) : okBlk lo hi o (directives pre ++ [Spike.Lib.A64.Flow.blD fn]) = true := by
  rcases hp with rfl | rfl
  · exact Spike.Lib.A64.Flow.okBlk_blD lo hi o fn
  · rw [okBlk_movImm]; exact Spike.Lib.A64.Flow.okBlk_blD _ _ _ fn

end Acc

/-! ## A lane store's states inside `W2` -/

section Lane

open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.A64.Flow (arun ldStep AS classify)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)
open Spike.Lib.Form (opdVal)
open Scc.Cert.Ph1A64 (runPhB runPhB_get blkPh_of_runPhB)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {ar : Arena} {Jv : InvS} {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **A chunk's pcs off the write abort's, and the pc right after it**: the
pcs of a code predicate's chunks off the write abort's (`hnab`) and the pc
after the chunk `blk` (`hE`). -/
theorem nab_snoc {Cd : Int64 → List Directive → Prop}
    (hnab : ∀ pc' blk, Cd pc' blk → ∀ k < blk.length, pc' + Int64.ofNat (4 * k) ∉ abPcs lab)
    {pc : Int64} {blk : List Directive} (h : Cd pc blk) (hE : pc + Int64.ofNat (4 * blk.length) ∉ abPcs lab) :
    ∀ k ≤ blk.length, pc + Int64.ofNat (4 * k) ∉ abPcs lab := fun k hk =>
  (Nat.lt_or_ge k blk.length).elim (hnab _ _ h k) fun h' => by
    rw [show k = blk.length by omega]; exact hE

/-- **A lane store's nodes inside `W2`** at the frames `fs` (`LaneW` at
`W2` for a code predicate `Cd` inside `CdC`, `hcd`): as `laneW_w2`, the pcs
of `Cd`'s chunks off the write abort's (`hnab`) and the pc right after a
chunk ending with a lane store's `strOff` too (`hend`). -/
theorem laneW_w2E {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra : Int64}
    {Cd : Int64 → List Directive → Prop} (hcd : ∀ pc' blk, Cd pc' blk → CdC prog okPc ph lab ra pc' blk)
    (hnab : ∀ pc' blk, Cd pc' blk → ∀ k < blk.length, pc' + Int64.ofNat (4 * k) ∉ abPcs lab)
    (hend : ∀ pc' blk (disp : Int), Cd pc' (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)) →
      pc' + Int64.ofNat (4 * (blk ++ directives (strOff .W64 .X9 (xs .X10) disp)).length) ∉ abPcs lab)
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (ms : MemSide isaLSE2) {pc : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand}
    {J : AS → Ctl → Prop} {P : AS → Ctl → Ctl → Prop}
    (hJp : ∀ σ c, J σ c → SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c)
    (hJ : ∀ σ c, J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs)
    (hP1 : ∀ σ c c1, J σ c → P σ c c1 → SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c1 ∧
      (∀ k, rsOf cx d = some k → ∀ v, SlotRepAt Λ.imms lbl (rsOf cx) (Spike.Lib.upd σ.slot k v) c1) ∧
      (fs = [] → ∀ a, c1.term ≠ .ret a) ∧ FrOk2 c1 fs)
    (hadr : ∀ σ c c1, J σ c → P σ c c1 →
      (∀ k, rsOf cx d = some k → ∀ r, opdVal (rsOf cx) (Spike.Lib.upd σ.slot k r) (.reg a.base) =
        opdVal (rsOf cx) σ.slot (.reg a.base)) ∧
      ∀ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat →
        HeapW Λ own ar lbl lsize F (vb + BitVec.ofInt 64 a.disp)) :
    LaneW Cd (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
      K exe endPc R F ms lbl cx pc d a w J P := by
  intro lb ls lv preL preS dL dS adL adS hb hs hv heL hLd hpL haL heS hSt hpS haS L B1 B2 pcL pcS hC1 hC2
  obtain ⟨off, hd⟩ : ∃ off, cx.slotOff d = .ok off := by
    cases h : cx.slotOff d with
    | ok off => exact ⟨off, rfl⟩
    | error e => simp [FnCtx.setReg, h, bind, Except.bind] at hs
  have hdk : rsOf cx d = some (off - cx.frame) := by simp [rsOf, hd]
  have hb0 : cx.getOp .X10 (.reg a.base) = .ok lb := hb
  have hoF : (oF cx).kill .X9 = oF cx := rfl
  have hoF16 : (oF cx).kill scratch0 = oF cx := rfl
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hls1 : (directives ls).length = 1 := by
    have hs' := hs
    rw [setReg_eq hf (by omega) hd] at hs'
    cases hs'; rfl
  obtain ⟨hcnL, hnsL⟩ := ldrOff_acc heL
  obtain ⟨hcnS, hnsS⟩ := strOff_acc heS
  have hCd : ∀ pc blk, CdC prog okPc ph lab ra pc blk → CdOf exe endPc pc blk := by
    rw [← hI.labOk]; exact cdOf_cdC hI.lays hI.endOk
  simp only [directives_append, heL, heS, List.length_append, List.length_singleton, hls1] at hC1 hC2
  -- the code
  have hc1 := hCd _ _ (hcd _ _ hC1)
  have hc2 := hCd _ _ (hcd _ _ hC2)
  have hc1' : CdOf exe endPc pc (B1 ++ ([dL] ++ directives ls)) := by
    simpa only [B1, List.append_assoc] using hc1
  have hcB1 := hc1'.left
  have hcL : CdOf exe endPc pcL [dL] := hc1'.right.left
  have hcls : CdOf exe endPc (pcL + Int64.ofNat 4) (directives ls) := hc1'.right.right
  have hpc2 : pc + Int64.ofNat (4 * ((directives lb).length + ((directives preL).length + 1) + 1)) =
      pcL + Int64.ofNat 4 + Int64.ofNat (4 * (directives ls).length) := by
    simp only [pcL, B1, hls1, List.length_append, Nat.mul_add, Nat.mul_one, Int64.ofNat_add, Int64.add_assoc]
  have hc2' : CdOf exe endPc (pcL + Int64.ofNat 4 + Int64.ofNat (4 * (directives ls).length))
      ((directives lv ++ directives lb ++ directives preS) ++ [dS]) := by
    rw [← hpc2]; simpa only [List.append_assoc] using hc2
  have hcB2 : CdOf exe endPc (pcL + Int64.ofNat 4) B2 := CdOf.append hcls hc2'.left
  have hcS : CdOf exe endPc pcS [dS] := by
    have := hc2'.right
    simpa only [pcS, B2, List.length_append, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc] using this
  -- the runs
  have hB1 : ∀ σ, ∃ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat ∧
      (arun L B1 ⟨pc, oF cx, σ⟩).pc = pcL ∧ (arun L B1 ⟨pc, oF cx, σ⟩).so = oF cx ∧
      (arun L B1 ⟨pc, oF cx, σ⟩).σ.slot = σ.slot ∧
      adL (arun L B1 ⟨pc, oF cx, σ⟩).σ.regs = vb + BitVec.ofInt 64 a.disp := by
    intro σ
    obtain ⟨vb, hvb, he⟩ := arun_getOp hf h1 hb0 L pc σ
    obtain ⟨regs, hp, -⟩ := arun_pre hpL L (pc + Int64.ofNat (4 * (directives lb).length)) hoF16
      { σ with regs := σ.regs.setXReg .X10 vb }
    have ha := haL L (pc + Int64.ofNat (4 * (directives lb).length)) (oF cx) { σ with regs := σ.regs.setXReg .X10 vb }
    have he' : arun L B1 ⟨pc, oF cx, σ⟩ = arun L (directives preL)
        ⟨pc + Int64.ofNat (4 * (directives lb).length), oF cx, { σ with regs := σ.regs.setXReg .X10 vb }⟩ := by
      simp only [B1, arun_append]; exact congrArg _ he
    rw [he'] at ⊢
    rw [hp] at ha ⊢
    refine ⟨vb, hvb, ?_, rfl, rfl, ?_⟩
    · simp only [pcL, B1, List.length_append, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
    · rw [ha]; simp
  have hB2 : ∀ σ : AS, ∃ vw vb : BitVec 64,
      opdVal (rsOf cx) (upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec) w = some vw.toNat ∧
      opdVal (rsOf cx) (upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec) (.reg a.base) = some vb.toNat ∧
      (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).pc = pcS ∧ (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).so = oF cx ∧
      (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.slot = upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec ∧
      adS (arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.regs = vb + BitVec.ofInt 64 a.disp ∧
      ((arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩).σ.regs.getXReg .X9).toBitVec = vw := by
    intro σ
    obtain ⟨hl, hs'⟩ := arun_setReg9 hf h1 hd hs L (pcL + Int64.ofNat 4) σ
    let σs : AS := { σ with slot := upd σ.slot (off - cx.frame) σ.regs.X9.toBitVec }
    obtain ⟨vw, hvw, he1⟩ := arun_getOp hf h1 hv L (pcL + Int64.ofNat 4 + 4) σs
    obtain ⟨vb, hvb, he2⟩ := arun_getOp hf h1 hb0 L
      (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length)) { σs with regs := σs.regs.setXReg .X9 vw }
    obtain ⟨regs, hp, hr⟩ := arun_pre hpS L (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) +
      Int64.ofNat (4 * (directives lb).length)) hoF16
      { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }
    have ha := haS L (pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) +
      Int64.ofNat (4 * (directives lb).length)) (oF cx) { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }
    have he' : arun L B2 ⟨pcL + Int64.ofNat 4, oF cx, σ⟩ = arun L (directives preS)
        ⟨pcL + Int64.ofNat 4 + 4 + Int64.ofNat (4 * (directives lv).length) + Int64.ofNat (4 * (directives lb).length),
          oF cx, { σs with regs := (σs.regs.setXReg .X9 vw).setXReg .X10 vb }⟩ := by
      simp only [B2, arun_append]
      rw [hs']
      change arun L (directives preS) (arun L (directives lb) (arun L (directives lv)
        ⟨_, ⟨-(cx.frame : Int), []⟩, σs⟩)) = _
      rw [he1]
      change arun L (directives preS) (arun L (directives lb) ⟨_, ⟨-(cx.frame : Int), []⟩, _⟩) = _
      rw [he2]; rfl
    rw [he'] at ⊢
    rw [hp] at ha ⊢
    refine ⟨vw, vb, hvw, hvb, ?_, rfl, rfl, ?_, ?_⟩
    · simp only [pcS, B2, List.length_append, hl, Nat.mul_add, Nat.mul_one, Int64.ofNat_add, Int64.add_assoc]
      rfl
    · rw [ha]; simp
    · rw [hr _ (by decide)]; simp
  -- the blocks covered
  have hok1 : okBlk (-(cx.frame : Int)) 0 (oF cx) B1 = true := by
    simp only [B1]; rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_getOp hf h1 h16 hb0]
    exact okBlk_pre hpL rfl
  have hok2 : okBlk (-(cx.frame : Int)) 0 ((oF cx).kill .X9) B2 = true := by
    simp only [B2, List.append_assoc]
    rw [hoF, show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_setReg9 hf h1 h16 hd hs, okBlk_getOp hf h1 h16 hv,
      okBlk_getOp hf h1 h16 hb0]
    exact okBlk_pre hpS rfl
  -- no branch before the accesses
  have hnt1 : ∀ k (hk : k < B1.length) a, classify B1[k] = some a → a.isTerm = false :=
    noTerm_of_okBlk_snoc (x := Spike.Lib.A64.Flow.blD "") (lo := -(cx.frame : Int)) (hi := 0) (o := oF cx) (by
      simp only [B1, List.append_assoc]
      rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_getOp hf h1 h16 hb0]
      exact okBlk_pre_bl hpL _ _ _ _)
  have hnt2 : ∀ k (hk : k < B2.length) a, classify B2[k] = some a → a.isTerm = false :=
    noTerm_of_okBlk_snoc (x := Spike.Lib.A64.Flow.blD "") (lo := -(cx.frame : Int)) (hi := 0)
      (o := (oF cx).kill .X9) (by
      simp only [B2, List.append_assoc]
      rw [hoF, show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, okBlk_setReg9 hf h1 h16 hd hs,
        okBlk_getOp hf h1 h16 hv, okBlk_getOp hf h1 h16 hb0]
      exact okBlk_pre_bl hpS _ _ _ _)
  -- the pcs
  have hE : ∀ N M : Nat, N = M → pc + Int64.ofNat N = pc + Int64.ofNat M := fun _ _ h => h ▸ rfl
  have eL : pcL = pc + Int64.ofNat (4 * B1.length) := rfl
  have eL4 : pcL + Int64.ofNat 4 = pc + Int64.ofNat (4 * (B1.length + 1)) := by
    simp only [pcL, Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)
  have e2 : pcL + Int64.ofNat 4 + Int64.ofNat (4 * (directives ls).length) =
      pc + Int64.ofNat (4 * (B1.length + 2)) := by
    simp only [pcL, hls1, Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)
  have eS : pcS =
      pc + Int64.ofNat (4 * (B1.length + 2 + (directives lv ++ directives lb ++ directives preS).length)) := by
    simp only [pcS, pcL, B2, List.length_append, hls1, Int64.add_assoc, ← Int64.ofNat_add]
    exact hE _ _ (by omega)
  -- the phases
  have hr1 : runPhB okPc ph lab pc ra (B1 ++ [dL] ++ directives ls) = true := by
    have := (hcd _ _ hC1).2.choose_spec.choose_spec.2.2
    simpa only [B1, List.append_assoc] using this
  have hr2 : runPhB okPc ph lab (pc + Int64.ofNat (4 * (B1.length + 2))) ra
      ((directives lv ++ directives lb ++ directives preS) ++ [dS]) = true := by
    have := (hcd _ _ hC2).2.choose_spec.choose_spec.2.2
    rw [← e2, ← hpc2]; simpa only [List.append_assoc] using this
  have hcl1 := classify_of_okBlk hok1
  have hcl2 := classify_of_okBlk hok2
  have hph1 : blkPh okPc ph (fun _ => false) lab pc ra B1 = true := by
    have := blkPh_of_runPhB (xs := []) (ys := B1) (zs := [dL] ++ directives ls)
      (by simpa only [List.nil_append, List.append_assoc] using hr1) hcl1
    simpa [Int64.add_zero] using this
  have hk1 : B1.length < (B1 ++ [dL] ++ directives ls).length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hk2 : B1.length + 1 < (B1 ++ [dL] ++ directives ls).length := by
    simp only [List.length_append, List.length_singleton, hls1]; omega
  have hk3 : 0 < B2.length := by simp only [B2, List.length_append, hls1]; omega
  obtain ⟨okL, pL, tL⟩ := runPhB_get hr1 hk1
  have hgL : (B1 ++ [dL] ++ directives ls)[B1.length]'hk1 = dL := by simp
  simp only [hgL, hcnL, List.mem_singleton, forall_eq] at tL
  have hokL : okPc pcL.toBitVec.toNat = true := okL
  have hphL : ph (pcL + Int64.ofNat 4).toBitVec.toNat = ph pcL.toBitVec.toNat := by
    rw [eL, tL, pL]
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hls1
  have hxm : x ∈ B2 := List.mem_append_left _ (by rw [hx]; exact List.mem_singleton_self _)
  obtain ⟨ax, hax⟩ := Option.isSome_iff_exists.mp (hcl2 x hxm)
  have hxt : ax.isTerm = false := hnt2 0 hk3 ax (by
    have : B2[0]'hk3 = x := by simp [B2, hx]
    rw [this]; exact hax)
  obtain ⟨-, pls, tls⟩ := runPhB_get hr1 hk2
  have hgs : (B1 ++ [dL] ++ directives ls)[B1.length + 1]'hk2 = x := by simp [hx]
  simp only [hgs, hax, aiTgts_noTerm hxt, List.mem_singleton, forall_eq] at tls
  have hlink : ph (pc + Int64.ofNat (4 * (B1.length + 2))).toBitVec.toNat =
      ph (pcL + Int64.ofNat 4).toBitVec.toNat := by
    rw [eL4, pls, ← tls]
    congr 3
    simp only [Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)
  have hph2 : blkPh okPc ph (fun _ => false) lab (pcL + Int64.ofNat 4) ra B2 = true := by
    have hl := blkPh_of_runPhB (xs := B1 ++ [dL]) (ys := directives ls) (zs := [])
      (by rw [List.append_nil]; exact hr1) (fun d hd => hcl2 d (List.mem_append_left _ hd))
    have hm := blkPh_of_runPhB (xs := []) (ys := directives lv ++ directives lb ++ directives preS) (zs := [dS])
      (by rw [List.nil_append]; exact hr2) (fun d hd => hcl2 d (List.mem_append_right _ hd))
    have e' : pc + Int64.ofNat (4 * (B1 ++ [dL]).length) = pcL + Int64.ofNat 4 := by
      rw [eL4]; simp only [List.length_append, List.length_singleton]
    rw [e'] at hl
    simp only [List.length_nil, Nat.mul_zero] at hm
    rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at hm
    refine blkPh_append hl ?_ ?_
    · rw [e2]; exact hm
    · rw [e2]; exact hlink
  have hk4 : (directives lv ++ directives lb ++ directives preS).length <
      ((directives lv ++ directives lb ++ directives preS) ++ [dS]).length := by simp
  obtain ⟨okS, pS, tS⟩ := runPhB_get hr2 hk4
  have hgS : ((directives lv ++ directives lb ++ directives preS) ++ [dS])[(directives lv ++ directives lb ++
      directives preS).length]'hk4 = dS := by simp
  simp only [hgS, hcnS, List.mem_singleton, forall_eq] at tS
  have hokS : okPc pcS.toBitVec.toNat = true := by
    rw [eS]
    have e : pc + Int64.ofNat (4 * (B1.length + 2)) +
        Int64.ofNat (4 * (directives lv ++ directives lb ++ directives preS).length) =
        pc + Int64.ofNat (4 * (B1.length + 2 + (directives lv ++ directives lb ++ directives preS).length)) := by
      simp only [Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)
    rw [← e]; exact okS
  have hphS : ph (pcS + Int64.ofNat 4).toBitVec.toNat = ph pcS.toBitVec.toNat := by
    have e : pcS = pc + Int64.ofNat (4 * (B1.length + 2)) +
        Int64.ofNat (4 * (directives lv ++ directives lb ++ directives preS).length) := by
      rw [eS]; simp only [Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)
    rw [e, tS, pS]
  -- off the write abort
  have hn2 := nab_snoc hnab hC2 (by
    have := hend _ (directives lv ++ directives lb) a.disp (by rw [heS]; simpa only [List.append_assoc] using hC2)
    rw [heS] at this
    simpa only [List.append_assoc] using this)
  have hn1 := nab_snoc hnab hC1 (by
    have := hnab _ _ hC2 0 (by simp; omega)
    simp only [List.length_append, List.length_singleton, hls1, Nat.mul_zero] at this ⊢
    rwa [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero] at this)
  rw [hpc2, e2] at hn2
  have hl1 : (directives lb ++ (directives preL ++ [dL]) ++ directives ls).length = B1.length + 2 := by
    simp only [B1, List.length_append, List.length_singleton, hls1]; omega
  have hl2 : (directives lv ++ directives lb ++ (directives preS ++ [dS])).length =
      (directives lv ++ directives lb ++ directives preS).length + 1 := by
    simp only [List.length_append, List.length_singleton]; omega
  rw [hl1] at hn1
  rw [hl2] at hn2
  have nxB1 : ∀ k < B1.length, pc + Int64.ofNat (4 * (k + 1)) ∉ abPcs lab := fun k hk => hn1 (k + 1) (by omega)
  have nxL : pcL + Int64.ofNat 4 ∉ abPcs lab := by rw [eL4]; exact hn1 _ (by omega)
  have nxB2 : ∀ k < B2.length, pcL + Int64.ofNat 4 + Int64.ofNat (4 * (k + 1)) ∉ abPcs lab := by
    intro k hk
    have hk' : k < 1 + (directives lv ++ directives lb ++ directives preS).length := by
      simpa only [B2, List.length_append, hls1] using hk
    cases k with
    | zero =>
      rw [show pcL + Int64.ofNat 4 + Int64.ofNat (4 * (0 + 1)) = pc + Int64.ofNat (4 * (B1.length + 2)) by
        simp only [pcL, Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)]
      exact hn1 _ (by omega)
    | succ j =>
      rw [show pcL + Int64.ofNat 4 + Int64.ofNat (4 * (j + 1 + 1)) =
          pc + Int64.ofNat (4 * (B1.length + 2)) + Int64.ofNat (4 * (j + 1)) by
        simp only [pcL, Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)]
      exact hn2 _ (by omega)
  have nxS : pcS + Int64.ofNat 4 ∉ abPcs lab := by
    rw [show pcS + Int64.ofNat 4 = pc + Int64.ofNat (4 * (B1.length + 2)) +
        Int64.ofNat (4 * ((directives lv ++ directives lb ++ directives preS).length + 1)) by
      rw [eS]; simp only [Int64.add_assoc, ← Int64.ofNat_add]; exact hE _ _ (by omega)]
    exact hn2 _ (by omega)
  -- the element's word at the load
  have hA1 : ∀ σ0 c0 c1, J σ0 c0 → P σ0 c0 c1 →
      HeapW Λ own ar lbl lsize F (adL (arun L B1 ⟨pc, oF cx, σ0⟩).σ.regs) := by
    intro σ0 c0 c1 hJ0 hP0
    obtain ⟨vb, hvb, -, -, -, hadL⟩ := hB1 σ0
    rw [hadL]
    exact (hadr σ0 c0 c1 hJ0 hP0).2 vb hvb
  -- the store's address and slots after `B2`
  have hx9 : ∀ σ0 (r : BitVec 64), (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ).regs.X9.toBitVec = r := by
    intro σ0 r; simp [ldStep]
  have hAS : ∀ σ0 c0 c1 (r : BitVec 64), J σ0 c0 → P σ0 c0 c1 →
      adS (arun L B2 ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9, ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ⟩).σ.regs =
        adL (arun L B1 ⟨pc, oF cx, σ0⟩).σ.regs ∧
      (arun L B2 ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9, ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ⟩).σ.slot =
        Spike.Lib.upd σ0.slot (off - cx.frame) r := by
    intro σ0 c0 c1 r hJ0 hP0
    obtain ⟨vb, hvb, -, -, hsl1, hadL⟩ := hB1 σ0
    rw [hoF]
    obtain ⟨vw, vb', -, hvb', -, -, hsl2, hadS, -⟩ := hB2 (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ)
    have hsl : (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ).slot = σ0.slot := hsl1
    rw [hx9, hsl] at hvb' hsl2
    have hvv : vb' = vb := BitVec.eq_of_toNat_eq (Option.some.inj
      (hvb'.symm.trans (((hadr σ0 c0 c1 hJ0 hP0).1 _ hdk r).trans hvb)))
    rw [hvv] at hadS
    exact ⟨by rw [hadS, hadL], hsl2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `B1`
    have hnw : noSlotWr B1 = true := by
      simp only [B1]
      rw [noSlotWr_append, noSlotWr_getOp hb0]
      rcases hpL with h | h <;> rw [h]
      · rfl
      · exact noSlotWr_movImm _ _
    exact blkW_w2BP' (n := ⟨pc, oF cx, J⟩) hI hR hal hlo hhi hl hh hsub hfit hFO hp hcB1 hph1 hok1
      (noRet_of_noTerm hnt1) (blkW_abC hI hcB1 hok1 hR hal hlo hhi hph1 hnt1 nxB1)
      (blkW_placedS hFS hJp hrs hfp (noSlotWr_dropLast hnw)) hJ
  · -- the load's node
    have haL' : ∀ σ c m, (Spike.Lib.A64.Flow.XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P).J σ c → F m →
        HeapW Λ own ar lbl lsize F (adL σ.regs) := by
      rintro σ c m ⟨σ0, c0, hJ0, hP0, rfl⟩ -
      exact hA1 σ0 c0 c hJ0 hP0
    have hS := nodeW_sfacts_ldH (n := dumN (Spike.Lib.A64.Flow.XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P))
      (Λ := Λ) (rS := rS) (lbl := lbl) hI hLd hnsL hcL (fun _ _ h => h.1 ▸ cfacts_c0) hokL hphL
      hR hR8 hl hh hsub hFO (by
        rintro σ c m ⟨-, c', hJ'⟩ hm
        have h := haL' σ c' m hJ' hm
        exact ⟨h.1, h.2.2.2.2.2 m hm⟩)
    have hab := nodeW_ab_ldH (R := R) (F := F)
      (n := Spike.Lib.A64.Flow.XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P) hI hLd hnsL hcL hokL nxL
      fun σ c m h hm => (haL' σ c m h hm).2.2.2.2.2 m hm
    have hpl := nodeW_placedS (exe := exe) (endPc := endPc) (R := R) (F := F) (Λ := Λ) (lbl := lbl) (fs := fs)
      (n := Spike.Lib.A64.Flow.XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P)
      (by
        rintro σ c ⟨σ0, c0, hJ0, hP0, rfl⟩
        obtain ⟨_, _, _, _, he1, _⟩ := hB1 σ0
        rw [he1]
        exact (hP1 σ0 c0 c hJ0 hP0).1) hrs hfp
    have hnw := nodeW_noWr_ldH (R := R) (F := F)
      (n := Spike.Lib.A64.Flow.XchgSeg.xsNL L B1 pc pcL (oF cx) (oF cx) J P) hLd hnsL hcL
      fun σ c m h hm => (haL' σ c m h hm).2.2.2.2.2 m hm
    refine NodeW.w2 hp hS (Spike.Lib.A64.AllocG.NodeW.imp (Spike.Lib.A64.AllocG.NodeW.imp
      (W := fun s c => AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c fs) hab hpl fun _ _ h1 h2 => ⟨h1, h2⟩) hnw
      fun s c h1 h2 =>
        ⟨h1.1, h1.2, fun _ _ _ _ => wrOkA_of_noWr h2.1, fun h => absurd h (by rw [h2.2]; decide)⟩) ?_
    rintro σ c ⟨σ0, c0, hJ0, hP0, -⟩
    exact (hP1 σ0 c0 c hJ0 hP0).2.2
  · -- `B2`
    have hnw2 : noSlotWr (directives lv ++ directives lb ++ directives preS) = true := by
      rw [noSlotWr_append, noSlotWr_append, noSlotWr_getOp hv, noSlotWr_getOp hb0]
      rcases hpS with h | h <;> rw [h]
      · rfl
      · exact noSlotWr_movImm _ _
    have hpl : BlkW (fun s c => PlacedS Λ lbl s c fs) (fun _ _ => False) exe endPc R F
        (Spike.Lib.A64.Flow.XchgSeg.xsNH ms lbl L B1 pc pcL (oF cx) (oF cx) .X9 adL J P) B2 := by
      rintro s σ c - - - - - hF ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, rfl⟩ k hk m hA' hD
      refine ⟨placedS_of_abs (s := { s with st := (m, _) }) hA' ?_ hrs (hfp _ (hFS _ _ hF hD)).choose_spec,
        fun _ h => h⟩
      obtain ⟨_, _, _, _, hsl1, _⟩ := hB1 σ0
      have hsl : (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ).slot = σ0.slot := hsl1
      obtain ⟨hs1, hs2, -, -⟩ := hP1 σ0 c0 c1 hJ0 hP0
      cases k with
      | zero =>
        show SlotRepAt _ _ _ (ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ).slot _
        rw [hsl]; exact hs1
      | succ k =>
        have htk : noSlotWr (List.take k (directives lv ++ directives lb ++ directives preS)) = true := by
          simp only [noSlotWr, List.all_eq_true] at hnw2 ⊢
          exact fun x hx => hnw2 x (List.mem_of_mem_take hx)
        have htake : List.take (k + 1) B2 =
            directives ls ++ List.take k (directives lv ++ directives lb ++ directives preS) := by
          simp only [B2, hx, List.singleton_append, List.take_succ_cons]
        show SlotRepAt _ _ _ (arun L (List.take (k + 1) B2) ⟨pcL + Int64.ofNat 4, (oF cx).kill .X9,
          ldStep .X9 r (arun L B1 ⟨pc, oF cx, σ0⟩).σ⟩).σ.slot _
        rw [htake, arun_append, hoF, (arun_setReg9 hf h1 hd hs _ _ _).2, arun_slot_noSlotWr L htk]
        simp only
        rw [hsl, hx9]
        exact hs2 _ hdk r
    exact blkW_w2BP' hI hR hal hlo hhi hl hh hsub hfit hFO hp hcB2 hph2 hok2 (noRet_of_noTerm hnt2)
      (blkW_abC hI hcB2 hok2 hR hal hlo hhi hph2 hnt2 nxB2) hpl
      (by rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, -, rfl⟩; exact (hP1 σ0 c0 c1 hJ0 hP0).2.2)
  · -- the store's node
    have haS' : ∀ σ c m, (Spike.Lib.A64.Flow.XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS (oF cx) (oF cx) (oF cx) .X9
        adL J P).J σ c → F m → HeapW Λ own ar lbl lsize F (adS σ.regs) := by
      rintro σ c m ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, -⟩ -
      rw [(hAS σ0 c0 c1 r hJ0 hP0).1]
      exact hA1 σ0 c0 c1 hJ0 hP0
    have hS := nodeW_sfacts_stH (n := dumN (Spike.Lib.A64.Flow.XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS (oF cx)
      (oF cx) (oF cx) .X9 adL J P)) (Λ := Λ) (rS := rS) (lbl := lbl) hI hSt hnsS hcS
      (fun _ _ h => h.1 ▸ cfacts_c0) hokS hphS hR hR8 hl hh hsub hFO (by
        rintro σ c m ⟨-, c', hJ'⟩ hm
        have h := haS' σ c' m hJ' hm
        exact ⟨h.2.1, h.2.2.2.2.2 m hm, h.2.2.1⟩)
    have hab := nodeW_ab_stH (R := R) (F := F) (n := Spike.Lib.A64.Flow.XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS
      (oF cx) (oF cx) (oF cx) .X9 adL J P) hI hSt hnsS hcS hokS nxS
      fun σ c m h hm => (haS' σ c m h hm).2.2.2.2.2 m hm
    have hpl := nodeW_placedS (exe := exe) (endPc := endPc) (R := R) (F := F) (Λ := Λ) (lbl := lbl) (fs := fs)
      (n := Spike.Lib.A64.Flow.XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS (oF cx) (oF cx) (oF cx) .X9 adL J P)
      (by
        rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, rfl, rfl⟩
        rw [(hAS σ0 c0 c1 r hJ0 hP0).2]
        exact (hP1 σ0 c0 c1 hJ0 hP0).2.1 _ hdk r) hrs hfp
    have hwr := nodeW_wr_stH (R := R) (F := F) (n := Spike.Lib.A64.Flow.XchgSeg.xsNS ms lbl L B1 B2 pc pcL pcS
      (oF cx) (oF cx) (oF cx) .X9 adL J P) hSt hnsS hcS fun σ c m h hm => (haS' σ c m h hm).2.2.2.2.2 m hm
    refine NodeW.w2 hp hS (Spike.Lib.A64.AllocG.NodeW.imp (Spike.Lib.A64.AllocG.NodeW.imp
      (W := fun s c => AbSt μ (Ab lab) s ∧ PlacedS Λ lbl s c fs) hab hpl fun _ _ h1 h2 => ⟨h1, h2⟩) hwr
      fun s c h1 h2 => ⟨h1.1, h1.2, fun _ _ _ _ => ?_, fun h => absurd h (by rw [h2.2]; decide)⟩) ?_
    · obtain ⟨σ, hJn, hFm, hw⟩ := h2.1
      have hh := haS' σ c s.st.1 hJn hFm
      exact ⟨fun L hL => by rw [hw L hL]; exact .inr (.inr (.inl hh.2.2.2.1)),
        fun hL => (hh.2.2.2.2.1 (hw _ hL).symm).elim⟩
    · rintro σ c ⟨σ0, c0, c1, r, w', hJ0, hP0, -, -, -, rfl⟩
      exact (hP1 σ0 c0 c1 hJ0 hP0).2.2


/-- **A lane store's nodes inside `W2`** at the frames `fs` (`LaneW` at
`W2` for the code predicate `CdC`): at the lane's node `⟨pc, oF cx, J⟩`,
whose controls are placed in the slot file (`hJp`) and exclude `main`'s
`ret` and `ZBad` (`hJ`); at its source relation `P` the exchange site's
control placed in the slot file, also with `d`'s slot updated, and
excluding `main`'s `ret` and `ZBad` (`hP1`), the base's value not moved by
`d`'s slot and the element's word a heap word (`HeapW`, `hadr`); the code
predicate's pcs off the write abort's (`hnab`); the phase `WriteAb.Ab`. -/
theorem laneW_w2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra : Int64}
    (hnab : ∀ pc' blk, CdC prog okPc ph lab ra pc' blk → ∀ k ≤ blk.length,
      pc' + Int64.ofNat (4 * k) ∉ abPcs lab)
    (hrs : ∀ r k, rsOf cx r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (ms : MemSide isaLSE2) {pc : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {w : Scc.IR.Operand}
    {J : AS → Ctl → Prop} {P : AS → Ctl → Ctl → Prop}
    (hJp : ∀ σ c, J σ c → SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c)
    (hJ : ∀ σ c, J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs)
    (hP1 : ∀ σ c c1, J σ c → P σ c c1 → SlotRepAt Λ.imms lbl (rsOf cx) σ.slot c1 ∧
      (∀ k, rsOf cx d = some k → ∀ v, SlotRepAt Λ.imms lbl (rsOf cx) (Spike.Lib.upd σ.slot k v) c1) ∧
      (fs = [] → ∀ a, c1.term ≠ .ret a) ∧ FrOk2 c1 fs)
    (hadr : ∀ σ c c1, J σ c → P σ c c1 →
      (∀ k, rsOf cx d = some k → ∀ r, opdVal (rsOf cx) (Spike.Lib.upd σ.slot k r) (.reg a.base) =
        opdVal (rsOf cx) σ.slot (.reg a.base)) ∧
      ∀ vb : BitVec 64, opdVal (rsOf cx) σ.slot (.reg a.base) = some vb.toNat →
        HeapW Λ own ar lbl lsize F (vb + BitVec.ofInt 64 a.disp)) :
    LaneW (CdC prog okPc ph lab ra) (fun s c => W2 Λ μ p rd G own rS Tk ar Jv Dt (Ab lab) lbl lsize s c fs)
      K exe endPc R F ms lbl cx pc d a w J P :=
  laneW_w2E hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hFS hp (fun _ _ h => h)
    (fun pc' blk h k hk => hnab pc' blk h k (Nat.le_of_lt hk)) (fun pc' blk _ h => hnab pc' _ h _ (Nat.le_refl _))
    hrs hfp ms hJp hJ hP1 hadr

end Lane

/--
info: 'Spike.Lib.LowerA64.laneW_w2' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneW_w2

/--
info: 'Spike.Lib.LowerA64.laneW_w2E' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms laneW_w2E

end Spike.Lib.LowerA64
