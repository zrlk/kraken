/-
**`scc_rt_alloc`'s states keep the write abort's phase at `hello1.w`'s
instance** (AArch64): the allocator's node obligations (`AllocW`,
`Spike/Lib/A64Alloc.lean`) inside `AbSt μ0 (WriteAb.Ab labT)`
(`Spike/Lib/A64AbSt.lean`), none moved.

- `blkW_ab`: a covered block whose targets are off the write abort's pcs
  (`blkAb`), its pcs off the sites (`blkPh`); `blkW_abG` with `blkW_abSt`'s
  target obligation instead of the check.
- `nodeW_ab_si`, `nodeW_ab_st`, `nodeW_ab_ldop`: a single instruction
  without an event, a store and an RMW of a word unmapped in private
  memory, at an off-site pc whose next pc is off the write abort's pcs.
- `labY`, `labT_eq_labY`: `labX` extended by the write abort's labels off
  its tables (`abTabX`), so the kernel reduces `abPcs`.
- `allocAb`: every node of `scc_rt_alloc`; its heap abort's call
  (`movz x0, #2; bl scc_rt_abort`) enters the dispatcher with `x0 = 2`, not
  the write abort's `4`.
-/
import Spike.Test.A64Hello1AllocW
import Spike.Lib.A64AbSt
import Spike.Lib.LowerA64.MovImm

namespace Spike.Test.A64Hello1W0

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND)
open Spike.Lib.A64.Rt (InstOk cellOf)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_ldop)
open Spike.Lib.A64ConsumerA (AbSt AbSt.ofLeaves blkW_abSt blkAb blkAb_sound)
open Spike.Lib.A64.WriteAb (Ab abPcs not_ab_of_pc)

/-! ## Generic nodes off the write abort's pcs -/

section Gen

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**: its pcs off the
sites (`hph`, as `blkW_postO`'s), every target of every instruction off
the write abort's pcs (`hab`). -/
theorem blkW_ab {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hab : blkAb lab (lab l + Int64.ofNat (4 * k)) ra blk = true) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph hab
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead hab ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abSt hcode hok hR hal hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) (blkAb_sound hab hret)

/-- **A covered block keeps the write abort's phase**, as `blkW_ab`, every
instruction's next state, at the abstract run's next pc and registers, out
of `Ab` (`htgt`, `blkW_abSt`'s at the labels `lab`). -/
theorem blkW_abG {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, Spike.Lib.A64.Flow.classify blk[k] = some a →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R (a.so (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead htgt ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abSt hcode hok hR hal hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) htgt

/-- The next state's pc off the write abort's pcs. -/
theorem not_ab_after {s : State} {p : Int64} {m : MachineData} (hpc : s.st.2 = p)
    (hnx : p + Int64.ofNat 4 ∉ abPcs lab) : ¬ Ab lab (after s 4 m) :=
  not_ab_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hpc]; exact hnx)

/-- **A node at a single instruction without an event** (`SI`) keeps the
write abort's phase: its pc off the sites, its next pc off the write
abort's pcs. -/
theorem nodeW_ab_si {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  refine ⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc ?_) fun t ht => ?_, fun _ h => h⟩
  · intro imm h; cases si <;> cases h
  · rw [Spike.Lib.A64.Flow.exec_si hc] at ht
    cases ht
    exact not_ab_after hpc hnx

/-- **A node at a store** `str Xt, [Xn, #i]` of a word unmapped in private
memory (`ha`) keeps the write abort's phase, as `nodeW_ab_si`. -/
theorem nodeW_ab_st {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {t b : XReg}
    {i : Int64} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, hdc, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha' (ha σ c s.st.1 hJ hD) (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
  refine ⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  exact ⟨trivial, fun _ _ => not_ab_after hpc hnx⟩

/-- **A node at an RMW** `ld<op><k> Xs, Xt, [Xn]` of a word unmapped in
private memory (`ha`) keeps the write abort's phase, as `nodeW_ab_si`. -/
theorem nodeW_ab_ldop {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {op : AtomicOp} {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ abPcs lab)
    (ha : ∀ σ c m, n.J σ c → F m → Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := cellOf hI hb he hs hn hpc
  have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
  have hex := exec_ldop hc (by rw [ha']; exact ha σ c s.st.1 hJ hD)
  refine ⟨AbSt.ofLeaves hP.noTake (atSvc_false_of_cellAt hc (by intro imm h; cases h)) fun t ht => ?_,
    fun _ h => h⟩
  rw [hex] at ht
  cases ht
  unfold EvTree.access
  split
  · exact fun _ _ => ⟨fun _ _ => trivial, not_ab_after hpc hnx⟩
  · trivial

end Gen

/-! ## The write abort's labels -/

section Lab

open Spike.Lib.A64.Flow.Hello1.Inst
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1_lays)
open Spike.Test.A64Hello1RtW (labX labT_eq_labX)

/-- The labels of the write abort's pcs off `labX`'s tables: the
dispatcher's tests, its jump to the write stub and the stub's. -/
def abTabX : List (Label × Nat) :=
  [(".L12_scc_rt_abort.0_entry", 4198304), (".L12_scc_rt_abort.2_next1", 4198340),
   (".L12_scc_rt_abort.4_next3", 4198376), (".L12_scc_rt_abort.6_next5", 4198412),
   (".L12_scc_rt_abort.7_is6", 4198432), ("scc_rt_abort_write", 4198704),
   (".L16_scc_rt_abort_write.0_entry", 4198720), ("scc_rt_abort_write_exit", 4198764)]

theorem abTabX_ok : abTabX.all tabChk = true := by decide +kernel

/-- `labX` extended by `abTabX`, so the kernel reduces the write abort's
pcs (`abPcs`). -/
noncomputable def labY (l : Label) : Int64 :=
  match abTabX.lookup l with
  | some n => Int64.ofNat n
  | none => labX l

/-- `labT` is `labY`: `abTabX`'s entries are the loaded thread's labels. -/
theorem labT_eq_labY : labT = labY := by
  funext l
  unfold labY
  cases hn : abTabX.lookup l with
  | some n =>
    have h := List.all_eq_true.mp abTabX_ok _ (Spike.Lib.A64.Flow.Ret0.Inst.lookup_mem hn)
    simp only [tabChk, Bool.and_eq_true, beq_iff_eq] at h
    show _ = Int64.ofNat n
    rw [← h.2, ← hello1_labT]
    exact Spike.Lib.A64.OwnLimRt.label_labIn hello1_lays rfl h.1
  | none => exact congrFun labT_eq_labX l

end Lab

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Test.A64Hello1RtW (hello1_instOk labT_eq_labX)
open Spike.Lib.A64.Flow.Hello1.Mem (hello1Exe hello1End)
open Spike.Lib.A64.Flow.Hello1.Inst

variable {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` with no `ret`, its targets off the write
abort's pcs. -/
local macro "bab " l:term:max k:term:max ok:term:max : tactic =>
  `(tactic| exact blkW_ab (hello1_instOk (rS := ⟨0, 0⟩)) (l := $l) (k := $k) (dead := fun _ => false) (ra := 0)
    (by decide +kernel) (by dsimp only [N]; decide +kernel) $ok hR hal (by omega) (by omega)
    (by rw [labT_eq_labX]; decide +kernel) (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    (fun _ _ _ => rfl) (by rw [labT_eq_labY]; decide +kernel))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "bsi " si:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact nodeW_ab_si (hello1_instOk (rS := ⟨0, 0⟩)) (si := $si) (l := $l) (k := $k)
    (p := labT $l + Int64.ofNat (4 * $k)) (by decide +kernel) rfl (by dsimp only [N]; decide +kernel)
    (by decide +kernel) (by rw [labT_eq_labY]; decide +kernel))

/-- **`scc_rt_alloc`'s states keep the write abort's phase**, none moved,
for a call `q` returning to `wc_rodata`'s `.sp0` (`hra`), in a region of
the allocator's frame, the counter and every header the code may store
unmapped in private memory (`hmem`, `hq`). -/
theorem allocAb (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms (_root_.Executable.labels hello1Exe).label)
    (hra : q.ra = (labT ".L18_wc_rodata.sp0").toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ0 (Ab labT) s) (fun _ _ => False) hello1Exe hello1End R F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hello1_labT]
  · bab "scc_rt_alloc" 0 b0_ok
  · bab ".L2_scc_rt_alloc.0_entry" 0 b1_ok
  · bab ".L2_scc_rt_alloc.0_entry" 4 b2_ok
  · bsi iAdrpC ".L2_scc_rt_alloc.1_cnt" 0
  · bsi iAddC ".L2_scc_rt_alloc.1_cnt" 1
  · bab ".L2_scc_rt_alloc.1_cnt" 2 b3_ok
  · refine nodeW_ab_ldop (hello1_instOk (rS := ⟨0, 0⟩)) (op := .ADD) (kk := .acqRel) (rs := .X9)
      (rt := .X11) (b := .X10) (l := ".L2_scc_rt_alloc.1_cnt") (k := 5)
      (p := labT ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5)) (by decide +kernel) rfl
      (by dsimp only [N]; decide +kernel) (by decide +kernel) (by rw [labT_eq_labY]; decide +kernel)
      fun σ c m hJ hF => ?_
    obtain ⟨-, h10, -⟩ := hJ
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact hmem _ (.inl rfl) m hF
  · bab ".L2_scc_rt_alloc.1_cnt" 6 b4_ok
  · bab ".L2_scc_rt_alloc.1_cnt" 15 b5_ok
  · bab ".L2_scc_rt_alloc.2_slow" 0 b6_ok
  · bab ".L2_scc_rt_alloc.2_slow" 4 b7_ok
  · refine blkW_abG (hello1_instOk (rS := ⟨0, 0⟩)) (l := ".L2_scc_rt_alloc.4_full") (k := 0)
      (dead := fun _ => false) (ra := 0) (by decide +kernel) (by dsimp only [N]; decide +kernel) b9_ok hR hal
      (by omega) (by omega) (by rw [labT_eq_labX]; decide +kernel)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) ?_
    intro σ c hJ k hk a ha s' _ _ hpc' hA'
    match k, hk with
    | 0, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      obtain ⟨-, rfl⟩ := ha
      refine not_ab_of_pc ?_
      rw [hpc']
      dsimp only [Spike.Lib.A64.Flow.AI.tgt, N]
      rw [labT_eq_labY]
      decide +kernel
    | 1, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      subst ha
      have hx := hA'.regs
      intro h
      rcases h with ⟨h1, -⟩ | ⟨h1, -⟩ | h1 | ⟨-, h4⟩ | ⟨h1, -⟩ | h1 | h1
      all_goals first
        | (rw [hpc'] at h1; revert h1; dsimp only [Spike.Lib.A64.Flow.AI.tgt]; rw [labT_eq_labY]; decide +kernel)
        | skip
      have hb9 : List.take 1 b9 = [Spike.Lib.LowerA64.movzD .X0 (2, 0)] := by decide
      rw [hx, hb9] at h4
      simp only [Spike.Lib.A64.Flow.arun, List.foldl,
        Spike.Lib.LowerA64.dstep_movz _ _ _ _ _ (by decide : 2 < 65536) (by decide : 0 < 4)] at h4
      revert h4
      simp only [Spike.Lib.A64.Flow.AI.step, Spike.Lib.LowerA64.mkStep, Reg64s.setXReg, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64]
      decide
  · bab ".L2_scc_rt_alloc.5_ok" 0 b11_ok
  · bsi iAdrpH ".L2_scc_rt_alloc.5_ok" 8
  · bsi iAddH ".L2_scc_rt_alloc.5_ok" 9
  · bab ".L2_scc_rt_alloc.5_ok" 10 b12_ok
  · refine nodeW_ab_st (hello1_instOk (rS := ⟨0, 0⟩)) (t := .X9) (b := .X10) (i := 0)
      (l := ".L2_scc_rt_alloc.5_ok") (k := 41) (p := labT ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41))
      (by decide +kernel) rfl (by dsimp only [N]; decide +kernel) (by decide +kernel)
      (by rw [labT_eq_labY]; decide +kernel) fun σ c m hJ hF => ?_
    obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, h10⟩ := hJ
    have hq' := hq m hF
    rw [hello1_labT] at hq'
    have hk := Spike.Lib.A64.Alloc.Call.k_toNat hq'.n_lt
    have hcl := hq'.cells
    have hra : Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 =
        Spike.Lib.A64.Alloc.H labT + o <<< 4 + (q.k * Spike.Lib.A64.Alloc.mOf q.h) <<< 3 := by
      rw [← h10]; simp [Spike.Lib.A64.Flow.rAddr, Reg64s.getXReg]
    have hAeq : (Spike.Lib.A64.Flow.rAddr σ.regs .X10 0).toNat = q.hdrAt ms o.toNat := by
      rw [hra, Spike.Lib.A64.Alloc.base_toNat (by omega) (by omega) (Spike.Lib.A64.Alloc.mOf_lt _)
        (by rw [hq'.heap]; exact hq'.room), hq'.heap, hk]
      rfl
    exact hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF
  · bab ".L2_scc_rt_alloc.5_ok" 42 b13_ok
  · refine Spike.Lib.LowerA64.BlkW.nodeW (blkW_ab (hello1_instOk (rS := ⟨0, 0⟩))
      (l := ".L2_scc_rt_alloc.5_ok") (k := 54) (blk := [iRet.toDir]) (lo := -160) (hi := 0)
      (dead := fun _ => false) (ra := labT ".L18_wc_rodata.sp0") (by decide +kernel)
      (by dsimp only [N]; decide +kernel) (by dsimp only [N]; decide) hR hal (by omega) (by omega)
      (by decide +kernel)
      (hret_of_run (lo := -160) (hi := 0) (by dsimp only [N]; decide) fun σ c hJ => ?_) (fun _ _ _ => rfl)
      (by rw [labT_eq_labY]; decide +kernel)) (List.cons_ne_nil _ _)
    obtain ⟨o, -, -, -, -, -, h30⟩ := hJ
    have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
    simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg,
      h30, hra]

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.A64Hello1W0.blkW_ab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_ab

/-- info: 'Spike.Test.A64Hello1W0.nodeW_ab_si' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_si

/-- info: 'Spike.Test.A64Hello1W0.nodeW_ab_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_st

/-- info: 'Spike.Test.A64Hello1W0.nodeW_ab_ldop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_ldop

/-- info: 'Spike.Test.A64Hello1W0.blkW_abG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abG

/-- info: 'Spike.Test.A64Hello1W0.labT_eq_labY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms labT_eq_labY

/-- info: 'Spike.Test.A64Hello1W0.allocAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAb

end Spike.Test.A64Hello1W0
