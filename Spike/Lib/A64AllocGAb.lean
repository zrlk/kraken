/-
**`scc_rt_alloc`'s states keep the write abort's phase at any instance**
(AArch64): `AllocW` (`Spike/Lib/A64Alloc.lean`) inside
`AbSt μ (WriteAb.Ab lab)`, none moved, for any executable with `InstOk`,
its program holding the allocator's code (`allocIn`), passing the phase
check (`allocPhOk`) and with its targets off the write abort's pcs
(`allocAbOkR`): `hello1.w`'s `allocAb` (`Spike/Test/A64Hello1AllocAb.lean`)
with the kernel's decisions over `labY`'s numeric tables replaced by
`allocAbOkR` at the labels `lab`.

- `blkW_ab`, `blkW_abG`, `not_ab_after`, `nodeW_ab_si`, `nodeW_ab_st`,
  `nodeW_ab_ldop`: `hello1.w`'s generic lemmas.
- `blkAbC_eq`, `allocAbOk_spec`: the check `allocAbOkR`
  (`Spike/Lib/A64AllocAbOk.lean`, every node's targets off `abPcs lab`, the
  heap abort's call target off every pc of `Ab` but the dispatcher's
  prologue, which `Ab` holds only at `x0 = 4`) node by node.
- `allocAb`.
-/
import Spike.Lib.A64AllocGSt
import Spike.Lib.A64AllocAbOk
import Spike.Lib.A64AbSt
import Spike.Lib.LowerA64.MovImm

namespace Spike.Lib.A64.AllocG

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

/-! ## The check -/

section Chk

open Spike.Lib.A64.Alloc
open Spike.Lib.A64.WriteAb (pcRet tailPcs failPcs dispTPcs g4Pcs stubPcs)

variable {lab : Label → Int64}

/-- **`blkAbC` is `blkAb`.** -/
theorem blkAbC_eq {p ra : Int64} {blk : List Directive} : blkAbC lab p ra blk = blkAb lab p ra blk := rfl

/-- **`allocAbOkR`'s facts**, one per node. -/
theorem allocAbOk_spec (h : allocAbOkR lab = true) :
    blkAb lab (lab "scc_rt_alloc" + Int64.ofNat (4 * 0)) 0 b0 = true ∧
    blkAb lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 0)) 0 b1 = true ∧
    blkAb lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 4)) 0 b2 = true ∧
    lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 0) + Int64.ofNat 4 ∉ abPcs lab ∧
    lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 1) + Int64.ofNat 4 ∉ abPcs lab ∧
    blkAb lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 2)) 0 b3 = true ∧
    lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) + Int64.ofNat 4 ∉ abPcs lab ∧
    blkAb lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 6)) 0 b4 = true ∧
    blkAb lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 15)) 0 b5 = true ∧
    blkAb lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 0)) 0 b6 = true ∧
    blkAb lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 4)) 0 b7 = true ∧
    lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) + Int64.ofNat 4 ∉ abPcs lab ∧
    lab "scc_rt_abort" ∉ abNoDispE lab ∧
    blkAb lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 0)) 0 b11 = true ∧
    lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 8) + Int64.ofNat 4 ∉ abPcs lab ∧
    lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 9) + Int64.ofNat 4 ∉ abPcs lab ∧
    blkAb lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 10)) 0 b12 = true ∧
    lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) + Int64.ofNat 4 ∉ abPcs lab ∧
    blkAb lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 42)) 0 b13 = true := by
  simp only [allocAbOkR, blkAbC_eq, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem] at h
  simpa only [and_assoc] using h

/-- **The heap abort's call target is out of `Ab`** at `x0 ≠ 4`, off every
other pc of it. -/
theorem not_ab_abort {s : State} (hpc : s.st.2 = lab "scc_rt_abort") (hx : s.st.1.regs.X0 ≠ 4)
    (hn : lab "scc_rt_abort" ∉ abNoDispE lab) : ¬ Ab lab s := by
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, h4⟩ | ⟨h, -⟩ | h | h)
  all_goals first
    | exact hx h4
    | (rw [hpc] at h; exact hn (by simp [abNoDispE, h]))

/-- **The `ret`'s targets off the write abort's pcs**: its return address. -/
theorem blkAb_ret {p ra : Int64} (h : ra ∉ abPcs lab) : blkAb lab p ra [iRet.toDir] = true := by
  have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
  simp only [blkAb, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true,
    List.getElem?_cons_zero, hc]
  simpa [iRet, aiTgts] using h

end Chk

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A block of `scc_rt_alloc` with no `ret`, its targets off the write
abort's pcs. -/
local macro "bab " hb:term:max ok:term:max hp:term:max ha:term:max : tactic =>
  `(tactic| exact blkW_ab hI (dead := fun _ => false) (ra := 0) $hb (by pc_tac) $ok hR hal (by omega) (by omega)
    $hp (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) $ha)

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "bsi " hb:term:max hp:term:max ha:term:max : tactic =>
  `(tactic| exact nodeW_ab_si hI $hb rfl (by pcs_tac) (phOne_spec $hp).1 $ha)

/-- **`scc_rt_alloc`'s states keep the write abort's phase**, none moved,
its code passing the phase check (`hph`) and its targets off the write
abort's pcs (`hab`), for a call `q` whose return address is off them
(`hraAb`) and in the entry's phase (`hra`), in a region of the allocator's frame, the counter and every
header the code may store unmapped in private memory (`hmem`, `hq`). -/
theorem allocAb (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (hab : allocAbOkR lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hraAb : Int64.ofBitVec q.ra ∉ abPcs lab)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19⟩ :=
    allocPhOk_spec hph
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a11', a12, a13, a14, a15, a16, a17⟩ :=
    allocAbOk_spec hab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · bab h0 b0_ok p0 a0
  · bab h1 b1_ok p1 a1
  · bab h2 b2_ok p2 a2
  · bsi h3 p3 a3
  · bsi h4 p4 a4
  · bab h5 b3_ok p5 a5
  · refine nodeW_ab_ldop hI (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) h6 rfl (by pcs_tac)
      (phOne_spec p6).1 a6 fun σ c m hJ hF => ?_
    obtain ⟨-, h10, -⟩ := hJ
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact hmem _ (.inl rfl) m hF
  · bab h7 b4_ok p7 a7
  · bab h8 b5_ok p8 a8
  · bab h9 b6_ok p9 a9
  · bab h10 b7_ok p10 a10
  · refine blkW_abG hI (dead := fun _ => false) (ra := 0) h11 (by pc_tac) b9_ok hR hal (by omega) (by omega) p11
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) ?_
    intro σ c hJ k hk a ha s' _ _ hpc' hA'
    match k, hk with
    | 0, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      obtain ⟨-, rfl⟩ := ha
      refine not_ab_of_pc ?_
      rw [hpc']
      dsimp only [Spike.Lib.A64.Flow.AI.tgt, N]
      exact a11
    | 1, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      subst ha
      refine not_ab_abort (by rw [hpc']; rfl) ?_ a11'
      intro h4
      have hx := hA'.regs
      have hb9 : List.take 1 b9 = [Spike.Lib.LowerA64.movzD .X0 (2, 0)] := by decide
      rw [hx, hb9] at h4
      simp only [Spike.Lib.A64.Flow.arun, List.foldl,
        Spike.Lib.LowerA64.dstep_movz _ _ _ _ _ (by decide : 2 < 65536) (by decide : 0 < 4)] at h4
      revert h4
      simp only [Spike.Lib.A64.Flow.AI.step, Spike.Lib.LowerA64.mkStep, Reg64s.setXReg, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64]
      decide
  · bab h12 b11_ok p12 a12
  · bsi h13 p13 a13
  · bsi h14 p14 a14
  · bab h15 b12_ok p15 a15
  · refine nodeW_ab_st hI (t := .X9) (b := .X10) (i := 0) h16 rfl (by pcs_tac) (phOne_spec p16).1 a16
      fun σ c m hJ hF => ?_
    obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addr (hq m hF) hle hn28 h10⟩) m hF
  · bab h17 b13_ok p17 a17
  · refine Spike.Lib.LowerA64.BlkW.nodeW (blkW_ab hI (blk := [iRet.toDir]) (lo := -160) (hi := 0)
      (dead := fun _ => false) (ra := Int64.ofBitVec q.ra) h18 (by pc_tac) (by dsimp only [N]; decide) hR hal
      (by omega) (by omega) (blkPh_ret p18 (by rw [hra, p19]))
      (hret_of_run (lo := -160) (hi := 0) (by dsimp only [N]; decide) fun σ c hJ => ?_) (fun _ _ _ => rfl)
      (blkAb_ret hraAb)) (List.cons_ne_nil _ _)
    obtain ⟨o, -, -, -, -, -, h30⟩ := hJ
    have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
    simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg,
      h30]

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.AllocG.allocAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAb

end Spike.Lib.A64.AllocG
