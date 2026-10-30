/-
**`scc_rt_alloc`'s states off the sites and carrying the state's facts at
any instance** (AArch64): `AllocW` (`Spike/Lib/A64Alloc.lean`) inside
`okPc`, `W0`'s abort sites (`AbortW0`) and the state's facts (`SFactsSt`),
for any executable with `InstOk`, its program holding the allocator's code
(`allocIn`), passing the phase check `allocPhOk`
(`Spike/Lib/A64AllocPh.lean`): `hello1.w`'s `allocPc`, `allocAbortW`,
`allocSt` (`Spike/Test/A64Hello1Alloc{Ctr,W}.lean`) with the kernel's
phase decisions at `labT` replaced by `allocPhOk`.

- `allocPhOk_spec`, `okPc_of_blkPh`, `phOne_spec`, `blkPh_ret`: the
  check's facts.
- `blkW_pc`, `nodeW_pc`, `blkW_okPc`, `nodeW_okPc`, `abortW0_of_pcOff`: states at their pcs.
- `dumN`, `BlkW.st`, `NodeW.st`: the state's facts at any control from
  `SFacts` at the source start's control (`Spike/Test/A64Hello1W0N.lean`'s,
  at any layout).
- `nodeW_si_postA`, `nodeW_st_postA`, `nodeW_ldop_postA`
  (`Spike/Test/A64Hello1AllocW.lean`'s).
- `allocPc`, `allocAbortW`, `allocSt`.
-/
import Spike.Lib.A64AllocG
import Spike.Lib.A64AllocPh

namespace Spike.Lib.A64.AllocG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND At AS)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk cellOf next_same own_at nodeW_postO)
open Scc.Cert.Rt.A64 (blockAt)
open Kraken.Promising.Lower.A64 (CellAt after exec_str_agrees exec_ldop access_agrees)
open Spike.Lib.A64ConsumerA (SFactsSt)
open Spike.Lib.A64.StubW (phOne)
open Spike.Lib.A64.W0G (AbortW0)

/-! ## The phase check's facts -/

section Ph

open Spike.Lib.A64.Alloc

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`allocPhOk`'s facts**, one per node. -/
theorem allocPhOk_spec (h : allocPhOk okPc ph lab = true) :
    blkPh okPc ph (fun _ => false) lab (lab "scc_rt_alloc" + Int64.ofNat (4 * 0)) 0 b0 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 0)) 0 b1 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.0_entry" + Int64.ofNat (4 * 4)) 0 b2 = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 0)) = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 1)) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 2)) 0 b3 = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5)) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 6)) 0 b4 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 15)) 0 b5 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 0)) 0 b6 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.2_slow" + Int64.ofNat (4 * 4)) 0 b7 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0)) 0 b9 = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 0)) 0 b11 = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 8)) = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 9)) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 10)) 0 b12 = true ∧
    phOne okPc ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41)) = true ∧
    blkPh okPc ph (fun _ => false) lab (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 42)) 0 b13 = true ∧
    okPc (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54)).toBitVec.toNat = true ∧
    ph (lab ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54)).toBitVec.toNat =
      ph (lab "scc_rt_alloc").toBitVec.toNat := by
  simpa only [allocPhOk, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

end Ph

/-- A block's phase check: every pc off the sites. -/
theorem okPc_of_blkPh {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List Directive} (h : blkPh okPc ph d lab pc ra blk = true) :
    ∀ k < blk.length, okPc (pc + Int64.ofNat (4 * k)).toBitVec.toNat = true := by
  intro k hk
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- A single instruction's check: its pc off the sites, its next pc in its
phase. -/
theorem phOne_spec {okPc : Nat → Bool} {ph : Nat → Nat} {p : Int64} (h : phOne okPc ph p = true) :
    okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := by
  simpa only [phOne, Bool.and_eq_true, beq_iff_eq] using h

/-- **The `ret`'s phase check** at the return address `ra`: its pc off the
sites, `ra` in its phase. -/
theorem blkPh_ret {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64} {p ra : Int64}
    (hok : okPc p.toBitVec.toNat = true) (hra : ph ra.toBitVec.toNat = ph p.toBitVec.toNat) :
    blkPh okPc ph d lab p ra [Spike.Lib.A64.Alloc.iRet.toDir] = true := by
  have hc : Spike.Lib.A64.Flow.classify Spike.Lib.A64.Alloc.iRet.toDir = some Spike.Lib.A64.Alloc.iRet := rfl
  have hm : p.toBitVec.toNat % 18446744073709551616 = p.toBitVec.toNat := Nat.mod_eq_of_lt p.toBitVec.isLt
  simp only [blkPh, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true,
    List.getElem?_cons_zero, hc]
  simp [Spike.Lib.A64.Alloc.iRet, aiTgts, hok, hra, hm]

/-! ## States at their pcs -/

section Pc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- A block node's states are at its pcs. -/
theorem blkW_pc {P : Nat → Prop} {n : ND} {blk : List Directive}
    (h : ∀ k < blk.length, P (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat) :
    BlkW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨h k hk, fun _ h => h⟩

/-- A node's states are at its pc. -/
theorem nodeW_pc {P : Nat → Prop} {n : ND} (h : P n.pc.toBitVec.toNat) :
    NodeW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ =>
    ⟨(congrArg (fun p : Int64 => P p.toBitVec.toNat) hpc).mpr h, fun _ h => h⟩

/-- A block node off the sites from its phase check at its pc. -/
theorem blkW_okPc {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64} {pc ra : Int64}
    {n : ND} {blk : List Directive} (hb : blkPh okPc ph d lab pc ra blk = true) (he : pc = n.pc) :
    BlkW (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F n blk :=
  blkW_pc (P := fun p => okPc p = true) fun k hk => he ▸ okPc_of_blkPh hb k hk

/-- A node off the sites from its pc's. -/
theorem nodeW_okPc {okPc : Nat → Bool} {p : Int64} {n : ND} (h : okPc p.toBitVec.toNat = true) (he : p = n.pc) :
    NodeW (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F n :=
  nodeW_pc (P := fun p => okPc p = true) (he ▸ h)

/-- **The abort sites at a pair off them**: vacuous. -/
theorem abortW0_of_pcOff {μ : Marks} {ar : Arena} {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : PcOff μ s) : AbortW0 μ ar s c fs :=
  fun k a ha hpc => (h.noAbort k a ha hpc).elim

end Pc

/-! ## The state's facts at any control -/

section St

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {K : State → State → Prop} {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop}
  {lbl : Lbl}

/-- **A node at the source start's control** (`A64Consumer.c0`, whose
`CFacts` hold, `cfacts_c0`): `n`'s pc and offsets, for the abstract states
of `n`'s invariant. -/
def dumN (n : ND) : ND := ⟨n.pc, n.o, fun σ c' => c' = Spike.Lib.A64Consumer.c0 ∧ ∃ c, n.J σ c⟩

/-- **A block's states carry the state's facts** (`SFactsSt`) at any
control of `n`'s invariant, from `SFacts` at the source start's control
(`dumN`): `SFacts`' state fields read no control. -/
theorem BlkW.st {n : ND} {blk : List Directive}
    (h : BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk) :
    BlkW (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    let h' := h s σ _ he hn hd hp hA hF ⟨rfl, c, hJ⟩ k hk m hA' hD
    ⟨h'.1.toSt, h'.2⟩

/-- **A node's states carry the state's facts** (as `BlkW.st`). -/
theorem NodeW.st {n : ND} (h : NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n)) :
    NodeW (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F n :=
  fun s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩ =>
    let h' := h s _ ⟨h1, h2, h3, h4, σ, hA, hF, rfl, c, hJ⟩
    ⟨h'.1.toSt, h'.2⟩

end St

/-! ## A store and an RMW of an unowned word after the take -/

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at a single instruction without an event** (`SI`) after the
take, in a region whose frame condition gives the words of `rS` off it
(`hFO`), its next pc in its phase. -/
theorem nodeW_si_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND}
    {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [si.toDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a store** `str Xt, [Xn, #i]` after the take, in a region
whose frame condition gives the words of `rS` off it (`hFO`), its next pc
in its phase: the word at the abstract state's address mapped, unmapped in
private memory and owned at no phase (`ha`). -/
theorem nodeW_st_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {t b : XReg} {i : Int64}
    {l : Label} {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.strDir t b i] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩ = true ∧
      Mem.loadInt m.dmem (Spike.Lib.A64.Flow.rAddr σ.regs b i) 8 = none ∧
      ∀ j w, (⟨Spike.Lib.A64.Flow.rAddr σ.regs b i, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : Spike.Lib.A64.Flow.rAddr s.st.1.regs b i = Spike.Lib.A64.Flow.rAddr σ.regs b i := by rw [hA.regs]
    have hex := exec_str_agrees hc ha' hun (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.getRegOrZr (.low (.reg t) .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex hT' hown' htk hO

/-- **A node at an unowned word's `ld<op><k> Xs, Xt, [Xn]`** after the take,
as `nodeW_st_postA`: every leaf owns what the state owns, the word written
owned at no phase. -/
theorem nodeW_ldop_postA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {op : AtomicOp}
    {kk : Kraken.RmwKind} {rs rt b : XReg} {l : Label} {k : Nat} {p : Int64}
    (hb : blockAt prog l k [Spike.Lib.A64.Flow.ldopDir op kk rs rt b] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨(σ.regs.getXReg b).toBitVec, 8⟩ = true ∧
      Mem.loadInt m.dmem (σ.regs.getXReg b).toBitVec 8 = none ∧
      ∀ j w, (⟨(σ.regs.getXReg b).toBitVec, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : (s.st.1.regs.getXReg b).toBitVec = (σ.regs.getXReg b).toBitVec := by rw [hA.regs]
    have hex := exec_ldop hc (by rw [ha']; exact hun)
    rw [ha', access_agrees (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)] at hex
    refine sfacts_ev (hC σ c hJ) hP hc (by intro imm h; cases h) hex (fun h => ?_)
      (.inl ⟨fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).1⟩,
        ⟨fun _ _ _ w h => by rw [own_at hown hpc] at h; exact hno _ w h, fun _ => trivial⟩⟩)
      (fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).2⟩) hO
    cases h with
    | rmw h => rw [hmw] at h; cases h
    | rmwRet _ h => cases h

end Node

/-- **A node's pc at its label and offset**, either side (`pc_tac` through
`dumN`). -/
macro "pcs_tac" : tactic =>
  `(tactic| (dsimp only [dumN, Spike.Lib.A64.Alloc.N]; first | (simp only [Int64.add_assoc]; rfl) | simp))

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.A64.Alloc (Call AllocW N iAdrpC iAddC iAdrpH iAddH iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_alloc`'s states are off the marks' sites** (`okPc`), its
code passing the phase check (`hph`). -/
theorem allocPc (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hph : allocPhOk okPc ph lab = true) :
    AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, -⟩ :=
    allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · exact blkW_okPc p0 (by pc_tac)
  · exact blkW_okPc p1 (by pc_tac)
  · exact blkW_okPc p2 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p3).1 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p4).1 (by pc_tac)
  · exact blkW_okPc p5 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p6).1 (by pc_tac)
  · exact blkW_okPc p7 (by pc_tac)
  · exact blkW_okPc p8 (by pc_tac)
  · exact blkW_okPc p9 (by pc_tac)
  · exact blkW_okPc p10 (by pc_tac)
  · exact blkW_okPc p11 (by pc_tac)
  · exact blkW_okPc p12 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p13).1 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p14).1 (by pc_tac)
  · exact blkW_okPc p15 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p16).1 (by pc_tac)
  · exact blkW_okPc p17 (by pc_tac)
  · exact nodeW_okPc p18 (by pc_tac)

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_alloc`'s states meet `W0`'s abort sites' obligation**
(vacuously, off them). -/
theorem allocAbortW (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hph : allocPhOk okPc ph lab = true) {ar : Arena} :
    AllocW ms q (fun s c => ∀ fs, AbortW0 μ ar s c fs) (fun _ _ => False) exe endPc R F :=
  AllocW.imp (allocPc hI hph) (Spike.Lib.A64.Alloc.AllocW.triv ms q) fun s _ h _ _ =>
    abortW0_of_pcOff (hI.off s h).1

set_option hygiene false in
/-- A block of `scc_rt_alloc` after the take, no `ret`, no dead target, at
the source start's control. -/
local macro "ablk " hb:term:max ok:term:max hp:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.A64.Rt.blkW_postO hI (lbl := Λ.static) (dead := fun _ => false) (ra := 0) $hb
    (by pcs_tac)
    $ok hR hal (by omega) (by omega) (fun _ _ hJ => hJ.1 ▸ cfacts_c0) $hp
    (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hl hh hsub hfit hFO))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "asi " hb:term:max hp:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_si_postA hI (lbl := Λ.static) $hb rfl (by pcs_tac) (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
    (phOne_spec $hp).1 (phOne_spec $hp).2 hR hR8 hl hh hsub hFO))

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control, none
moved by `K`, its code passing the phase check (`hph`), for a call `q`
whose return address is in the phase of the function's entry (`hra`), the
owned words factoring through the phase (`hown`), in a region of the
allocator's frame (8-aligned) whose frame condition gives the stack range
off it (`hFO`) and the call's premises at any allocation site (`hq`,
`Call.OKS`), the counter and every header
the code may store unmapped in private memory (`hmem`), owned at no phase
(`hno`), the memory side's writable words mapped (`hmp`). -/
theorem allocStS (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OKS ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F := by
  have hR8 : R.base.toNat % 8 = 0 := by omega
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19⟩ :=
    allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · ablk h0 b0_ok p0
  · ablk h1 b1_ok p1
  · ablk h2 b2_ok p2
  · asi h3 p3
  · asi h4 p4
  · ablk h5 b3_ok p5
  · refine NodeW.st (nodeW_ldop_postA hI hown (lbl := Λ.static) (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11)
      (b := .X10)
      h6 rfl (by pcs_tac) (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p6).1 (phOne_spec p6).2
      hR hR8 hl hh hsub hFO fun σ c m hJ hF => ?_)
    obtain ⟨-, c, -, h10, -⟩ := hJ
    have hq' := hq m hF
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact ⟨hmp _ hq'.mp, hmem _ (.inl rfl) m hF, hno _ (.inl rfl)⟩
  · ablk h7 b4_ok p7
  · ablk h8 b5_ok p8
  · ablk h9 b6_ok p9
  · ablk h10 b7_ok p10
  · ablk h11 b9_ok p11
  · ablk h12 b11_ok p12
  · asi h13 p13
  · asi h14 p14
  · ablk h15 b12_ok p15
  · refine NodeW.st (nodeW_st_postA hI hown (lbl := Λ.static) (t := .X9) (b := .X10) (i := 0) h16 rfl (by pcs_tac)
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p16).1 (phOne_spec p16).2 hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, o, ⟨-, hle, -, hn28, -, hlo⟩, -, -, h10⟩ := hJ
    have hq' := hq m hF
    have hAeq := hdr_addrS hq' hle hn28 h10
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = Spike.Lib.A64.Flow.rAddr σ.regs .X10 0 := by
      rw [← hAeq]; simp
    obtain ⟨-, hmp', -⟩ := hq'.hdr o.toNat hlo hle
    exact ⟨hmp _ (hofn ▸ hmp'), hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF, hno _ (.inr ⟨o.toNat, hle, hAeq⟩)⟩
  · ablk h17 b13_ok p17
  · refine NodeW.st (Spike.Lib.LowerA64.BlkW.nodeW (Spike.Lib.A64.Rt.blkW_postO hI
      (lbl := Λ.static) (blk := [iRet.toDir]) (lo := -160) (hi := 0) (dead := fun _ => false)
      (ra := Int64.ofBitVec q.ra) h18
      (by pcs_tac) (by dsimp only [dumN, N]; decide) hR hal (by omega) (by omega)
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (blkPh_ret p18 (by rw [hra, p19]))
      (hret_of_run (lo := -160) (hi := 0) (by dsimp only [dumN, N]; decide) fun σ c hJ => ?_) (fun _ _ _ => rfl)
      hl hh hsub hfit hFO) (List.cons_ne_nil _ _))
    obtain ⟨-, c, o, -, -, -, -, -, h30⟩ := hJ
    have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
    simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
    simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, Reg64s.getXReg,
      h30]

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control:
`allocStS` at a buffer allocation (`Call.OK`). -/
theorem allocSt (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab "scc_rt_alloc").toBitVec.toNat)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F :=
  allocStS hI hA hph hown hR hal hlo hhi hl hh hsub hfit hFO (fun m h => (hq m h).toS) hra hmp hmem hno

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.AllocG.allocPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocPc

/-- info: 'Spike.Lib.A64.AllocG.allocAbortW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbortW

/-- info: 'Spike.Lib.A64.AllocG.allocSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocSt

/-- info: 'Spike.Lib.A64.AllocG.allocStS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocStS

end Spike.Lib.A64.AllocG
