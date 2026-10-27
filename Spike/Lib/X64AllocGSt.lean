/-
**`scc_rt_alloc`'s states off the sites and carrying the state's facts at
any instance** (x86-64): `AllocW` (`Spike/Lib/X64Alloc.lean`) inside
`okPc`, `W0`'s abort sites (`AbortW0`) and the state's facts (`SFactsSt`),
for any executable with `InstOk`, its cells holding the allocator's code
(`allocIn`), passing the phase check `allocPhOk`
(`Spike/Lib/X64AllocPh.lean`): `hello1.x`'s `allocPc`, `allocAbortW`,
`allocSt` (`Spike/Test/X64Hello1Alloc{Ctr,W}.lean`) with the kernel's
phase decisions at `labT` replaced by `allocPhOk`. The twin of
`Spike/Lib/A64AllocGSt.lean`, name for name.

- `allocPhOk_spec`, `okPc_of_blkPh`, `phOne_spec`, `blkPh_ret`: the
  check's facts.
- `blkW_pc`, `nodeW_pc`, `blkW_okPc`, `nodeW_okPc`, `abortW0_of_pcOff`:
  states at their pcs.
- `dumN`, `BlkW.st`, `NodeW.st`: the state's facts at any control from
  `SFacts` at the source start's control (`Spike/Test/X64Hello1W0N.lean`'s,
  at any layout).
- `nodeW_si_postA`, `nodeW_st_postA`, `nodeW_xadd_postA`
  (`Spike/Test/X64Hello1AllocW.lean`'s).
- `allocPc`, `allocAbortW`, `allocSt`.
-/
import Spike.Lib.X64AllocG
import Spike.Lib.X64AllocPh

namespace Spike.Lib.X64.AllocG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide FragS Frag Arena)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND At AS SI FI bAddr xaddDir stDir mB eaddr_mB cellOff arun)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk cellOf next_same own_at nodeW_postO nodeW_fi_postO)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (CellAt after exec_store_agrees exec_xaddG_agrees eaddr)
open Spike.Lib.X64ConsumerA (SFactsSt)
open Spike.Lib.X64.StubW (phOne)
open Spike.Lib.X64.W0G (AbortW0)

/-! ## The phase check's facts -/

section Ph

open Spike.Lib.X64.Alloc

variable {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64}

/-- **`allocPhOk`'s facts**, one per node (the `ret`'s two). -/
theorem allocPhOk_spec (h : allocPhOk okPc ph lab = true) :
    aBlk okPc ph lab fnL 0 bPro = true ∧ aBlk okPc ph lab entryL 0 bChk = true ∧
    aBlk okPc ph lab entryL 16 bJ1 = true ∧ phOne okPc ph (lab cntL + Int64.ofNat 0) 7 = true ∧
    aBlk okPc ph lab cntL 7 bC1 = true ∧ phOne okPc ph (lab cntL + Int64.ofNat 19) 5 = true ∧
    aBlk okPc ph lab cntL 24 bC2 = true ∧ aBlk okPc ph lab cntL 59 bJ2 = true ∧
    aBlk okPc ph lab slowL 0 bSlow = true ∧ aBlk okPc ph lab slowL 16 bJ3 = true ∧
    aBlk okPc ph lab fullL 0 bFull = true ∧ aBlk okPc ph lab okL 0 bO0 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 11) 3 = true ∧ aBlk okPc ph lab okL 14 bO1 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 29) 3 = true ∧ aBlk okPc ph lab okL 32 bO2 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 36) 7 = true ∧ aBlk okPc ph lab okL 43 bO3 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 58) 3 = true ∧ aBlk okPc ph lab okL 61 bO4 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 88) 4 = true ∧ aBlk okPc ph lab okL 92 bO5 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 107) 3 = true ∧ aBlk okPc ph lab okL 110 bO6 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 125) 3 = true ∧ aBlk okPc ph lab okL 128 bO7 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 140) 3 = true ∧ aBlk okPc ph lab okL 143 bO8 = true ∧
    phOne okPc ph (lab okL + Int64.ofNat 170) 3 = true ∧ aBlk okPc ph lab okL 173 bO9 = true ∧
    okPc (lab okL + Int64.ofNat 226).toBitVec.toNat = true ∧
    ph (lab okL + Int64.ofNat 226).toBitVec.toNat = ph (lab fnL).toBitVec.toNat := by
  simpa only [allocPhOk, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

end Ph

/-- A block's phase check: every pc off the sites. -/
theorem okPc_of_blkPh {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64}
    {pc ra : Int64} {blk : List (Directive × Nat)} (h : blkPh okPc ph d lab pc ra blk = true) :
    ∀ k < blk.length, okPc (pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat = true := by
  intro k hk
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true] at this
  exact this.1.1

/-- A single instruction's check: its pc off the sites, its next pc in its
phase. -/
theorem phOne_spec {okPc : Nat → Bool} {ph : Nat → Nat} {p : Int64} {z : Nat} (h : phOne okPc ph p z = true) :
    okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat := by
  simpa only [phOne, Bool.and_eq_true, beq_iff_eq] using h

/-- **The `ret`'s phase check** at the return address `ra`: its pc off the
sites, `ra` in its phase. -/
theorem blkPh_ret {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64} {p ra : Int64}
    (hok : okPc p.toBitVec.toNat = true) (hra : ph ra.toBitVec.toNat = ph p.toBitVec.toNat) :
    blkPh okPc ph d lab p ra [(Spike.Lib.X64.Alloc.iRet.toDir, 1)] = true := by
  have hc : Spike.Lib.X64.classify Spike.Lib.X64.Alloc.iRet.toDir = some Spike.Lib.X64.Alloc.iRet := rfl
  have h0 : p + Int64.ofNat (cellOff [(Spike.Lib.X64.Alloc.iRet.toDir, 1)] 0) = p :=
    Spike.Lib.X64.Flow.ofNat_zero' p
  simp only [blkPh, List.length_singleton, List.range_one, List.all_cons, List.all_nil, Bool.and_true,
    List.getElem?_cons_zero, hc, h0]
  simp [Spike.Lib.X64.Alloc.iRet, aiTgts, hok, hra]

/-! ## States at their pcs -/

section Pc

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- A block node's states are at its pcs. -/
theorem blkW_pc {P : Nat → Prop} {n : ND} {blk : List (Directive × Nat)}
    (h : ∀ k < blk.length, P (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat) :
    BlkW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n blk :=
  fun _ _ _ _ _ _ _ _ _ _ k hk _ _ _ => ⟨h k hk, fun _ h => h⟩

/-- A node's states are at its pc. -/
theorem nodeW_pc {P : Nat → Prop} {n : ND} (h : P n.pc.toBitVec.toNat) :
    NodeW (fun s _ => P (pcOf s)) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ =>
    ⟨(congrArg (fun p : Int64 => P p.toBitVec.toNat) hpc).mpr h, fun _ h => h⟩

/-- A block node off the sites from its phase check at its pc. -/
theorem blkW_okPc {okPc : Nat → Bool} {ph : Nat → Nat} {d : Nat → Bool} {lab : Label → Int64} {pc ra : Int64}
    {n : ND} {blk : List (Directive × Nat)} (hb : blkPh okPc ph d lab pc ra blk = true) (he : pc = n.pc) :
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

/-- **A node at the source start's control** (`X64Consumer.c0`, whose
`CFacts` hold, `cfacts_c0`): `n`'s pc and offsets, for the abstract states
of `n`'s invariant. -/
def dumN (n : ND) : ND := ⟨n.pc, n.o, fun σ c' => c' = Spike.Lib.X64Consumer.c0 ∧ ∃ c, n.J σ c⟩

/-- **A block's states carry the state's facts** (`SFactsSt`) at any
control of `n`'s invariant, from `SFacts` at the source start's control
(`dumN`): `SFacts`' state fields read no control. -/
theorem BlkW.st {n : ND} {blk : List (Directive × Nat)}
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

/-! ## A single instruction, a store and a `lock xadd` of an unowned word after the take -/

section Node

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop}

/-- **A node at a single instruction without an event** (`SI`) after the
take, in a region whose frame condition gives the words of `rS` off it
(`hFO`), its next pc in its phase. -/
theorem nodeW_si_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {si : SI} {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(si.toDir, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun _s c σ hs hn _ hpc _ _ hJ hP hO =>
    sfacts_si (hC σ c hJ) hP (cellOf hI hb he hs hn hpc) (next_same hI hpc hph) hO

/-- **A node at a store** `movq %r, k(%b)` after the take, in a region
whose frame condition gives the words of `rS` off it (`hFO`), its next pc
in its phase: the word at the abstract state's address mapped, unmapped in
private memory and owned at no phase (`ha`). -/
theorem nodeW_st_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(stDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧ ∀ j w, (⟨bAddr σ.regs b k, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_store_agrees hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    obtain ⟨hT', hown', htk⟩ := store_facts (Λ := Λ) (own := own) (Tk := Tk) (k := .plain) (s := s)
      (m := s.st.1) (V := (s.st.1.regs.get (.low r .W64)).setWidth 128) hmw
      (next_same hI hpc hph _).2
      (.inl ⟨(next_same hI hpc hph _).1, fun w h => by
        rw [own_at hown hpc] at h; exact hno _ w h⟩)
    exact sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex hT' hown' htk hO

/-- **A node at an unowned word's `lock xaddq %r, k(%b)`** after the take,
as `nodeW_st_postA`: every leaf owns what the state owns, the word written
owned at no phase. -/
theorem nodeW_xadd_postA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    {ownOf : Nat → List (Loc × Val)} (hown : ∀ s, own s = ownOf (ph (pcOf s))) {n : ND} {b r : Reg64} {k : Int64}
    {z : Nat} {l : Label} {off : Nat} {p : Int64} (hb : blockAtB cells l off [(xaddDir b k r, z)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hC : ∀ σ c, n.J σ c → CFacts Λ lbl c)
    (hok : okPc p.toBitVec.toNat = true) (hph : ph (p + Int64.ofNat z).toBitVec.toNat = ph p.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (ha : ∀ σ c m, n.J σ c → F m → Kernel.mapped (K0 Λ) true ⟨bAddr σ.regs b k, 8⟩ = true ∧
      Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧ ∀ j w, (⟨bAddr σ.regs b k, 8⟩, w) ∉ ownOf j) :
    NodeW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F n :=
  nodeW_postO hI hp hok hR hR8 hl hh hsub hFO fun s c σ hs hn hdc hpc hA hD hJ hP hO => by
    have hc := cellOf hI hb he hs hn hpc
    obtain ⟨hmw, hun, hno⟩ := ha σ c s.st.1 hJ hD
    have ha' : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
    have hex := exec_xaddG_agrees (w := .W64) hc ha' hun (Spike.Lib.X64.agrees_of_decls hdc _ _)
    refine sfacts_ev (hC σ c hJ) hP hc (by intro w w' h; cases h) hex (fun h => ?_)
      (.inl ⟨fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).1⟩,
        ⟨fun _ _ _ w h => by rw [own_at hown hpc] at h; exact hno _ w h, fun _ => trivial⟩⟩)
      (fun v _ => ⟨fun _ _ => trivial, (next_same hI hpc hph _).2⟩) hO
    cases h with
    | rmw h => rw [hmw] at h; cases h
    | rmwRet _ h => cases h

end Node

/-! ## `scc_rt_alloc`'s nodes -/

section Alloc

open Spike.Lib.X64.Alloc (Call AllocW N iCtr iHeap iRmw iHdr iRet fnL bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok
  bJ2_ok bSlow_ok bJ3_ok bFull_ok bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)
open Spike.Lib.X64.Flow.Ret0.Inst (cfacts_c0)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_alloc`'s states are off the marks' sites** (`okPc`), its
code passing the phase check (`hph`). -/
theorem allocPc (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hph : allocPhOk okPc ph lab = true) :
    AllocW ms q (fun s _ => okPc (pcOf s) = true) (fun _ _ => False) exe endPc R F := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, -⟩ := allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · exact blkW_okPc p0 (by pc_tac)
  · exact blkW_okPc p1 (by pc_tac)
  · exact blkW_okPc p2 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p3).1 (by pc_tac)
  · exact blkW_okPc p4 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p5).1 (by pc_tac)
  · exact blkW_okPc p6 (by pc_tac)
  · exact blkW_okPc p7 (by pc_tac)
  · exact blkW_okPc p8 (by pc_tac)
  · exact blkW_okPc p9 (by pc_tac)
  · exact blkW_okPc p10 (by pc_tac)
  · exact blkW_okPc p11 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p12).1 (by pc_tac)
  · exact blkW_okPc p13 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p14).1 (by pc_tac)
  · exact blkW_okPc p15 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p16).1 (by pc_tac)
  · exact blkW_okPc p17 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p18).1 (by pc_tac)
  · exact blkW_okPc p19 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p20).1 (by pc_tac)
  · exact blkW_okPc p21 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p22).1 (by pc_tac)
  · exact blkW_okPc p23 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p24).1 (by pc_tac)
  · exact blkW_okPc p25 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p26).1 (by pc_tac)
  · exact blkW_okPc p27 (by pc_tac)
  · exact nodeW_okPc (phOne_spec p28).1 (by pc_tac)
  · exact blkW_okPc p29 (by pc_tac)
  · exact nodeW_okPc p30 (by pc_tac)

omit [Kraken.Executable.ValidLayout exe] in
/-- **`scc_rt_alloc`'s states meet `W0`'s abort sites' obligation**
(vacuously, off them). -/
theorem allocAbortW (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hph : allocPhOk okPc ph lab = true) {ar : Arena} :
    AllocW ms q (fun s c => ∀ fs, AbortW0 μ ar s c fs) (fun _ _ => False) exe endPc R F :=
  AllocW.imp (allocPc hI hph) (Spike.Lib.X64.Alloc.AllocW.triv ms q) fun s _ h _ _ =>
    abortW0_of_pcOff (hI.off s h).1

set_option hygiene false in
/-- A block of `scc_rt_alloc` after the take, no `ret`, no dead target, at
the source start's control. -/
local macro "ablk " hb:term:max ok:term:max hp:term:max : tactic =>
  `(tactic| exact BlkW.st (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static) (dead := fun _ => false) (ra := 0) $hb
    (by pc_tac) $ok hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0) $hp
    (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl) hsub hfit hFO))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "asi " hb:term:max hp:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_si_postA hI (lbl := Λ.static) $hb rfl (by pc_tac)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec $hp).1 (phOne_spec $hp).2 hR hR8 hl hh hsub hFO))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "afi " hb:term:max hp:term:max : tactic =>
  `(tactic| exact NodeW.st (nodeW_fi_postO hI (lbl := Λ.static) $hb rfl (by pc_tac)
    (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec $hp).1 (phOne_spec $hp).2 hR hR8 hl hh hsub hFO))

/-- **`scc_rt_alloc`'s states carry the state's facts** at any control, none
moved by `K`, its code passing the phase check (`hph`), for a call `q`
whose return address is in the phase of the function's entry (`hra`), the
owned words factoring through the phase (`hown`), in a region of the
allocator's frame (8-aligned) whose frame condition gives the stack range
off it (`hFO`) and the call's premises (`hq`), the counter and every header
the code may store unmapped in private memory (`hmem`), owned at no phase
(`hno`), the memory side's writable words mapped (`hmp`). -/
theorem allocSt (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {ownOf : Nat → List (Loc × Val)}
    (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hq : ∀ m, F m → q.OK ms lab)
    (hra : ph (Int64.ofBitVec q.ra).toBitVec.toNat = ph (lab fnL).toBitVec.toNat)
    (hmp : ∀ L, ms.mp L true → Kernel.mapped (K0 Λ) true L = true)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hno : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ j w, (⟨a, 8⟩, w) ∉ ownOf j) :
    AllocW ms q (fun s _ => SFactsSt Λ μ own rS Tk s) K exe endPc R F := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31⟩ := allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hI.labOk]
  · ablk h0 bPro_ok p0
  · ablk h1 bChk_ok p1
  · ablk h2 bJ1_ok p2
  · asi h3 p3
  · ablk h4 bC1_ok p4
  · refine NodeW.st (nodeW_xadd_postA hI hown (lbl := Λ.static) (b := .rcx) (k := 0) (r := .rax) h5 rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p5).1 (phOne_spec p5).2 hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, -, hcx, -⟩ := hJ
    have hq' := hq m hF
    rw [ctr_addr hq' hcx]
    exact ⟨hmp _ hq'.mp, hmem _ (.inl rfl) m hF, hno _ (.inl rfl)⟩
  · ablk h6 bC2_ok p6
  · ablk h7 bJ2_ok p7
  · ablk h8 bSlow_ok p8
  · ablk h9 bJ3_ok p9
  · ablk h10 bFull_ok p10
  · ablk h11 bO0_ok p11
  · afi h12 p12
  · ablk h13 bO1_ok p13
  · afi h14 p14
  · ablk h15 bO2_ok p15
  · asi h16 p16
  · ablk h17 bO3_ok p17
  · afi h18 p18
  · ablk h19 bO4_ok p19
  · afi h20 p20
  · ablk h21 bO5_ok p21
  · afi h22 p22
  · ablk h23 bO6_ok p23
  · afi h24 p24
  · ablk h25 bO7_ok p25
  · afi h26 p26
  · ablk h27 bO8_ok p27
  · refine NodeW.st (nodeW_st_postA hI hown (lbl := Λ.static) (b := .rcx) (k := 0) (r := .rax) h28 rfl rfl
      (fun _ _ hJ => hJ.1 ▸ cfacts_c0) (phOne_spec p28).1 (phOne_spec p28).2 hR hR8 hl hh hsub hFO
      fun σ c m hJ hF => ?_)
    obtain ⟨-, c, o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    have hq' := hq m hF
    have hAeq := hdr_addr hq' hle hn28 hcx
    have hofn : BitVec.ofNat 64 (q.hdrAt ms o.toNat) = bAddr σ.regs .rcx 0 := by
      rw [← hAeq]; simp
    obtain ⟨-, hmp', -⟩ := hq'.hdr o.toNat hle
    exact ⟨hmp _ (hofn ▸ hmp'), hmem _ (.inr ⟨o.toNat, hle, hAeq⟩) m hF, hno _ (.inr ⟨o.toNat, hle, hAeq⟩)⟩
  · ablk h29 bO9_ok p29
  · refine NodeW.st (Spike.Lib.LowerX64.BlkW.nodeW (Spike.Lib.X64.Rt.blkW_postO hI (lbl := Λ.static)
      (blk := [(iRet.toDir, 1)]) (lo := -160) (hi := 8) (dead := fun _ => false) (ra := Int64.ofBitVec q.ra)
      h30 rfl (by dsimp only [dumN, N]; decide) hR hlo hhi hR8 hl hh (fun _ _ hJ => hJ.1 ▸ cfacts_c0)
      (blkPh_ret p30 (by rw [hra, p31]))
      (hret_of_run (lo := -160) (hi := 8) (by dsimp only [dumN, N]; decide) fun σ c hJ => ?_)
      (fun _ _ _ => rfl) hsub hfit hFO) (List.cons_ne_nil _ _))
    obtain ⟨-, c, o, -, -, -, -, -, h0⟩ := hJ
    have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
    simp only [arun, List.foldl, Spike.Lib.X64.dstep, hc]
    simp only [iRet, Spike.Lib.X64.AI.tgt, dumN, N, Spike.Lib.X64.Alloc.oE]
    rw [h0]

end Alloc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.AllocG.allocPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocPc

/-- info: 'Spike.Lib.X64.AllocG.allocAbortW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocAbortW

/-- info: 'Spike.Lib.X64.AllocG.allocSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms allocSt

end Spike.Lib.X64.AllocG
