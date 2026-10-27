/-
**`hello1.w`'s `wc_rodata` at cells other than `MSR` on AArch64**: the
node obligations of `wc_rodata`'s segments and of `scc_rt_alloc` strengthened
to states at cells other than an `MSR`, none moved by `K`, so that
`SegW.keepTP` (`Spike/Lib/A64KeepTP.lean`) carries the thread pointer
across them.

- `NoMsrW W K`: `W`, at a cell other than an `MSR`, not moved by `K`;
  `noMsrAt_of_code`: a state at a cell of a code segment with no `MSR`;
- `NodeW.noMsr`, `BlkW.noMsr`, `ProW.noMsr`: a node's, a block node's, a
  prologue's obligation at code with no `MSR` is one inside `NoMsrW W K`;
- `SegW.keepTPN`: `SegW.keepTP` for a segment inside `NoMsrW W K` (the
  outside moves vacuous), back inside `W`; `SegW.keepTPN'`: into a `W`
  relative to the thread pointer (`SegW.keepTP'`);
- `alloc_code_of`: `scc_rt_alloc`'s code from `allocIn`; `AllocW.noMsr`:
  its obligations inside `NoMsrW W K`;
- `Hello1.RdPreW.noMsr`, `Hello1.RdPostLW.noMsr`: `wc_rodata`'s, in any
  valid layout of `hello1Prog`.
-/
import Spike.Lib.A64KeepTP
import Spike.Lib.A64Hello1RodataPostS

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap labelGap)
open Spike.Lib.A64.KeepTP (NoMsrAt dNoMsr TP tpXa)

set_option linter.unusedSimpArgs false

/-! ## Nodes at cells other than `MSR` -/

/-- **`W` at cells other than an `MSR`, not moved by `K`.** -/
def NoMsrW (W : Frag isaLSE2) (K : State → State → Prop) : Frag isaLSE2 :=
  fun s c => W s c ∧ NoMsrAt s ∧ ∀ s', ¬ K s s'

/-- A state at a cell of a code segment with no `MSR`. -/
theorem noMsrAt_of_code {st s : State} {pc : Int64} {ds : List Directive} (h : CodeAt st pc ds)
    (hds : ds.all dNoMsr = true) {j : Nat} (hj : j < ds.length) (he : s.exe = st.exe)
    (hn : s.endPc = st.endPc) (hp : s.st.2 = pc + Int64.ofNat (4 * j)) : NoMsrAt s :=
  ⟨ds[j], 4, h.cell (List.getElem?_eq_getElem hj) he hn hp, List.all_eq_true.mp hds _ (List.getElem_mem hj)⟩

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **A node at code with no `MSR`** is inside `NoMsrW W K`. -/
theorem NodeW.noMsr {n : ND} {ds : List Directive} (h : NodeW W K exe endPc R F n)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ds) (hne : 0 < ds.length)
    (hds : ds.all dNoMsr = true) : NodeW (NoMsrW W K) K exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, -, hpc, -⟩ := id hAt
  obtain ⟨hw, hk⟩ := h s c hAt
  exact ⟨⟨hw, noMsrAt_of_code (hcode s he hn) hds hne rfl rfl (by rw [hpc, ofNat4_zero]), hk⟩, hk⟩

/-- **A block node with no `MSR`** is inside `NoMsrW W K`. -/
theorem BlkW.noMsr {n : ND} {blk : List Directive} (h : BlkW W K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hds : blk.all dNoMsr = true) : BlkW (NoMsrW W K) K exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  obtain ⟨hw, hK⟩ := h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  exact ⟨⟨hw, noMsrAt_of_code (hcode s he hn) hds hk rfl rfl rfl, hK⟩, hK⟩

/-- **A segment inside `NoMsrW W K` keeps the thread pointer** (`SegW.keepTP`,
the outside moves vacuous). -/
theorem SegW.keepTPN {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {P Q : Frag isaLSE2} {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    (h : SegW (NoMsrW W K) K p lbl (tpXa ms t) P Q) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  (KeepTP.SegW.keepTP hK h (fun _ _ hw => hw.2.1) fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim).mono_W
    fun _ _ hw => hw.1

/-- **A segment inside `NoMsrW W' K` keeps the thread pointer, into a `W`
relative to it** (`SegW.keepTP'`, the outside moves vacuous; `hW`: `W'`'s
states at thread pointer `t` are in `W`). -/
theorem SegW.keepTPN' {W' : Frag isaLSE2} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    (h : SegW (NoMsrW W' K) K p lbl (tpXa ms t) P Q) (hW : ∀ s c, W' s c → TP t s → W s c) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  KeepTP.SegW.keepTP' hK h (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
    fun s c hw ht => hW s c hw.1 ht

/-- **A prologue at code with no `MSR`** is inside `NoMsrW W K`. -/
theorem ProW.noMsr {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop} (h : ProW W K exe endPc R F ms pc0 Z lim L ps J)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 (chkHead Z))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4) [ldrDir .X10 .X10 lim])
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4) (chkBr L))
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4 + 4 + 4) (frameSet Z ps))
    (h0 : (chkHead Z).all dNoMsr = true) (h1 : [ldrDir .X10 .X10 lim].all dNoMsr = true)
    (h2 : (chkBr L).all dNoMsr = true) (h3 : (frameSet Z ps).all dNoMsr = true) :
    ProW (NoMsrW W K) K exe endPc R F ms pc0 Z lim L ps J :=
  ⟨BlkW.noMsr h.w0 hc0 h0, NodeW.noMsr h.w1 hc1 (by simp) h1, BlkW.noMsr h.w2 hc2 h2, BlkW.noMsr h.w3 hc3 h3⟩

end W

/-! ## `scc_rt_alloc` -/

section Alloc

open Scc.Cert.Rt.A64.Print (code_field add4 add0)
open Spike.Lib.A64.Alloc

variable {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop} {q : Call}

/-- **`scc_rt_alloc`'s code** in any valid layout of a program with
`allocIn`. -/
theorem alloc_code_of [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true) :
    Code ms q exe endPc := by
  simp only [allocIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ := hprog
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact code_field hp hend h0 (by simp only [N, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, add4, add0])
  · exact code_field hp hend h3 (by simp only [N, add4, add0])
  · exact code_field hp hend h4 (by simp only [N, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, add4, add0])
  · exact code_field hp hend h6 (by simp only [N, add4, add0])
  · exact code_field hp hend h7 (by simp only [N, add4, add0])
  · exact code_field hp hend h8 (by simp only [N, add4, add0])
  · exact code_field hp hend h9 (by simp only [N, add4, add0])
  · exact code_field hp hend h10 (by simp only [N, add4, add0])
  · exact code_field hp hend h11 (by simp only [N, add4, add0])
  · exact code_field hp hend h12 (by simp only [N, add4, add0])
  · exact code_field hp hend h13 (by simp only [N, add4, add0])
  · exact code_field hp hend h14 (by simp only [N, add4, add0])
  · exact code_field hp hend h15 (by simp only [N, add4, add0])
  · exact code_field hp hend h16 (by simp only [N, add4, add0])
  · exact code_field hp hend h17 (by simp only [N, add4, add0])
  · exact code_field hp hend h18 (by simp only [N, add4, add0])

/-- **`scc_rt_alloc` at its code is inside `NoMsrW W K`**: none of its
blocks is an `MSR`. -/
theorem AllocW.noMsr (h : AllocW ms q W K exe endPc R F) (hc : Code ms q exe endPc) :
    AllocW ms q (NoMsrW W K) K exe endPc R F :=
  ⟨BlkW.noMsr h.e hc.e (by decide), BlkW.noMsr h.entry hc.entry (by decide),
    BlkW.noMsr h.n2 hc.n2 (by decide), NodeW.noMsr h.cnt hc.cnt (by simp) (by decide),
    NodeW.noMsr h.cnt1 hc.cnt1 (by simp) (by decide), BlkW.noMsr h.cnt2 hc.cnt2 (by decide),
    NodeW.noMsr h.rmw hc.rmw (by simp) (by decide), BlkW.noMsr h.n4 hc.n4 (by decide),
    BlkW.noMsr h.n5 hc.n5 (by decide), BlkW.noMsr h.slow hc.slow (by decide),
    BlkW.noMsr h.n7 hc.n7 (by decide), BlkW.noMsr h.full hc.full (by decide),
    BlkW.noMsr h.ok hc.ok (by decide), NodeW.noMsr h.ok1 hc.ok1 (by simp) (by decide),
    NodeW.noMsr h.ok2 hc.ok2 (by simp) (by decide), BlkW.noMsr h.n12 hc.n12 (by decide),
    NodeW.noMsr h.hdr hc.hdr (by simp) (by decide), BlkW.noMsr h.n13 hc.n13 (by decide),
    NodeW.noMsr h.ret hc.ret (by simp) (by decide)⟩

end Alloc

/-! ## `wc_rodata` -/

namespace Hello1

open Spike.Lib.A64.Alloc (Call AllocW)

variable {ms : MemSide isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}

/-- **`wc_rodata` up to the allocator's return is inside `NoMsrW W K`** in any
valid layout of `hello1Prog`. -/
theorem RdPreW.noMsr (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    {J0 Jc : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 Jc) :
    RdPreW (NoMsrW W K) K exe endPc R F ms J0 Jc := by
  have hin := hello1_rodataPro
  simp only [h1RodataPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have he := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at he
  refine ⟨ProW.noMsr h.pro (code_of hp hend b0 ?_) (code_of hp hend b1 ?_) (code_of hp hend b2 ?_)
    (code_of hp hend b3 ?_) (by decide) (by decide) (by decide) (by decide),
    BlkW.noMsr h.e (code_of hp hend he.1 (ofNat4_zero _)) (by decide),
    fun q hok hq => AllocW.noMsr (h.alloc q hok hq) (alloc_code_of hp hend hello1_alloc)⟩
  · rw [e0, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]
  · rw [e0]; simp only [ofNat4_succ, ofNat4_zero]

/-- **`wc_rodata` from the allocator's return is inside `NoMsrW W K`** in any
valid layout of `hello1Prog`. -/
theorem RdPostLW.noMsr (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} (h : RdPostLW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4) :
    RdPostLW (NoMsrW W K) K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  exact ⟨BlkW.noMsr h.s0 (code_of hp hend c0 (ofNat4_zero _)) (by decide),
    NodeW.noMsr h.l1 (code_of hp hend c1 rfl) (by simp) (by decide),
    BlkW.noMsr h.s1 (code_of hp hend c2 rfl) (by decide),
    NodeW.noMsr h.x1 (code_of hp hend c3 rfl) (by simp) (by decide),
    BlkW.noMsr h.s2 (code_of hp hend c4 rfl) (by decide),
    NodeW.noMsr h.l2 (code_of hp hend c5 rfl) (by simp) (by decide),
    BlkW.noMsr h.s3 (code_of hp hend c6 rfl) (by decide),
    NodeW.noMsr h.x2 (code_of hp hend c7 rfl) (by simp) (by decide),
    BlkW.noMsr h.s4 (code_of hp hend c8 rfl) (by decide)⟩

end Hello1

end Spike.Lib.A64.Flow
