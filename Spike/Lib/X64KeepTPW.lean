/-
**Node obligations at cells other than `syscall` on x64**: a node's, a
block node's, a prologue's and `scc_rt_alloc`'s obligations strengthened to
states at cells other than a `syscall`, none moved by `K`, so that
`SegW.keepTP` (`Spike/Lib/X64KeepTP.lean`) carries `fsBase` across them. The
AArch64 mirror is the first half of `Spike/Lib/A64Hello1RodataTP.lean`.

- `NoSetFsW W K`: `W`, at no `arch_prctl`, not moved by `K`;
  `noSetFsAt_of_code`: a state at a cell of a code segment with no `syscall`;
- `NodeW.noSetFs`, `BlkW.noSetFs`, `XProW.noSetFs`: a node's, a block
  node's, a prologue's obligation at code with no `syscall` is one inside
  `NoSetFsW W K` (a prologue has none);
- `SegW.keepTPN`: `SegW.keepTP` for a segment inside `NoSetFsW W K` (the
  outside moves vacuous), back inside `W`;
- `Alloc.AllocW.noSetFs`: `scc_rt_alloc`'s obligations inside `NoSetFsW W K`
  in any valid layout of cells with its code (`allocIn`).
-/
import Spike.Lib.X64KeepTP
import Spike.Lib.X64Alloc

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64
open Spike.Lib.X64.KeepTP (NoSetFsAt dNoSys TP tpXa noSetFsAt_of_cell)
open Spike.Lib.X64.Flow (XProW xHead xLea xCmp xFr xSt ofNat_zero')
open Scc.Cert.Rt.X64 (Lays endOf code_field)

set_option linter.unusedSimpArgs false

/-! ## Nodes at cells other than `syscall` -/

/-- **`W` at no `arch_prctl`, not moved by `K`.** -/
def NoSetFsW (W : Frag isa) (K : State → State → Prop) : Frag isa :=
  fun s c => W s c ∧ NoSetFsAt s ∧ ∀ s', ¬ K s s'

/-- A code segment with no `syscall`. -/
def cNoSys (cs : List (Directive × Nat)) : Bool := cs.all fun c => dNoSys c.1

/-- **A state at a cell of a code segment with no `syscall`** is at no
`arch_prctl`. -/
theorem noSetFsAt_of_code {st s : State} {pc : Int64} {cs : List (Directive × Nat)} (h : CodeAt st pc cs)
    (hcs : cNoSys cs = true) {j : Nat} (hj : j < cs.length) (he : s.exe = st.exe)
    (hn : s.endPc = st.endPc) (hp : s.st.2 = pc + Int64.ofNat (cellOff cs j)) : NoSetFsAt s :=
  noSetFsAt_of_cell (h.cell (List.getElem?_eq_getElem hj) he hn hp)
    (List.all_eq_true.mp hcs _ (List.getElem_mem hj))

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- **A node at code with no `syscall`** is inside `NoSetFsW W K`. -/
theorem NodeW.noSetFs {n : ND} {cs : List (Directive × Nat)} (h : NodeW W K exe endPc R F n)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc cs) (hne : 0 < cs.length)
    (hcs : cNoSys cs = true) : NodeW (NoSetFsW W K) K exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, -, hpc, -⟩ := id hAt
  obtain ⟨hw, hk⟩ := h s c hAt
  refine ⟨⟨hw, noSetFsAt_of_code (hcode s he hn) hcs hne rfl rfl ?_, hk⟩, hk⟩
  rw [hpc, cellOff, List.take_zero]; simp

/-- **A block node with no `syscall`** is inside `NoSetFsW W K`. -/
theorem BlkW.noSetFs {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hcs : cNoSys blk = true) : BlkW (NoSetFsW W K) K exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  obtain ⟨hw, hK⟩ := h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  exact ⟨⟨hw, noSetFsAt_of_code (hcode s he hn) hcs hk rfl rfl rfl, hK⟩, hK⟩

/-- **A segment inside `NoSetFsW W K` keeps `fsBase`** (`SegW.keepTP`, the
outside moves vacuous). -/
theorem SegW.keepTPN {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {P Q : Frag isa} {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : SegW (NoSetFsW W K) K p lbl (tpXa ms t) P Q) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  (KeepTP.SegW.keepTP hK h (fun _ _ hw => hw.2.1) fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim).mono_W
    fun _ _ hw => hw.1

/-- **A stack-checked prologue** (at its code, as `xPrologue_segW` asks it)
is inside `NoSetFsW W K`: none of its cells is a `syscall`. -/
theorem Flow.XProW.noSetFs {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 xHead)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 1 + 3) (xLea Z zl))
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl) [(fsDir .r11 lim, zf)])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf) (xCmp L z1 z2))
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2)
        (xFr Z zs ps)) :
    XProW (NoSetFsW W K) K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨BlkW.noSetFs h.w0 hc0 (by simp [cNoSys, xHead, dNoSys]),
    BlkW.noSetFs h.w1 hc1 (by simp [cNoSys, xLea, dNoSys]),
    NodeW.noSetFs h.w2 hc2 (by simp) (by simp [cNoSys, fsDir, dNoSys]),
    BlkW.noSetFs h.w3 hc3 (by simp [cNoSys, xCmp, dNoSys]),
    BlkW.noSetFs h.w4 hc4 (by simp [cNoSys, xFr, xSt, dNoSys])⟩

end W

/-! ## `scc_rt_alloc` -/

namespace Alloc

variable {ms : MemSide isa} {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop} {q : Call}
  {cells : List (Directive × Nat)}

set_option hygiene false in
/-- A block node of `scc_rt_alloc` at `l + k`, its code from `allocIn`. -/
local macro "ablk " w:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact BlkW.noSetFs $w
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _))
    (by decide))

set_option hygiene false in
/-- A single-instruction node of `scc_rt_alloc` at `l + k`. -/
local macro "anod " w:term:max l:term:max k:term:max b:term:max : tactic =>
  `(tactic| exact NodeW.noSetFs $w
    (code_field hp hend (b := $b) (by simp only [hin', iCtr, iHeap, iRmw, iHdr, iRet]) (l := $l) (off := $k)
      (by first | rfl | exact ofNat_zero' _))
    (by decide) (by decide))

/-- **`scc_rt_alloc` at its code is inside `NoSetFsW W K`**: none of its
cells is a `syscall`, in any valid layout of cells with its code
(`allocIn`). -/
theorem AllocW.noSetFs {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : allocIn cells = true) (h : AllocW ms q W K exe endPc R F) :
    AllocW ms q (NoSetFsW W K) K exe endPc R F := by
  have hin' := hin
  simp only [allocIn, fiAt, iCtr, iHeap, iRmw, iHdr, iRet, Bool.and_eq_true] at hin'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ablk h.e fnL 0
  · ablk h.entry entryL 0
  · ablk h.j1 entryL 16
  · anod h.cnt cntL 0 [(iCtr.toDir, 7)]
  · ablk h.c1 cntL 7
  · anod h.rmw cntL 19 [(iRmw, 5)]
  · ablk h.c2 cntL 24
  · ablk h.j2 cntL 59
  · ablk h.slow slowL 0
  · ablk h.j3 slowL 16
  · ablk h.full fullL 0
  · ablk h.ok okL 0
  · anod h.f1 okL 11 [((FI.shr_cl .rax).toDir, 3)]
  · ablk h.o1 okL 14
  · anod h.f2 okL 29 [((FI.and_rr .rax .rcx).toDir, 3)]
  · ablk h.o2 okL 32
  · anod h.s2 okL 36 [(iHeap.toDir, 7)]
  · ablk h.o3 okL 43
  · anod h.f3 okL 58 [((FI.shl_cl .rax).toDir, 3)]
  · ablk h.o4 okL 61
  · anod h.f4 okL 88 [((FI.imul_rr .rax .rcx).toDir, 4)]
  · ablk h.o5 okL 92
  · anod h.f5 okL 107 [((FI.shl_cl .rax).toDir, 3)]
  · ablk h.o6 okL 110
  · anod h.f6 okL 125 [((FI.shl_cl .rax).toDir, 3)]
  · ablk h.o7 okL 128
  · anod h.f7 okL 140 [((FI.or_rr .rax .rcx).toDir, 3)]
  · ablk h.o8 okL 143
  · anod h.hdr okL 170 [(iHdr, 3)]
  · ablk h.o9 okL 173
  · anod h.ret okL 226 [(iRet.toDir, 1)]

end Alloc

end Spike.Lib.X64
