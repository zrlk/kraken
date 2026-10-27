/-
**`hello1.w`'s `wc_rodata` at cells other than `syscall` on x64**: the
node obligations of `wc_rodata`'s segments and of `scc_rt_alloc` strengthened
to states at cells other than a `syscall`, none moved by `K`, so that
`SegW.keepTP` (`Spike/Lib/X64KeepTP.lean`) carries the `%fs` base across
them. The x64 twin of `Spike/Lib/A64Hello1RodataTP.lean`: no x86-64
instruction writes `fsBase`, so the cell condition is only that the state
asks for no `arch_prctl(ARCH_SET_FS)` (`NoSetFsAt`), which holds at any cell
other than a `syscall`.

- `dNoSys`, `csNoSys`: a directive other than `syscall`, a code segment of
  them;
- `NoSetFsW W K`: `W`, asking for no `arch_prctl(ARCH_SET_FS)`, not moved
  by `K`; `noSetFsAt_of_code`: a state at a cell of a code segment with no
  `syscall`;
- `NodeW.noSetFs`, `BlkW.noSetFs`, `XProW.noSetFs`: a node's, a block
  node's, a prologue's obligation at code with no `syscall` is one inside
  `NoSetFsW W K`;
- `SegW.keepTPN`: `SegW.keepTP` for a segment inside `NoSetFsW W K` (the
  outside moves vacuous), back inside `W`;
- `AllocW.noSetFs`: `scc_rt_alloc`'s obligations inside `NoSetFsW W K`, in
  any valid layout of cells with `allocIn`;
- `Hello1.RdPreW.noSetFs`, `Hello1.RdPostLW.noSetFs`: `wc_rodata`'s, in any
  valid layout of `hello1Cells`.
-/
import Spike.Lib.X64KeepTP
import Spike.Lib.X64Hello1RodataPostS

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)

set_option linter.unusedSimpArgs false

/-! ## Nodes at cells other than `syscall` -/

/-- A directive other than a `syscall`. -/
def dNoSys : Directive → Bool
  | .instr (.regular _ _ .syscall) => false
  | _ => true

/-- A code segment with no `syscall`. -/
abbrev csNoSys (cs : List (Directive × Nat)) : Bool := cs.all fun c => dNoSys c.1

/-- **`W` asking for no `arch_prctl(ARCH_SET_FS)`, not moved by `K`.** -/
def NoSetFsW (W : Frag isa) (K : State → State → Prop) : Frag isa :=
  fun s c => W s c ∧ NoSetFsAt s ∧ ∀ s', ¬ K s s'

/-- A state at a cell of a code segment with no `syscall` asks for no
`arch_prctl(ARCH_SET_FS)` (the kernel sees no system call there). -/
theorem noSetFsAt_of_code {st s : State} {pc : Int64} {cs : List (Directive × Nat)} (h : CodeAt st pc cs)
    (hds : csNoSys cs = true) {j : Nat} (hj : j < cs.length) (he : s.exe = st.exe)
    (hn : s.endPc = st.endPc) (hp : s.st.2 = pc + Int64.ofNat (cellOff cs j)) : NoSetFsAt s := by
  have hc := h.cell (List.getElem?_eq_getElem hj) he hn hp
  have hd : dNoSys (cs.get ⟨j, hj⟩).1 = true := List.all_eq_true.mp hds _ (List.getElem_mem hj)
  have hf := Scc.Sem.X64.atSyscall_false_of_cellAt hc fun w w' heq => by
    rw [heq] at hd; simp [dNoSys] at hd
  intro hat
  have hat' : Scc.Sem.X64.atSyscall s = true := hat
  rw [hf] at hat'
  cases hat'

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- **A node at code with no `syscall`** is inside `NoSetFsW W K`. -/
theorem NodeW.noSetFs {n : ND} {ds : List (Directive × Nat)} (h : NodeW W K exe endPc R F n)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc ds) (hne : 0 < ds.length)
    (hds : csNoSys ds = true) : NodeW (NoSetFsW W K) K exe endPc R F n := by
  intro s c hAt
  obtain ⟨he, hn, -, hpc, -⟩ := id hAt
  obtain ⟨hw, hk⟩ := h s c hAt
  exact ⟨⟨hw, noSetFsAt_of_code (hcode s he hn) hds hne rfl rfl (by rw [hpc]; exact (ofNat_zero' _).symm), hk⟩,
    hk⟩

/-- **A block node with no `syscall`** is inside `NoSetFsW W K`. -/
theorem BlkW.noSetFs {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hds : csNoSys blk = true) : BlkW (NoSetFsW W K) K exe endPc R F n blk := by
  intro s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  obtain ⟨hw, hK⟩ := h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD'
  exact ⟨⟨hw, noSetFsAt_of_code (hcode s he hn) hds hk rfl rfl rfl, hK⟩, hK⟩

/-- **A segment inside `NoSetFsW W K` keeps the `%fs` base** (`SegW.keepTP`,
the outside moves vacuous). -/
theorem SegW.keepTPN {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {P Q : Frag isa} {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : SegW (NoSetFsW W K) K p lbl (tpXa ms t) P Q) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  (KeepTP.SegW.keepTP hK h (fun _ _ hw => hw.2.1) fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim).mono_W
    fun _ _ hw => hw.1

/-- **A segment inside `NoSetFsW W' K` keeps the `%fs` base, `W` asked
only there** (`SegW.keepTP'`, the outside moves vacuous): the conclusion
is inside `W`, which `W'` gives at `fsBase = t` (`hW`). -/
theorem SegW.keepTPN' {W' : Frag isa} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {P Q : Frag isa} {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    (h : SegW (NoSetFsW W' K) K p lbl (tpXa ms t) P Q) (hW : ∀ s c, W' s c → TP t s → W s c) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) :=
  KeepTP.SegW.keepTP' hK h (fun _ _ hw => hw.2.1) (fun _ _ hw s' hk _ => (hw.2.2 s' hk).elim)
    fun s c hw ht => hW s c hw.1 ht

/-- **A prologue at code with no `syscall`** is inside `NoSetFsW W K`. -/
theorem XProW.noSetFs {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 xHead)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 1 + 3) (xLea Z zl))
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl) [(fsDir .r11 lim, zf)])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf) (xCmp L z1 z2))
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2) (xFr Z zs ps))
    (h0 : csNoSys xHead = true) (h1 : csNoSys (xLea Z zl) = true)
    (h2 : csNoSys [(fsDir .r11 lim, zf)] = true) (h3 : csNoSys (xCmp L z1 z2) = true)
    (h4 : csNoSys (xFr Z zs ps) = true) :
    XProW (NoSetFsW W K) K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨BlkW.noSetFs h.w0 hc0 h0, BlkW.noSetFs h.w1 hc1 h1, NodeW.noSetFs h.w2 hc2 (by simp) h2,
    BlkW.noSetFs h.w3 hc3 h3, BlkW.noSetFs h.w4 hc4 h4⟩

end W

/-! ## `scc_rt_alloc` -/

section Alloc

open Spike.Lib.X64.Alloc

variable {ms : MemSide isa} {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop} {q : Call}

set_option hygiene false in
/-- A block node's or a node's obligation at `l + k`, its code from
`allocIn`. -/
local macro "anf " f:ident w:term:max l:term:max k:term:max : tactic =>
  `(tactic| exact $f $w (code_field hp hend (by simp only [hin']) (l := $l) (off := $k)
    (by first | rfl | exact ofNat_zero' _)) (by decide))

set_option hygiene false in
local macro "ann " w:term:max l:term:max k:term:max b:term:max : tactic =>
  `(tactic| exact NodeW.noSetFs $w (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (b := $b)
    (by first | rfl | exact ofNat_zero' _)) (by simp) (by decide))

/-- **`scc_rt_alloc` is inside `NoSetFsW W K`** in any valid layout of
cells with its code (`allocIn`): none of its cells is a `syscall`. -/
theorem AllocW.noSetFs {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : allocIn cells = true) (h : AllocW ms q W K exe endPc R F) :
    AllocW ms q (NoSetFsW W K) K exe endPc R F := by
  have hin' := hin
  simp only [allocIn, fiAt, Bool.and_eq_true] at hin'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · anf BlkW.noSetFs h.e fnL 0
  · anf BlkW.noSetFs h.entry entryL 0
  · anf BlkW.noSetFs h.j1 entryL 16
  · ann h.cnt cntL 0 [(iCtr.toDir, 7)]
  · anf BlkW.noSetFs h.c1 cntL 7
  · ann h.rmw cntL 19 [(iRmw, 5)]
  · anf BlkW.noSetFs h.c2 cntL 24
  · anf BlkW.noSetFs h.j2 cntL 59
  · anf BlkW.noSetFs h.slow slowL 0
  · anf BlkW.noSetFs h.j3 slowL 16
  · anf BlkW.noSetFs h.full fullL 0
  · anf BlkW.noSetFs h.ok okL 0
  · ann h.f1 okL 11 [((FI.shr_cl .rax).toDir, 3)]
  · anf BlkW.noSetFs h.o1 okL 14
  · ann h.f2 okL 29 [((FI.and_rr .rax .rcx).toDir, 3)]
  · anf BlkW.noSetFs h.o2 okL 32
  · ann h.s2 okL 36 [(iHeap.toDir, 7)]
  · anf BlkW.noSetFs h.o3 okL 43
  · ann h.f3 okL 58 [((FI.shl_cl .rax).toDir, 3)]
  · anf BlkW.noSetFs h.o4 okL 61
  · ann h.f4 okL 88 [((FI.imul_rr .rax .rcx).toDir, 4)]
  · anf BlkW.noSetFs h.o5 okL 92
  · ann h.f5 okL 107 [((FI.shl_cl .rax).toDir, 3)]
  · anf BlkW.noSetFs h.o6 okL 110
  · ann h.f6 okL 125 [((FI.shl_cl .rax).toDir, 3)]
  · anf BlkW.noSetFs h.o7 okL 128
  · ann h.f7 okL 140 [((FI.or_rr .rax .rcx).toDir, 3)]
  · anf BlkW.noSetFs h.o8 okL 143
  · ann h.hdr okL 170 [(iHdr, 3)]
  · anf BlkW.noSetFs h.o9 okL 173
  · ann h.ret okL 226 [(iRet.toDir, 1)]

end Alloc

/-! ## `wc_rodata` -/

namespace Hello1

open Spike.Lib.X64.Alloc (Call AllocW)

variable {ms : MemSide isa} {exe : _root_.Executable} [Executable.ValidLayout exe]
  {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}

/-- **`wc_rodata` up to the allocator's return is inside `NoSetFsW W K`** in
any valid layout of `hello1Cells`. -/
theorem RdPreW.noSetFs (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    {J0 Jc : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 Jc) :
    RdPreW (NoSetFsW W K) K exe endPc R F ms J0 Jc := by
  have hin := hello1_rodataPro
  simp only [h1RodataPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label "wc_rodata" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_rodata.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have he := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at he
  refine ⟨XProW.noSetFs h.pro (code_field hp hend b0 (ofNat_zero' _)) (code_field hp hend b1 ?_)
    (code_field hp hend b2 ?_) (code_field hp hend b3 ?_) (code_field hp hend b4 ?_)
    (by decide) (by decide) (by decide) (by decide) (by decide),
    BlkW.noSetFs h.e (code_field hp hend he.1 (ofNat_zero' _)) (by decide),
    fun q hok hq => AllocW.noSetFs hp hend Alloc.hello1_allocIn (h.alloc q hok hq)⟩
  · rw [h4, ofNat_zero']
  · rw [h4]
  · rw [h4, ofNat_add']
  · rw [h4, ofNat_add', ofNat_add', ofNat_add']

/-- **`wc_rodata` from the allocator's return is inside `NoSetFsW W K`** in
any valid layout of `hello1Cells`. -/
theorem RdPostLW.noSetFs (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    {Jp Jp' J1 J2 J2' J3 J4 : AS → Ctl → Prop} (h : RdPostLW W K exe endPc R F Jp Jp' J1 J2 J2' J3 J4) :
    RdPostLW (NoSetFsW W K) K exe endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have hin := hello1_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := hin
  exact ⟨BlkW.noSetFs h.s0 (code_field hp hend c0 (ofNat_zero' _)) (by decide),
    NodeW.noSetFs h.l1 (code_field hp hend c1 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s1 (code_field hp hend c2 rfl) (by decide),
    NodeW.noSetFs h.x1 (code_field hp hend c3 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s2 (code_field hp hend c4 rfl) (by decide),
    NodeW.noSetFs h.l2 (code_field hp hend c5 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s3 (code_field hp hend c6 rfl) (by decide),
    NodeW.noSetFs h.x2 (code_field hp hend c7 rfl) (by simp) (by decide),
    BlkW.noSetFs h.s4 (code_field hp hend c8 rfl) (by decide)⟩

end Hello1

end Spike.Lib.X64.Flow

/-- info: 'Spike.Lib.X64.Flow.SegW.keepTPN'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.SegW.keepTPN'
