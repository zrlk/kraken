/-
**`scc_rt_alloc_tcb` at any header, inside `W`** (x86-64): the second
call's callee segment (a spawn's TCB, before the `clone`), lifting
`Spike/Lib/X64Ret0AllocTcbG.lean`'s walks to the node and segment level of
`tcbN`/`TcbW`/`allocTcb_segW` (`Spike/Lib/X64Ret0.lean`,
`Spike/Lib/Rt/X64Segs.lean`), unchanged but for the header `h`. The first
half of the x86-64 twin of `Spike/Lib/Rt/A64RtTcbG.lean`; the phase facts
and `tcbW_genG` are in `Spike/Lib/Rt/X64RtTcbG.lean`.

    entry  %rdi = h, %rsi = 1 (`PreG`)
    exit   %rax = pinned + n0 + 8·mOf h + 8, the TCB (`PostG`, `tcbOf`)
    words  scc_rt_pinned_next: n0 → n0 + lenOf h (owned at the add);
           the header word pinned + n0 + 8·mOf h (`hdrA`) := h | 1 << 36
           (owned at no phase)

- `TcbGG`, `hdrA`, `tcbOf`: the ghosts, the header's word and the TCB.
- `tcbNG`, `tcbXG`, `TcbWG`, `TcbOkG`: `tcbN`, `tcbX`, `TcbW`, `TcbOk` at `h`.
- `allocTcbG_segW`: the callee segment inside `W` (`allocTcb_segW` at `h`).

Where x86-64 differs from AArch64: one node per block or single
instruction of x86-64's feasible path (`TN`, as `tcbN`), the values between
them those of `X64Ret0AllocTcbG.path_valsG`; the frame is `Fr g (s*G h g)`.
-/
import Spike.Lib.Rt.X64Segs
import Spike.Lib.X64Ret0AllocTcbG

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The nodes at a header `h` -/

/-- **The ghosts of a call at header `h`**: the frame's, the header, the
counter's old value `n0`, the source control. -/
structure TcbGG where
  g : AllocTcb.G
  h : BitVec 64
  n0 : BitVec 64
  c0 : Ctl

section Tcb

open AllocTcb (oI Fr lenL okL)

variable (lab : Label → Int64) (q : TcbGG)

/-- **The header's word**: `scc_rt_pinned + n0 + 8·mOf h`. -/
abbrev hdrA : BitVec 64 := pinA lab + q.n0 + AllocTcb.mOf q.h <<< 3

/-- **The TCB** the call returns: one word past the header. -/
abbrev tcbOf : BitVec 64 := hdrA lab q + 8#64

def tcbNG : TN → ND
  | .e => ⟨lab AllocTcb.fnL, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.PreG q.g q.h σ⟩
  | .entry => ⟨lab AllocTcb.entryL, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ⟩
  | .j1 => ⟨lab AllocTcb.entryL + Int64.ofNat 20, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ⟩
  | .len => ⟨lab lenL, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ⟩
  | .shr1 => ⟨lab lenL + Int64.ofNat 11, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = q.h ∧ σ.regs.rcx.toBitVec = 8#64⟩
  | .l1 => ⟨lab lenL + Int64.ofNat 14, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ ∧ σ.regs.rax.toBitVec = q.h >>> 8⟩
  | .and1 => ⟨lab lenL + Int64.ofNat 29, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = q.h >>> 8 ∧ σ.regs.rcx.toBitVec = 16383#64⟩
  | .l2 => ⟨lab lenL + Int64.ofNat 32, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s0G q.h q.g) σ ∧ σ.regs.rax.toBitVec = AllocTcb.nOf q.h⟩
  | .shr2 => ⟨lab lenL + Int64.ofNat 47, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.sAG q.h q.g) σ ∧
      σ.regs.rax.toBitVec = q.h ∧ σ.regs.rcx.toBitVec = 22#64⟩
  | .l3 => ⟨lab lenL + Int64.ofNat 50, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.sAG q.h q.g) σ ∧ σ.regs.rax.toBitVec = q.h >>> 22⟩
  | .and2 => ⟨lab lenL + Int64.ofNat 65, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.sAG q.h q.g) σ ∧
      σ.regs.rax.toBitVec = q.h >>> 22 ∧ σ.regs.rcx.toBitVec = 16383#64⟩
  | .l4 => ⟨lab lenL + Int64.ofNat 68, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.sAG q.h q.g) σ ∧ σ.regs.rax.toBitVec = AllocTcb.mOf q.h⟩
  | .imul1 => ⟨lab lenL + Int64.ofNat 95, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s1G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = AllocTcb.nOf q.h + AllocTcb.mOf q.h⟩
  | .l5 => ⟨lab lenL + Int64.ofNat 99, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s1G q.h q.g) σ ∧ σ.regs.rax.toBitVec = 1#64 * (AllocTcb.nOf q.h + AllocTcb.mOf q.h)⟩
  | .shl1 => ⟨lab lenL + Int64.ofNat 132, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s1G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = AllocTcb.nOf q.h + AllocTcb.mOf q.h + 1#64 ∧ σ.regs.rcx.toBitVec = 3#64⟩
  | .l6 => ⟨lab lenL + Int64.ofNat 135, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s1G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = AllocTcb.lenOf q.h⟩
  | .lea1 => ⟨lab lenL + Int64.ofNat 139, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s2G q.h q.g) σ⟩
  | .arg => ⟨lab lenL + Int64.ofNat 146, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s2G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = pnA lab⟩
  | .rmw => ⟨AllocTcb.rmwPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s2G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = AllocTcb.lenOf q.h ∧ σ.regs.rcx.toBitVec = pnA lab⟩
  | .bnd => ⟨lab lenL + Int64.ofNat 163, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s2G q.h q.g) σ ∧
      σ.regs.rax.toBitVec = q.n0⟩
  | .j2 => ⟨lab lenL + Int64.ofNat 198, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s3G q.h q.g q.n0) σ⟩
  | .ok => ⟨lab okL, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s3G q.h q.g q.n0) σ⟩
  | .o1 => ⟨lab okL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s3G q.h q.g q.n0) σ ∧
      σ.regs.rax.toBitVec = pinA lab⟩
  | .imul2 => ⟨lab okL + Int64.ofNat 34, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s4G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = AllocTcb.mOf q.h⟩
  | .o2 => ⟨lab okL + Int64.ofNat 38, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s4G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 * AllocTcb.mOf q.h⟩
  | .shl2 => ⟨lab okL + Int64.ofNat 53, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s4G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = AllocTcb.mOf q.h ∧ σ.regs.rcx.toBitVec = 3#64⟩
  | .o3 => ⟨lab okL + Int64.ofNat 56, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s4G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = AllocTcb.mOf q.h <<< 3⟩
  | .shl3 => ⟨lab okL + Int64.ofNat 74, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = 36#64⟩
  | .o4 => ⟨lab okL + Int64.ofNat 77, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = 1#64 <<< 36⟩
  | .or1 => ⟨lab okL + Int64.ofNat 95, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = q.h ∧ σ.regs.rcx.toBitVec = 1#64 <<< 36⟩
  | .o5 => ⟨lab okL + Int64.ofNat 98, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = q.h ||| 1#64 <<< 36⟩
  | .hdr => ⟨AllocTcb.hdrPc lab, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ ∧
      σ.regs.rax.toBitVec = q.h ||| 1#64 <<< 36 ∧ σ.regs.rcx.toBitVec = hdrA lab q⟩
  | .ret => ⟨lab okL + Int64.ofNat 143, oI, fun σ c => c = q.c0 ∧ Fr q.g (AllocTcb.s5G q.h q.g q.n0 (pinA lab)) σ⟩

/-- **The exit**: at the return address, `PostG`. -/
def tcbXG : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, AllocTcb.oR, fun σ c => c = q.c0 ∧ AllocTcb.PostG q.g q.h q.n0 (pinA lab) σ⟩

/-- `PostG`'s `%rax` is `tcbOf`. -/
theorem postG_tcbOf {g : AllocTcb.G} {σ : AS} (hP : AllocTcb.PostG g q.h q.n0 (pinA lab) σ) :
    σ.regs.rax.toBitVec = tcbOf lab q := hP.2.2

end Tcb

/-- **The counter's add** at `h` (`TcbOk` with `lenOf h`). -/
structure TcbOkG (ms : MemSide isa) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (h n0 : BitVec 64) : Prop where
  next : StOk ms F (pnA (_root_.Executable.labels exe).label) (n0 + AllocTcb.lenOf h)
  own : OwnAt ms exe endPc (AllocTcb.rmwPc (_root_.Executable.labels exe).label)
    (pnA (_root_.Executable.labels exe).label) n0

theorem TcbOkG.mono {ms : MemSide isa} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {h n0 : BitVec 64} (hT : TcbOkG ms F exe endPc h n0) (hFF : ∀ m, F' m → F m) : TcbOkG ms F' exe endPc h n0 :=
  ⟨hT.next.mono hFF, hT.own⟩

/-- **The node obligations inside `W`** (`TcbW` at `h`). -/
def TcbWG (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : TcbGG) : TN → Prop
  | .e => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e) AllocTcb.atPro
  | .entry => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .entry) AllocTcb.atChk
  | .j1 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .j1) AllocTcb.atJ1
  | .len => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .len) AllocTcb.atL0
  | .shr1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .shr1)
  | .l1 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l1) AllocTcb.atL1
  | .and1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .and1)
  | .l2 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l2) AllocTcb.atL2
  | .shr2 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .shr2)
  | .l3 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l3) AllocTcb.atL3
  | .and2 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .and2)
  | .l4 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l4) AllocTcb.atL4
  | .imul1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .imul1)
  | .l5 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l5) AllocTcb.atL5
  | .shl1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .shl1)
  | .l6 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .l6) AllocTcb.atL6
  | .lea1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .lea1)
  | .arg => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .arg) AllocTcb.atArg
  | .rmw => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .bnd) AllocTcb.atBnd
  | .j2 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .j2) AllocTcb.atJ2
  | .ok => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ok)
  | .o1 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .o1) AllocTcb.atO1
  | .imul2 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .imul2)
  | .o2 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .o2) AllocTcb.atO2
  | .shl2 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .shl2)
  | .o3 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .o3) AllocTcb.atO3
  | .shl3 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .shl3)
  | .o4 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .o4) AllocTcb.atO4
  | .or1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .or1)
  | .o5 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .o5) AllocTcb.atO5
  | .hdr => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .hdr)
  | .ret => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ret) AllocTcb.atRet

/-! ## The callee segment -/

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) (by first | rfl | exact ofNat_zero' _)) $w
      fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- `tnodeW` for a block split by its return label `r` after `n` rows
(`blockAcrossB`, `Spike.Lib.X64.code_field_blockAcrossB`). -/
local macro "tnodeWA " b:ident ok:ident l:term:max k:term:max n:term:max r:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (Spike.Lib.X64.code_field_blockAcrossB hp hend (by simp only [hin']) (l := $l) (m := $r) (off := $k)
      (List.take_append_drop $n _) (by first | rfl | exact ofNat_zero' _))
      $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

set_option hygiene false in
/-- A node at an instruction with undefined flags writing `%rax` inside `W`, at `l + k`
(`z` bytes), to node `j`, its obligation `w`; the invariant's facts are left. -/
local macro "fnodeW " fi:term:max l:term:max k:term:max z:term:max j:term:max w:term:max : tactic =>
  `(tactic| refine flag_ndW (fi := $fi) rfl hF
    (code_field hp hend (by simp only [hin']) (l := $l) (off := $k) rfl) $w
      fun σ c hJ fl => ⟨c, .refl c, .inl ⟨$j, ofNat_add' _ $k $z, rfl, ?_⟩⟩)

/-- **`scc_rt_alloc_tcb` is one segment inside `W`** (`alloc_tcb_seg`, its
states' obligations `hW`): in any valid layout of any cells with its code (`hin`), from its
entry to its return, for any region holding its frame of 176, the saved
`%rbp` and the return address, and any frame condition implying `F0`,
given: room for the TCB below `2^17` (`hn`), the header word's facts
(`hhdr`), and the counter's add's (`htcb`). -/
theorem allocTcbG_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : AllocTcb.allocTcbIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -184) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbGG) (hn : q.n0.toNat + (AllocTcb.lenOf q.h).toNat ≤ 131072)
    (hhdr : StOk ms F0 (hdrA (_root_.Executable.labels exe).label q) (q.h ||| 1#64 <<< 36))
    (htcb : TcbOkG ms F0 exe endPc q.h q.n0) (hW : ∀ i, TcbWG W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbXG (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, AllocTcb.fiAt, AllocTcb.siAt, hdrBlk_eq, rmwBlk_eq, Bool.and_eq_true] at hin'
  have eEntry := label_labelGapB (a := AllocTcb.fnL) (b := AllocTcb.entryL) (off := 19) hp (by simp only [hin'])
  have pv := AllocTcb.path_valsG q.h
  refine fn_segW (N := tcbNG _ q) (E := tcbXG _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 20 (hW TN.j1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ1_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.len, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case len =>
    tnodeW AllocTcb.atL0 AllocTcb.atL0_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL0_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.shr1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr1 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 11 3 TN.l1 (hW TN.shr1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.1⟩
  case l1 =>
    tnodeW AllocTcb.atL1 AllocTcb.atL1_ok AllocTcb.lenL 14 (hW TN.l1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL1_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and1, by rw [h1]; exact ofNat_add' _ 14 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and1 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 29 3 TN.l2 (hW TN.and1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.1⟩
  case l2 =>
    tnodeW AllocTcb.atL2 AllocTcb.atL2_ok AllocTcb.lenL 32 (hW TN.l2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL2_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shr2, by rw [h1]; exact ofNat_add' _ 32 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shr2 =>
    fnodeW (.shr_cl .rax) AllocTcb.lenL 47 3 TN.l3 (hW TN.shr2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shr_rax ha hc fl).trans pv.2.2.1⟩
  case l3 =>
    tnodeW AllocTcb.atL3 AllocTcb.atL3_ok AllocTcb.lenL 50 (hW TN.l3)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL3_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.and2, by rw [h1]; exact ofNat_add' _ 50 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case and2 =>
    fnodeW (.and_rr .rax .rcx) AllocTcb.lenL 65 3 TN.l4 (hW TN.and2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.and_rax ha hc fl).trans pv.2.2.2.1⟩
  case l4 =>
    tnodeW AllocTcb.atL4 AllocTcb.atL4_ok AllocTcb.lenL 68 (hW TN.l4)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL4_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul1, by rw [h1]; exact ofNat_add' _ 68 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul1 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.lenL 95 4 TN.l5 (hW TN.imul1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.imul_rax ha hc fl⟩
  case l5 =>
    tnodeW AllocTcb.atL5 AllocTcb.atL5_ok AllocTcb.lenL 99 (hW TN.l5)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atL5_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl1, by rw [h1]; exact ofNat_add' _ 99 33, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl1 =>
    fnodeW (.shl_cl .rax) AllocTcb.lenL 132 3 TN.l6 (hW TN.shl1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.1⟩
  case l6 =>
    tnodeW AllocTcb.atL6 AllocTcb.atL6_ok AllocTcb.lenL 135 (hW TN.l6)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atL6_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.lea1, by rw [h1]; exact ofNat_add' _ 135 4, by rw [h2]; rfl, rfl, h3⟩
  case lea1 =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned_next") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 139) rfl) (hW TN.lea1)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ofNat_add' _ 139 7, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 146 (hW TN.arg)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.rmw, by rw [h1]; exact ofNat_add' _ 146 12, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.lenL) (off := 158) rfl) htcb.own (hW TN.rmw)
      fun m σ c _ hD hJ => ?_
    dsimp only [tcbNG] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = pnA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = AllocTcb.lenOf q.h := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, htcb.next.rt, htcb.next.mp, htcb.next.G, htcb.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨TN.bnd, ofNat_add' _ 158 5, rfl, rfl, by simpa [ownStep, AllocTcb.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 163 (hW TN.bnd)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walkG (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨TN.j2, by rw [h1]; exact ofNat_add' _ 163 35, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 198 (hW TN.j2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atJ2_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    refine si_ndW (si := .leaRip .rax "scc_rt_pinned") (z := 7) rfl hF
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 0) (ofNat_zero' _)) (hW TN.ok)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.o1, ?_, rfl, ?_⟩⟩
    · show _ + Int64.ofNat 7 = _ + Int64.ofNat 7; rfl
    · obtain ⟨rfl, hJ⟩ := hJ
      exact ⟨rfl, AllocTcb.si_fr _ _ hJ, AllocTcb.si_rax _ _ σ⟩
  case o1 =>
    tnodeW AllocTcb.atO1 AllocTcb.atO1_ok AllocTcb.okL 7 (hW TN.o1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO1_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.imul2, by rw [h1]; exact ofNat_add' _ 7 27, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case imul2 =>
    fnodeW (.imul_rr .rax .rcx) AllocTcb.okL 34 4 TN.o2 (hW TN.imul2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.imul_rax ha hc fl⟩
  case o2 =>
    tnodeW AllocTcb.atO2 AllocTcb.atO2_ok AllocTcb.okL 38 (hW TN.o2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO2_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl2, by rw [h1]; exact ofNat_add' _ 38 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl2 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 53 3 TN.o3 (hW TN.shl2)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.1⟩
  case o3 =>
    tnodeW AllocTcb.atO3 AllocTcb.atO3_ok AllocTcb.okL 56 (hW TN.o3)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO3_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.shl3, by rw [h1]; exact ofNat_add' _ 56 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case shl3 =>
    fnodeW (.shl_cl .rax) AllocTcb.okL 74 3 TN.o4 (hW TN.shl3)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, (AllocTcb.shl_rax ha hc fl).trans pv.2.2.2.2.2.2⟩
  case o4 =>
    tnodeW AllocTcb.atO4 AllocTcb.atO4_ok AllocTcb.okL 77 (hW TN.o4)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO4_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.or1, by rw [h1]; exact ofNat_add' _ 77 18, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case or1 =>
    fnodeW (.or_rr .rax .rcx) AllocTcb.okL 95 3 TN.o5 (hW TN.or1)
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    exact ⟨rfl, AllocTcb.fi_fr rfl hJ fl, AllocTcb.or_rax ha hc fl⟩
  case o5 =>
    tnodeW AllocTcb.atO5 AllocTcb.atO5_ok AllocTcb.okL 98 (hW TN.o5)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atO5_walkG (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨TN.hdr, by rw [h1]; exact ofNat_add' _ 98 42, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (b := .rcx) (k := 0) (r := .rax) (z := 3)
      (code_field hp hend (by simp only [hin']) (l := AllocTcb.okL) (off := 140) rfl) (hW TN.hdr)
      fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = hdrA (_root_.Executable.labels exe).label q := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = q.h ||| 1#64 <<< 36 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨hhdr.rt, hhdr.mp, hhdr.G, hhdr.unmapped m (hFF m hD), q.c0,
      .refl q.c0, .inl ⟨TN.ret, ofNat_add' _ 140 3, rfl, rfl, hJ⟩⟩
  case ret =>
    tnodeWA AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 143 11 AllocTcb.retL (hW TN.ret)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


end TcbProof

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.postG_tcbOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.postG_tcbOf

/-- info: 'Spike.Lib.X64.Rt.TcbOkG.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkG.mono

/-- info: 'Spike.Lib.X64.Rt.allocTcbG_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.allocTcbG_segW
