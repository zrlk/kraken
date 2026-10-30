/-
**`scc_rt_alloc_tcb` at any header, inside `W`** (AArch64): the second
call's callee segment (a spawn's TCB, before the `clone`), lifting
`Spike/Lib/A64Ret0AllocTcbG.lean`'s walks to the node and segment level of
`tcbN`/`TcbW`/`allocTcb_segW`/`tcbW_gen` (`Spike/Lib/A64Ret0.lean`,
`Spike/Lib/Rt/A64Segs.lean`, `Spike/Lib/Rt/A64RtTcb.lean`), unchanged but
for the header `h`.

    entry  x0 = h, x1 = 1 (`PreG`)
    exit   x0 = pinned + n0 + 8·mOf h + 8, the TCB (`PostG`, `tcbOf`)
    words  scc_rt_pinned_next: n0 → n0 + lenOf h (owned at the add);
           the header word pinned + n0 + 8·mOf h (`hdrA`) := h | 1 << 36
           (owned at no phase)

- `TcbGG`, `hdrA`, `tcbOf`: the ghosts, the header's word and the TCB.
- `tcbNG`, `tcbXG`, `TcbWG`, `TcbOkG`: `tcbN`, `tcbX`, `TcbW`, `TcbOk` at `h`.
- `allocTcbG_segW`: the callee segment inside `W` (`allocTcb_segW` at `h`).
- `TcbPhG`, `tcbW_genG`: the node obligations from the phase facts
  (`TcbPh`, `tcbW_gen` at `h`).
-/
import Spike.Lib.Rt.A64Segs
import Spike.Lib.Rt.A64RtTcb
import Spike.Lib.A64Ret0AllocTcbG

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer

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

variable (lab : Label → Int64) (q : TcbGG)

/-- **The header's word**: `scc_rt_pinned + n0 + 8·mOf h`. -/
abbrev hdrA : BitVec 64 := pinA lab + q.n0 + AllocTcb.mOf q.h <<< 3

/-- **The TCB** the call returns: one word past the header. -/
abbrev tcbOf : BitVec 64 := hdrA lab q + 8#64

/-- **The nodes** (`tcbN` at `h`). -/
def tcbNG : TN → ND
  | .e => ⟨lab AllocTcb.fnL, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.PreG q.g q.h σ⟩
  | .entry => ⟨lab AllocTcb.entryL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0G q.h q.g σ⟩
  | .j1 => ⟨lab AllocTcb.entryL + Int64.ofNat (4 * 4), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0G q.h q.g σ⟩
  | .len => ⟨lab AllocTcb.lenL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr0G q.h q.g σ⟩
  | .adrp => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 32), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr1G q.h q.g σ⟩
  | .add => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 33), AllocTcb.oI, fun σ c => c = q.c0 ∧
      ∃ σ0, AllocTcb.Fr1G q.h q.g σ0 ∧ σ = (SI.adrp .X9 "scc_rt_pinned_next").step lab σ0⟩
  | .arg => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 34), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1G q.h q.g σ ∧ σ.regs.X9.toBitVec = pnA lab⟩
  | .rmw => ⟨AllocTcb.rmwPc lab, AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1G q.h q.g σ ∧ σ.regs.X9.toBitVec = AllocTcb.lenOf q.h ∧ σ.regs.X10.toBitVec = pnA lab⟩
  | .bnd => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 38), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr1G q.h q.g σ ∧ σ.regs.X11.toBitVec = q.n0⟩
  | .j2 => ⟨lab AllocTcb.lenL + Int64.ofNat (4 * 47), AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr2G q.h q.g q.n0 σ⟩
  | .ok => ⟨lab AllocTcb.okL, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr2G q.h q.g q.n0 σ⟩
  | .ok1 => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 1), AllocTcb.oI, fun σ c => c = q.c0 ∧
      ∃ σ0, AllocTcb.Fr2G q.h q.g q.n0 σ0 ∧ σ = (SI.adrp .X9 "scc_rt_pinned").step lab σ0⟩
  | .ok2 => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 2), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr2G q.h q.g q.n0 σ ∧ σ.regs.X9.toBitVec = pinA lab⟩
  | .hdr => ⟨AllocTcb.hdrPc lab, AllocTcb.oI, fun σ c => c = q.c0 ∧ AllocTcb.Fr3G q.h q.g q.n0 (pinA lab) σ ∧
      σ.regs.X9.toBitVec = q.h ||| 1#64 <<< 36 ∧ σ.regs.X10.toBitVec = hdrA lab q⟩
  | .ret => ⟨lab AllocTcb.okL + Int64.ofNat (4 * 30), AllocTcb.oI, fun σ c => c = q.c0 ∧
      AllocTcb.Fr3G q.h q.g q.n0 (pinA lab) σ⟩

/-- **The exit**: at the return address, `PostG`. -/
def tcbXG : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, AllocTcb.oE, fun σ c => c = q.c0 ∧ AllocTcb.PostG q.g q.h q.n0 (pinA lab) σ⟩

/-- `PostG`'s `x0` is `tcbOf`. -/
theorem postG_tcbOf {g : AllocTcb.G} {σ : Flow.AS} (hP : AllocTcb.PostG g q.h q.n0 (pinA lab) σ) :
    σ.regs.X0.toBitVec = tcbOf lab q := hP.2.2.2

end Tcb

/-- **The counter's add** at `h` (`TcbOk` with `lenOf h`). -/
structure TcbOkG (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (h n0 : BitVec 64) : Prop where
  next : StOk ms F exe endPc (pnA (_root_.Executable.labels exe).label) (n0 + AllocTcb.lenOf h)
  own : OwnAt ms exe endPc (AllocTcb.rmwPc (_root_.Executable.labels exe).label)
    (pnA (_root_.Executable.labels exe).label) n0

theorem TcbOkG.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {h n0 : BitVec 64} (hT : TcbOkG ms F exe endPc h n0) (hFF : ∀ m, F' m → F m) : TcbOkG ms F' exe endPc h n0 :=
  ⟨hT.next.mono hFF, hT.own⟩

/-- **The node obligations inside `W`** (`TcbW` at `h`). -/
def TcbWG (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : TcbGG) : TN → Prop
  | .e => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e) AllocTcb.atPro
  | .entry => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .entry) AllocTcb.atChk
  | .j1 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .j1) AllocTcb.atJ1
  | .len => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .len) AllocTcb.atLen
  | .adrp => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .adrp)
  | .add => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .add)
  | .arg => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .arg) AllocTcb.atArg
  | .rmw => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .bnd) AllocTcb.atBnd
  | .j2 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .j2) AllocTcb.atJ2
  | .ok => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ok)
  | .ok1 => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ok1)
  | .ok2 => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ok2) AllocTcb.atOk
  | .hdr => NodeW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .hdr)
  | .ret => BlkW W K exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .ret) AllocTcb.atRet

/-! ## The callee segment -/

section TcbProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_alloc_tcb` inside `W`: the block, its `okBlk`, its code, its
obligation; the edge is left. -/
local macro "tnodeW " b:ident ok:ident l:term:max k:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend (by simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin; simp only [hin])
      (l := $l) (k := $k) (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_alloc_tcb` at `h` is one segment inside `W`** (`allocTcb_segW`
at `h`): room for `lenOf h` bytes below `2^17` (`hn`), the header word's
facts at `hdrA` (`hhdr`), the counter's add's (`htcb`). -/
theorem allocTcbG_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hin : AllocTcb.allocTcbIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : TcbGG) (hn : q.n0.toNat + (AllocTcb.lenOf q.h).toNat ≤ 131072)
    (hhdr : StOk ms F0 exe endPc (hdrA (_root_.Executable.labels exe).label q) (q.h ||| 1#64 <<< 36))
    (htcb : TcbOkG ms F0 exe endPc q.h q.n0) (hW : ∀ i, TcbWG W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (tcbNG (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (tcbXG (_root_.Executable.labels exe).label q x) s c) := by
  have hin' := hin
  simp only [AllocTcb.allocTcbIn, Bool.and_eq_true] at hin'
  have eEntry := label_labelGap hp hin'.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  refine fn_segW (N := tcbNG _ q) (E := tcbXG _ q) (fun i => ?_) TN.e
  cases i
  case e =>
    tnodeW AllocTcb.atPro AllocTcb.atPro_ok AllocTcb.fnL 0 (hW TN.e)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atPro_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    tnodeW AllocTcb.atChk AllocTcb.atChk_ok AllocTcb.entryL 0 (hW TN.entry)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atChk_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.j1, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j1 =>
    tnodeW AllocTcb.atJ1 AllocTcb.atJ1_ok AllocTcb.entryL 4 (hW TN.j1)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    rw [AllocTcb.atJ1_run]
    exact .inl ⟨TN.len, rfl, rfl, hJ⟩
  case len =>
    tnodeW AllocTcb.atLen AllocTcb.atLen_ok AllocTcb.lenL 0 (hW TN.len)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atLen_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨TN.adrp, by rw [h1]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case adrp =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.adrp) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    exact (ofNat4_succ' _ 32).symm
  case add =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned_next") hF
      (code_of hp hend hin'.1.1.1.1.1.1.1.1.1.2 rfl) (hW TN.add) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 33).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr1G _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    tnodeW AllocTcb.atArg AllocTcb.atArg_ok AllocTcb.lenL 34 (hW TN.arg)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atArg_walkG (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndW hF (code_of hp hend hin'.1.1.1.1.1.1.1.2 rfl) htcb.own (hW TN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [tcbNG] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨TN.bnd, (ofNat4_succ' _ 37).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact htcb.next.mono hFF
    · simpa [ldStep, AllocTcb.Fr1G, AllocTcb.Fr0G] using hJ
    · simp [ldStep]
  case bnd =>
    tnodeW AllocTcb.atBnd AllocTcb.atBnd_ok AllocTcb.lenL 38 (hW TN.bnd)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atBnd_walkG (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨TN.j2, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j2 =>
    tnodeW AllocTcb.atJ2 AllocTcb.atJ2_ok AllocTcb.lenL 47 (hW TN.j2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    rw [AllocTcb.atJ2_run]
    exact .inl ⟨TN.ok, rfl, rfl, hJ⟩
  case ok =>
    refine si_ndW (si := .adrp .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.1.2 (ofNat4_zero _)) (hW TN.ok) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok1, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case ok1 =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_pinned") hF
      (code_of hp hend hin'.1.1.1.2 rfl) (hW TN.ok1) fun σ c hJ => ⟨c, .refl c, .inl ⟨TN.ok2, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, AllocTcb.labStep_fr2G _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case ok2 =>
    tnodeW AllocTcb.atOk AllocTcb.atOk_ok AllocTcb.okL 2 (hW TN.ok2)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := AllocTcb.atOk_walkG (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨TN.hdr, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case hdr =>
    refine rtst_ndW (code_of hp hend hin'.1.2 rfl) (hW TN.hdr) fun m σ c _ hD hJ => ?_
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    have ha : rAddr σ.regs .X10 0 = hdrA (_root_.Executable.labels exe).label q := by
      rw [← h10]; simp [rAddr, Reg64s.getXReg]
    rw [ha, Spike.Lib.A64.Alloc.getRegOrZr_x]
    refine ⟨hhdr.rt, hhdr.mp, ?_, hhdr.unmapped m (hFF m hD), q.c0, .refl q.c0,
      .inl ⟨TN.ret, (ofNat4_succ' _ 29).symm, rfl, rfl, hJ⟩⟩
    have : (σ.regs.getXReg .X9).toBitVec = q.h ||| 1#64 <<< 36 := by
      rw [← h9]; simp [Reg64s.getXReg]
    rw [this]; exact hhdr.G
  case ret =>
    tnodeW AllocTcb.atRet AllocTcb.atRet_ok AllocTcb.okL 30 (hW TN.ret)
    dsimp only [tcbNG, tcbXG] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := AllocTcb.atRet_walkG (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩


end TcbProof

/-! ## The node obligations from the phase facts -/

namespace Tcb

open Spike.Lib.A64.Flow.Ret0.AllocTcb

/-- **`scc_rt_alloc_tcb`'s phase facts at `h`** (`TcbPh` with the add's
update by `lenOf h` and the header's word at `pinned + n0 + 8·mOf h`). -/
structure TcbPhG (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab ra : Label → Int64) (h n0 : BitVec 64) : Prop where
  e : blkPh okPc ph (tcbDead lab fnL 0) lab (lab fnL + Int64.ofNat (4 * 0)) (ra fnL) atPro = true
  entry : blkPh okPc ph (tcbDead lab entryL 0) lab (lab entryL + Int64.ofNat (4 * 0)) (ra entryL) atChk = true
  j1 : blkPh okPc ph (tcbDead lab entryL 4) lab (lab entryL + Int64.ofNat (4 * 4)) (ra entryL) atJ1 = true
  len : blkPh okPc ph (tcbDead lab lenL 0) lab (lab lenL + Int64.ofNat (4 * 0)) (ra lenL) atLen = true
  arg : blkPh okPc ph (tcbDead lab lenL 34) lab (lab lenL + Int64.ofNat (4 * 34)) (ra lenL) atArg = true
  bnd : blkPh okPc ph (tcbDead lab lenL 38) lab (lab lenL + Int64.ofNat (4 * 38)) (ra lenL) atBnd = true
  j2 : blkPh okPc ph (tcbDead lab lenL 47) lab (lab lenL + Int64.ofNat (4 * 47)) (ra lenL) atJ2 = true
  ok2 : blkPh okPc ph (tcbDead lab okL 2) lab (lab okL + Int64.ofNat (4 * 2)) (ra okL) atOk = true
  ret : blkPh okPc ph (tcbDead lab okL 30) lab (lab okL + Int64.ofNat (4 * 30)) (ra okL) atRet = true
  fullNe : (lab entryL + Int64.ofNat (4 * 4)).toBitVec.toNat ≠ (lab fullL).toBitVec.toNat
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  noTk : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  rmwIn : ∃ v, (⟨pnA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨pnA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) (lenOf h)).setWidth 128) = true
  hdrNo : ∀ j w, (⟨pinA lab + n0 + mOf h <<< 3, 8⟩, w) ∉ ownOf j

/-- **`scc_rt_alloc_tcb`'s states inside `W` at `h`** (`tcbW_gen` at `h`). -/
theorem tcbW_genG {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Label → Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : allocTcbIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) (q : TcbGG)
    (hq : q.c0 = c0) (hra : q.g.ra = (ra okL).toBitVec) (hph : TcbPhG okPc ph Tk ownOf lab ra q.h q.n0)
    (hmP : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨pnA lab, 8⟩ = true)
    (hmH : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨hdrA lab q, 8⟩ = true)
    (hunP : ∀ m, F m → Mem.loadInt m.dmem (pnA lab) 8 = none)
    (hunH : ∀ m, F m → Mem.loadInt m.dmem (hdrA lab q) 8 = none) :
    ∀ i, TcbWG (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F q i := by
  have h := hin
  simp only [allocTcbIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bEn⟩, bJ1⟩, bLen⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ2⟩, bO⟩, bO1⟩, bO2⟩, bH⟩,
    bRet⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ tcbPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat4_zero _) atPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr atPro_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case entry =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bEn (ofNat4_zero _) atChk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.entry
      (hnr atChk_noRet)
      (fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atChk_walkG lab _ hJ.2).1]
        simp only [tcbDead, beq_self_eq_true, Bool.true_and, beq_eq_false_iff_ne, ne_eq]
        exact hph.fullNe)
      (hT _ (by simp [tcbPcs]))
  case j1 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bJ1 rfl atJ1_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j1
      (hnr atJ1_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case len =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bLen (ofNat4_zero _) atLen_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.len
      (hnr atLen_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case adrp =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 32)) (by simp [siPcs])
    exact nodeW_si_pre hI bA rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case add =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab lenL + Int64.ofNat (4 * 33)) (by simp [siPcs])
    exact nodeW_si_pre hI bA1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case arg =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bArg rfl atArg_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr atArg_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case rmw =>
    dsimp only [TcbWG]; rw [hI.labOk]
    refine nodeW_ldop_pre hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk (hT _ (by simp [tcbPcs]))
      (hT _ (by simp [tcbPcs])) (fun σ _ hJ => hJ.2.2.2) hmP hunP hph.rmwIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.rmwUpd
  case bnd =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bBnd rfl atBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr atBnd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case j2 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bJ2 rfl atJ2_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j2
      (hnr atJ2_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case ok =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 0)) (by simp [siPcs])
    exact nodeW_si_pre hI bO rfl (ofNat4_zero _).symm (hC _ fun _ _ hJ => hJ.1) this.1
      (hT _ (by simp [tcbPcs, siPcs])) this.2
  case ok1 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 1)) (by simp [siPcs])
    exact nodeW_si_pre hI bO1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs])) this.2
  case ok2 =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bO2 rfl atOk_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok2
      (hnr atOk_noRet) (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))
  case hdr =>
    dsimp only [TcbWG]; rw [hI.labOk]
    have := hsi (lab okL + Int64.ofNat (4 * 29)) (by simp [siPcs])
    refine nodeW_st_pre hI hown bH rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [tcbPcs, siPcs]))
      this.2 (fun σ _ hJ => ?_) hmH hunH hph.hdrNo
    rw [rAddr_zero]
    exact hJ.2.2.2
  case ret =>
    dsimp only [TcbWG]; rw [hI.labOk]
    exact blkW_pre hI bRet rfl atRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ret
      (hret_of_run atRet_ok fun _ _ hJ => by
        dsimp only [tcbNG] at hJ ⊢
        rw [(atRet_walkG lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (hT _ (by simp [tcbPcs]))

end Tcb

end Spike.Lib.A64.Rt
