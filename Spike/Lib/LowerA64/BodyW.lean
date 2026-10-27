/-
**A lowered body's blocks inside the consumer's facts** (AArch64): the
`hWb`/`hWs` obligations of `fn0_seg` (`Spike/Lib/LowerA64/Fn.lean`) and
`MainSeg` (`Spike/Lib/LowerA64/Main.lean`), discharged for any program
with an instance's facts (`InstOk`, `Spike/Lib/Rt/A64RtW.lean`).

The segment's controls move with the source (each node's control a local
run from the function's entry `c0` reaches), so the fragment here is the
one before `SegW.lag` (`Spike/Lib/SegLag.lean`) holds the control back at
`c0`: `BodyW0` pairs a `Quiet` control with `SFacts` at `c0`. Under
`SegW.lag` with `C := (· = c0)` it gives `SFacts` at the held-back control
(`bodyW0_lag`).

- `bodyPhOk`, `blkPh_of_inBody`: the phase check of every block of the
  body (`bodyBlks`, `blkPh` at its offset after the body's label, a `ret`'s
  target the return address `ra`), and a block of the body (`InBody`)
  passes it.
- `mem_bodyBlks`, `blockAt_of_bodyBlks`, `okBlk_bodyBlks`: a block of the
  body is the checked `+`'s, its store or the return's; `bodyIn` places it;
  its cover at the frame's offsets.
- `blkW_body0`: a block of the body at any node with the frame's offsets
  whose controls a local run from `c0` reaches, the saved pair `fp`/`ra`
  in their cells, is inside `BodyW0` (`blkW_postO` at `c0`; the return
  block's `ret` to `ra` by `FrJ`, the others without `ret`).
- `hWb_of`, `hWs_of`: `fn0_seg`'s `hWb`, `hWs` from it.
- `quiet_c0`: their `hQ` for an `Accepted0` program from the consumer's
  start `A64Consumer.c0` (`quiet_of_accepted0`, `Spike/Lib/Quiet0.lean`).
-/
import Spike.Lib.LowerA64.BodyIn
import Spike.Lib.Rt.A64RtW
import Spike.Lib.SegLag
import Spike.Lib.Quiet0

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Scc.Sem (Marks Range)
open Spike.Lib.A64Consumer (CFacts SFacts blkPh hret_of_run noRetBlk noRet_false Own Lbl)
open Spike.Lib.A64.Rt (InstOk blkW_postO)
open Spike.Lib.A64.Flow.Ret0 (StackOff)

/-! ## The phase check -/

/-- **The phase check of a lowered body**: every block of `bodyBlks` passes
`blkPh` at its offset after the body's label `l`, a `ret`'s target `ra`. -/
def bodyPhOk (okPc : Nat → Bool) (ph : Nat → Nat) (dead : Nat → Bool) (lab : Label → Int64) (cx : FnCtx)
    (l : Label) (is : List Scc.IR.Inst) (ws : List Scc.IR.Operand) (ra : Int64) : Bool :=
  (bodyBlks cx 0 is ws).all fun x => blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * x.1)) ra x.2

/-- **A block of the body passes the phase check.** -/
theorem blkPh_of_inBody {okPc : Nat → Bool} {ph : Nat → Nat} {dead : Nat → Bool} {lab : Label → Int64}
    {cx : FnCtx} {l : Label} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} {ra pc : Int64}
    {blk : List Directive} (hb : InBody lab cx l is ws pc blk) (h : bodyPhOk okPc ph dead lab cx l is ws ra = true) :
    blkPh okPc ph dead lab pc ra blk = true := by
  obtain ⟨j, rfl, hj⟩ := hb
  exact List.all_eq_true.mp h _ hj

/-! ## The body's blocks -/

section Blocks

variable {cx : FnCtx}

/-- **A block of the body** is the checked `+`'s, its store or the
return's. -/
theorem mem_bodyBlks : ∀ {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat}
    {blk : List Directive}, (j, blk) ∈ bodyBlks cx k is ws →
    (∃ a b la lb, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ blk = addDirs cx la lb) ∨
    (∃ d off, cx.slotOff d = .ok off ∧ blk = strDirs off) ∨
    (∃ w lw, cx.getOp .X0 w = .ok lw ∧ blk = directives (lw ++ cx.leave ++ [ret]))
  | [], k, ws, j, blk, h => by
    match ws, h with
    | [w], h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyBlks, hg] at h
      | ok lw =>
        simp only [bodyBlks, hg, List.mem_singleton, Prod.mk.injEq] at h
        exact .inr (.inr ⟨w, lw, hg, h.2⟩)
    | [], h => simp [bodyBlks] at h
    | _ :: _ :: _, h => simp [bodyBlks] at h
  | i :: is, k, ws, j, blk, h => by
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyBlks, ha, hb, hd, List.not_mem_nil] at h
      case ok.ok.ok la lb off =>
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with h | h | h
        · exact .inl ⟨a, b, la, lb, ha, hb, h.2⟩
        · exact .inr (.inl ⟨d, off, hd, h.2⟩)
        · exact mem_bodyBlks h
    all_goals simp [bodyBlks] at h

/-- **`bodyIn` places every block of the body** at its offset. -/
theorem blockAt_of_bodyBlks {prog : List Directive} {l : Label} :
    ∀ {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat} {blk : List Directive},
    bodyIn prog cx l k is ws = true → (j, blk) ∈ bodyBlks cx k is ws → blockAt prog l j blk = true
  | [], k, ws, j, blk, hi, h => by
    match ws, hi, h with
    | [w], hi, h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyBlks, hg] at h
      | ok lw =>
        simp only [bodyBlks, hg, List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa only [bodyIn, hg] using hi
    | [], _, h => simp [bodyBlks] at h
    | _ :: _ :: _, _, h => simp [bodyBlks] at h
  | i :: is, k, ws, j, blk, hi, h => by
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyBlks, ha, hb, hd, List.not_mem_nil] at h
      case ok.ok.ok la lb off =>
        simp only [bodyIn, ha, hb, hd, Bool.and_eq_true] at hi
        obtain ⟨⟨h1, h2⟩, h3⟩ := hi
        simp only [List.mem_cons, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | h
        · exact h1
        · exact h2
        · exact blockAt_of_bodyBlks h3 h
    all_goals simp [bodyBlks] at h

variable (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
include hf h1 h16

/-- **A block of the body is covered** at the frame's offsets. -/
theorem okBlk_bodyBlks {is : List Scc.IR.Inst} {k : Nat} {ws : List Scc.IR.Operand} {j : Nat}
    {blk : List Directive} (h : (j, blk) ∈ bodyBlks cx k is ws) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) blk = true := by
  rcases mem_bodyBlks h with ⟨a, b, la, lb, ha, hb, rfl⟩ | ⟨d, off, hd, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [addDirs, directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_addChecked _
  · obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
    have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
    have hds : strDirs off = [(.X9, Int64.ofInt off)].map fun q => spStr q.1 q.2 := rfl
    rw [hds]
    refine okBlk_spStrs (by simp [oF]; omega) fun q hq => ?_
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [oF, ho, offOk, decide_eq_true_eq]
    omega
  · have hge := frame_ge16 hf
    have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_leave hf h1, okBlk_getOp hf h1 h16 hg]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this

end Blocks

/-- **No `ret` but at the end**: in a covered block a `ret` is the last
instruction, so a block whose last instruction is not one has none. -/
theorem noRet_of_last (lab : Label → Int64) {lo hi : Int} {blk : List Directive} {am : AM}
    (h : okBlk lo hi am.so blk = true) (hl : ∀ d, blk.getLast? = some d → ∀ r, classify d ≠ some (.ret r)) :
    ∀ k (hk : k < blk.length) r, A64.Flow.classify blk[k] = some (.ret r) → False := by
  intro k hk r hr
  obtain ⟨a, ha, -, hterm⟩ := okBlk_get lab (am := am) h hk
  rw [hr] at ha
  cases ha
  by_cases hk1 : k + 1 < blk.length
  · exact absurd (hterm hk1) (by simp [AI.isTerm])
  · have he : blk.getLast? = some blk[k] := by
      rw [List.getLast?_eq_getElem?]
      simp only [show blk.length - 1 = k by omega, List.getElem?_eq_getElem hk]
    exact hl _ he r hr

/-! ## The blocks inside `SFacts` at the entry -/

/-- **The body's fragment before the lag**: a `Quiet` control, the state
in `SFacts` at the function's entry control `c0`. -/
def BodyW0 (Λ : Scc.Sem.Layout) (μ : Marks) (own : Own) (rS : Range) (Tk : State → Prop) (lbl : Lbl)
    (c0 : Ctl) : Frag isaLSE2 :=
  fun s c => Quiet c ∧ SFacts Λ μ own rS Tk lbl s c0

/-- **The lag of a segment inside `BodyW0`**: with the control held back at
`c0`, the segment is inside `SFacts` (`SegW.lag`, `C := (· = c0)`), under a
memory side with the kernel model `Scc.Sem.A64.abi` (`hK`: `SFacts`' default write
tail, no `write`, rules out a `write` to the output). -/
theorem bodyW0_lag {Λ : Scc.Sem.Layout} {μ : Marks} {own : Own} {rS : Range} {Tk : State → Prop} {lbl : Lbl}
    {c0 : Ctl} {K : State → State → Prop} {p : Prog} {al : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (h : SegW (BodyW0 Λ μ own rS Tk lbl c0) K p al ms P Q) :
    SegW (fun s c => SFacts Λ μ own rS Tk lbl s c) K p al ms (Lag p (· = c0) P) (Lag p (· = c0) Q) :=
  h.lag (fun _ _ h => h.1)
    (fun _ _ h K' hK' ha buf n hd => by
      rw [hK] at hK'; cases hK'
      exact h.2.wrTail ha 1 buf n hd)
    fun _ _ _ h _ hc => hc ▸ h.2

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl} {cx : FnCtx} {l : Label}
  {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} {fp ra : BitVec 64}

/-- **A block of the body is inside `BodyW0`** at any node with the frame's
offsets (`hno`) whose controls a local run from `c0` reaches, the saved
pair in its cells (`hJ`): `blkW_postO` at `c0` (its facts `hC0`), the
block placed by `bodyIn` (`hbody`), its phase check `bodyPhOk` with no dead
target and the return address `ra` (`hph`), the controls a local run from
`c0` reaches `Quiet` (`hQ`). -/
theorem blkW_body0 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) (hbody : bodyIn prog cx l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cx l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {n : ND} (hno : n.o = oF cx) (hJ : ∀ σ c, n.J σ c → LocalRun p c0 c ∧ FrJ fp ra σ.slot)
    {blk : List Directive} (hin : InBody lab cx l is ws n.pc blk) :
    BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F n blk := by
  have hphb := blkPh_of_inBody hin hph
  obtain ⟨j, hpc, hj⟩ := hin
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ okBlk_bodyBlks hf h1 h16 hj
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
  have hret : ∀ σ c, n'.J σ c → ∀ k (hk : k < blk.length) r, A64.Flow.classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n'.pc, n'.o, σ⟩).σ.regs.getRegOrZr r).signed = Int64.ofBitVec ra := by
    rcases mem_bodyBlks hj with ⟨a, b, la, lb, ha, hb, rfl⟩ | ⟨d, off, hd, rfl⟩ | ⟨w, lw, hg, rfl⟩
    · intro σ _ _ k hk r hr
      refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
      rw [addDirs, directives_append, directives_addChecked, List.getLast?_append] at hd
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
      subst hd
      simp [A64.Flow.classify]
    · have hn : noRetBlk (strDirs off) = true := by
        simp [noRetBlk, strDirs, directives, ins, A64.Flow.classify, RegOnly, spW64, i64]
      exact fun _ _ _ k hk r hr => (noRet_false hn k hk r hr).elim
    · refine hret_of_run hok fun σ c ⟨_, c1, hJ1⟩ => ?_
      have hfj := (hJ σ c1 hJ1).2
      have hge := frame_ge16 hf
      have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
      show (arun lab (directives (lw ++ cx.leave ++ [ret])) ⟨n.pc, n.o, σ⟩).pc = _
      rw [hno, directives_leave hf h1, arun_append]
      obtain ⟨v, -, hrun⟩ := arun_getOp hf h1 hg lab n.pc σ
      rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, hrun]
      obtain ⟨hpc', -⟩ := arun_epi lab (n.pc + Int64.ofNat (4 * (directives lw).length)) (-(cx.frame : Int))
        { σ with regs := σ.regs.setXReg .X0 v } (Int64.ofInt cx.frame)
      have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
        rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
      rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc'
      rw [hpc']
      exact congrArg Int64.ofBitVec hfj.2
  have H := blkW_postO (n := n') (dead := fun _ => false) (ra := Int64.ofBitVec ra) (l := l) (k := j) hI
    (blockAt_of_bodyBlks hbody hj) hpc.symm hok hR hal hlo hhi (fun _ _ h => h.1 ▸ hC0) (hpc ▸ hphb)
    hret (fun _ _ _ => rfl) hl hh hsub hfit hFO
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hp hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨hQ c (hJ σ c hJn).1, hW⟩, hK⟩

/-- **`fn0_seg`'s `hWb`**: the body's blocks at its nodes inside `BodyW0`. -/
theorem hWb_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) (hbody : bodyIn prog cx l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cx l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s blk, CdOf exe endPc pc blk → InBody (_root_.Executable.labels exe).label cx l is ws pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (bodyN p al cx fp ra c0 pc t s) blk :=
  fun _ _ _ _ _ hin => blkW_body0 hI hf h1 h16 hbody hph hR hal hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) (hI.labOk ▸ hin)

/-- **`fn0_seg`'s `hWs`**: the body's blocks at its pending stores inside
`BodyW0`. -/
theorem hWs_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (h16 : cx.frame % 16 = 0) (hbody : bodyIn prog cx l 0 is ws = true)
    (hph : bodyPhOk okPc ph (fun _ => false) lab cx l is ws (Int64.ofBitVec ra) = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s k blk, CdOf exe endPc pc blk → InBody (_root_.Executable.labels exe).label cx l is ws pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (pendN p al cx fp ra c0 pc t s k) blk :=
  fun _ _ _ _ _ _ hin => blkW_body0 hI hf h1 h16 hbody hph hR hal hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) (hI.labOk ▸ hin)

end W

/-- **`hWb_of`'s and `hWs_of`'s `hQ`** for an `Accepted0` program from the
consumer's start: every control a local run reaches is `Quiet`. -/
theorem quiet_c0 {p : Prog} (hp : Scc.Lower.Accepted0 p = true) :
    ∀ c, LocalRun p Spike.Lib.A64Consumer.c0 c → Quiet c :=
  quiet_of_accepted0 hp rfl rfl

end Spike.Lib.LowerA64
