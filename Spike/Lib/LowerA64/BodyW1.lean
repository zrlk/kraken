/-
**A call-free `Accepted1` body's blocks inside the consumer's facts**
(AArch64): `body1_seg`'s `hW`/`hWp` obligations at the code predicate
`Cd1` (`Spike/Lib/LowerA64/Blocks1.lean`), next to `BodyW.lean`'s
`Accepted0` ones.

- `blkW_body1`: a construct's block at `Cd1` at any node with the frame's
  offsets whose controls a local run from `c0` reaches, the saved pair
  `fp`/`ra` in their cells, is inside `BodyW0` (`blkW_postO` at `c0`; the
  return block's `ret` to `ra` by `FrJ`, the others without `ret`).
- `hWb1_of`, `hWs1_of`: `body1_seg`'s `hW`, `hWp` from it.
- `quiet_c1`: their `hQ` for a main-only `Accepted1` program from the
  consumer's start (`quiet_of_accepted1main`, `Spike/Lib/Quiet1.lean`).
-/
import Spike.Lib.LowerA64.BodyW
import Spike.Lib.LowerA64.Blocks1
import Spike.Lib.Quiet1

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

section W

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {p : Prog} {c0 : Ctl} {cx : FnCtx} {fp ra : BitVec 64}

/-- **A construct's block of a call-free `Accepted1` body is inside
`BodyW0`** at any node with the frame's offsets (`hno`) whose controls a
local run from `c0` reaches, the saved pair in its cells (`hJ`): the block
at `Cd1` (placed, its phase check passed, its kind). -/
theorem blkW_body1 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {n : ND} (hno : n.o = oF cx) (hJ : ∀ σ c, n.J σ c → LocalRun p c0 c ∧ FrJ fp ra σ.slot)
    {blk : List Directive} (hcd : Cd1 prog okPc ph lab cx (Int64.ofBitVec ra) n.pc blk) :
    BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F n blk := by
  obtain ⟨hk, l, j, hpc, hb, hphb⟩ := hcd
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ kind1_ok hf h1 h16 hk
  let n' : ND := ⟨n.pc, n.o, fun σ c => c = c0 ∧ ∃ c1, n.J σ c1⟩
  have hret : ∀ σ c, n'.J σ c → ∀ k (hk : k < blk.length) r, A64.Flow.classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n'.pc, n'.o, σ⟩).σ.regs.getRegOrZr r).signed = Int64.ofBitVec ra := by
    rcases hk with ⟨a, b, la, lb, ha, hb', h | h | ⟨T, h⟩⟩ | ⟨d, off, hd, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
    · subst h
      intro σ _ _ k hk r hr
      refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
      rw [addDirs, directives_append, directives_addChecked, List.getLast?_append] at hd
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
      subst hd
      simp [A64.Flow.classify]
    · subst h
      intro σ _ _ k hk r hr
      refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
      rw [subDirs, directives_append, directives_subSat, List.getLast?_append] at hd
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
      subst hd
      simp [A64.Flow.classify]
    · subst h
      intro σ _ _ k hk r hr
      refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
      rw [brDirs, directives_append, directives_cmpJcc, List.getLast?_append] at hd
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
      subst hd
      simp [A64.Flow.classify]
    · have hn : noRetBlk (strDirs off) = true := by
        simp [noRetBlk, strDirs, directives, ins, A64.Flow.classify, RegOnly, spW64, i64]
      exact fun _ _ _ k hk r hr => (noRet_false hn k hk r hr).elim
    · have hn : noRetBlk (jmpDirs F) = true := by
        simp [noRetBlk, jmpDirs, directives, jmp, ins, A64.Flow.classify]
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
    hb hpc hok hR hal hlo hhi (fun _ _ h => h.1 ▸ hC0) (hpc ▸ hphb)
    hret (fun _ _ _ => rfl) hl hh hsub hfit hFO
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨hW, hK⟩ := H s σ c0 he hn hd hp hA hF ⟨rfl, c, hJn⟩ k hk m hA' hD
  exact ⟨⟨hQ c (hJ σ c hJn).1, hW⟩, hK⟩

/-- **`body1_seg`'s `hW`**: the body's blocks at its nodes inside
`BodyW0`. -/
theorem hWb1_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s blk, Cd1 prog okPc ph lab cx (Int64.ofBitVec ra) pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (bodyN p al cx fp ra c0 pc t s) blk :=
  fun _ _ _ _ hcd => blkW_body1 hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) hcd

/-- **`body1_seg`'s `hWp`**: the body's blocks at its pending stores
inside `BodyW0`. -/
theorem hWs1_of {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hf : FrameOk cx)
    (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hC0 : CFacts Λ lbl c0) (hQ : ∀ c, LocalRun p c0 c → Quiet c)
    {al : WeakMem.AllocLabel → Option Nat} :
    ∀ pc t s k blk, Cd1 prog okPc ph lab cx (Int64.ofBitVec ra) pc blk →
      BlkW (BodyW0 Λ μ own rS Tk lbl c0) K exe endPc R F (pendN p al cx fp ra c0 pc t s k) blk :=
  fun _ _ _ _ _ hcd => blkW_body1 hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hC0 hQ rfl
    (fun _ _ (h : _ ∧ _ ∧ _) => ⟨h.2.2, h.2.1⟩) hcd

/-- **`body1_seg`'s `hCd`**: a block at `Cd1` is in the code. -/
theorem cdOf_cd1 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {ra' : Int64} :
    ∀ pc blk, Cd1 prog okPc ph lab cx ra' pc blk → CdOf exe endPc pc blk :=
  fun _ _ ⟨_, _, _, hpc, hb, _⟩ => code_of hI.lays hI.endOk hb (by rw [hI.labOk]; exact hpc)

end W

/-- **`hWb1_of`'s and `hWs1_of`'s `hQ`** for a main-only `Accepted1`
program from the consumer's start: every control a local run reaches is
`Quiet`. -/
theorem quiet_c1 {d : Decl} (hp : Scc.Lower.Accepted1 [d] = true) :
    ∀ c, LocalRun [d] Spike.Lib.A64Consumer.c0 c → Quiet c :=
  quiet_of_accepted1main hp rfl rfl

end Spike.Lib.LowerA64
