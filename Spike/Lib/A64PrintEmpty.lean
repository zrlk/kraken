/-
**A call of `print` on an empty slice** (AArch64): `print_callW`
(`Spike/Lib/A64PrintCall.lean`) with count `x1 = 0`. The loop's first test
leaves at once, so the write system call is never reached: its node's
invariant asks for a byte left (`PrintA.JIlt`, `k < 0`) and `hsvc` is
vacuous (`SegW.of_not`, `Spike/Lib/SegWOfNot.lean`). The source does not
move inside the call: the predicate `Pe σC` of the call state holds at
entry and return (the caller
runs the source's empty call, `printCall_empty` in
`Spike/Lib/Src/PrintCallSrc.lean`, before or after the segment), and no
abort is reachable (`Qc = False`).
-/
import Spike.Lib.A64PrintCall
import Spike.Lib.SegWOfNot

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open PrintCall

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` with count 0 is one segment inside `W`**, with
`print`'s blocks asked only under frame conditions that know the call
(`pFJ`): `print_callW'` as `print_call_emptyW` is `print_callW`. -/
theorem print_call_emptyW' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = 0)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR nC.o.sp R) F')
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pe σC c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_callW' (Pc := fun σC _ => Pe σC) (Qc := fun _ _ _ => False) hp hend hprog hF hR hal hlo hhi hk16 hpc
    hP0 (fun σ c hJ => by rw [hz σ c hJ]; decide) hW
    (fun _ σC c hJ _ => SegW.of_not <| by
      rintro _ _ ⟨-, -, -, -, -, -, -, ⟨⟨k, -, hk, -⟩, -⟩⟩
      rw [hz σC c hJ] at hk; exact Nat.not_lt_zero k hk)
    hret (fun _ _ _ _ _ _ _ h => h.elim)

/-- **A call of `print` with count 0 is one segment inside `W`**:
`print_callW` with `Pc σC k := Pe σC` and `Qc := False`, its system call
unreachable. The call site gives `x1 = 0` (`hz`) and `Pe` at the call
state (`hP0`); the return lands with `Pe σC` (`hret`). -/
theorem print_call_emptyW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = 0)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pe σC c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_call_emptyW' hp hend hprog hF hR hal hlo hhi hk16 hpc hP0 hz
    (fun σC c hJ _ hJF => (hW σC c hJ).mono fun m h => (hJF.2 m h).1) hret

end Fn

end Spike.Lib.A64.Flow
