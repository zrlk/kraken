/-
**A call of `print` on an empty slice** (x86-64): `print_callW`
(`Spike/Lib/X64PrintCall.lean`) with count `%rsi = 0`; the twin of
`Spike/Lib/A64PrintEmpty.lean`. The loop's first test leaves at once, so
the write system call is never reached: its node's invariant asks for a
byte left (`PrintA.JIlt`, `k < 0`) and `hsys` is vacuous (`SegW.of_not`,
`Spike/Lib/SegWOfNot.lean`). The source does not move inside the call: the
predicate `Pe σC` of the call state holds at entry and return (the caller
runs the source's empty call, `printCall_empty` in
`Spike/Lib/Src/PrintCallSrc.lean`, before or after the segment), and no
abort is reachable (`Qc = False`).
-/
import Spike.Lib.X64PrintCall
import Spike.Lib.SegWOfNot

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib
open Scc.Cert.Rt.X64 (Lays endOf)
open PrintCall

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` with count 0 is one segment inside `W`**, with
`print`'s blocks asked only under frame conditions that know the call
(`pFJ`): `print_callW'` as `print_call_emptyW` is `print_callW`. -/
theorem print_call_emptyW' {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = 0)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR (nC.o.sp - 8) R) F')
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → Pe σC c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_callW' (Pc := fun σC _ => Pe σC) (Qc := fun _ _ _ => False) hp hend hprog hF hR hlo hhi hk8 hpc
    hP0 (fun σ c hJ => by rw [hz σ c hJ]; decide) hW
    (fun _ σC c hJ _ => SegW.of_not <| by
      rintro _ _ ⟨-, -, -, -, -, -, -, ⟨k, -, hk, -⟩, -⟩
      rw [hz σC c hJ] at hk; exact Nat.not_lt_zero k hk)
    hret (fun _ _ _ _ _ _ _ h => h.elim)


/-- **A call of `print` with count 0 is one segment inside `W`**:
`print_callW` with `Pc σC k := Pe σC` and `Qc := False`, its system call
unreachable. The call site gives `%rsi = 0` (`hz`) and `Pe` at the call
state (`hP0`); the return lands with `Pe σC` (`hret`). -/
theorem print_call_emptyW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = 0)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → Pe σC c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c') :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) :=
  print_call_emptyW' hp hend hprog hF hR hlo hhi hk8 hpc hP0 hz
    (fun σC c hJ _ hJF => (hW σC c hJ).mono fun m h => (hJF.2 m h).1) hret
end Fn

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.print_call_emptyW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_emptyW

/-- info: 'Spike.Lib.X64.print_call_emptyW'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_emptyW'
