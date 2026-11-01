/-
**The worker's abort facts at the child's entry** (row 5i-hab1, P5's example, AArch64): the
segment `hsegIP_abX` puts `AbX μ lab` at every entry of `PI` (`abX_of_PI`); the child after main's real `clone`
is such an entry once `ChildPrem` holds there (`SegR.childP_of_cloneX`), so `AbFacts` holds of that state
(`abX_child`). The fragment is not vacuous: it is a fact of the spawned child's first state.

- `abX_of_PI`: `PI hp i G0 w` states have `AbX μ (LH hp i).lab`.
- `abX_child`: at `ClonePreH`, the child's state after the clone has `AbFacts μ (WriteAb.Ab (LH hp i).lab)`,
  given `ChildPrem` at the clone's data.
-/
import Spike.Lib.HelloSegIPAb
import Spike.Lib.A64HelloChildX

namespace Spike.Lib.HelloAssemblyI

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Handover
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem childP_of_cloneX wordsX kidH)
open Spike.Lib.A64.Flow.Worker.Hello.AbObl (AbX MarksL)
open Spike.Lib.HelloPostAb (AbFacts)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open SccCode (helloProg)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (G0 : ιH hp i → Loc → Val → Prop)

/-- **`AbX` at `PI`'s entries** (`hsegIP_abX`'s entry and invariant). -/
theorem abX_of_PI {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) {μ : Marks} (hμ : MarksL μ (LH hp i).lab) :
    ∀ w s c fs, PI hp i G0 w s c fs → AbX μ (LH hp i).lab s c fs := by
  intro w s c fs hP
  obtain ⟨_, hin, hS, -⟩ := hsegIP_abX hp i G0 hpa hhp hlo hμ w
  exact (hS s c fs (hin s c fs hP)).2.2

/-- **`AbFacts` at the child's first state** (module doc). -/
theorem abX_child {asm : String} (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) {μ : Marks} (hμ : MarksL μ (LH hp i).lab) (w : ιH hp i)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = (LH hp i).exe ∧ st.endPc = endH hp i ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) (hal : (r1.lo + r1.size) % 16 = 0) (hsz : 272 ≤ r1.size)
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) :
    ∃ (th : Thread isaLSE2) (tls : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
      (ChildPrem (LH hp i).exe (endH hp i) (LH hp i).pfx (SRH hp i w).lbl
          (fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w)
          (Spike.Lib.A64.Flow.DFrame (Spike.Lib.A64.Flow.Worker.Wake.Child.childR (r1.lo + r1.size) (-272))
            (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
          (wordsX th) (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)) w0 w1 w2 w3 w4 n m →
        AbFacts μ (Spike.Lib.A64.WriteAb.Ab (LH hp i).lab) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st) := by
  haveI := (LH hp i).valid
  have ho : o.prog = helloProg := Except.ok.inj (hpa.symm.trans hhp)
  have hl : Scc.Cert.Rt.A64.Lays (LH hp i).exe helloProg (LH hp i).pfx := by rw [← ho]; exact (LH hp i).lays
  obtain ⟨th, tls, hth, hcall, -, hP⟩ :=
    childP_of_cloneX (lbl' := (SRH hp i w).lbl)
      (ms := fun _ => Spike.Lib.HelloMsW.msWH (LH hp i) (GH hp i G0) (SRH hp i) w) hl rfl h hX htop hal hsz
      T w0 w1 w2 w3 w4 n m
  exact ⟨th, tls, hth, hcall, fun hpr => abX_of_PI hp i G0 hpa hhp hlo hμ w _ _ _ (hP hpr)⟩

end Inst

end Spike.Lib.HelloAssemblyI

/-- info: 'Spike.Lib.HelloAssemblyI.abX_of_PI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.abX_of_PI

/-- info: 'Spike.Lib.HelloAssemblyI.abX_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAssemblyI.abX_child
