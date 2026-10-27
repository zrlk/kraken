/-
**The user `main` called after a setup block, at depth, from its exits by
placements** (AArch64): the interface `MainCallWS`
(`Spike/Lib/Rt/A64MainSS.lean`) at `scc_rt_main`'s post `MainPost2`
(`Spike/Lib/LowerA64/MainExit2.lean`), from a segment of `main`'s body to
its exits `ExitC2SL` at the empty frames (return type `int`) whose aborts
never end.

- `mainCallWS_of_exitC2SL`: at every frame condition and ghost of the
  interface, a segment inside `W` from `main`'s entry `uNM` to `ExitC2SL`
  at the ghost's `x29`/`x30` and a start `c0`, and one from its aborts to
  nothing, give `MainCallWS … (MainPost2 p lbl c0)` (`mainPost2_of_exit`).
  Generic in `W`: the fragment the rows' facts are stated over is the
  caller's.
-/
import Spike.Lib.LowerA64.MainExit2
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.Rt.A64MainSS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The user `main` after a setup block at depth, from its exits**
(`MainCallWS` at `MainPost2 p lbl c0`): at every frame condition and ghost
`g` of the interface, a segment inside `W` from the entry `uNM` to `main`'s
exits `ExitC2SL` at `g`'s `x29`/`x30`, the thread pointer `tp`, the start
`c0`, the empty frames and return type `int` (`hseg`), and one from its
aborts `Ab` to nothing (the abort's own segment, e.g. the `exit_group` at an
abort site). -/
theorem mainCallWS_of_exitC2SL {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.WcG, g.ra = ra → g.tp = tp →
      ∃ Ab : FragS isaLSE2,
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
            (Spike.Lib.A64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU Pre g)).at [])
          (ExitC2SL p lbl exe endPc (R.callee (-Z.toInt) (-D) 0) F' g.fp g.ra tp c0 [] .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.MainCallWS W K p lbl ms exe endPc R F fn Z D ZU Pre (MainPost2 p lbl c0) ra tp := by
  intro F' hR0 hal hF' hFF g hra htp
  obtain ⟨Ab, h1, hAb⟩ := hseg F' hR0 hal hF' hFF g hra htp
  refine (SegWS.seq_left (Q := Ab)
    (E := (At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (Spike.Lib.A64.Rt.uNx (MainPost2 p lbl c0) g)).at [])
    (h1.mono_post ?_) hAb).mono_post fun _ _ _ h => h.elim False.elim id
  rintro s c fs (⟨rfl, hx⟩ | h)
  · exact .inr ⟨mainPost2_of_exit hx, rfl⟩
  · exact .inl h

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainCallWS_of_exitC2SL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainCallWS_of_exitC2SL

end Spike.Lib.LowerA64
