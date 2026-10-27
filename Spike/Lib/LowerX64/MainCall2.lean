/-
**The user `main` called after a setup block, at depth, from its exits by
placements** (x86-64): the interface `MainCallWS`
(`Spike/Lib/Rt/X64MainSS.lean`) at `scc_rt_main`'s post `UPostR`
(`Spike/Lib/LowerX64/MainExit2.lean`), from a segment of `main`'s body to
its exits `ExitC2SL` at the empty frames (return type `int`) whose aborts
never end.

- `mainCallWS_of_exitC2SL`: at every frame condition and ghost of the
  interface with the callee region's base the entry's `%rsp`, a segment
  inside `W` from `main`'s entry `uNM` to `ExitC2SL` at the ghost's
  `%rbp`/return address and some start, and one from its aborts to nothing,
  give `MainCallWS … (UPostR p lbl)` (`uPostR_ret`, the empty hold-back).
  Generic in `W`: the fragment the rows' facts are stated over is the
  caller's.
-/
import Spike.Lib.LowerX64.MainExit2
import Spike.Lib.Rt.X64MainSS

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **The user `main` after a setup block at depth, from its exits**
(`MainCallWS` at `UPostR`): at every frame condition and ghost `g` of the
interface with the callee region's base the entry's `%rsp`, a segment inside
`W` at the empty frames from the entry `uNM` to `main`'s exits `ExitC2SL` at
`int` with `g`'s frame pointer and return address and the thread pointer
`tp` (`hseg`), and one from its aborts `Ab` to nothing; the return past `ret`
is `uNx` at `UPostR` (`uPostR_ret`). -/
theorem mainCallWS_of_exitC2SL {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
      FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.X64.Flow.Ret0.CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
      ∀ g : Spike.Lib.X64.Flow.Ret0.WcG, g.ra = ra → g.tp = tp →
      (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp →
      ∃ (Ab : FragS isa) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
            (Spike.Lib.X64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F fn ZU Pre g)).at [])
          (ExitC2SL p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' []
            .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWS W K p lbl ms exe endPc R F fn Z D ZU Pre (UPostR p lbl) ra tp := by
  intro F' hR0 hF' hFF g hra htp
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uNM])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g hra htp hbase
  refine (SegWS.seq_left (Q := Ab) (E := (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
      (Spike.Lib.X64.Rt.uNx (UPostR p lbl) g)).at []) (h1.mono_post fun s c fs h => ?_) hAb).mono_post
      fun s c fs h => ?_
  · rcases h with ⟨rfl, c1, -, hA⟩ | h
    · exact .inr ⟨uPostR_ret hbase (.refl _) hA, rfl⟩
    · exact .inl h
  · exact h.elim False.elim id

/--
info: 'Spike.Lib.LowerX64.mainCallWS_of_exitC2SL' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainCallWS_of_exitC2SL

end Spike.Lib.LowerX64
