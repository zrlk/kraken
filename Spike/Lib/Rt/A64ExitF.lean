/-
**`main`'s exit from a pair with pending frames** (AArch64): the
`exit_group` tail of `Spike/Lib/Rt/A64SegsS.lean` (`exitTail_segWS`) at any
frames `fs`, for a source still inside a call (a callee's `ret` held back at
the caller's frames) when the runtime's exit is reached. The mirror of
`Spike/Lib/Rt/X64ExitF.lean`.

- `MainExitF`: `MainExitS` from the frames `fs`: a frame run from `(c, fs)`
  back to depth 0, then `main`'s exit (`MainExit`);
- `MainExitF.ofS`: `MainExitS` is `MainExitF` at the empty frames;
- `exitGroup_of_mainExitF`: the `exit_group` row's obligation at the pair a
  frame run reaches back at depth 0 (`SysOk`), off an abort site;
- `MainExitFA`: the frame run from `(c, fs)` back to depth 0 at every
  state, `main`'s exit after it off an abort site (`hexit`'s shape at
  pending frames: at an abort site with `fs ≠ []` the row still needs the
  run); `MainExitFA.ofS`, `MainExitFA.ofF`, `exitGroup_of_mainExitFA`;
- `exitTail_segWSF`: the tail's segment at `fs`; the row at the `svc` is
  `OutS.pre` at the empty frames, as the consumer's `exit_group` step takes
  it (a frame run to `fs₁ = []`, then `SysOk`).
-/
import Spike.Lib.Rt.A64SegsS

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0

set_option linter.unusedSimpArgs false

/-- **`main` returns with code `v` after a frame run from the frames `fs`**:
the source runs, through the pending frames' returns, to a control at depth
0 from which `main` returns with code `v` (`MainExit`). -/
def MainExitF {I : ISA} (p : Prog) (ms : MemSide I) (s : I.State) (c : Ctl) (fs : List TermRun.Frame)
    (v : Nat) : Prop :=
  ∃ c', FrameRun p (c, fs) (c', []) ∧ MainExit p ms s c' v

/-- `MainExitS` is `MainExitF` at the empty frames. -/
theorem MainExitF.ofS {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl} {v : Nat}
    (h : MainExitS p ms s c v) : MainExitF p ms s c [] v :=
  h

/-- **The `exit_group` row's obligation from `MainExitF`**: at an abort site
the row needs no run; off one, the frame run back to depth 0 and `main`'s
exit. -/
theorem exitGroup_of_mainExitF {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} {v : Nat} (hfs : fs = [] ∨ ¬ ms.abortAt s)
    (h : ¬ ms.abortAt s → MainExitF p ms s c fs v) :
    ∃ c', FrameRun p (c, fs) (c', []) ∧ SysOk p ms s c' (.exitGroup v) := by
  by_cases hab : ms.abortAt s
  · rcases hfs with rfl | hn
    · exact ⟨c, .refl _, SysOk.exitGroup_abort hab⟩
    · exact absurd hab hn
  · obtain ⟨c', hr, hx⟩ := h hab
    exact ⟨c', hr, SysOk.exitGroup_main fun _ => hx⟩

/-- **`main`'s exit after a frame run from the frames `fs`, off an abort
site**: the source runs, through the pending frames' returns, to a control
at depth 0 from which, off an abort site, `main` returns with code `v`. The
run is asked at an abort site too (where the `exit_group` row needs no
`MainExit`), so it serves the row at pending frames, unlike `MainExitF`
under `¬ abortAt`. -/
def MainExitFA {I : ISA} (p : Prog) (ms : MemSide I) (s : I.State) (c : Ctl) (fs : List TermRun.Frame)
    (v : Nat) : Prop :=
  ∃ c', FrameRun p (c, fs) (c', []) ∧ (¬ ms.abortAt s → MainExit p ms s c' v)

/-- `MainExitS` off an abort site is `MainExitFA` at the empty frames. -/
theorem MainExitFA.ofS {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl} {v : Nat}
    (h : ¬ ms.abortAt s → MainExitS p ms s c v) : MainExitFA p ms s c [] v := by
  by_cases hab : ms.abortAt s
  · exact ⟨c, .refl _, fun hn => absurd hab hn⟩
  · obtain ⟨c', hr, hx⟩ := h hab
    exact ⟨c', hr, fun _ => hx⟩

/-- `MainExitF` off an abort site, at the frames `fs`, with the run at an
abort site, is `MainExitFA`. -/
theorem MainExitFA.ofF {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} {v : Nat} (hr : ∃ c', FrameRun p (c, fs) (c', []))
    (h : ¬ ms.abortAt s → MainExitF p ms s c fs v) : MainExitFA p ms s c fs v := by
  by_cases hab : ms.abortAt s
  · obtain ⟨c', hr⟩ := hr
    exact ⟨c', hr, fun hn => absurd hab hn⟩
  · obtain ⟨c', hr, hx⟩ := h hab
    exact ⟨c', hr, fun _ => hx⟩

/-- **The `exit_group` row's obligation from `MainExitFA`**: the frame run
back to depth 0, and `main`'s exit off an abort site. -/
theorem exitGroup_of_mainExitFA {I : ISA} {p : Prog} {ms : MemSide I} {s : I.State} {c : Ctl}
    {fs : List TermRun.Frame} {v : Nat} (h : MainExitFA p ms s c fs v) :
    ∃ c', FrameRun p (c, fs) (c', []) ∧ SysOk p ms s c' (.exitGroup v) :=
  let ⟨c', hr, hx⟩ := h
  ⟨c', hr, SysOk.exitGroup_main hx⟩

section Helpers

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The `exit_group` tail at the frames `fs`, `main`'s exit after a frame
run back to depth 0** (`exitTail_segWS` at any frames): the block lifted at
`fs`; at the `svc` the row is at the pair a frame run from `(c, fs)` reaches
at depth 0 (`hok`, `OutS.pre` at `[]`; the call has no successor). -/
theorem exitTail_segWSF {W : FragS isaLSE2} {K : State → State → Prop} {n : ND} {k : Int64} {Q : FragS isaLSE2}
    {fs : List TermRun.Frame}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hW : ExitW (fun s c => W s c fs) K exe endPc R F n k)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      ∃ c', FrameRun p (c, fs) (c', []) ∧ SysOk p (ms []) s c' (.exitGroup σ0.regs.X0.toNat)) :
    SegWS W K p lbl ms ((At exe endPc R F n).at fs) Q := by
  refine (SegWS.liftS fs (W₀ := fun s c => W s c fs) (Q₀ := At exe endPc R F (exitNx n)) ?_
    fun _ _ h => h).seq ?_
  · refine (seg_ndW (W := fun s c => W s c fs) (K := K) (N := fun _ : Unit => exitNx n)
      (E := fun e : Empty => e.elim) (by simp [exitTail])
      (exitTail_ok hk h16) hF hR hal hlo hhi hc hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    rw [exitTail_run]
    refine ⟨rfl, by simp [SO.le, exitNx], rfl, σ, hJ, ?_⟩
    show (σ.regs.setXReg .X8 94#64).X0 = σ.regs.X0
    rfl
  · refine SegWS.step (fun s c fs' ⟨hA, e⟩ => by subst e; exact (hW.w1 s c hA).1)
      (fun s c fs' ⟨hA, _⟩ => (hW.w1 s c hA).2) ?_
    rintro s c fs' ⟨hAt, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h8, σ0, hJ0, hx0⟩ := id hAt
    have hcell : CellAt s svcDir 4 := (hcs s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [exitNx])
    have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ0.regs.X0.toNat) := by
      rw [← hx0, ← svcCall_exitGroup h8, svcCall, ← hA.regs]; rfl
    obtain ⟨c', hr, hok'⟩ := hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ, hA, hD, hx0⟩
    exact .pre c' [] hr (.sys _ _ hK (Scc.Sem.A64.atSvc_of_cellAt hcell) hd hok' fun s' hs' => by
      rw [certSuccs_exitGroup] at hs'; cases hs')

/-- `exitTail_segWS` is `exitTail_segWSF` at the empty frames. -/
example {W : FragS isaLSE2} {K : State → State → Prop} {n : ND} {k : Int64} {Q : FragS isaLSE2}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : Spike.Lib.offOk lo hi (n.o.sp + k.toInt) = true)
    (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hW : ExitW (nilW W) K exe endPc R F n k)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      ∃ c', FrameRun p (c, []) (c', []) ∧ SysOk p (ms []) s c' (.exitGroup σ0.regs.X0.toNat)) :
    SegWS W K p lbl ms ((At exe endPc R F n).at []) Q :=
  exitTail_segWSF hK hF hR hal hlo hhi hk h16 hc hcs hW hok

end Helpers

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.exitGroup_of_mainExitF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitGroup_of_mainExitF

/-- info: 'Spike.Lib.A64.Rt.exitTail_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitTail_segWSF

end Spike.Lib.A64.Rt
