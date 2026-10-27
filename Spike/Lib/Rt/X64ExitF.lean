/-
**`main`'s exit from a pair with pending frames** (x86-64): the `exit_group`
tail of `Spike/Lib/Rt/X64SegsS.lean` (`xExitTail_segWS`) at any frames `fs`,
for a source still inside a call (a callee's `ret` held back at the
caller's frames) when the runtime's exit is reached.

- `MainExitF`: `MainExitS` from the frames `fs`: a frame run from `(c, fs)`
  back to depth 0, then `main`'s exit (`MainExit`);
- `MainExitF.ofS`: `MainExitS` is `MainExitF` at the empty frames;
- `exitGroup_of_mainExitF`: the `exit_group` row's obligation at the pair a
  frame run reaches back at depth 0 (`SysOk`), off an abort site;
- `MainExitFA`: the frame run from `(c, fs)` back to depth 0 at every
  state, `main`'s exit after it off an abort site (`hexit`'s shape at
  pending frames: at an abort site with `fs ≠ []` the row still needs the
  run); `MainExitFA.ofS`, `MainExitFA.ofF`, `exitGroup_of_mainExitFA`;
- `xExitTail_segWSF`: the tail's segment at `fs`; the row at the `syscall`
  is `OutS.pre` at the empty frames, as the consumer's `exit_group` step
  takes it (`NodesA.sysRowX`: a frame run to `fs₁ = []`, then `SysOk`).
-/
import Spike.Lib.Rt.X64SegsS

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0

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

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The `exit_group` tail at the frames `fs`, `main`'s exit after a frame
run back to depth 0** (`xExitTail_segWS` at any frames): the block lifted at
`fs`; at the `syscall` the row is at the pair a frame run from `(c, fs)`
reaches at depth 0 (`hok`, `OutS.pre` at `[]`; the call has no
successor). -/
theorem xExitTail_segWSF {W : FragS isa} {K : State → State → Prop} {n : ND} {Q : FragS isa} {sp b : Int}
    {k : Int64} {z0 z1 z2 z3 : Nat} {fs : List TermRun.Frame}
    (hno : n.o = ⟨sp, [(.rbp, b)]⟩) (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)])
    (hW0 : BlkW (fun s c => W s c fs) K exe endPc R F n (xExit k z0 z1 z2))
    (hW1 : NodeW (fun s c => W s c fs) K exe endPc R F (xExitNx n sp b z0 z1 z2))
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      ∃ c', FrameRun p (c, fs) (c', []) ∧ SysOk p (ms []) s c' (.exitGroup σ0.regs.rax.toNat)) :
    SegWS W K p lbl ms ((At exe endPc R F n).at fs) Q := by
  refine (SegWS.liftS fs (Q₀ := At exe endPc R F (xExitNx n sp b z0 z1 z2)) ?_ fun _ _ h => h).seq ?_
  · refine (seg_ndW (N := fun _ : Unit => xExitNx n sp b z0 z1 z2) (E := fun e : Empty => e.elim)
      (by simp [xExit]) (hno ▸ xExit_ok k z0 z1 z2 hk) hF hR hlo hhi hc0 hW0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    obtain ⟨h1, h2, h3⟩ := xExit_run (Executable.labels exe).label n.pc sp b σ k z0 z1 z2
    rw [hno]
    refine ⟨h1, ?_, h2, σ, hJ, h3⟩
    simp only [xExit]; x64simp; simp [xExitNx, SO.le, lk]
  · refine SegWS.step (fun s c fs' ⟨hA, e⟩ => by subst e; exact (hW1 s c hA).1)
      (fun s c fs' ⟨hA, _⟩ => (hW1 s c hA).2) ?_
    rintro s c fs' ⟨hAt, rfl⟩
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, h231, σ0, hJ0, hx0⟩ := id hAt
    have hc : CellAt s (op64 .syscall) z3 := (hc1 s he hn).cell0 rfl rfl hpc
    have hd : Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.x64 (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) =
        some (.exitGroup σ0.regs.rax.toNat) := by
      have e : σ.regs.rdi.toNat = σ0.regs.rax.toNat := congrArg BitVec.toNat hx0
      rw [← e, ← syscallCall_exitGroup h231, syscallCall, ← hA.regs]; rfl
    obtain ⟨c', hr, hok'⟩ := hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ, hA, hD, hx0⟩
    exact .pre c' [] hr (.sys _ _ hK (Scc.Sem.X64.atSyscall_of_cellAt hc) hd hok' fun s' hs' => by
      rw [certSuccs_exitGroup] at hs'; cases hs')

end Helpers

end Spike.Lib.X64.Rt

/--
info: 'Spike.Lib.X64.Rt.xExitTail_segWSF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.X64.Rt.xExitTail_segWSF
