/-
**`main`'s exit from its body's exits at pending frames** (x86-64): the
twins of `UPostR`, `uPostR_ret`, `uPostR_exit` and `mainCallWS_of_exitC2SL`
(`Spike/Lib/LowerX64/MainExit2.lean`, `Spike/Lib/LowerX64/MainCall2.lean`)
for a pair held at a callee's `ret` at depth (`MainCallWSF`, `MainExitFA`,
`Spike/Lib/Rt/X64MainSSF.lean`, `Spike/Lib/Rt/X64ExitF.lean`).

- `UPostRF`: the user function's post at a pair at the frames `fs`: a frame
  run from `(c, fs)` back to depth 0 reaches the return of `v` (`RetV`);
  `UPostR.toF`: `UPostR` is `UPostRF` at the empty frames;
- `uPostRF_ret`: `uPostR_ret` from a frame run at any frames back to depth 0;
- `uPostRF_exit`: at a pair `UPostRF` relates to the number in `%rdi`,
  `MainExitFA` with that number mod 256 (`uPostR_exit` after the run; at an
  abort site the run alone);
- `ExitC2SLF`: `ExitC2SL` with the pair at any frames a frame run takes to
  the return's control at the body's frames (the return held at a callee's
  `ret`); `ExitC2SL.toF`, `ExitC2SLF.trans`;
- `mainCallWSF_of_exitC2SLF`: `MainCallWSF … UPostRF` from a segment of
  `main`'s body to `ExitC2SLF` at `int` at `[]`, its aborts never ending.
-/
import Spike.Lib.LowerX64.MainCall2
import Spike.Lib.Rt.X64MainSSF

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.LowerNode (RetL)

/-- **The user function's post at a pair at the frames `fs`**: a frame run
from `(c, fs)` back to depth 0 reaches the return of `v` (`RetV`). -/
def UPostRF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) (fs : List TermRun.Frame)
    (v : BitVec 64) : Prop :=
  ∃ c', FrameRun p (c, fs) (c', []) ∧ RetV lbl c' v

/-- `UPostR` is `UPostRF` at the empty frames. -/
theorem UPostR.toF {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c : Ctl} {v : BitVec 64}
    (h : UPostR p lbl c v) : UPostRF p lbl c [] v :=
  h

/-- **`main`'s return at the interface's post from pending frames**
(`uPostR_ret` at `UPostRF`): the return's exit by placements past `ret` in
the rebased region at `c`, a frame run from `(cb, fs)` reaching `c` at
depth 0, is `uNx` at `UPostRF` at `fs` at `cb`. -/
theorem uPostRF_ret {p : Prog} {exe : _root_.Executable} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {F : MachineData → Prop} {g : Spike.Lib.X64.Flow.Ret0.WcG} {c0 cb c : Ctl} {s : State} {tp : UInt64}
    {fs : List TermRun.Frame} (hbase : R.base = g.sp) (hr : FrameRun p (cb, fs) (c, []))
    (hA : At exe endPc (rbR R) F ((retNSL p lbl g.fp g.ra c0 .int).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.X64.Rt.uNx (fun c v => UPostRF p lbl c fs v) g) s cb := by
  obtain ⟨he, hn, hdc, hpc, σ, hA', hD, ⟨c', hr', hv⟩, hJ⟩ := uPostR_ret hbase (.refl _) hA
  exact ⟨he, hn, hdc, hpc, σ, hA', hD, ⟨c', hr.trans hr', hv⟩, hJ⟩

/-- **`main`'s exit at the post `UPostRF`** (`MainExitFA`): from a pair at
the frames `fs` a frame run takes back to depth 0 to `main`'s `ret` of the
number in `%rdi`, placed there, the run, and off an abort site `main`'s exit
with the number mod 256 (`uPostR_exit`). -/
theorem uPostRF_exit {p : Prog} {Λ : Scc.Sem.Layout} {lbl : Lbl} {ms : MemSide isa}
    (hpl : ∀ s c, Placed Λ lbl s c → ms.pl s c) {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (fs : List TermRun.Frame) (v : BitVec 64),
      UPostRF p lbl c fs v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        Spike.Lib.X64.Rt.MainExitFA p ms s c fs v.toNat := by
  rintro R' F' s c fs v ⟨c', hr, hv⟩ ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩
  by_cases hab : ms.abortAt s
  · exact ⟨c', hr, fun hn => absurd hab hn⟩
  obtain ⟨c'', hr', hx'⟩ := uPostR_exit hpl R' F' s c' v ⟨c', .refl _, hv⟩
    ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ hab
  exact ⟨c'', hr.trans hr', fun _ => hx'⟩

/-- **The body's exits at the frames `fs` by placements, held at pending
frames**: `ExitC2SL` with the pair at any frames `fs'` from which a frame
run reaches the return's control `c1` at `fs` (a callee's `ret` held through
`main`'s return), the machine at `retNSL` at `c1`. -/
def ExitC2SLF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isa) : FragS isa := fun s c fs' =>
  (∃ c1, FrameRun p (c, fs') (c1, fs) ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((retNSL p lbl fp ra c0' ty).withTp tp) s c1) ∨ Ab s c fs'

/-- `ExitC2SL` is `ExitC2SLF` (the empty run). -/
theorem ExitC2SL.toF {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {fs : List TermRun.Frame} {ty : Ty} {Ab : FragS isa} :
    ∀ s c fs', ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' →
      ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ c _ h => h.imp_left fun ⟨e, h⟩ => ⟨c, e ▸ .refl _, h⟩

/-- **`ExitC2SLF` re-anchored by a frame run** of the ghost. -/
theorem ExitC2SLF.trans {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl}
    {fs : List TermRun.Frame} {ty : Ty} {Ab : FragS isa} (hr : FrameRunM p (c0, fs) (c0', fs)) :
    ∀ s c fs', ExitC2SLF p lbl exe endPc R F fp ra tp c0' fs ty Ab s c fs' →
      ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ _ _ h => h.imp_left fun ⟨c1, h1, c2, hr', h⟩ => ⟨c1, h1, c2, hr.trans hr', h⟩

/-- **`ExitC2SLF` held further back**: a frame run from the pair to the
held one keeps the exit. -/
theorem ExitC2SLF.back {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {fs : List TermRun.Frame} {ty : Ty} {s : State} {c c' : Ctl} {fs₁ fs₂ : List TermRun.Frame}
    (hr : FrameRun p (c, fs₁) (c', fs₂))
    (h : ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty (fun _ _ _ => False) s c' fs₂) :
    ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty (fun _ _ _ => False) s c fs₁ :=
  h.imp_left (fun ⟨c1, h1, h⟩ => ⟨c1, hr.trans h1, h⟩) |>.elim .inl False.elim

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isa} {K : State → State → Prop}

/-- **The user `main` after a setup block at depth, from its exits held at
pending frames** (`MainCallWSF` at `UPostRF`): `mainCallWS_of_exitC2SL`
with the body's exits `ExitC2SLF`; the return past `ret` is `NxF` at
`UPostRF` (`uPostRF_ret` along the held run). -/
theorem mainCallWSF_of_exitC2SLF {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
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
          (ExitC2SLF p lbl exe endPc (rbR (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8)) F' g.fp g.ra tp c0' []
            .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.X64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre (UPostRF p lbl) ra tp := by
  intro F' hR0 hF' hFF g hra htp
  by_cases hbase : (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).base = g.sp
  case neg =>
    refine SegWS.empty fun s c fs h => hbase ?_
    obtain ⟨⟨-, -, -, -, σ, hA, -, ⟨-, -, -, hsp, -⟩, -⟩, -⟩ := h
    have := hA.so .rsp 0 (by simp [SO.get, Spike.Lib.X64.Rt.uNM])
    rw [← hsp]
    simpa [Region.addr, Reg64s.get64] using this.symm
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hF' hFF g hra htp hbase
  refine (SegWS.seq_left (Q := Ab)
      (E := Spike.Lib.X64.Rt.NxF exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (UPostRF p lbl) g)
      (h1.mono_post fun s c fs h => ?_) hAb).mono_post fun s c fs h => ?_
  · rcases h with ⟨c1, hr, c2, -, hA⟩ | h
    · exact .inr (uPostRF_ret hbase hr hA)
    · exact .inl h
  · exact h.elim False.elim id

/--
info: 'Spike.Lib.LowerX64.uPostRF_exit' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uPostRF_exit

/--
info: 'Spike.Lib.LowerX64.mainCallWSF_of_exitC2SLF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainCallWSF_of_exitC2SLF

end Spike.Lib.LowerX64
