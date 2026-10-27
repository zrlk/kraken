/-
**`main`'s exit from its body's exits at pending frames** (AArch64; the
twin of `Spike/Lib/LowerX64/MainExitF.lean`): `MainPost2`, `mainPost2_of_exit`,
`mainExit2_of_post` and `mainCallWS_of_exitC2SL`
(`Spike/Lib/LowerA64/MainExit2.lean`, `Spike/Lib/LowerA64/MainCall2.lean`)
for a pair held at a callee's `ret` at depth (`MainCallWSF`, `MainExitFA`,
`Spike/Lib/Rt/A64MainSSF.lean`, `Spike/Lib/Rt/A64ExitF.lean`).

- `UPostRF`: the user function's post at a pair at the frames `fs`: a frame
  run from `(c, fs)` back to depth 0 reaches the return of `v` (`RetV`);
  `UPostRF.ofPost2`: `MainPost2` is `UPostRF` at the empty frames;
- `uPostRF_ret`: the return's exit by placements at `int`, reached by a
  frame run from `(cb, fs)` at depth 0, is `uNx` at `UPostRF` at `fs` at `cb`
  (`mainPost2_of_exit`'s shape);
- `uPostRF_exit`: at a pair `UPostRF` relates to the number in `x0`,
  `MainExitFA` with that number mod 256 under the rows' memory side at the
  empty frames (`mainExit2_of_retV` after the run; at an abort site the run
  alone);
- `ExitC2SLF`: `ExitC2SL` with the pair at any frames a frame run takes to
  the return's control at the body's frames (the return held at a callee's
  `ret`); `ExitC2SL.toF`, `ExitC2SLF.trans`, `ExitC2SLF.back`;
- `mainCallWSF_of_exitC2SLF`: `MainCallWSF … UPostRF` from a segment of
  `main`'s body to `ExitC2SLF` at `int` at `[]`, its aborts never ending.
-/
import Spike.Lib.LowerA64.MainCall2
import Spike.Lib.Rt.A64MainSSF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Sem (Marks)
open Spike.Lib.A64Consumer (Lbl Lsize msOf)
open Spike.Lib.A64ConsumerS (OwnS InvS)
open Spike.Lib.A64ConsumerA (msOfAX)
open Spike.Lib.LowerNode (RetL)

/-- **The user function's post at a pair at the frames `fs`**: a frame run
from `(c, fs)` back to depth 0 reaches the return of `v` (`RetV`). -/
def UPostRF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c : Ctl) (fs : List TermRun.Frame)
    (v : BitVec 64) : Prop :=
  ∃ c', FrameRun p (c, fs) (c', []) ∧ RetV lbl c' v

/-- `MainPost2` is `UPostRF` at the empty frames (the empty run). -/
theorem UPostRF.ofPost2 {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {c0 c : Ctl} {v : BitVec 64}
    (h : MainPost2 p lbl c0 c v) : UPostRF p lbl c [] v :=
  let ⟨_, _, _, hv⟩ := h
  ⟨c, .refl _, hv⟩

/-- **`main`'s return at the interface's post from pending frames**
(`mainPost2_of_exit` at `UPostRF`): the return's exit by placements at `int`
at `c`, a frame run from `(cb, fs)` reaching `c` at depth 0, is `uNx` at
`UPostRF` at `fs` at `cb`. -/
theorem uPostRF_ret {p : Prog} {exe : _root_.Executable} {endPc : Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {R : Region} {F : MachineData → Prop} {g : Spike.Lib.A64.Flow.Ret0.WcG} {c0 cb c : Ctl} {s : State}
    {tp : UInt64} {fs : List TermRun.Frame} (hr : FrameRun p (cb, fs) (c, []))
    (hA : At exe endPc R F ((retNSL p lbl g.fp g.ra c0 .int).withTp tp) s c) :
    At exe endPc R F (Spike.Lib.A64.Rt.uNx (fun c v => UPostRF p lbl c fs v) g) s cb := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, ⟨⟨hJ, -⟩, hL⟩, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h29, h30⟩ := id hJ
  exact ⟨he, hn, hd, hpc, σ, hA, hF, ⟨c, hr, retV_of_retJS_int hJ hL⟩, h29, h30⟩

/-- **`main`'s exit at the post `UPostRF`** (`MainExitFA`, under the rows'
memory side at the empty frames): from a pair at the frames `fs` a frame run
takes back to depth 0 to `main`'s `ret` of the number in `x0`, the run, and
off an abort site `main`'s exit with the number mod 256
(`mainExit2_of_retV`). -/
theorem uPostRF_exit {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl}
    {ls : Lsize} {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} :
    ∀ (R' : Region) (F' : MachineData → Prop) s c (fs : List TermRun.Frame) (v : BitVec 64),
      UPostRF p lbl c fs v →
      At exe endPc R' F' ⟨pc, o, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c →
        Spike.Lib.A64.Rt.MainExitFA p (msOfAX Λ μ p rd G own ar I ab lbl ls []) s c fs v.toNat := by
  rintro R' F' s c fs v ⟨c', hr, hv⟩ ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩
  exact ⟨c', hr, fun hab => mainExit2_of_retV hv ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ hab⟩

/-- **The body's exits at the frames `fs` by placements, held at pending
frames**: `ExitC2SL` with the pair at any frames `fs'` from which a frame
run reaches the return's control `c1` at `fs` (a callee's `ret` held through
`main`'s return), the machine at `retNSL` at `c1`. -/
def ExitC2SLF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (fs : List TermRun.Frame)
    (ty : Ty) (Ab : FragS isaLSE2) : FragS isaLSE2 := fun s c fs' =>
  (∃ c1, FrameRun p (c, fs') (c1, fs) ∧ ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    At exe endPc R F ((retNSL p lbl fp ra c0' ty).withTp tp) s c1) ∨ Ab s c fs'

/-- `ExitC2SL` is `ExitC2SLF` (the empty run). -/
theorem ExitC2SL.toF {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {fs : List TermRun.Frame} {ty : Ty} {Ab : FragS isaLSE2} :
    ∀ s c fs', ExitC2SL p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' →
      ExitC2SLF p lbl exe endPc R F fp ra tp c0 fs ty Ab s c fs' :=
  fun _ c _ h => h.imp_left fun ⟨e, h⟩ => ⟨c, e ▸ .refl _, h⟩

/-- **`ExitC2SLF` re-anchored by a frame run** of the ghost. -/
theorem ExitC2SLF.trans {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 c0' : Ctl}
    {fs : List TermRun.Frame} {ty : Ty} {Ab : FragS isaLSE2} (hr : FrameRunM p (c0, fs) (c0', fs)) :
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

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {W : FragS isaLSE2} {K : State → State → Prop}

/-- **The user `main` after a setup block at depth, from its exits held at
pending frames** (`MainCallWSF` at `UPostRF`): `mainCallWS_of_exitC2SL`
with the body's exits `ExitC2SLF`; the return past `ret` is `NxF` at
`UPostRF` (`uPostRF_ret` along the held run). -/
theorem mainCallWSF_of_exitC2SLF {R : Region} {F : MachineData → Prop} {fn : Label} {Z : Int64} {D : Int}
    {ZU : Int64} {Pre : Ctl → Reg64s → Prop} {ra : BitVec 64} {tp : UInt64}
    (hseg : ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK →
      (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 → FStable (R.callee (-Z.toInt) (-D) 0) F' →
      (∀ m, F' m → F m ∧ Spike.Lib.A64.Flow.Ret0.CallerCells R (-Z.toInt) (-D) 0 m) →
      ∀ g : Spike.Lib.A64.Flow.Ret0.WcG, g.ra = ra → g.tp = tp →
      ∃ (Ab : FragS isaLSE2) (c0' : Ctl),
        SegWS W K p lbl ms
          ((At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
            (Spike.Lib.A64.Rt.uNM (_root_.Executable.labels exe).label (ms []) F exe endPc fn ZU Pre g)).at [])
          (ExitC2SLF p lbl exe endPc (R.callee (-Z.toInt) (-D) 0) F' g.fp g.ra tp c0' [] .int Ab) ∧
        SegWS W K p lbl ms Ab (fun _ _ _ => False)) :
    Spike.Lib.A64.Rt.MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU Pre (UPostRF p lbl) ra tp := by
  intro F' hR0 hal hF' hFF g hra htp
  obtain ⟨Ab, c0', h1, hAb⟩ := hseg F' hR0 hal hF' hFF g hra htp
  refine (SegWS.seq_left (Q := Ab)
      (E := Spike.Lib.A64.Rt.NxF exe endPc (R.callee (-Z.toInt) (-D) 0) F' (UPostRF p lbl) g)
      (h1.mono_post fun s c fs h => ?_) hAb).mono_post fun s c fs h => ?_
  · rcases h with ⟨c1, hr, c2, -, hA⟩ | h
    · exact .inr (uPostRF_ret hr hA)
    · exact .inl h
  · exact h.elim False.elim id

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.uPostRF_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms uPostRF_exit

/--
info: 'Spike.Lib.LowerA64.mainCallWSF_of_exitC2SLF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mainCallWSF_of_exitC2SLF

end Spike.Lib.LowerA64
