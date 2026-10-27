/-
**`main`'s exit from its `Accepted2` body's exits** (AArch64): the user
`main`'s exit by placements (`ExitC2SL` at the empty frames, return type
`int`) is `scc_rt_main`'s post at the return (`MainPost2`: the result in
`x0` a number the source returns, after a frame run from the start), and
there the `exit_group` is `main`'s exit under the rows' memory side
(`MainExit` at `msOfAX`, `mainS_segW`'s `hexit`).

- `MainPost2`: the post at the return: from the start `c0` a frame run at
  the empty frames and a local run reach the control, at `ret` of the
  number represented by `x0` (`RetV`).
- `retV_of_retJS_int`: `RetJS` at return type `int` is `RetV` of `x0`.
- `mainPost2_of_exit`: `ExitC2SL`'s return pair at the empty frames gives
  `MainPost2` at `x0`, with `x29`/`x30` restored (`uNx`'s invariant).
- `mainExit2_of_retV`, `mainExit2_of_post`: `MainExit` at `msOfAX`'s
  empty frames from `RetV` (`uPost_exit`).
-/
import Spike.Lib.LowerA64.RetSL
import Spike.Lib.LowerA64.StartU
import Spike.Lib.A64ConsumerA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Sem (Marks)
open Spike.Lib.A64Consumer (Lbl Lsize msOf)
open Spike.Lib.A64ConsumerS (OwnS InvS)
open Spike.Lib.A64ConsumerA (msOfAX)
open Spike.Lib.LowerNode (RetL)

/-- **`scc_rt_main`'s post at the user `main`'s return**: from the start
`c0` a frame run at the empty frames and a local run reach the control `c`,
at `ret` of the number represented by `v` (`RetV`). -/
def MainPost2 (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (c0 : Ctl) (c : Ctl) (v : BitVec 64) : Prop :=
  ∃ c0', FrameRunM p (c0, []) (c0', []) ∧ LocalRun p c0' c ∧ RetV lbl c v

/-- **The return by placements at `int` is the return of `x0`**
(`RetJS.toJ2_int`, `RetL.int`). -/
theorem retV_of_retJS_int {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : AS} {c : Ctl}
    (h : RetJS lbl fp ra σ c) (hL : RetL .int c) : RetV lbl c σ.regs.X0.toBitVec := by
  obtain ⟨a, t, ws, ht, hh, he, hlen, hv, -, -⟩ := RetJS.toJ2_int h hL
  obtain ⟨a', t', w, ht', he', n, hn, -⟩ := RetL.int hL
  rw [ht] at ht'
  cases ht'
  rw [he] at he'
  cases he'
  exact ⟨a, t, w, ht, hh, he, ⟨n, hn⟩, hv 0 (by simp) (by decide)⟩

/-- **`main`'s exit pair is `scc_rt_main`'s post** (`uNx`'s invariant at
`MainPost2`): at the empty frames, `ExitC2SL`'s return (not its aborts) at
return type `int` gives the post at `x0`, `x29` and `x30` restored. -/
theorem mainPost2_of_exit {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {fp ra : BitVec 64} {tp : UInt64} {c0 : Ctl}
    {s : State} {c : Ctl} (h : ∃ c0', FrameRunM p (c0, []) (c0', []) ∧
      At exe endPc R F ((retNSL p lbl fp ra c0' .int).withTp tp) s c) :
    At exe endPc R F ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ c =>
      MainPost2 p lbl c0 c σ.regs.X0.toBitVec ∧ σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra⟩ s c := by
  obtain ⟨c0', hr, he, hn, hd, hpc, σ, hA, hF, ⟨⟨hJ, hloc⟩, hL⟩, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h29, h30⟩ := id hJ
  exact ⟨he, hn, hd, hpc, σ, hA, hF, ⟨c0', hr, hloc, retV_of_retJS_int hJ hL⟩, h29, h30⟩

/-- **`main`'s exit at a return of `x0`** under the rows' memory side at
the empty frames (`uPost_exit` at the empty local run): the `exit_group`
of the number in `x0` there is `main` returning it mod 256. -/
theorem mainExit2_of_retV {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl}
    {ls : Lsize} {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} {R : Region}
    {F : MachineData → Prop} {s : State} {c : Ctl} {v : BitVec 64} (hv : RetV lbl c v)
    (hx : At exe endPc R F ⟨pc, o, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c)
    (hab : ¬ (msOfAX Λ μ p rd G own ar I ab lbl ls []).abortAt s) :
    MainExit p (msOfAX Λ μ p rd G own ar I ab lbl ls []) s c v.toNat := by
  obtain ⟨c', hr, hpl, hex⟩ := uPost_exit (p := p) (Λ := Λ) (μ := μ) (rd := rd) (G := G)
    (own := fun s => own s []) (ls0 := ls) rfl R F s c v ⟨rfl, c, .refl _, hv⟩ hx (by cases ab <;> exact hab)
  exact ⟨c', hr, by cases ab <;> exact ⟨rfl, hpl⟩, hex⟩

/-- **`main`'s exit at `scc_rt_main`'s post** (`mainS_segW`'s `hexit` at
`MainPost2`, under the rows' memory side at the empty frames). -/
theorem mainExit2_of_post {p : Prog} {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl}
    {ls : Lsize} {exe : _root_.Executable} {endPc : Int64} {pc : Int64} {o : SO} {c0 : Ctl} :
    ∀ (R : Region) (F : MachineData → Prop) s c (v : BitVec 64), MainPost2 p lbl c0 c v →
      At exe endPc R F ⟨pc, o, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c →
      ¬ (msOfAX Λ μ p rd G own ar I ab lbl ls []).abortAt s →
      MainExit p (msOfAX Λ μ p rd G own ar I ab lbl ls []) s c v.toNat :=
  fun _ _ _ _ _ ⟨_, _, _, hv⟩ hx hab => mainExit2_of_retV hv hx hab

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.mainPost2_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainPost2_of_exit

/-- info: 'Spike.Lib.LowerA64.mainExit2_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms mainExit2_of_post

end Spike.Lib.LowerA64
