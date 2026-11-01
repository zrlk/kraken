/-
**The worker's thread rows at any call depth** (hello.w; the frame-aware
twin of `Spike/Lib/SegThr.lean`'s `OutT`, over `Spike/Lib/SegS.lean`'s
fragments with frames): hello's worker calls `print` (and `print` calls
`printL`), so its rows pair the target with a source control *and* the
source worker's suspended frames.

- `OutTS`: what one instruction of the worker does at frames `fs`:
  - `pre`: a frame run to `(c₁, fs₁)`, then an `OutL` row there (the memory
    side at `fs₁`), as `OutS.pre` with `OutL` for `Out`;
  - `frame`: a silent instruction whose source side is a frame run (a
    call's `bl`, a callee's `ret`), as `OutS.frame`;
  - `fnc`: a fence (`dmb ish` in `print`), the source a frame run, at any
    depth;
  - `top`: a frame run to depth `0`, then an `OutT` row there (the
    worker's `unpk` and `texit` after `print` returned: wake's rows
    unchanged).
- `OutTS.mono`, `OutTS.run` (a frame run before), `OutTS.top0` (`top` with
  no frame run), `OutTS.ofT` (`OutT` at depth `0`), `OutTS.ofS` (`OutS`, its
  `Out` rows as `OutL` rows).
-/
import Spike.Lib.SegThr
import Spike.Lib.SegS

namespace Spike.Lib.HelloSegThrS

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib

/-- **What one instruction of the worker does at frames `fs`** (see the
module doc). -/
inductive OutTS {I : ISA} (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (ms : List TermRun.Frame → MemSide I)
    (X : FragS I) (s : I.State) (c : Ctl) (fs : List TermRun.Frame) : Prop where
  /-- A frame run, then an `OutL` row at the frames reached. -/
  | pre (c₁ : Ctl) (fs₁ : List TermRun.Frame) :
      FrameRun p (c, fs) (c₁, fs₁) → OutL p lbl (ms fs₁) (fun s c => X s c fs₁) s c₁ → OutTS p lbl ms X s c fs
  /-- A silent instruction, the source a frame run (a call, a return). -/
  | frame (s' : I.State) (c' : Ctl) (fs' : List TermRun.Frame) :
      I.exec s = some (.done s') → FrameRun p (c, fs) (c', fs') → X s' c' fs' → OutTS p lbl ms X s c fs
  /-- A fence, the source a frame run (it stutters, possibly none). -/
  | fnc (k : Kraken.FenceKind) (s' : I.State) (c' : Ctl) (fs' : List TermRun.Frame) :
      I.exec s = some (.fence k fun _ => .done s') → FrameRun p (c, fs) (c', fs') → X s' c' fs' →
      OutTS p lbl ms X s c fs
  /-- A frame run to depth `0`, then a thread row (`unpk`, `texit`, or any
  `OutT` row). -/
  | top (c₁ : Ctl) : FrameRun p (c, fs) (c₁, []) → OutT p lbl (ms []) (fun s c => X s c []) s c₁ →
      OutTS p lbl ms X s c fs

namespace OutTS

variable {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I}
  {X Y : FragS I} {s : I.State} {c : Ctl} {fs : List TermRun.Frame}

theorem mono (h : OutTS p lbl ms X s c fs) (hXY : ∀ s c fs, X s c fs → Y s c fs) : OutTS p lbl ms Y s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (h.mono fun s c => hXY s c fs₁)
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr (hXY _ _ _ hx)
  | fnc k s' c' fs' he hr hx => exact .fnc k s' c' fs' he hr (hXY _ _ _ hx)
  | top c₁ hr h => exact .top c₁ hr (h.mono fun s c => hXY s c [])

/-- **A frame run before a row** is a row. -/
theorem run {c₁ : Ctl} {fs₁ : List TermRun.Frame} (hr : FrameRun p (c, fs) (c₁, fs₁))
    (h : OutTS p lbl ms X s c₁ fs₁) : OutTS p lbl ms X s c fs := by
  cases h with
  | pre c₂ fs₂ hr' h => exact .pre c₂ fs₂ (hr.trans hr') h
  | frame s' c' fs' he hr' hx => exact .frame s' c' fs' he (hr.trans hr') hx
  | fnc k s' c' fs' he hr' hx => exact .fnc k s' c' fs' he (hr.trans hr') hx
  | top c₂ hr' h => exact .top c₂ (hr.trans hr') h

/-- `top` with no frame run: an `OutT` row at depth `0`. -/
theorem top0 (hfs : fs = []) (h : OutT p lbl (ms []) (fun s c => X s c []) s c) : OutTS p lbl ms X s c fs :=
  .top c (hfs ▸ .refl _) h

/-- An `OutT` row at depth `0`. -/
theorem ofT (h : OutT p lbl (ms []) (fun s c => X s c []) s c) : OutTS p lbl ms X s c [] := top0 rfl h

/-- An `OutS` row (its `Out` rows are `OutL` rows). -/
theorem ofS (h : OutS p lbl ms X s c fs) : OutTS p lbl ms X s c fs := by
  cases h with
  | pre c₁ fs₁ hr h => exact .pre c₁ fs₁ hr (.out h)
  | frame s' c' fs' he hr hx => exact .frame s' c' fs' he hr hx

end OutTS

end Spike.Lib.HelloSegThrS
