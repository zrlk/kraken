/-
**The suspended frames' records and the arena's memory side at a larger
level** (AArch64): the placement transport of the levels' static stack
invariant (`Spike/Lib/LowerA64/Stk2.lean`) across a fresh allocation
(`lvlLe_upd`): a record's facts, the records and a context with its
suspended frames, stated at the level `(lbl, lsize)`, hold at any level
above it (`LvlLe`), the base context `CxOk` transported alongside; and the
arena's memory side `msOfAX` at the larger level places every pair it placed,
owns the same words and leaves runtime no address it did not. The twin of
`Spike/Lib/LowerX64/StkMono2.lean`.

- `CallerAt2.mono_lbl`, `StkFrOk.mono_lbl`, `StkOk.mono_lbl`, `CxOkS.mono_lbl`:
  the records at a larger level (`CalleeF2.mono`; `BodyPt`, the region nesting and the return
  site do not mention the level);
- `Placed.mono_lbl`: a placed control at more placed labels;
- `msOfAX_pl_mono_lbl`, `msOfAX_own_lbl`, `msOfAX_rt_anti_lbl`: `msOfAX`'s
  placed pairs, owned words and runtime addresses across levels.
-/
import Spike.Lib.LowerA64.Stk2
import Spike.Lib.LowerA64.LevelMono2
import Spike.Lib.A64ConsumerA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode

/-! ## The records at a larger level -/

section Stk

variable {p : Prog} {lbl lbl' : WeakMem.AllocLabel → Option Nat} {lsize lsize' : WeakMem.AllocLabel → Nat}
  {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
  {CxOk CxOk' : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
      (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **The caller pinned at a call site at a larger level.** -/
theorem CallerAt2.mono_lbl (hv : LvlLe lbl lsize lbl' lsize') {cx : FnCtx} {R : Region} {D : Int}
    {fp ra : BitVec 64} {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop} {c0 : Ctl} {t : Expr}
    {env : Scc.Lower.Env} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : CallerAt2 p lbl lsize cx R D fp ra q frm F' c0 t env lits cs bufs) :
    CallerAt2 p lbl' lsize' cx R D fp ra q frm F' c0 t env lits cs bufs := fun m hm =>
  let ⟨mC, σC, c, ha, hk, hct, hj, he, hf, hr⟩ := h m hm
  ⟨mC, σC, c, ha, hk, hct, Spike.Lib.Form.NodeJE.mono_lbl hv.1 hj, he.mono hv.2, hf, hr⟩

/-- **A record's facts at a larger level**, the caller's context `CxOk`
transported to `CxOk'` (`hCx`). -/
theorem StkFrOk.mono_lbl (hv : LvlLe lbl lsize lbl' lsize')
    (hCx : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → CxOk' j R F fs fp ra tp G0 Ab)
    {k : StkKey} {a : StkFr} {f : TermRun.Frame} {fs : List TermRun.Frame}
    (h : StkFrOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk k a f fs) :
    StkFrOk (p := p) (lbl := lbl') (lsize := lsize') hcode CxOk' k a f fs :=
  let ⟨d, hd, hc, hra, hg, hb, h0, h8, hlo, hk, hst, hcal, hbl, hlk, hcl, hpin, hln⟩ := h
  ⟨d, hd, hCx _ _ _ _ _ _ _ _ _ hc, hra, hg, hb, h0, h8, hlo, hk, hst, hcal.mono hv, hbl, hlk, hcl, hpin.mono_lbl hv,
    hln⟩

/-- **The records at a larger level**, the callers' contexts transported
(`hCx`). -/
theorem StkOk.mono_lbl (hv : LvlLe lbl lsize lbl' lsize')
    (hCx : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → CxOk' j R F fs fp ra tp G0 Ab)
    {k : StkKey} {st : List StkFr} {fs : List TermRun.Frame}
    (h : StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k st fs) :
    StkOk (p := p) (lbl := lbl') (lsize := lsize') hcode CxOk' Bot k st fs :=
  StkOkB.mono (fun _ _ _ _ ha => StkFrOk.mono_lbl hv hCx ha) (fun _ _ h => h) h

/-- **A context with its suspended frames at a larger level**, the base
context transported (`hCx`). -/
theorem CxOkS.mono_lbl (hv : LvlLe lbl lsize lbl' lsize')
    (hCx : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → CxOk' j R F fs fp ra tp G0 Ab)
    {j : Nat} {R : Region} {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64}
    {G0 : Ctl → Prop} {Ab : FragS isaLSE2}
    (h : CxOkS (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot j R F fs fp ra tp G0 Ab) :
    CxOkS (p := p) (lbl := lbl') (lsize := lsize') hcode CxOk' Bot j R F fs fp ra tp G0 Ab :=
  let ⟨hc, st, hst⟩ := h
  ⟨hCx _ _ _ _ _ _ _ _ _ hc, st, StkOk.mono_lbl hv hCx hst⟩

end Stk

end Spike.Lib.LowerA64

/-! ## The arena's memory side at a larger level -/

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl lbl' : Lbl} {lsize lsize' : Lsize}
  {fs : List TermRun.Frame} {s : State} {c : Ctl}

/-- **A placed control at more placed labels.** -/
theorem Placed.mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b) (h : Placed Λ lbl s c) :
    Placed Λ lbl' s c :=
  let ⟨envm, hrep, htot, himm⟩ := h
  ⟨envm, fun x ty ws hx k wd wp hwd hwp => wordPlaceRep_mono_lbl hl (hrep x ty ws hx k wd wp hwd hwp), htot, himm⟩

/-- **`msOfAX`'s placed pairs at more placed labels.** -/
theorem msOfAX_pl_mono_lbl (hl : ∀ l b, lbl l = some b → lbl' l = some b)
    (h : (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pl s c) :
    (msOfAX Λ μ p rd G own ar I ab lbl' lsize' fs).pl s c := by
  cases ab
  · exact ⟨h.1, Placed.mono_lbl hl h.2⟩
  · exact ⟨h.1, Placed.mono_lbl hl h.2⟩

/-- **`msOfAX`'s owned words do not depend on the level.** -/
theorem msOfAX_own_lbl :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).own = (msOfAX Λ μ p rd G own ar I ab lbl' lsize' fs).own := by
  cases ab <;> rfl

/-- **`msOfAX`'s runtime addresses at a larger level were runtime's**: every
label placed at the smaller level is placed alike, no larger. -/
theorem msOfAX_rt_anti_lbl (hv : Spike.Lib.LowerNode.LvlLe lbl lsize lbl' lsize') {a : Nat}
    (h : (msOfAX Λ μ p rd G own ar I ab lbl' lsize' fs).rt a) :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).rt a := by
  have key : ∀ (lbl₀ : Lbl) (lsize₀ : Lsize),
      (msOfAX Λ μ p rd G own ar I ab lbl₀ lsize₀ fs).rt a ↔
        ¬ ∃ l b, lbl₀ l = some b ∧ (lrange lsize₀ l b).contains a := by
    intro _ _; cases ab <;> exact Iff.rfl
  rw [key] at h ⊢
  rintro ⟨l, b, hb, hlo, hhi⟩
  refine h ⟨l, b, hv.1 l b hb, hlo, ?_⟩
  have := hv.2 l
  simp only [lrange] at hlo hhi ⊢
  omega

end Spike.Lib.A64ConsumerA

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.CxOkS.mono_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.CxOkS.mono_lbl

/-- info: 'Spike.Lib.A64ConsumerA.msOfAX_pl_mono_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.msOfAX_pl_mono_lbl

/-- info: 'Spike.Lib.A64ConsumerA.msOfAX_rt_anti_lbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.msOfAX_rt_anti_lbl
