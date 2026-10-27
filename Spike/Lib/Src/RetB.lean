import Spike.Lib.Src.NJLB
import Spike.Lib.Src.NJLC

/-!
**The source facts at a return's exit** (ISA-neutral), for a caller's
`EnvB.ret` and `EnvB.mono` across a call: against the caller's labels `L`
and memory `sm` at the call, the exit's labels and memory extend them, the
exit's memory is `MemB`, and the returned atom has its slices at the
callee's declared return type (`callsOk2`'s `ret` check).

- `Ext`: labels and memory extending others (`.refl`, `.trans`);
- `RetB`: the facts; `RetB.mono_entry` (weaker entry labels and memory);
- `RetL`: the facts for the caller's layouts only (`EnvLit`), `RetL.envLit`,
  `RetL.words`, `RetL.int` (one number at `int`);
- `RetB.frame`: the caller's `EnvB` at the exit's labels and memory
  (`EnvB.mono`), extended by the result (`EnvB.ret`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Scc.Lower (LitV litAt unbuf shapeOf)

/-- **Labels and memory extending others**: every label of `L` in `L'`,
every cell of `sm` in `sm'`. -/
def Ext (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (L' : WeakMem.AllocLabel → Prop)
    (sm' : WeakMem.Memory) : Prop :=
  (∀ l, L l → L' l) ∧ ∀ sa, HasCell sm sa → HasCell sm' sa

theorem Ext.refl (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) : Ext L sm L sm :=
  ⟨fun _ h => h, fun _ h => h⟩

theorem Ext.trans {L L' L'' : WeakMem.AllocLabel → Prop} {sm sm' sm'' : WeakMem.Memory} (h : Ext L sm L' sm')
    (h' : Ext L' sm' L'' sm'') : Ext L sm L'' sm'' :=
  ⟨fun l hl => h'.1 l (h.1 l hl), fun sa hc => h'.2 sa (h.2 sa hc)⟩

/-- **The source facts at a return's exit** against the caller's labels `L`
and memory `sm` at the call: some labels `L'` and memory `sm'` extending
them (`Ext`) with `MemB` at some bound, the control at `ret a` with `a`'s
slices in some layouts `lc` whose layout at `a`, literals dropped, is
`ty`'s. -/
def RetB (L : WeakMem.AllocLabel → Prop) (sm : WeakMem.Memory) (ty : Ty) (c : Ctl) : Prop :=
  ∃ L' sm' B', Ext L sm L' sm' ∧ MemB L' sm' B' ∧
    ∃ a lc, c.term = .ret a ∧ EnvSl (SlP L' sm') lc c.env ∧ (litAt lc a).erase = shapeOf ty

/-- **`RetB` at smaller entry labels and memory.** -/
theorem RetB.mono_entry {L L0 : WeakMem.AllocLabel → Prop} {sm sm0 : WeakMem.Memory} {ty : Ty} {c : Ctl}
    (h0 : Ext L0 sm0 L sm) (h : RetB L sm ty c) : RetB L0 sm0 ty c :=
  let ⟨L', sm', B', hx, hB, rest⟩ := h
  ⟨L', sm', B', h0.trans hx, hB, rest⟩

/-- **The source facts at a return's exit for the caller's layouts**: the
control at `ret a`, `a` in some layouts `lc` the environment keeps
(`EnvLit`, `a` bound or a literal below `2^64`) whose layout at `a`,
literals dropped, is `ty`'s, with `a`'s slices at some labels and memory,
and `a`'s words as many as its layout's (`RetL.words`: as `ty`'s). -/
def RetL (ty : Ty) (c : Ctl) : Prop :=
  ∃ a lc, c.term = .ret a ∧ EnvLit lc c.env ∧ InLits lc a ∧ (∀ n, a = .lit n → n < 2 ^ 64) ∧
    (litAt lc a).erase = shapeOf ty ∧ (∃ L sm, EnvSl (SlP L sm) lc c.env) ∧
    ∃ t ws, TermRun.evalAt c.env a = some (t, ws) ∧ ws.length = (litAt lc a).words.length

/-- **The returned words, as many as the return type's layout's** (`RetL`'s
words against its erase conjunct, `SliceL.words_erase`). -/
theorem RetL.words {ty : Ty} {c : Ctl} (h : RetL ty c) :
    ∃ a t ws, c.term = .ret a ∧ TermRun.evalAt c.env a = some (t, ws) ∧
      ws.length = (shapeOf ty).words.length := by
  obtain ⟨a, lc, ht, -, -, -, hr, -, t, ws, he, hl⟩ := h
  exact ⟨a, t, ws, ht, he, by rw [hl, ← hr, SliceL.words_erase]⟩

/-- **A return at `int` returns one number below `2^64`** (`RetL`'s layout
a leaf, `EnvLit.evalAt'`). -/
theorem RetL.int {c : Ctl} (h : RetL .int c) :
    ∃ a t w, c.term = .ret a ∧ TermRun.evalAt c.env a = some (t, [w]) ∧ IsNum w := by
  obtain ⟨a, lc, ht, hl, hsc, hlit, hr, -, t, ws, he, hlen⟩ := h
  have hm : litMask (litAt lc a) = [true] := by
    rw [← litMask_erase, hr]; rfl
  have h1 : ws.length = 1 := by rw [hlen, ← litMask_length, hm]; rfl
  obtain ⟨w, rfl⟩ := List.length_eq_one_iff.1 h1
  exact ⟨a, t, w, ht, he, NumL.one (hl.evalAt' hsc hlit he).2 hm⟩

/-- **The caller's layouts after the return** (`envLit_ret`): the caller's
environment at `lf`, extended by the returned words, at the walk's binding
of the result. -/
theorem RetL.envLit {fr : TermRun.Frame} {c : Ctl} {lf : List (String × LitV)} (h : RetL fr.ty c)
    (hf : FrameLit fr lf) :
    ∃ a, c.term = .ret a ∧ ∀ t ws, TermRun.evalAt c.env a = some (t, ws) →
      EnvLit ((fr.x, shapeOf fr.ty) :: lf) ((fr.x, fr.ty, ws) :: fr.env) := by
  obtain ⟨a, lc, ht, hl, hsc, hlit, hr, -, -⟩ := h
  exact ⟨a, ht, fun t ws he => envLit_ret hl hsc hlit he hr hf⟩

/-- **The caller's frame after the return**: the caller's `EnvB` at the
call's labels and memory, at the exit's (`EnvB.mono`), extended by the
returned words (`EnvB.ret`), with `MemB` at the exit's. -/
theorem RetB.frame {L : WeakMem.AllocLabel → Prop} {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {c : Ctl}
    {fr : TermRun.Frame}
    {lits : List (String × LitV)} {cs bufs : List (String × Nat)} (h : RetB L sm fr.ty c)
    (hf : EnvB lits cs bufs L sm lsize fr.env) :
    ∃ L' sm' B' a, c.term = .ret a ∧ MemB L' sm' B' ∧ ∀ t ws, TermRun.evalAt c.env a = some (t, ws) →
      EnvB ((fr.x, shapeOf fr.ty) :: lits) (unbuf fr.x cs) (unbuf fr.x bufs) L' sm' lsize
        ((fr.x, fr.ty, ws) :: fr.env) := by
  obtain ⟨L', sm', B', ⟨hL, hm⟩, hB, a, lc, ht, hs, hr⟩ := h
  exact ⟨L', sm', B', a, ht, hB, fun t ws he => EnvB.ret hs he hr (hf.mono hL hm fun _ _ => Nat.le_refl _)⟩

end Spike.Lib.LowerNode

/-- info: 'Spike.Lib.LowerNode.RetB.frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.RetB.frame

/-- info: 'Spike.Lib.LowerNode.RetL.envLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.RetL.envLit

/-- info: 'Spike.Lib.LowerNode.RetL.int' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.RetL.int
