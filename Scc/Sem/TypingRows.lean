/-
**Typing facts in the form the code-emitting rows consume** (`Scc/DESIGN.md`
§10). The per-construct rows work on a source thread's control (its term and
environment, one frame, no type arguments), not on a whole thread, and they
are stated for every pair of an invariant, with no reachability; the typing
reaches them as a guard on the control at each instruction, discharged by
the global proof from the reachable source configuration related to the
target.

- `TypedAt p σs t env`: `ThreadTyped` of the control `(t, env)` with type
  arguments `σs` (`threadTyped_iff`, `ThreadTyped.typedAt`); the
  defined-operand facts on it (`TypedAt.add_num`, `ifeq_num`, `parity_num`,
  `ifnull_def`).
- *Checked `+`, fall-through*: `valRep_addW` (the target's sum, when it does
  not carry, represents the source's `addW`), `small_addW`; *saturating
  `-`*: `valRep_subW` (truncated subtraction on both sides, no typing
  needed), `small_subW`. A result some word represents is small, so the
  binding keeps `NoBigNumT` (`NoBigNumT.push`).
- *Checked `+`, abort edge*: `TypedAt.carry_nums`: in a typed control, two
  words representing target values whose sum carries are numbers whose sum
  is at least `2^64` (the numeric part of `Spike.Lib.OvfReady`).
- *Tests*: `valRep_num` (a number's representative is the number: `ifeq`
  and `parity` decide alike on both sides), `TypedAt.ifnull_iff` (`null` is
  exactly the word `0`, when every placed label's base is positive:
  `MemRel.lbl_pos`, `MemRelP.lbl_pos`, `Components.lbl_pos` from
  `Layout.WF.pos`).
- *Transport*: `transfer_typedAt`: at each reachable target configuration,
  the related source (a `CoreProj` source from `main`'s start, for a program
  passing `SrcChecks`) has every thread with no type arguments `TypedAt` at
  its control.
-/
import Scc.Sem.Typing
import Scc.Sem.SrcProj
import Scc.Sem.MemRelP

namespace Scc.Sem

open CoreLang CoreTerm CoreTyping TermRun TermSound

/-! ## Typed controls -/

/-- **A typed control**: `ThreadTyped` of the thread with term `t`,
environment `env` and type arguments `σs` (the rest of a thread plays no
part in it). -/
def TypedAt (p : Prog) (σs : List Ty) (t : Expr) (env : TermRun.Env) : Prop :=
  ThreadTyped p { term := t, env := env, σs := σs }

/-- `ThreadTyped` is `TypedAt` of the thread's control. -/
theorem threadTyped_iff {p : Prog} {th : TermRun.TTh} : ThreadTyped p th ↔ TypedAt p th.σs th.term th.env :=
  Iff.rfl

theorem ThreadTyped.typedAt {p : Prog} {th : TermRun.TTh} (h : ThreadTyped p th) :
    TypedAt p th.σs th.term th.env :=
  h

namespace TypedAt

variable {p : Prog} {σs : List Ty} {t : Expr} {env : TermRun.Env}

/-- `ThreadTyped.add_num` on a control. -/
theorem add_num (h : TypedAt p σs t env) {x : String} {a b : At} {e : Expr} (ht : t = .let_ x (.add a b) e)
    {c : At} (hc : c = a ∨ c = b) {rt : Ty} {w : TermRun.Word} (he : evalAt env c = some (rt, [w])) :
    ∃ n, w.val = .num n :=
  ThreadTyped.add_num h ht hc he

/-- `ThreadTyped.ifeq_num` on a control. -/
theorem ifeq_num (h : TypedAt p σs t env) {a b : At} {yes no : Expr} (ht : t = .ifeq a b yes no)
    {c : At} (hc : c = a ∨ c = b) {rt : Ty} {w : TermRun.Word} (he : evalAt env c = some (rt, [w])) :
    (∃ n, w.val = .num n) ∨ ∃ l, w.val = .loc ⟨l, 0⟩ 0 :=
  ThreadTyped.ifeq_num h ht hc he

/-- `ThreadTyped.parity_num` on a control. -/
theorem parity_num (h : TypedAt p σs t env) {a : At} {k : String} {ev od : Expr} (ht : t = .parity a k ev od)
    {rt : Ty} {w : TermRun.Word} (he : evalAt env a = some (rt, [w])) : ∃ n, w.val = .num n :=
  ThreadTyped.parity_num h ht he

/-- `ThreadTyped.ifnull_def` on a control. -/
theorem ifnull_def (h : TypedAt p σs t env) {a : At} {y : String} {e₁ e₂ : Expr} (ht : t = .ifnull a e₁ y e₂)
    {rt : Ty} {w : TermRun.Word} (he : evalAt env a = some (rt, [w])) :
    w.val = .null ∨ ∃ l g, w.val = .loc l g :=
  ThreadTyped.ifnull_def h ht he

end TypedAt

/-! ## Arithmetic -/

variable {lbl : WeakMem.AllocLabel → Option Nat}

/-- **A number's representative is the number.** -/
theorem valRep_num {n v : Nat} (h : ValRep lbl (.num n) v) : v = n := h.2

/-- **The checked `+`, fall-through**: when the target's sum of the
representatives does not carry, it represents the source's `addW` (an
operand that is not a number makes the result `undef`, which every word
represents). -/
theorem valRep_addW {wa wb : TermRun.Word} {va vb : Nat} (ha : ValRep lbl wa.val va) (hb : ValRep lbl wb.val vb)
    (hlt : va + vb < 2 ^ 64) : ValRep lbl (addW wa wb).val (va + vb) := by
  unfold addW
  split
  · rename_i n m hn hm
    rw [hn] at ha; rw [hm] at hb
    obtain ⟨-, rfl⟩ := ha; obtain ⟨-, rfl⟩ := hb
    exact ⟨hlt, rfl⟩
  · trivial

/-- **The saturating `-`**: the target's truncated difference of the
representatives represents the source's `subW` (truncated as well). -/
theorem valRep_subW {wa wb : TermRun.Word} {va vb : Nat} (ha : ValRep lbl wa.val va) (hb : ValRep lbl wb.val vb) :
    ValRep lbl (subW wa wb).val (va - vb) := by
  unfold subW
  split
  · rename_i n m hn hm
    rw [hn] at ha; rw [hm] at hb
    obtain ⟨hn', rfl⟩ := ha; obtain ⟨-, rfl⟩ := hb
    exact ⟨by omega, rfl⟩
  · trivial

/-- The fall-through result of the checked `+` is small. -/
theorem small_addW {wa wb : TermRun.Word} {va vb : Nat} (ha : ValRep lbl wa.val va) (hb : ValRep lbl wb.val vb)
    (hlt : va + vb < 2 ^ 64) : Small (addW wa wb) :=
  small_of_valRep (valRep_addW ha hb hlt)

/-- The result of the saturating `-` is small. -/
theorem small_subW {wa wb : TermRun.Word} {va vb : Nat} (ha : ValRep lbl wa.val va) (hb : ValRep lbl wb.val vb) :
    Small (subW wa wb) :=
  small_of_valRep (valRep_subW ha hb)

/-- **The checked `+`, abort edge**: in a typed control at
`let x = a + b in e`, operand words representing target values whose sum
carries are numbers whose sum is at least `2^64`. -/
theorem TypedAt.carry_nums {p : Prog} {σs : List Ty} {t : Expr} {env : TermRun.Env} (h : TypedAt p σs t env)
    {x : String} {a b : At} {e : Expr} (ht : t = .let_ x (.add a b) e) {ta tb : Ty} {wa wb : TermRun.Word}
    (hea : evalAt env a = some (ta, [wa])) (heb : evalAt env b = some (tb, [wb])) {va vb : Nat}
    (ha : ValRep lbl wa.val va) (hb : ValRep lbl wb.val vb) (hc : 2 ^ 64 ≤ va + vb) :
    ∃ n m, wa.val = .num n ∧ wb.val = .num m ∧ 2 ^ 64 ≤ n + m := by
  obtain ⟨n, hn⟩ := h.add_num ht (.inl rfl) hea
  obtain ⟨m, hm⟩ := h.add_num ht (.inr rfl) heb
  rw [hn] at ha; rw [hm] at hb
  refine ⟨n, m, hn, hm, ?_⟩
  rw [← valRep_num ha, ← valRep_num hb]; exact hc

/-! ## Tests -/

/-- **`ifnull` decides alike on both sides**: in a typed control at an
`ifnull` test, the tested word is `null` exactly when its representative
is `0`, when every placed label's base is positive. -/
theorem TypedAt.ifnull_iff {p : Prog} {σs : List Ty} {t : Expr} {env : TermRun.Env} (h : TypedAt p σs t env)
    {a : At} {y : String} {e₁ e₂ : Expr} (ht : t = .ifnull a e₁ y e₂) {rt : Ty} {w : TermRun.Word}
    (he : evalAt env a = some (rt, [w])) (hpos : ∀ l b, lbl l = some b → 0 < b) {v : Nat}
    (hv : ValRep lbl w.val v) : w.val = .null ↔ v = 0 := by
  rcases h.ifnull_def ht he with hn | ⟨l, g, hl⟩
  · rw [hn] at hv; exact ⟨fun _ => hv, fun _ => hn⟩
  · rw [hl] at hv
    obtain ⟨-, x, hx, rfl⟩ := hv
    simp only [wordAddr, Option.map_eq_some_iff] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    have := hpos _ _ hb
    rw [hl]
    exact ⟨fun h => (by cases h), fun h => (by omega)⟩

/-- **Placed bases are positive** under the memory relation and a
well-formed layout (`Layout.WF.pos`): the side condition of `ifnull_iff`. -/
theorem MemRel.lbl_pos {Λ : Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {pairs : List Nat} (h : MemRel Λ lbl lsize ts tm sm pairs)
    (hwf : Λ.WF) : ∀ l b, lbl l = some b → 0 < b :=
  fun l b hl => by
    rcases (h.lbl_range l b hl).2 with hs | hs | ⟨-, hs⟩
    · exact hwf.lo_pos (.inl hs)
    · exact hwf.lo_pos (.inr hs)
    · exact Nat.lt_of_lt_of_le (hwf.pos Λ.pinned (by simp [Layout.regions])) hs.1

/-- `MemRel.lbl_pos` under the memory relation with promises. -/
theorem MemRelP.lbl_pos {Λ : Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat}
    {tm : Kraken.Promising.Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF) : ∀ l b, lbl l = some b → 0 < b :=
  fun l b hl => by
    rcases (h.lbl_range l b hl).2 with hs | hs | ⟨-, hs⟩
    · exact hwf.lo_pos (.inl hs)
    · exact hwf.lo_pos (.inr hs)
    · exact Nat.lt_of_lt_of_le (hwf.pos Λ.pinned (by simp [Layout.regions])) hs.1

/-- `MemRel.lbl_pos` under the components of `R`. -/
theorem Components.lbl_pos {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg}
    (h : Components M Λ w t s) (hwf : Λ.WF) : ∀ l b, w.lbl l = some b → 0 < b :=
  fun l b hl => by
    rcases (h.lbl_range l b hl).2 with hs | hs | ⟨-, hs⟩
    · exact hwf.lo_pos (.inl hs)
    · exact hwf.lo_pos (.inr hs)
    · exact Nat.lt_of_lt_of_le (hwf.pos Λ.pinned (by simp [Layout.regions])) hs.1

/-! ## Transport -/

section Transport

open Scc.Sem.SrcProj Scc.Sem.SrcStart

variable {T : Target} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : T.Asm}

/-- **Typed controls at the target**: each reachable target configuration is
related to a source configuration every thread of whose core with no type
arguments is `TypedAt` at its control (the guard of the per-construct rows),
for a `CoreProj` source started at `main` and a program passing
`SrcChecks`. -/
theorem transfer_typedAt (h : Sim T S Λ B asm) {p : Prog} {r : Ty} (hp : SrcChecks p r) {arch : WeakMem.Arch}
    {cap : Nat} (hP : CoreProj S p Promises.Knobs.all arch cap (SrcSem.mainInit cap))
    {t0 t : T.M.Cfg} {tr : List Ev} (h0 : T.load asm Λ = some t0) (hr : T.M.Run (T.marks asm Λ) t0 tr t) :
    ∃ s, h.R t s ∧ (∀ (i : Nat) (th : TermRun.TTh), (S.core s).ths[i]? = some th → th.σs = [] → TypedAt p [] th.term th.env) ∧
      ∃ w : Witness T.M, Components T.M Λ w t (S.core s) := by
  obtain ⟨s, hR, hty, hw⟩ := transfer_typed h hp hP h0 hr
  exact ⟨s, hR, fun i th hi hσ => hσ ▸ (hty i th hi).typedAt, hw⟩

end Transport

/-! ## Tests -/

-- A carry-free sum of two numbers is represented by the target's sum.
example : ValRep (fun _ => none) (addW (cst (.num 3)) (cst (.num 4))).val 7 :=
  valRep_addW (va := 3) (vb := 4) ⟨by decide, rfl⟩ ⟨by decide, rfl⟩ (by decide)

-- An `undef` operand: any target word represents the result.
example (v : Nat) : ValRep (fun _ => none) (addW (cst .undef) (cst (.num 4))).val v := by
  simp [addW, cst, Promises.TVal.mk0, ValRep]

-- The saturating `-` floors at `0` on both sides.
example : ValRep (fun _ => none) (subW (cst (.num 3)) (cst (.num 4))).val 0 :=
  valRep_subW (va := 3) (vb := 4) ⟨by decide, rfl⟩ ⟨by decide, rfl⟩

/-- Every thread of a configuration `SrcStart`'s test source reaches with no
type arguments is typed at its control. -/
theorem typedAt_test {tr : List Ev} {s : TermRun.Cfg} (hs : (SrcSem.source SrcStart.testP [SrcStart.mainD]).Reach tr s)
    {i : Nat} {th : TermRun.TTh} (hi : s.ths[i]? = some th) :
    TypedAt [SrcStart.mainD] th.σs th.term th.env :=
  (SrcProj.srcTyped_test tr s hs i th hi).typedAt

end Scc.Sem
