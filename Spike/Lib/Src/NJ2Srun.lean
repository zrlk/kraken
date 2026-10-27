import Spike.Lib.Src.NJ2

/-!
**The code-free forms under `NJ'`** (ISA-neutral): each of `sstep`'s `let`
forms moves the node invariant with locatives past it, the bound variable at
the placements `sstep` gives it.

- `NJ'.nameI`, `NJ'.pair`, `NJ'.pack`, `NJ'.packT`, `NJ'.asLanes` (of a
  literal below `2^64`); `NJ'.atom` is in `NJ2`;
- `close_nil`: closing over no types is the identity.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)

/-- **Closing over no types** is the identity. -/
theorem close_nil (τ : Ty) : TermRun.close [] τ = τ := TermStep.substTs_nil' τ 0 0

section NJ'

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **`let x = nameI a` emits nothing**: `x` bound to `a`'s placements. -/
theorem NJ'.nameI {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJ' p lbl rs (.let_ x (.nameI a) e) s sl c) (ha : sevalAt s a = some (t, pls)) :
    NJ' p lbl rs e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_nameI hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons_evalAt ha he x⟩

/-- **`let x = (a, b)` emits nothing**: `x` bound to the concatenated
placements (a product is not numeric). -/
theorem NJ'.pair {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t u : Ty}
    {pa pb : List WordPl} (h : NJ' p lbl rs (.let_ x (.pair a b) e) s sl c) (ha : sevalAt s a = some (t, pa))
    (hb : sevalAt s b = some (u, pb)) : NJ' p lbl rs e ((x, .prod t u, pa ++ pb) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨us, he', hw'⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  obtain ⟨hr2, hj2⟩ :=
    hj.step (Spike.Lib.Form.localStep_pair hj.1 he he') (hw.append hw') (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons_of_not rfl _⟩

/-- **`let x = pack a at w : τ` emits nothing**: `x` bound at `τ` to `a`'s
placements; `τ` not numeric (a package type is not). -/
theorem NJ'.pack {x w : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t τ : Ty}
    {pls : List WordPl} (h : NJ' p lbl rs (.let_ x (.pack a w τ) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hτ : numTy τ = false) : NJ' p lbl rs e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_pack (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons_of_not hτ _⟩

/-- **`let x = packT a σ τ` emits nothing**, as `pack`. -/
theorem NJ'.packT {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t σ τ : Ty}
    {pls : List WordPl} (h : NJ' p lbl rs (.let_ x (.packT a σ τ) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hτ : numTy τ = false) : NJ' p lbl rs e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_packT (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons_of_not hτ _⟩

/-- **`let x = asLanes sg w n` of a literal below `2^64` emits nothing**:
`x` bound to the immediate `n` (a number below `2^64`). -/
theorem NJ'.asLanes {x : String} {sg : Bool} {w : Wd} {n : Nat} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c : Ctl} (h : NJ' p lbl rs (.let_ x (.asLanes sg w (.lit n)) e) s sl c) (hn : n < 2 ^ 64) :
    NJ' p lbl rs e ((x, .lanes sg w, [.one (.imm (UInt64.ofNat n))]) :: s) sl c := by
  obtain ⟨c1, hr, hj, hnum⟩ := h
  have hst := Spike.Lib.Form.localStep_asLanes (p := p) (n := n) hj.1 rfl
    (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0])
  have hw : WordsRep lbl (opdVal rs sl) [TermRun.cst (.num (n % TermRun.W64))] [.one (.imm (UInt64.ofNat n))] := by
    refine ⟨⟨n, ?_, ?_⟩, trivial⟩
    · rw [Spike.Lib.Form.opdVal_imm]; simp [Nat.mod_eq_of_lt hn]
    · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  refine ⟨_, hr.trans hr2, hj2, hnum.cons fun _ => ?_⟩
  simp only [List.mem_singleton, forall_eq]
  exact ⟨n % TermRun.W64, by simp [TermRun.cst, Promises.TVal.mk0],
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn⟩

end NJ'

end Spike.Lib.LowerNode
