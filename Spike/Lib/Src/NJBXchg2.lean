import Spike.Lib.Src.NJLB
import Spike.Lib.Src.HeapLit

/-!
**The node invariant past a lane store** (ISA-neutral). `let x = xchgAt b i
v` is not a local step: the source reads the cell's word `w'` (a hold) and
stores `v`'s. The node after it binds `x` to `w'` at the walk's layout
`.leaf none` (`opLit`), represented by the register `d` the lowering loads
the cell into.

The buffers' memory `sm` of `NJB` is a ghost (the facts on the real memory
are the memory side's), so it stays: `EnvB`, `MemB` at the same `L`, `sm`,
`B`. The held word is a number below `2^64` (`IsNum`, the memory side's
reads at an `elem2` buffer).

- `NodeJ.xchg2`, `NodeJE.xchg2`: the node part of `NJB.xchg2` (`NJB`'s is
  `NodeJE`, the types up to a buffer's literal lengths).
- `NJB.xchg2`: from the node's parts at the `let` (after the local run to
  the exchange site) to `NJB` at `e` with `x` bound to `w'` in `d`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv WordsRep)
open Scc.Sem (ValRep)
open Scc.Lower (LitV csAfter bufsAfter elem2)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
  {lits : List (String × LitV)} {cs bufs : List (String × Nat)} {L : WeakMem.AllocLabel → Prop}
  {sm : WeakMem.Memory} {lsize : WeakMem.AllocLabel → Nat} {B : Nat}

/-- **`let x = xchgAt b i v`, the node part**: `NodeJ` at the exchange site
`c1`, the held word `w'` represented by `r` (`hr`), which the slot `k` of
the register `d` takes (`upd sl k r`, no other binding's operand at `k`,
`hfr`). Then `NodeJ` at `e` with `x` bound to `w'`. -/
theorem NodeJ.xchg2 {x : String} {bv i v : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c1 : Ctl}
    {u : Ty} {w' : TermRun.Word}
    (hj : NodeJ lbl rs (.let_ x (.xchgAt bv i v) e) s sl c1)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {r : BitVec 64} (hr : ValRep lbl w'.val r.toNat) :
    NodeJ lbl rs e ((x, u, [.one (.reg d)]) :: s) (upd sl k r) ⟨e, (x, u, [w']) :: c1.env, none⟩ := by
  have hwr : WordsRep lbl (opdVal rs (upd sl k r)) [w'] [.one (.reg d)] := by
    refine ⟨⟨r.toNat, ?_, hr⟩, trivial⟩
    simp [opdVal, hd, upd_apply]
  have hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs (upd sl k r) o = opdVal rs sl o :=
    fun q hq pl hpl o ho => Spike.Lib.Form.opdVal_upd fun r' k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r' k' hor hr']
  exact ⟨rfl, rfl, (hj.2.2.congr hsl).bind x u hwr⟩

/-- **`let x = xchgAt b i v`, the node part** (`NodeJ.xchg2` at
`NodeJE`). -/
theorem NodeJE.xchg2 {x : String} {bv i v : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c1 : Ctl}
    {u : Ty} {w' : TermRun.Word}
    (hj : NodeJE lbl rs (.let_ x (.xchgAt bv i v) e) s sl c1)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {r : BitVec 64} (hr : ValRep lbl w'.val r.toNat) :
    NodeJE lbl rs e ((x, u, [.one (.reg d)]) :: s) (upd sl k r) ⟨e, (x, u, [w']) :: c1.env, none⟩ := by
  have hwr : WordsRep lbl (opdVal rs (upd sl k r)) [w'] [.one (.reg d)] := by
    refine ⟨⟨r.toNat, ?_, hr⟩, trivial⟩
    simp [opdVal, hd, upd_apply]
  have hsl : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, opdVal rs (upd sl k r) o = opdVal rs sl o :=
    fun q hq pl hpl o ho => Spike.Lib.Form.opdVal_upd fun r' k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r' k' hor hr']
  exact ⟨rfl, rfl, (hj.2.2.congr hsl).bind x rfl hwr⟩

/-- **`let x = xchgAt b i v`**: the node's parts at the exchange site `c1`
(`NodeJE`, `EnvLit`, `EnvB`, `MemB`, `EnvSmall`), the held word `w'` a number (`hw`) of
the element type `u` (`elem2`), represented by `r` (`hr`), which the slot
`k` of the register `d` takes (`upd sl k r`, no other binding's operand at
`k`, `hfr`). Then `NJB` at `e` with `x` bound to `w'`, the walk's next
state. -/
theorem NJB.xchg2 {x : String} {bv i v : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c1 : Ctl}
    {u : Ty} {w' : TermRun.Word}
    (hj : NodeJE lbl rs (.let_ x (.xchgAt bv i v) e) s sl c1) (hn : EnvLit lits c1.env)
    (hb : EnvB lits cs bufs L sm lsize c1.env) (hm : MemB L sm B) (hS : EnvSmall c1.env) (hu : elem2 u = true)
    (hw : IsNum w')
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {r : BitVec 64} (hr : ValRep lbl w'.val r.toNat) :
    NJB p lbl rs ((x, .leaf none) :: lits) (csAfter x cs (.xchgAt bv i v)) (bufsAfter x cs bufs (.xchgAt bv i v))
      L sm lsize B e ((x, u, [.one (.reg d)]) :: s) (upd sl k r) ⟨e, (x, u, [w']) :: c1.env, none⟩ :=
  ⟨_, .refl _, NodeJE.xchg2 hj hd hfr hr, envLit_xchgAt hn hu hw,
    hb.cons (SliceL.leaf _ _) (by rintro _ (h | h) <;> cases h) (by intro _ _ h; cases h), hm,
    EnvSmall.cons hS (WordsSmall.isNum hw)⟩

end Spike.Lib.LowerNode
