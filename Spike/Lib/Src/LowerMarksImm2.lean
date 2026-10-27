import Spike.Lib.Src.LowerMarks2
import Spike.Lib.Src.ImmIn2

/-!
# Every placement-trace point of an `Accepted2` block has its immediates

`lowerDeclMarks_immIn2`: every mark of `lowerDeclMarks` on a block `d` of an
`Accepted2` program (not the extern and its loop) is at a point where every
immediate word is the literal `imms2Of p` records (`ImmIn2`): the trace's
points are the walk's (`lowerExpr_marks`), and the walk's points have their
immediates (`immIn_imms2Of`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower

/-- The run of a block's lowering body adds only points of its walk. -/
theorem declBody_marks (cx : Scc.Lower.Ctx) (arg : String) (t : Ty) (ps : List Operand) (body : Expr)
    {s : BState} (hs : s = {}) {s' : BState}
    (h : (do markWords t ps; markAt (.block "entry") ([(arg, t, ps)], body); lowerExpr cx [(arg, t, ps)] body :
      B Unit) s = .ok ((), s')) :
    ∀ mk ∈ s'.marks, ∃ n, InW (lowerEnvs2 cx [(arg, t, ps)] n body) mk.2 := by
  subst hs
  obtain ⟨_, s1, h1, h⟩ := bind_ok_inv h
  obtain ⟨_, s2, h2, h⟩ := bind_ok_inv h
  have hc1 := kc_markWords t ps {} _ s1 rfl h1
  obtain ⟨-, hm1⟩ := hm_markWords none t ps {} _ s1 rfl h1
  obtain ⟨-, hc2, -, hm2⟩ := markAt_ok h2
  have hc2' : s2.cur.isSome = true := by rw [hc2]; exact hc1
  intro mk hk
  refine ⟨s2.next, ?_⟩
  rcases lowerExpr_marks cx body _ s2 s' hc2' h mk hk with hk | hk
  · rcases hm2 mk hk with ⟨hk, -⟩ | rfl
    · rcases hm1 mk hk with hk | hk
      · simp at hk
      · cases hk
    · exact InW.head (mem_lowerEnvs2_head _ _ _ _)
  · exact hk

theorem buildFuncMarks_ok {name : String} {params : List Reg} {cs : Bool} {body : B Unit} {f : Func}
    {marks : Array (Node × Point)} (h : buildFuncMarks name params cs body = .ok (f, marks)) :
    ∃ s', body {} = .ok ((), s') ∧ s'.marks = marks := by
  unfold buildFuncMarks at h
  rcases hb : body {} with e | ⟨⟨⟩, s'⟩ <;>
    simp [hb, StateT.run, bind, Except.bind, pure, Except.pure] at h
  exact ⟨s', rfl, h.2⟩

/-- **The lowering's trace points have their immediates** (`ImmIn2`). -/
theorem lowerDeclMarks_immIn2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {externs : List (String × Scc.Frontend.Extern)}
    (hext : ∀ d ∈ p, (externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL"))
    {obj : Scc.ObjLayout} {frames : Option Nat} {f : Func} {marks : Array (Node × Point)}
    (h : lowerDeclMarks p externs d obj frames = .ok (f, marks)) :
    ∀ mk ∈ marks, ImmIn2 (imms2Of p) mk.2.1 mk.2.2 := by
  unfold lowerDeclMarks at h
  rcases hv : Scc.Obj.valWords d.argTy with _ | n <;> simp only [hv] at h
  · cases h
  have key : ∀ name cs, buildFuncMarks name ((List.range n).map fun k => s!"{d.arg}.{k}") cs (do
      markWords d.argTy (((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)
      markAt (.block "entry") ([(d.arg, d.argTy, ((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)], d.body)
      lowerExpr { prog := p, externs, fn := d.name, obj, frames }
        [(d.arg, d.argTy, ((List.range n).map fun k => s!"{d.arg}.{k}").map .reg)] d.body) = .ok (f, marks) →
      ∀ mk ∈ marks, ImmIn2 (imms2Of p) mk.2.1 mk.2.2 := by
    intro name cs hb mk hk
    obtain ⟨s', hs', rfl⟩ := buildFuncMarks_ok hb
    obtain ⟨m, hm⟩ := declBody_marks _ _ _ _ _ rfl hs' mk hk
    obtain ⟨q, hq, he⟩ := hm
    have := immIn_imms2Of hp (cx := { prog := p, externs, fn := d.name, obj, frames }) rfl hext hd hne hnl
      (ps := ((List.range n).map fun k => s!"{d.arg}.{k}").map .reg) (fun o ho => by
        simp only [List.mem_map] at ho; obtain ⟨r, -, rfl⟩ := ho; exact ⟨r, rfl⟩)
      (by simp [hv]) m q hq
    rw [← he]; exact this
  simp only [pure, Except.pure, bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · exact key _ _ h
    · cases h

end Spike.Lib.LowerNode
