/-
**`scc_rt_main` is one of the runtime's functions** (ISA-free): the
lowering's runtime functions (`Scc.Lower.Inv.rtFuncs`, built by `mapM`)
contain `Inv.mainThread0`, the main-thread function that calls the user
`main`. Used by `Spike/Lib/LowerX64/MainNeed.lean` and
`Spike/Lib/LowerA64/MainNeed.lean`.
-/
import Scc.Lower.InvProg

namespace Spike.Lib

/-- **An `ok` entry of a list of results is in its `mapM`**, when that succeeds. -/
theorem mem_of_mapM_ok {α : Type} : ∀ {l : List (Except String α)} {rt : List α} {x : α},
    l.mapM id = .ok rt → Except.ok x ∈ l → x ∈ rt
  | [], _, _, _, hx => by cases hx
  | y :: l, rt, x, h, hx => by
    simp only [List.mapM_cons, id] at h
    cases y with
    | error e => cases h
    | ok v =>
      cases hl : l.mapM id with
      | error e => simp [hl, bind, Except.bind] at h
      | ok vs =>
        simp only [hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with hx | hx
        · cases hx; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_of_mapM_ok hl hx)

/-- **`scc_rt_main` is one of the runtime's functions** (`rtFuncs`' second). -/
theorem mainThread0_mem {lay : Scc.Layout} {e : Scc.Frontend.Entry} {sw : Nat}
    {rt : List Scc.IR.Func} (h : Scc.Lower.Inv.rtFuncs lay e sw = .ok rt) :
    Scc.Lower.Inv.mainThread0 e sw ∈ rt := by
  unfold Scc.Lower.Inv.rtFuncs at h
  refine mem_of_mapM_ok h ?_
  rw [← Scc.Lower.Inv.mainThreadF_eq]
  simp

end Spike.Lib
