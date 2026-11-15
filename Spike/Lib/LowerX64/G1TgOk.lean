/-
**The branch-target check passes on every `Accepted2` program** (x86-64):
`tgOkB` on scc's x86-64 code cells (`Spike/Lib/LowerX64/UserTgt.lean`), at
every configuration, assembled size table and label offset table, without
deciding it on the program, from the user functions' segments
(`UserPartStmt`).

Where the cells are empty the check passes trivially. Otherwise they are
the header's directives, the runtime functions', the user functions', then
a tail starting with a label (`lowerAll_parts`, the runtime's data names
being no user labels: `runtimeData_noWcL`). The header and the runtime
functions hold no user label (`rtFunc_noWcL`), so their indices pass
(`tgInvAt_prefix`); each user function's directives form a `UserPart`
(`UserPartStmt`) and the tail holds no user label, so the cells have the
local invariant `TgInv` (`tgInv_of_parts`) and pass the check
(`tgOkB_of_tgInv`).

- `emitFuncs_mem`, `emitFuncs_append`: `emitFuncs`'s results, each from a
  function's `emitFuncAt`, split along the function list;
- `abortMsg_noWcL`, `runtimeData_noWcL`: the runtime's data names are no
  user labels;
- `tgOkB_accepted2`: the statement (`TgOkBStmt`'s body), from
  `UserPartStmt`.
-/
import Spike.Lib.LowerX64.G1TgRt
import Spike.Lib.LowerX64.G1TgEmit
import Spike.Lib.LowerX64.G1TgUserStmt

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64

/-! ## `emitFuncs` -/

/-- **Each of `emitFuncs`'s results is a function's `emitFuncAt`.** -/
theorem emitFuncs_mem {p : Scc.IR.Program} {areas : List (Scc.IR.Sym × Nat)} :
    ∀ {fs : List Scc.IR.Func} {n : Nat} {rs : List (List Item × List Map)}, emitFuncs p areas fs n = .ok rs →
      ∀ r ∈ rs, ∃ f ∈ fs, ∃ m k, emitFuncAt p areas f m = .ok (r.1, k, r.2)
  | [], n, rs, h => by
    cases h
    intro r hr
    simp at hr
  | f :: fs, n, rs, h => by
    unfold emitFuncs at h
    cases h1 : emitFuncAt p areas f n with
    | error e => rw [h1] at h; cases h
    | ok r =>
      obtain ⟨items, n', ms⟩ := r
      rw [h1] at h
      change (emitFuncs p areas fs n' >>= fun rest => pure ((items, ms) :: rest)) = Except.ok rs at h
      cases h2 : emitFuncs p areas fs n' with
      | error e => rw [h2] at h; cases h
      | ok rest =>
        rw [h2] at h
        cases h
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨f, List.mem_cons_self .., n, n', h1⟩
        · obtain ⟨g, hg, m, k, hk⟩ := emitFuncs_mem h2 r hr
          exact ⟨g, List.mem_cons_of_mem _ hg, m, k, hk⟩

/-- **`emitFuncs` along an appended function list**: the first list's
results, then the second's. -/
theorem emitFuncs_append {p : Scc.IR.Program} {areas : List (Scc.IR.Sym × Nat)} :
    ∀ {fs gs : List Scc.IR.Func} {n : Nat} {rs : List (List Item × List Map)},
      emitFuncs p areas (fs ++ gs) n = .ok rs →
      ∃ rs1 rs2 n', rs = rs1 ++ rs2 ∧ emitFuncs p areas fs n = .ok rs1 ∧ emitFuncs p areas gs n' = .ok rs2
  | [], gs, n, rs, h => ⟨[], rs, n, rfl, rfl, h⟩
  | f :: fs, gs, n, rs, h => by
    rw [List.cons_append] at h
    unfold emitFuncs at h
    cases h1 : emitFuncAt p areas f n with
    | error e => rw [h1] at h; cases h
    | ok r =>
      obtain ⟨items, n', ms⟩ := r
      rw [h1] at h
      change (emitFuncs p areas (fs ++ gs) n' >>= fun rest => pure ((items, ms) :: rest)) = Except.ok rs at h
      cases h2 : emitFuncs p areas (fs ++ gs) n' with
      | error e => rw [h2] at h; cases h
      | ok rest =>
        rw [h2] at h
        cases h
        obtain ⟨rs1, rs2, n'', rfl, h3, h4⟩ := emitFuncs_append h2
        refine ⟨(items, ms) :: rs1, rs2, n'', rfl, ?_, h4⟩
        unfold emitFuncs
        rw [h1]
        change (emitFuncs p areas fs n' >>= fun rest => pure ((items, ms) :: rest)) = _
        rw [h3]
        rfl

/-! ## The runtime's data -/

/-- An abort message's name is no user label. -/
theorem abortMsg_noWcL (k : Scc.IR.AbortKind) : ¬ WcL (Scc.Lower.Names.abortMsg k) := by
  rw [show Scc.Lower.Names.abortMsg k = "scc_rt_" ++ ("msg" ++ toString k.code) by
    simp only [Scc.Lower.Names.abortMsg]; rfl]
  exact not_wcL_rt _

/-- **The runtime's data names are no user labels** (`scc_rt_` names). -/
theorem runtimeData_noWcL (lay : Scc.Layout) : ∀ d ∈ Scc.Lower.Runtime.data lay, ¬ WcL d.name := by
  intro d hd
  simp only [Scc.Lower.Runtime.data, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hd
  rcases hd with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k, -, rfl⟩
  all_goals dsimp only
  all_goals first | decide | exact abortMsg_noWcL _

/-! ## The check -/

/-- **The branch-target check passes on scc's x86-64 output of every
`Accepted2` program**, at every configuration, assembled size table and
label offset table (`TgOkBStmt`'s body), given that each user function's
code is a user function's segment (`UserPartStmt`). -/
theorem tgOkB_accepted2 (HU : UserPartStmt) :
    ∀ (cfg : Scc.Config) (p : CoreTerm.Prog) (sizes : List Nat) (labelOffs : List (String × Nat)),
      Scc.Lower.Accepted2 p = true →
      tgOkB (Scc.Cert.PlaceOK.Out.prog
        (Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)) = true := by
  intro cfg p sizes labelOffs hp
  show tgOkB (Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes) = true
  by_cases hne : Scc.Cert.PlaceOK.X64.cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes = []
  · rw [hne]; rfl
  cases hl : Scc.Lower.X64.lowerAll? cfg p with
  | error err =>
    exfalso
    apply hne
    have : Scc.Lower.X64.lowerAll cfg p = default := by unfold Scc.Lower.X64.lowerAll; rw [hl]
    rw [this]
    rfl
  | ok e =>
    obtain ⟨ws, rt, hws, hrt, -, hir, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_x64 cfg hp hl
    have hd : ∀ d ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.data, ¬ WcL d.name := by
      rw [hir]; exact runtimeData_noWcL _
    obtain ⟨areas, rs, H, Tl, hf, hcells, hH, hTl, L, hL⟩ := lowerAll_parts hne hd
    rw [hir] at hf
    obtain ⟨rs1, rs2, n', rfl, h1, h2⟩ := emitFuncs_append (fs := rt) hf
    apply tgOkB_of_tgInv
    rw [hcells]
    have hprog : H ++ ((rs1 ++ rs2).map (fun (r : List Item × List Map) => dOf r.1) ++ [Tl]).flatten =
        (H ++ (rs1.map fun (r : List Item × List Map) => dOf r.1).flatten) ++
          (rs2.map (fun (r : List Item × List Map) => dOf r.1) ++ [Tl]).flatten := by
      simp only [List.map_append, List.flatten_append, List.append_assoc]
    -- the user functions' segments
    have hU : ∀ r ∈ rs2, UserPart (dOf r.1) := by
      intro r hr
      obtain ⟨f, hf2, m, k, hk⟩ := emitFuncs_mem h2 r hr
      exact HU cfg p ws rt hp hws hrt f hf2 areas m _ hk
    refine tgInv_of_parts _ (H ++ (rs1.map fun (r : List Item × List Map) => dOf r.1).flatten)
      (rs2.map (fun (r : List Item × List Map) => dOf r.1) ++ [Tl]) hprog ?_ ?_ ?_
    · -- the header and the runtime functions: no user label
      refine tgInvAt_prefix (fun L' hL' => ?_) hprog
      rcases List.mem_append.mp hL' with hL' | hL'
      · exact hH L' hL'
      · obtain ⟨ds, hds, hL'⟩ := List.mem_flatten.mp hL'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hds
        obtain ⟨f, hf1, m, k, hk⟩ := emitFuncs_mem h1 r hr
        exact rtFunc_noWcL hrt hf1 hk L' hL'
    · -- each part
      intro Q hQ
      rcases List.mem_append.mp hQ with hQ | hQ
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hQ
        exact .inr (hU r hr)
      · rw [List.mem_singleton.mp hQ]
        exact .inl hTl
    · -- each part starts with a label
      intro Q hQ d hd
      rcases List.mem_append.mp hQ with hQ | hQ
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hQ
        obtain ⟨name, P', hP, -⟩ := hU r hr
        rw [hP] at hd
        cases hd
        rfl
      · rw [List.mem_singleton.mp hQ, hL] at hd
        cases hd
        rfl

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.runtimeData_noWcL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.runtimeData_noWcL

/-- info: 'Spike.Lib.LowerX64.tgOkB_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.tgOkB_accepted2
