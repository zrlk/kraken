/-
**Distinct code block symbols from `PlaceOK`** (x86-64), the twin of
`Spike/Lib/LowerA64/UserInj.lean`: on a program whose output passes
`PlaceOK`, two code blocks with one symbol (`Names.user`, which is not
injective: `f'` and `f_u27_` are both `wc_f_u27_`) are one code block, so a
call names its callee exactly. Where AArch64 reads the function index off
the stack check's local label, x86-64 uses `PlaceOK`'s distinct labels
(`labelsNodupL`) and each function's label in the code cells, in order
(`Spike.Lib.LowerX64.EmitLabels`).

- `name_funcs1`: the symbol of the `k`th user function;
- `user_inj_of_placeOK`, `userInj_of_placeOK`: a code block's symbol
  determines its index (`UserInj`);
- `calleeRow_name_of_placeOK`: `calleeRow_name_of_fnPh1` without its
  `UserInj` hypothesis.
-/
import Spike.Lib.LowerX64.EmitLabels
import Spike.Lib.LowerX64.CalleeRow

namespace Spike.Lib.LowerX64

open Scc.Emit.X64
open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.NeedX64 (row?)
open Scc.Lower.Inv (Res1 func1 params1R)
open Spike.Lib.LowerShape (allInsts)
open Spike.Lib.LowerNode (Pairwise2 LowC funcs1)

/-! ## Distinct symbols -/

/-- The `k`th user function after the runtime's is named by its declaration's symbol. -/
theorem name_funcs1 {rt : List Scc.IR.Func} {p : Prog} {rs : List Res1} (hl : rs.length = p.length) {k : Nat}
    (hk : k < p.length) :
    ∃ h : rt.length + k < (rt ++ funcs1 p rs).length,
      (rt ++ funcs1 p rs)[rt.length + k].name = Scc.Lower.Names.user p[k].name := by
  have hk' : k < (funcs1 p rs).length := by simp [funcs1, List.length_zipWith, hl, hk]
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_right (by omega)]
  simp [funcs1, List.getElem_zipWith, func1]

/-- **A code block's symbol determines it** on a program whose output
passes `PlaceOK` (see the module docstring): two code blocks with one
`Names.user` symbol are at one index. -/
theorem user_inj_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j j' : Nat} (hj : j < p.length) (hj' : j' < p.length)
    (he : Scc.Lower.Names.user p[j].name = Scc.Lower.Names.user p[j'].name) : j = j' := by
  have hne : cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes ≠ [] := by
    intro h0
    have : a1 (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) ⟨Λ⟩ = false := by
      simp [X64.a1, Out.ofEmitted, h0, Scc.Sem.X64.codeLabel, Scc.Sem.labelAddr]
    rw [placeOKAt_eq_false_of_a1 this] at h
    cases h
  have hnd : (labs ((cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes).map (·.1))).Nodup := by
    cases ha : a2 (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) ⟨Λ⟩
    · rw [placeOKAt_eq_false_of_a2 ha] at h
      cases h
    · have h2 : Scc.Cert.Link.X64.labelsNodupL (Int64.ofNat Λ.code.lo)
          (cellsOfEmitted (Scc.Lower.X64.lowerAll cfg p) sizes) = true := by
        simp only [a2, Scc.Cert.Link.X64.loadOk, Scc.Cert.Link.X64.sizeOkL, Bool.and_eq_true] at ha
        exact ha.1.1.1.1.1.1.1.1.1.2
      exact labs_nodup_of_labelsNodupL h2
  obtain ⟨areas, rs', H, Z, hf, hcells⟩ := lowerAll_cells hne
  rw [hir] at hf
  change emitFuncs _ areas (rt ++ funcs1 p rs) 0 = _ at hf
  obtain ⟨hl, hall⟩ := emitFuncs_labels hf
  rw [hcells] at hnd
  obtain ⟨ha, hna⟩ := name_funcs1 (rt := rt) hrs.1 hj
  obtain ⟨hb, hnb⟩ := name_funcs1 (rt := rt) hrs.1 hj'
  have := index_inj hl (fun i hi => (hall i hi).2) (labs_blocks_nodup hnd) ha hb (by rw [hna, hnb, he])
  omega

/-- **Distinct code block symbols from `PlaceOK`**: `UserInj`, the
hypothesis of `calleeRow_name_of_fnPh1`, from `user_inj_of_placeOK`. -/
theorem userInj_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Res1 → Prop} {rs : List Res1} {rt : List Scc.IR.Func} (hrs : Pairwise2 P p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs)) :
    UserInj p :=
  fun _ _ hj hj' he => user_inj_of_placeOK h hrs hir hj hj' he

/-- **A call site's rows with the callee's name, from `PlaceOK` alone**:
`calleeRow_name_of_fnPh1` with its `UserInj` hypothesis discharged by
`userInj_of_placeOK`. -/
theorem calleeRow_name_of_placeOK {cfg : Scc.Config} {p : Prog} (hp : Scc.Lower.Accepted1 p = true)
    {sizes : List Nat} {labelOffs : List (String × Nat)} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {fo : Option Nat} {rs : List Res1} {rt : List Scc.IR.Func}
    (hrs : Pairwise2 (LowC p cfg.layout.obj fo) p rs)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs1 p rs))
    {j : Nat} {d : Decl} {r : Res1} (hd : p[j]? = some d) (hr : rs[j]? = some r)
    {ds : List Scc.IR.Reg} {g : String} {ws : List Scc.IR.Operand}
    (hg : Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r) (hgp : g ∈ p.map (·.name)) :
    let tbl := (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.need
    let ir := (Scc.Lower.X64.lowerAll cfg p).low.ir
    ∃ (j' : Nat) (dg : Decl) (rg : Res1), j' < j ∧ p[j']? = some dg ∧ rs[j']? = some rg ∧ dg.name = g ∧
      ∃ (a : String) (nd : Nat) (a' : String) (ng : Nat),
        let sd := (frOf ir (func1 (Scc.Lower.Names.user d.name) (params1R d) r)).size
        let sg := (frOf ir (func1 (Scc.Lower.Names.user dg.name) (params1R dg) rg)).size
        row? tbl (Scc.Lower.Names.user d.name) = some (a, sd + 8, nd) ∧
        row? tbl (Scc.Lower.Names.user g) = some (a', sg + 8, ng) ∧
        sd + 8 ≤ nd ∧ sg + 8 ≤ ng ∧ sd + 8 + 8 + ng ≤ nd :=
  calleeRow_name_of_fnPh1 hp (userInj_of_placeOK h hrs hir) h hrs hir hd hr hg hgp

end Spike.Lib.LowerX64
