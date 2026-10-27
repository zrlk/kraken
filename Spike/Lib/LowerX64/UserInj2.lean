/-
**Distinct `Accepted2` code blocks have distinct symbols** (x86-64): the
twin of `Spike/Lib/LowerX64/UserInj.lean` for the compiled blocks of an
`Accepted2` program (`compiled2 p`, lowered to `funcs2`), by `PlaceOK`'s
distinct labels (`labelsNodupL`) and each function's label in the code
cells, in order (`Spike.Lib.LowerX64.EmitLabels`).

- `name_funcs2`: the symbol of the `k`th user function;
- `user_inj2_of_placeOK`: a compiled block's symbol determines its index.
-/
import Spike.Lib.LowerX64.UserInj
import Spike.Lib.LowerX64.LowerProgC2X

namespace Spike.Lib.LowerX64

open Scc.Emit.X64
open CoreLang CoreTerm
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.LowerShape (func2)
open Spike.Lib.LowerNode (Pairwise2 Low2 compiled2 funcs2)

/-- The `k`th user function after the runtime's is named by its compiled
block's symbol. -/
theorem name_funcs2 {rt : List Scc.IR.Func} {p : Prog} {ws : List Low2} (hl : ws.length = (compiled2 p).length)
    {k : Nat} (hk : k < (compiled2 p).length) :
    ∃ h : rt.length + k < (rt ++ funcs2 p ws).length,
      (rt ++ funcs2 p ws)[rt.length + k].name = Scc.Lower.Names.user (compiled2 p)[k].name := by
  have hk' : k < (funcs2 p ws).length := by simp [funcs2, List.length_zipWith, hl, hk]
  refine ⟨by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_right (by omega)]
  simp [funcs2, List.getElem_zipWith, func2]

/-- **A compiled block's symbol determines it** on an `Accepted2` program
whose output passes `PlaceOK`: two compiled blocks with one `Names.user`
symbol are at one index. -/
theorem user_inj2_of_placeOK {cfg : Scc.Config} {p : Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)
    {P : Decl → Low2 → Prop} {ws : List Low2} {rt : List Scc.IR.Func} (hws : Pairwise2 P (compiled2 p) ws)
    (hir : (Scc.Lower.X64.lowerAll cfg p).low.ir = Scc.Lower.Inv.progOf cfg.layout rt (funcs2 p ws))
    {j j' : Nat} (hj : j < (compiled2 p).length) (hj' : j' < (compiled2 p).length)
    (he : Scc.Lower.Names.user (compiled2 p)[j].name = Scc.Lower.Names.user (compiled2 p)[j'].name) : j = j' := by
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
  change emitFuncs _ areas (rt ++ funcs2 p ws) 0 = _ at hf
  obtain ⟨hl, hall⟩ := emitFuncs_labels hf
  rw [hcells] at hnd
  obtain ⟨ha, hna⟩ := name_funcs2 (rt := rt) hws.1 hj
  obtain ⟨hb, hnb⟩ := name_funcs2 (rt := rt) hws.1 hj'
  have := index_inj hl (fun i hi => (hall i hi).2) (labs_blocks_nodup hnd) ha hb (by rw [hna, hnb, he])
  omega

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.user_inj2_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms user_inj2_of_placeOK

end Spike.Lib.LowerX64
