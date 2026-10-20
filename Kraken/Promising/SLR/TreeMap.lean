/-
The erasure WPs of a mapped event tree (ISA-generic).

The ISA adapters (`AArch64.exec`, `X64.exec`) map the machine state into the
thread state last (`EvTree.map`), so an instruction rule over
`EvTree.EraseWP`/`EvTree.EraseWPR` meets a mapped tree. These lemmas move the
map into the postcondition.

## Contents

- `EvTree.eraseWP_map`: for `EvTree.EraseWP`. The same statement and proof
  as the original design's copy in `SLR/AArch64Bridge.lean`, here without the AArch64
  imports so that the x64 bridge (`SLR/X64Bridge.lean`) can use it (the two
  ISAs' syntax modules cannot be imported together). On merging, the
  AArch64 bridge should import this file and drop its copy.
- `EvTree.eraseWPR_map`: for the bounded-reach WP `EvTree.EraseWPR`
  (`SLR/ReachRules.lean`), as needed by `ThreadRuleR.wp`.
-/
import Kraken.Promising.SLR.ReachRules

namespace Kraken.Promising.SLR

/-- **The erasure WP of a mapped tree** is the tree's, with the postcondition
precomposed (the ISA adapters map the machine state into the thread state
last). -/
theorem _root_.Kraken.Promising.EvTree.eraseWP_map {I : ISA} {A : Arch} {tid : Nat} {iv : InstrViews}
    {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {σ τ : Type} (f : σ → τ)
    (Post : τ → Res → Ghost → Ctx → Prop) :
    ∀ (tr : EvTree σ) (r : Res) (g : Ghost) (cx : Ctx),
      (tr.map f).EraseWP A tid iv rF T c t Post r g cx ↔ tr.EraseWP A tid iv rF T c t (fun s => Post (f s)) r g cx
  | .done _, _, _, _ => Iff.rfl
  | .fault _, _, _, _ => Iff.rfl
  | .choose _ k, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWP]
    exact forall_congr' fun i => EvTree.eraseWP_map f Post (k i) r g cx
  | .load _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWP]
    exact forall_congr' fun x => imp_congr_right fun _ => EvTree.eraseWP_map f Post (ret _) r g _
  | .store _ _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWP]
    refine and_congr ?_ (imp_congr_right fun _ => EvTree.eraseWP_map f Post (ret false) r g _)
    refine forall_congr' fun cx' => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact exists_congr fun r' => exists_congr fun g' => and_congr_right fun _ =>
      EvTree.eraseWP_map f Post (ret true) r' g' cx'
  | .fence _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWP]
    exact EvTree.eraseWP_map f Post (ret ()) r g _
  | .rmw _ _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWP]
    refine forall_congr' fun x => imp_congr_right fun _ => and_congr
      (imp_congr_right fun _ => EvTree.eraseWP_map f Post (ret _) r g _) ?_
    refine forall_congr' fun new => imp_congr_right fun _ => forall_congr' fun cx' =>
      imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact exists_congr fun r' => exists_congr fun g' => and_congr_right fun _ =>
      EvTree.eraseWP_map f Post (ret _) r' g' _

/-- **The erasure WP with bounded reach of a mapped tree** is the tree's,
with the postcondition precomposed. -/
theorem _root_.Kraken.Promising.EvTree.eraseWPR_map {I : ISA} {A : Arch} {tid : Nat} {iv : InstrViews}
    {rF : Nat → Res} {T : Nat → Prop} {c : Config I} {t : Thread I} {σ τ : Type} (f : σ → τ)
    (Post : τ → Res → Ghost → Ctx → Prop) :
    ∀ (tr : EvTree σ) (r : Res) (g : Ghost) (cx : Ctx),
      (tr.map f).EraseWPR A tid iv rF T c t Post r g cx ↔ tr.EraseWPR A tid iv rF T c t (fun s => Post (f s)) r g cx
  | .done _, _, _, _ => Iff.rfl
  | .fault _, _, _, _ => Iff.rfl
  | .choose _ k, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWPR]
    exact forall_congr' fun i => EvTree.eraseWPR_map f Post (k i) r g cx
  | .load _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWPR]
    exact forall_congr' fun x => imp_congr_right fun _ => EvTree.eraseWPR_map f Post (ret _) r g _
  | .store _ _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWPR]
    refine and_congr ?_ (imp_congr_right fun _ => EvTree.eraseWPR_map f Post (ret false) r g _)
    refine forall_congr' fun cx' => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ =>
      imp_congr_right fun _ => ?_
    exact exists_congr fun r' => exists_congr fun g' => and_congr_right fun _ => and_congr_right fun _ =>
      EvTree.eraseWPR_map f Post (ret true) r' g' cx'
  | .fence _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWPR]
    exact EvTree.eraseWPR_map f Post (ret ()) r g _
  | .rmw _ _ _ _ ret, r, g, cx => by
    simp only [EvTree.map, EvTree.EraseWPR]
    refine forall_congr' fun x => imp_congr_right fun _ => and_congr
      (imp_congr_right fun _ => EvTree.eraseWPR_map f Post (ret _) r g _) ?_
    refine forall_congr' fun new => imp_congr_right fun _ => forall_congr' fun cx' =>
      imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => imp_congr_right fun _ => ?_
    exact exists_congr fun r' => exists_congr fun g' => and_congr_right fun _ => and_congr_right fun _ =>
      EvTree.eraseWPR_map f Post (ret _) r' g' _

end Kraken.Promising.SLR

