/-
**An `Accepted2` program's user functions are user segments** (x86-64):
scc's code for each user function of an `Accepted2` program (`funcs2`)
is a user function's segment (`UserPart`, `Spike/Lib/LowerX64/G1TgSeg.lean`),
the hypothesis `UserPartStmt` of the branch-target check.

The function's name is a user name, so no user label (`WcL`); its blocks
are of `lowerC2`'s shape (`BlockC2`) and branch only to its blocks
(`func2_brClosed`). Its directives are its name's label then directives in
which every label is followed by a non-label, ending with a non-label
(`emitFuncAt_lf`, `Spike/Lib/LowerX64/G1TgHT.lean`), and every direct jump
goes to a user label of the function (`userFunc_tgts`,
`Spike/Lib/LowerX64/G1TgTgt.lean`).

- `not_wcL_user`: a user name is no user label;
- `funcs2_c2`: a user function's name, blocks and branches;
- `userPart_of`: a user function's directives form a `UserPart`, from its
  jumps' targets;
- `userPartStmt`: `UserPartStmt`.
-/
import Spike.Lib.LowerX64.G1TgHT
import Spike.Lib.LowerX64.G1TgUserStmt
import Spike.Lib.LowerX64.G1TgTgt

namespace Spike.Lib.LowerX64

open Kraken
open Scc.Emit.X64
open Spike.Lib.LowerShape (BlockC2 termTgts func2_brClosed lowerC2_brClosed lowerC2_resC2)
open Spike.Lib.LowerNode (Pairwise2 LowC2 compiled2 funcs2)
open Spike.Lib.X64.AllocG (abLabs)

/-- **A user name is no user label** (`WcL`): it starts `wc_`. -/
theorem not_wcL_user (g : String) : ¬ WcL (Scc.Lower.Names.user g) := by
  intro h
  unfold WcL Scc.Lower.Names.user at h
  rw [String.toList_append] at h
  have := congrArg List.head? h
  simp at this

/-- **A user function of an `Accepted2` program**: a user name, every block
of `lowerC2`'s shape, every branch to one of its blocks. -/
theorem funcs2_c2 {p : CoreTerm.Prog} {obj : Scc.ObjLayout} {ws : List Spike.Lib.LowerNode.Low2}
    (hws : Pairwise2 (LowC2 p obj) (compiled2 p) ws) {f : Scc.IR.Func} (hf : f ∈ funcs2 p ws) :
    (∃ g, f.name = Scc.Lower.Names.user g) ∧ (∀ b ∈ f.blocks, BlockC2 b) ∧
      ∀ b ∈ f.blocks, ∀ L ∈ termTgts b.term, ∃ b' ∈ f.blocks, b'.label = L := by
  unfold funcs2 at hf
  rw [← List.map_uncurry_zip_eq_zipWith, List.mem_map] at hf
  obtain ⟨⟨d, w⟩, hdw, rfl⟩ := hf
  simp only [Function.uncurry]
  obtain ⟨-, -, hlow⟩ := hws.2 _ hdw
  have hres := lowerC2_resC2 _ _ _ _ _ _ _ hlow
  have hbr := lowerC2_brClosed _ _ _ _ _ _ _ hlow
  refine ⟨⟨_, rfl⟩, fun b hb => ?_, func2_brClosed hbr⟩
  simp only [Spike.Lib.LowerShape.func2, List.mem_cons] at hb
  rcases hb with rfl | hb
  · exact ⟨hres.1, hres.2.1⟩
  · exact hres.2.2 b hb

/-- **A user function's directives form a `UserPart`**, from its blocks'
shape and its direct jumps' targets (user labels of the function, none of
the write abort's). -/
theorem userPart_of {P : Scc.IR.Program} {areas} {f : Scc.IR.Func} {n : Nat} {r}
    (h : emitFuncAt P areas f n = .ok r) {g : String} (hname : f.name = Scc.Lower.Names.user g)
    (hblk : ∀ b ∈ f.blocks, BlockC2 b)
    (htg : ∀ d ∈ dOf r.1, ∀ T, dirTgt d = some T → WcL T ∧ T ∉ abLabs ∧ Directive.label T ∈ dOf r.1) :
    UserPart (dOf r.1) := by
  obtain ⟨P', hP, hlf, hlast⟩ := emitFuncAt_lf h hblk
  have hnw : ¬ WcL f.name := by rw [hname]; exact not_wcL_user g
  refine ⟨f.name, P', hP, hnw, hlf, hlast, fun d hd T hT => ?_⟩
  obtain ⟨hw, hab, hm⟩ := htg d (by rw [hP]; exact List.mem_cons_of_mem _ hd) T hT
  refine ⟨hw, hab, ?_⟩
  rw [hP] at hm
  rcases List.mem_cons.mp hm with e | hm
  · cases e
    exact absurd hw hnw
  · exact hm

/-- **Each user function's code is a user function's segment**
(`UserPartStmt`). -/
theorem userPartStmt : UserPartStmt := by
  intro cfg p ws rt _ hws _ f hf areas n r h
  obtain ⟨⟨g, hname⟩, hblk, hbr⟩ := funcs2_c2 hws hf
  exact userPart_of h hname hblk (userFunc_tgts h g hname hblk hbr)

/-- info: 'Spike.Lib.LowerX64.userPartStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms userPartStmt

end Spike.Lib.LowerX64
