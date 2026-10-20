/-
A thread text that calls the lowered FlatHashMap `take` and `lookup`, and its
static facts for the AArch64 lowering kit. ISA: AArch64 (`isa`).

`flatWhole` is `main` (`FlatWholeSpec.lean`), the lowered `take` and
`lookup` verbatim, and a trailing label `done` that marks the end of the text
(the kit's stuck-at-end lemma).

The text makes no shared access: every load and store of the callees goes to
the table, which lives in the thread's `dmem`. The kit's static facts hold at
every layout: `flatWhole_rmwLive`, `flatWhole_phase1F` (`Phase1TreeF`) and
`flatWhole_noFault` (`DirsNoFault`). They are checked fragment by fragment and
in chunks of 20 directives (one check of the whole 156-directive text exceeds
the kernel's recursion depth); `MOVZ`/`MOVK` are discharged by lemmas generic
in the immediate (`movz_phase1F`, …), since unfolding a 16-bit immediate
shifted by 32 or 48 also exceeds it.
-/
import Kraken.Promising.Lower.FlatWholeSpec
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.Promising.SLR.EnvG.A64MovImm
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.Lower.Flat.Whole

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser
open Kraken.Promising.Lower.Flat Kraken.Promising.Lower.Flat.Take

/-- The end marker. -/
def doneFrag : Program := parseAArch64("
done:
")

/-- **The whole text**: `main`, `flat_take`, `flat_lookup`, `done`. -/
def flatWhole : Program := mainFrag ++ flatTake ++ flatLookup ++ doneFrag

/-- info: 156 -/
#guard_msgs in
#eval flatWhole.length

theorem flatWhole_wf : Program.WF flatWhole := by decide
theorem flatWhole_ne : flatWhole.any (fun d => !d.isLabel) = true := by decide
theorem flatWhole_hs :
    [mainFrag, flatTake, flatLookup].all (Program.subBlocksOfE · flatWhole) = true := by decide

/-- Text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def wLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize flatWhole

set_option maxRecDepth 4000 in
instance wValid : Executable.ValidLayout (wLayout flatWhole) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## `MOVZ` and `MOVK`, generic in the immediate

The generic lemmas are `Kraken.Promising.AArch64.EnvG.movz_phase1F`,
`movk_phase1F`, `movz_noFault` and `movk_noFault` (`SLR/EnvG/A64MovImm.lean`);
the names below are kept as aliases. -/

section MovImm

theorem movz_phase1F {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirPhase1F e (.instr ⟨w, .MOVZ dst imm sh⟩) z :=
  Kraken.Promising.AArch64.EnvG.movz_phase1F dst imm sh e z

theorem movk_phase1F {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirPhase1F e (.instr ⟨w, .MOVK dst imm sh⟩) z :=
  Kraken.Promising.AArch64.EnvG.movk_phase1F dst imm sh e z

theorem movz_noFault {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirNoFault e (.instr ⟨w, .MOVZ dst imm sh⟩) z :=
  Kraken.Promising.AArch64.EnvG.movz_noFault dst imm sh e z

theorem movk_noFault {w : RegWidth} (dst : RegOrZr w) (imm : ConstExpr) (sh : MovShift w)
    (e : _root_.Executable) (z : Nat) : DirNoFault e (.instr ⟨w, .MOVK dst imm sh⟩) z :=
  Kraken.Promising.AArch64.EnvG.movk_noFault dst imm sh e z

end MovImm

/-! ## Per-fragment checks -/

set_option hygiene false in
/-- `frag_phase1F p`: `dirs_phase1F`'s per-directive check for the directives
of `p`, a definition possibly under `List.take`/`List.drop`; `MOVZ`/`MOVK` by
the generic lemmas. -/
local macro "frag_phase1F " p:ident : tactic => `(tactic| (
  intro d hd e z
  simp only [$p:ident, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals first
    | exact Kraken.Promising.Lower.Flat.Whole.movz_phase1F _ _ _ e z
    | exact Kraken.Promising.Lower.Flat.Whole.movk_phase1F _ _ _ e z
    | intro s pc
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF, Kraken.Promising.SLR.EnvG.DetAccess,
    Kraken.Promising.SLR.EnvG.SingleAccessS2, Kraken.Promising.SLR.EnvG.AccessFree,
    _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty]))
  all_goals (by_cases hz : s.status.z = true <;>
    simp [hz, Kraken.Promising.AArch64.toEv, Kraken.Promising.SLR.EnvG.Phase1ShapeF,
      Kraken.Promising.SLR.EnvG.DetAccess, Kraken.Promising.SLR.EnvG.SingleAccessS2,
      Kraken.Promising.SLR.EnvG.AccessFree, Kraken.Promising.EvTree.access_empty])))

set_option hygiene false in
/-- `frag_noFault p`: `dirs_no_fault`'s per-directive check, as `frag_phase1F`. -/
local macro "frag_noFault " p:ident : tactic => `(tactic| (
  intro d hd e z
  simp only [$p:ident, List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals first
    | exact Kraken.Promising.Lower.Flat.Whole.movz_noFault _ _ _ e z
    | exact Kraken.Promising.Lower.Flat.Whole.movk_noFault _ _ _ e z
    | intro s pc
  all_goals try simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.AArch64.toEv, Kraken.Promising.EvTree.NoFault, _root_.MachineData.load, _root_.MachineData.store,
    _root_.MachineData.loadK, _root_.MachineData.storeK, _root_.MachineData.rmwK,
    _root_.MachineData.setRegOrZr, _root_.MachineData.setRegOrSp, _root_.RegOrSp.interpBase,
    _root_.AddrExpr.checkSPAlignment, _root_.AddrExpr.interpLoad, _root_.AddrExpr.interpStore,
    _root_.UnscaledAddrExpr.checkSPAlignment, _root_.UnscaledAddrExpr.interpLoad,
    _root_.UnscaledAddrExpr.interpStore, _root_.Literal.interpLoad, _root_.AddrOrLit.interpLoad,
    Kraken.Promising.EvTree.access_empty]
  all_goals (repeat' (first | split |
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.EvTree.NoFault, Kraken.Promising.EvTree.access_empty]))
  all_goals try (refine Kraken.Promising.prop_ite (P := fun x =>
                Kraken.Promising.EvTree.NoFault (Kraken.Promising.AArch64.toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.AArch64.toEv, Kraken.Promising.EvTree.NoFault])))

/-- A property of every element, chunk by chunk (`take`/`drop`). -/
theorem forall_mem_split {α : Type} {P : α → Prop} (L : List α) (n : Nat) (h1 : ∀ d ∈ L.take n, P d)
    (h2 : ∀ d ∈ L.drop n, P d) : ∀ d ∈ L, P d := by
  intro d hd
  rw [← List.take_append_drop n L, List.mem_append] at hd
  exact hd.elim (h1 d) (h2 d)

theorem main_phase1F : ∀ d ∈ mainFrag, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F mainFrag
theorem done_phase1F : ∀ d ∈ doneFrag, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F doneFrag
theorem lookup_phase1F : ∀ d ∈ flatLookup, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  refine forall_mem_split _ 20 (by frag_phase1F flatLookup) (forall_mem_split _ 20 ?_ ?_)
  · frag_phase1F flatLookup
  · frag_phase1F flatLookup
theorem take_phase1F1 : ∀ d ∈ flatTake.take 20, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F flatTake
theorem take_phase1F2 : ∀ d ∈ (flatTake.drop 20).take 20, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F flatTake
theorem take_phase1F3 : ∀ d ∈ (flatTake.drop 40).take 20, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F flatTake
theorem take_phase1F4 : ∀ d ∈ (flatTake.drop 60).take 10, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F flatTake
theorem take_phase1F5 : ∀ d ∈ flatTake.drop 70, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  frag_phase1F flatTake
theorem take_phase1F : ∀ d ∈ flatTake, ∀ (e : _root_.Executable) z, DirPhase1F e d z :=
  forall_mem_split _ 20 take_phase1F1 <| forall_mem_split _ 20 take_phase1F2 <| forall_mem_split _ 20 take_phase1F3 <|
    forall_mem_split _ 10 take_phase1F4 take_phase1F5

theorem main_noFault : ∀ d ∈ mainFrag, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault mainFrag
theorem done_noFault : ∀ d ∈ doneFrag, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault doneFrag
theorem lookup_noFault : ∀ d ∈ flatLookup, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  refine forall_mem_split _ 20 (by frag_noFault flatLookup) (forall_mem_split _ 20 ?_ ?_)
  · frag_noFault flatLookup
  · frag_noFault flatLookup
theorem take_noFault1 : ∀ d ∈ flatTake.take 20, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault flatTake
theorem take_noFault2 : ∀ d ∈ (flatTake.drop 20).take 20, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault flatTake
theorem take_noFault3 : ∀ d ∈ (flatTake.drop 40).take 20, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault flatTake
theorem take_noFault4 : ∀ d ∈ (flatTake.drop 60).take 10, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault flatTake
theorem take_noFault5 : ∀ d ∈ flatTake.drop 70, ∀ (e : _root_.Executable) z, DirNoFault e d z := by
  frag_noFault flatTake
theorem take_noFault : ∀ d ∈ flatTake, ∀ (e : _root_.Executable) z, DirNoFault e d z :=
  forall_mem_split _ 20 take_noFault1 <| forall_mem_split _ 20 take_noFault2 <| forall_mem_split _ 20 take_noFault3 <|
    forall_mem_split _ 10 take_noFault4 take_noFault5

section Static
variable [layout : _root_.Layout]

theorem flatWhole_rmwLive : (layout flatWhole).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem flatWhole_phase1F [Executable.ValidLayout (layout flatWhole)] : Phase1TreeF (layout flatWhole) := by
  refine phase1TreeF_of_dirs (dirsPhase1F_layout fun d hd => ?_)
  simp only [flatWhole, List.mem_append] at hd
  rcases hd with ((h | h) | h) | h
  · exact main_phase1F d h
  · exact take_phase1F d h
  · exact lookup_phase1F d h
  · exact done_phase1F d h

theorem flatWhole_noFault : DirsNoFault (layout flatWhole) := by
  refine dirsNoFault_layout fun d hd => ?_
  simp only [flatWhole, List.mem_append] at hd
  rcases hd with ((h | h) | h) | h
  · exact main_noFault d h
  · exact take_noFault d h
  · exact lookup_noFault d h
  · exact done_noFault d h

end Static

end Kraken.Promising.Lower.Flat.Whole
