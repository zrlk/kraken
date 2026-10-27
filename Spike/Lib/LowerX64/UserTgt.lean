/-
**A user function's construct blocks jump to positions off the write
abort, by a check of the code** (x86-64): `cxBlk2_ofW2`'s `hTg`
(`Spike/Lib/LowerX64/CxBlk2Of.lean`) at any code predicate inside `CdCLE`
from one Boolean check of the cells (`tgOkB`). In the run of every label
`L0` of a user function (`WcL L0`, none of the write abort's), each `jmp` or
`jcc` target `L` labels the cells, its run is nonempty and it is none of the
write abort's labels (`tgtOkB`); so `L`'s first cell is a position off the
write abort (`PosOff` at `(L, 0)`). A construct's block (`Kind2`) has no
`call` (`noCall_kind2`), so `hTg`'s call disjunct is void. Runtime runs
(e.g. `print`'s loop, whose `jmp` enters the write abort) are not checked:
`CdCL` holds of no piece of theirs.

- `tgtOkB`, `tgOkB`: the check of a target and of the cells;
- `noCallD`, `noCallD_getOp`, `noCallD_getOps`, `noCallD_kindD`,
  `noCallD_kindD2`, `noCall_kind2`: a construct's directives have no `call`;
- `posOff_of_tgtOkB`: a checked target's label is a position off the write
  abort;
- `hTg_of_tgOkB`: `cxBlk2_ofW2`'s `hTg` from `tgOkB`.
-/
import Spike.Lib.LowerX64.CdCLE
import Spike.Lib.LowerX64.NoSlotWr

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (AI classify)
open Scc.Emit.X64 (Item i64 i32 xm xr or_ oi rel mem)
open Scc.Cert.Rt.X64 (labelIdx run blockAt labelIdx_spec)
open Spike.Lib.X64.AllocG (abLabs)

/-! ## The check -/

/-- **A checked jump target**: `L` labels the cells, its run is nonempty,
and it is none of the write abort's labels. -/
def tgtOkB (cells : List (Directive × Nat)) (L : Label) : Bool :=
  (labelIdx cells L).isSome && !(run cells L).isEmpty && decide (L ∉ abLabs)

/-- **The jump targets of a user function's runs are checked**: for every
label `L0` of the cells in a user function's run (`WcL`) and none of the
write abort's, every `jmp` or `jcc` of `L0`'s run goes to a checked target
(`tgtOkB`). -/
def tgOkB (cells : List (Directive × Nat)) : Bool :=
  cells.all fun c => match c.1 with
    | .label L0 => !(decide (WcL L0) && decide (L0 ∉ abLabs)) || (run cells L0).all fun c' =>
        match classify c'.1 with
        | some (.jmp L) => tgtOkB cells L
        | some (.jcc _ L) => tgtOkB cells L
        | _ => true
    | _ => true

/-- **A checked target's label is a position off the write abort** (its
first cell's). -/
theorem posOff_of_tgtOkB {cells : List (Directive × Nat)} {L : Label} (h : tgtOkB cells L = true)
    (lab : Label → Int64) : PosOff cells lab (lab L) := by
  simp only [tgtOkB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq] at h
  obtain ⟨⟨hl, hr⟩, hL⟩ := h
  refine ⟨L, 0, ⟨hl, 0, List.length_pos_iff.mpr hr, by simp⟩, hL, ?_⟩
  rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]

/-! ## No `call` in a construct's block -/

/-- **Directives with no `call`.** -/
def noCallD (ds : List Directive) : Bool :=
  ds.all fun d => match classify d with
    | some (.call _) => false
    | _ => true

theorem noCallD_append {a b : List Directive} : noCallD (a ++ b) = (noCallD a && noCallD b) := by
  simp [noCallD, List.all_append]

/-- **An operand's load has no `call`.** -/
theorem noCallD_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : noCallD (dirs l) = true := by
  rcases getOp_cases ha with ⟨_, _, _, _, hl⟩ | ⟨_, _, hl⟩ <;> rw [hl]
  · rfl
  · simp only [noCallD, List.all_cons, List.all_nil, Bool.and_true, i64, Scc.Emit.X64.op, xr, classify]
    split
    · next a h =>
      split at h
      · cases h
      · cases h
    · rfl

/-- **Operands' loads have no `call`.** -/
theorem noCallD_getOps {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List (Scc.IR.Operand × Reg64)} {c : List Item}, getOps fr l = .ok c → noCallD (dirs c) = true
  | [], c, h => by cases h; rfl
  | (a, r) :: rest, c, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    rw [dirs_append, noCallD_append, noCallD_getOp ha, noCallD_getOps hr]; rfl

/-- **A construct's directives have no `call`.** -/
theorem noCallD_kindD {fr : Scc.Emit.X64.Frame} {ds : List Directive} (hk : KindD fr ds) : noCallD ds = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, rfl | rfl | ⟨T, rfl⟩⟩ | ⟨d, o, -, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · rw [addDirs, dirs_append, dirs_append, noCallD_append, noCallD_append, noCallD_getOp ha,
      noCallD_getOp hb]; rfl
  · rw [subDirs, dirs_append, dirs_append, noCallD_append, noCallD_append, noCallD_getOp ha,
      noCallD_getOp hb]; rfl
  · rw [brDirs, dirs_append, dirs_append, noCallD_append, noCallD_append, noCallD_getOp ha,
      noCallD_getOp hb]; rfl
  · rfl
  · rfl
  · rw [retDirs, dirs_append, noCallD_append, noCallD_getOp hg, dirs_epiItems]; rfl

/-- **An `Accepted2` construct's directives have no `call`.** -/
theorem noCallD_kindD2 {fr : Scc.Emit.X64.Frame} {ds : List Directive} (hk : KindD2 fr ds) : noCallD ds = true := by
  rcases hk with hk | ⟨ws, lw, -, hg, rfl⟩
  · exact noCallD_kindD hk
  · rw [retDirs, dirs_append, noCallD_append, noCallD_getOps hg, dirs_epiItems]; rfl

/-- **A construct's block has no `call`.** -/
theorem noCall_kind2 {fr : Scc.Emit.X64.Frame} {blk : List (Directive × Nat)} (hk : Kind2 fr blk) {k : Nat}
    (hkl : k < blk.length) (L : Label) : classify blk[k].1 ≠ some (.call L) := by
  have h := List.all_eq_true.mp (noCallD_kindD2 hk) blk[k].1
    (List.mem_map.mpr ⟨blk[k], List.getElem_mem hkl, rfl⟩)
  intro he
  rw [he] at h
  cases h

/-! ## `hTg` from the check -/

/-- **A construct's block of a code predicate inside `CdCLE` jumps to
positions off the write abort** (`cxBlk2_ofW2`'s `hTg`), the cells passing
`tgOkB`: the block is in the run of a user function's label `L0` none of the
write abort's (`CdCL`, `blockAt`), whose `jmp`s and `jcc`s go to checked
targets (`posOff_of_tgtOkB`); it has no `call` (`noCall_kind2`). -/
theorem hTg_of_tgOkB {cells : List (Directive × Nat)} (hc : tgOkB cells = true) {okPc : Nat → Bool}
    {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64} {fr : Scc.Emit.X64.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdCLE cells okPc ph lab ra pc blk)
    (lab' : Label → Int64) :
    ∀ pc blk, SubCd Cd pc blk → Kind2 fr blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k].1 = some (.jmp L) ∨ classify blk[k].1 = some (.call L) ∨
        ∃ cc, classify blk[k].1 = some (.jcc cc L)) → PosOff cells lab' (lab' L) := by
  intro pc blk hsub hk k hkl L hj
  obtain ⟨pc0, pre, post, hcd, -⟩ := hsub
  obtain ⟨⟨-, L0, j, off, ⟨hL0, hW⟩, -, hb, -⟩, -⟩ := hCd _ _ hcd
  simp only [blockAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
  obtain ⟨⟨hl, -⟩, hb⟩ := hb
  -- the block's `k`th cell is in `L0`'s run
  have hmem : blk[k] ∈ run cells L0 := by
    have h1 : blk[k] ∈ pre ++ blk ++ post :=
      List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem hkl))
    rw [← hb] at h1
    exact List.mem_of_mem_drop (List.mem_of_mem_take h1)
  -- `label L0` is a cell
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hl
  obtain ⟨⟨z, hz⟩, -⟩ := labelIdx_spec hn
  have hcell := List.all_eq_true.mp hc _ (List.mem_of_getElem? hz)
  simp only [hW, hL0, not_false_eq_true, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at hcell
  have ht := List.all_eq_true.mp hcell _ hmem
  rcases hj with hj | hj | ⟨cc, hj⟩
  · rw [hj] at ht; exact posOff_of_tgtOkB ht lab'
  · exact absurd hj (noCall_kind2 hk hkl L)
  · rw [hj] at ht; exact posOff_of_tgtOkB ht lab'

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.posOff_of_tgtOkB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.posOff_of_tgtOkB

/-- info: 'Spike.Lib.LowerX64.noCall_kind2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.noCall_kind2

/-- info: 'Spike.Lib.LowerX64.hTg_of_tgOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hTg_of_tgOkB
