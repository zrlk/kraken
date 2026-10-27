/-
**The direct branch targets of the user code, decided** (AArch64; the twin
of `Spike/Lib/LowerX64/UserTgt.lean`): every `b`, `b.cond`, `cbz` and
`cbnz` in a run of a label passing `q` and none of the write abort's
(`abLabs`) goes to a label with a nonempty run, itself none of the write
abort's (`tgOkQB`, a Boolean check over the output's directives); each such
target is then a position off the write abort (`PosOff`, at offset `0`).
A block of the code predicate at such a label (`hQ`) of a construct or a
`ret` (`Kind2`) has no `bl` (its last instruction is not one, and a `bl`
ends a covered block), so `cxBlk2_ofW2`'s `hTg` follows (`hTg_of_tgOkQB`).
A tail call's `b f` to a function symbol fails the check (its label's run
is empty); `Kind2` has none.

- `tgtOkB`, `dTgt`, `tgOkQB`, `tgOkB`: the checks (`tgOkB` at the user
  functions' runs, `WcL`);
- `posOff_of_tgtOkB`: a passing target is a position off the write abort;
- `tgtOkB_of_tgOkQB`: the targets of a block of a checked run pass;
- `noBl_of_last`, `noBl_kind2`: no `bl` in a `Kind2` block;
- `hTg_of_tgOkQB`: `cxBlk2_ofW2`'s `hTg` from the check, at a code predicate
  whose blocks sit at checked labels; `hTg_of_tgOkB` at `CdCLE`.
-/
import Spike.Lib.LowerA64.CdCLE
import Spike.Lib.LowerA64.Kind2SFacts

namespace Spike.Lib.LowerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow (AI classify okBlk AM)
open Scc.Cert.Rt.A64 (labelIdx run blockAt InRun labelIdx_spec)
open Spike.Lib.A64.AllocG (abLabs)
open Scc.Emit.A64 Scc.Lower.InvA64

/-! ## The checks -/

/-- **A branch target passes**: a label of the program with a nonempty run,
none of the write abort's. -/
def tgtOkB (prog : List Directive) (L : Label) : Bool :=
  (labelIdx prog L).isSome && !(run prog L).isEmpty && !abLabs.contains L

/-- **The direct branch target** of a covered instruction: `b`, `b.cond`,
`cbz`, `cbnz` (not `bl`, not `ret`). -/
def dTgt : Option AI → Option Label
  | some (.b L) => some L
  | some (.bcond _ L) => some L
  | some (.cbz _ L) => some L
  | some (.cbnz _ L) => some L
  | _ => none

/-- **Every direct branch of a checked run passes**: the runs of the labels
passing `q` and none of the write abort's. -/
def tgOkQB (q : Label → Bool) (prog : List Directive) : Bool :=
  prog.all fun d => match d with
    | .label L0 => !(q L0 && !abLabs.contains L0) ||
        (run prog L0).all fun c => match dTgt (classify c) with
          | some L => tgtOkB prog L
          | none => true
    | _ => true

/-- **The check at the user functions' runs** (`WcL`, the code predicate
`CdCL`'s labels). -/
def tgOkB (prog : List Directive) : Bool := tgOkQB wcL prog

/-- **A passing target is a position off the write abort** (offset `0` of
its run). -/
theorem posOff_of_tgtOkB {prog : List Directive} {L : Label} (h : tgtOkB prog L = true) (lab : Label → Int64) :
    PosOff prog lab (lab L) := by
  simp only [tgtOkB, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨hs, hne⟩, hab⟩ := h
  refine ⟨L, 0, ⟨hs, List.length_pos_iff.mpr hne⟩, fun hm => ?_, by simp⟩
  simp [hm] at hab

/-- **The direct targets of a block at a checked label pass.** -/
theorem tgtOkB_of_tgOkQB {q : Label → Bool} {prog : List Directive} (hc : tgOkQB q prog = true) {L0 : Label}
    {j : Nat} {b : List Directive} (hb : blockAt prog L0 j b = true) (hq : q L0 = true) (hL0 : L0 ∉ abLabs)
    {k : Nat} (hk : k < b.length) {L : Label} (ht : dTgt (classify b[k]) = some L) : tgtOkB prog L = true := by
  simp only [blockAt, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hs, hrun⟩ := hb
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  have hmem : Directive.label L0 ∈ prog := List.mem_of_getElem? (labelIdx_spec hi).1
  have hall := List.all_eq_true.mp hc _ hmem
  have hq' : (q L0 && !abLabs.contains L0) = true := by simp [hq, hL0]
  simp only [hq', Bool.not_true, Bool.false_or] at hall
  have hbk : b[k] ∈ run prog L0 := by
    have : b[k] ∈ ((run prog L0).drop j).take b.length := by rw [hrun]; exact List.getElem_mem hk
    exact List.mem_of_mem_drop (List.mem_of_mem_take this)
  have := List.all_eq_true.mp hall _ hbk
  rw [ht] at this
  exact this

/-! ## No `bl` in a `Kind2` block -/

/-- **No `bl` but at the end**: in a covered block a `bl` is the last
instruction (as `noRet_of_last`). -/
theorem noBl_of_last {lo hi : Int} :
    ∀ {o : Spike.Lib.A64.Flow.SO} {blk : List Directive}, okBlk lo hi o blk = true →
      (∀ d, blk.getLast? = some d → ∀ L, classify d ≠ some (.bl L)) →
      ∀ k (hk : k < blk.length) L, classify blk[k] ≠ some (.bl L)
  | _, [], _, _, k, hk, _ => absurd hk (by simp)
  | o, d :: ds, h, hl, k, hk, L => by
    simp only [okBlk] at h
    cases hcd : classify d with
    | none => rw [hcd] at h; cases h
    | some a =>
      rw [hcd] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨-, ht⟩, hr⟩ := h
      cases k with
      | zero =>
        intro hb
        simp only [List.getElem_cons_zero] at hb
        rw [hcd] at hb
        cases hb
        have hds : ds = [] := by simpa [AI.isTerm] using ht
        subst hds
        exact hl d rfl L hcd
      | succ k =>
        simp only [List.getElem_cons_succ]
        refine noBl_of_last hr (fun d' hd' => hl d' ?_) k (by simpa using hk) L
        cases ds with
        | nil => simp at hd'
        | cons e es => rw [List.getLast?_cons_cons]; exact hd'

/-- A `ret`-ended block ends with no `bl`. -/
theorem last_ret_noBl (xs : List Item) :
    ∀ d, (directives (xs ++ [ret])).getLast? = some d → ∀ L, classify d ≠ some (.bl L) := by
  intro d hd L
  rw [directives_append, List.getLast?_append] at hd
  simp only [directives, ret, ins, List.filterMap_cons, List.filterMap_nil, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hd
  subst hd
  simp [Spike.Lib.A64.Flow.classify]

/-- **A `Kind2` block has no `bl`**: it is covered (`okBlk_kind2`) and its
last instruction is a `b.cs`, a `csel`, a `b.eq`, a `str`, a `b` or a `ret`. -/
theorem noBl_kind2 {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {blk : List Directive} (hk : Kind2 cx blk) : ∀ k (hk : k < blk.length) L, classify blk[k] ≠ some (.bl L) := by
  have hok := okBlk_kind2 hf h1 h16 hk
  refine noBl_of_last hok ?_
  rcases hk with ⟨⟨a, b, la, lb, ha, hb', h | h | ⟨T, h⟩⟩ | ⟨d, off, hd, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩⟩ |
    ⟨vs, ls, -, hl, rfl⟩
  · subst h
    intro d hd L
    rw [addDirs, directives_append, directives_addChecked, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · subst h
    intro d hd L
    rw [subDirs, directives_append, directives_subSat, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly]
  · subst h
    intro d hd L
    rw [brDirs, directives_append, directives_cmpJcc, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · intro d' hd L
    simp only [strDirs, directives, ins, List.filterMap_cons, List.filterMap_nil, List.getLast?_singleton,
      Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify, spW64, i64]
  · intro d hd L
    simp only [jmpDirs, directives, jmp, ins, List.filterMap_cons, List.filterMap_nil, List.getLast?_singleton,
      Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · exact last_ret_noBl _
  · exact last_ret_noBl _

/-! ## `cxBlk2_ofW2`'s `hTg` -/

/-- **`cxBlk2_ofW2`'s `hTg` from the check**: at a code predicate each of
whose pieces sits in the run of a label passing `q` and none of the write
abort's (`hQ`), every `b`, `b.cond`, `cbz` or `cbnz` of a `Kind2` part goes
to a position off the write abort, and it has no `bl`. -/
theorem hTg_of_tgOkQB {q : Label → Bool} {prog : List Directive} (hc : tgOkQB q prog = true) {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {Cd : Int64 → List Directive → Prop}
    (hQ : ∀ pc blk, Cd pc blk → ∃ L j, q L = true ∧ L ∉ abLabs ∧ blockAt prog L j blk = true)
    (lab : Label → Int64) :
    ∀ pc blk, SubCd Cd pc blk → Kind2 cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff prog lab (lab L) := by
  rintro pc blk ⟨pc0, pre, suf, hcd, -⟩ hk k hkl L ht
  obtain ⟨L0, j, hq, hL0, hb⟩ := hQ _ _ hcd
  have hkl' : pre.length + k < (pre ++ blk ++ suf).length := by simp; omega
  have he : (pre ++ blk ++ suf)[pre.length + k] = blk[k] := by
    simp [hkl]
  have hd : dTgt (classify blk[k]) = some L := by
    rcases ht with h | h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp only [h, dTgt]
    exact absurd h (noBl_kind2 hf h1 h16 hk k hkl L)
  rw [← he] at hd
  exact posOff_of_tgtOkB (tgtOkB_of_tgOkQB hc hb hq hL0 hkl' hd) lab

/-- **`cxBlk2_ofW2`'s `hTg` from `tgOkB`** at a code predicate of pieces at
`CdCLE` (`hTg_of_tgOkQB`, its pieces at `CdCL`'s labels: user functions'
and none of the write abort's). -/
theorem hTg_of_tgOkB {prog : List Directive} (hc : tgOkB prog = true) {cx : FnCtx}
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {Cd : Int64 → List Directive → Prop}
    {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
    (hCd : ∀ pc blk, Cd pc blk → CdCLE prog okPc ph lab ra pc blk) (lab' : Label → Int64) :
    ∀ pc blk, SubCd Cd pc blk → Kind2 cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff prog lab' (lab' L) :=
  hTg_of_tgOkQB hc hf h1 h16 (fun pc blk h =>
    let ⟨⟨_, L, j, ⟨hL, hW⟩, _, hb, _⟩, _⟩ := hCd pc blk h
    ⟨L, j, hW, hL, hb⟩) lab'

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.posOff_of_tgtOkB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.posOff_of_tgtOkB

/-- info: 'Spike.Lib.LowerA64.tgtOkB_of_tgOkQB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tgtOkB_of_tgOkQB

/-- info: 'Spike.Lib.LowerA64.noBl_of_last' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.noBl_of_last

/-- info: 'Spike.Lib.LowerA64.last_ret_noBl' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.last_ret_noBl

/-- info: 'Spike.Lib.LowerA64.noBl_kind2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.noBl_kind2

/-- info: 'Spike.Lib.LowerA64.hTg_of_tgOkQB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hTg_of_tgOkQB

/-- info: 'Spike.Lib.LowerA64.hTg_of_tgOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hTg_of_tgOkB
