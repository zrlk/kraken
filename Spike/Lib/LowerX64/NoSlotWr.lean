/-
**No slot written before a block's last instruction** (x86-64; the twin
of `Spike/Lib/LowerA64/NoSlotWr.lean`): the premise `noSlotWr blk.dropLast`
of `blkW_placedS` (`Spike/Lib/LowerX64/PlacedBlk.lean`) for the blocks of
an `Accepted2` body's code.

- `noSlotWrD`: `noSlotWr` on a block's directives;
- `noSlotWrD_getOp`, `noSlotWrD_getOps`: an operand's loads write no slot;
- `noSlotWrD_kindD`, `noSlotWrD_kindD2`: a construct's directives write no
  slot before their last (the store alone writes one, as its last);
- `noSlotWr_kind1`, `noSlotWr_kind2`: the same on a sized block;
- `noSlotWr_zip`, `noSlotWr_dropLast`: sized blocks of directives.
-/
import Spike.Lib.LowerX64.PlacedBlk
import Spike.Lib.LowerX64.Body2

namespace Spike.Lib.LowerX64

open Kraken.Promising.X64
open Spike.Lib.X64 (AI classify)
open Scc.Emit.X64 (Item i64 i32 xm xr or_ oi rel mem)

/-- **Directives writing no slot.** -/
def noSlotWrD (ds : List Directive) : Bool :=
  ds.all fun d => match classify d with
    | some a => !a.slotWr
    | none => true

theorem noSlotWr_eq (blk : List (Directive × Nat)) : noSlotWr blk = noSlotWrD (blk.map (·.1)) := by
  induction blk with
  | nil => rfl
  | cons x xs ih => simp only [noSlotWr, noSlotWrD, List.all_cons, List.map_cons] at ih ⊢; rw [ih]; rfl

theorem noSlotWrD_append {a b : List Directive} : noSlotWrD (a ++ b) = (noSlotWrD a && noSlotWrD b) := by
  simp [noSlotWrD, List.all_append]

theorem noSlotWrD_dropLast {ds : List Directive} (h : noSlotWrD ds = true) : noSlotWrD ds.dropLast = true := by
  simp only [noSlotWrD, List.all_eq_true] at h ⊢
  exact fun x hx => h x (List.dropLast_subset _ hx)

/-- **A sized block of directives writing no slot writes none.** -/
theorem noSlotWr_zip {ds : List Directive} {zs : List Nat} (h : noSlotWrD ds = true) :
    noSlotWr (ds.zip zs) = true := by
  simp only [noSlotWr, noSlotWrD, List.all_eq_true] at h ⊢
  intro x hx
  exact h x.1 (List.of_mem_zip hx).1

/-- **A block's prefix without its last** from its directives'. -/
theorem noSlotWr_dropLast {blk : List (Directive × Nat)} (h : noSlotWrD (blk.map (·.1)).dropLast = true) :
    noSlotWr blk.dropLast = true := by
  rw [noSlotWr_eq, List.map_dropLast]; exact h

/-- **An operand's load writes no slot.** -/
theorem noSlotWrD_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : noSlotWrD (dirs l) = true := by
  rcases getOp_cases ha with ⟨_, _, _, _, hl⟩ | ⟨_, _, hl⟩ <;> rw [hl]
  · rfl
  · simp only [noSlotWrD, List.all_cons, List.all_nil, Bool.and_true, i64, Scc.Emit.X64.op, xr, classify]
    split
    · next a h =>
      split at h
      · cases h; rfl
      · cases h
    · rfl

/-- **Operands' loads write no slot.** -/
theorem noSlotWrD_getOps {fr : Scc.Emit.X64.Frame} :
    ∀ {l : List (Scc.IR.Operand × Reg64)} {c : List Item}, getOps fr l = .ok c → noSlotWrD (dirs c) = true
  | [], c, h => by cases h; rfl
  | (a, r) :: rest, c, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    rw [dirs_append, noSlotWrD_append, noSlotWrD_getOp ha, noSlotWrD_getOps hr]; rfl

theorem noSlotWrD_epi : noSlotWrD Spike.Lib.X64.epi = true := rfl

/-- **A construct's directives write no slot before their last.** -/
theorem noSlotWrD_kindD {fr : Scc.Emit.X64.Frame} {ds : List Directive} (hk : KindD fr ds) :
    noSlotWrD ds.dropLast = true := by
  rcases hk with ⟨a, b, la, lb, ha, hb, rfl | rfl | ⟨T, rfl⟩⟩ | ⟨d, o, -, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · refine noSlotWrD_dropLast ?_
    rw [addDirs, dirs_append, dirs_append, noSlotWrD_append, noSlotWrD_append, noSlotWrD_getOp ha,
      noSlotWrD_getOp hb]; rfl
  · refine noSlotWrD_dropLast ?_
    rw [subDirs, dirs_append, dirs_append, noSlotWrD_append, noSlotWrD_append, noSlotWrD_getOp ha,
      noSlotWrD_getOp hb]; rfl
  · refine noSlotWrD_dropLast ?_
    rw [brDirs, dirs_append, dirs_append, noSlotWrD_append, noSlotWrD_append, noSlotWrD_getOp ha,
      noSlotWrD_getOp hb]; rfl
  · rfl
  · rfl
  · refine noSlotWrD_dropLast ?_
    rw [retDirs, dirs_append, noSlotWrD_append, noSlotWrD_getOp hg, dirs_epiItems]; rfl

/-- **An `Accepted2` construct's directives write no slot before their
last.** -/
theorem noSlotWrD_kindD2 {fr : Scc.Emit.X64.Frame} {ds : List Directive} (hk : KindD2 fr ds) :
    noSlotWrD ds.dropLast = true := by
  rcases hk with hk | ⟨ws, lw, -, hg, rfl⟩
  · exact noSlotWrD_kindD hk
  · refine noSlotWrD_dropLast ?_
    rw [retDirs, dirs_append, noSlotWrD_append, noSlotWrD_getOps hg, dirs_epiItems]; rfl

theorem noSlotWr_kind1 {fr : Scc.Emit.X64.Frame} {blk : List (Directive × Nat)} (hk : Kind1 fr blk) :
    noSlotWr blk.dropLast = true :=
  noSlotWr_dropLast (noSlotWrD_kindD hk)

theorem noSlotWr_kind2 {fr : Scc.Emit.X64.Frame} {blk : List (Directive × Nat)} (hk : Kind2 fr blk) :
    noSlotWr blk.dropLast = true :=
  noSlotWr_dropLast (noSlotWrD_kindD2 hk)

/-- **A one-cell block writes no slot before its last** (a store, a
`callq`). -/
theorem noSlotWr_single (d : Directive) (z : Nat) : noSlotWr [(d, z)].dropLast = true := rfl

/--
info: 'Spike.Lib.LowerX64.noSlotWr_kind2' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms noSlotWr_kind2

end Spike.Lib.LowerX64
