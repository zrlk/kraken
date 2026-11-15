/-
**AArch64 code at another base, or with a tail appended** (shared by the
linked proofs of post-pass texts): the granule pass leaves the pre-pass
cells unchanged, re-places `scc_text_end` after a tail (a `.zero` filler,
`.Lgw0:`, one descriptor word), and the post-pass executable's code base
moves. These are the facts of the canonical loader's code labels
(`Scc.Cert.Link.A64.codeOf`), code end and thread
(`Scc/Sem/TargetA64.lean`), and of the runtime's phase table and sites
(`Scc/Cert/Rt/PhasesA64.lean`), under both changes; the label facts are
`Spike/Lib/TextTail.lean`'s.

- `codeOf_shift`, `codeOf_append_of`, `codeOf_append_none`: a code label at
  another base, or with a tail appended;
- `codeEnd_shift`, `codeEnd_append`: the end of the code under both;
- `threadAt_append_st`: the loaded thread's machine state does not see the
  tail;
- `phTabBy_mono`, `phTabOf_append_of`, `phOf_append_of`: the phase table
  and phases keep their values once every row label resolves in the cells;
- `phTabShift`, `ph_shift`, `phTabOf_shift`, `phOf_shift`: they move with
  the base (no wrap past `2 ^ 64`);
- `sitesOf_shift`, `sitesOf_append_of`, `okPcOf_shift`, `okPcOf_append_of`:
  the sites and the pcs off them, likewise.
-/
import Spike.Lib.TextTail
import Scc.Cert.Rt.PhasesA64

namespace Spike.Lib.A64TextTail

open Scc.Sem Scc.Sem.A64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (PhRange PhTab phTabBy phTabOf phOf inRs sitesBy sitesOf okPcOf siteLabels bPR bLR bNR bTR)

/-! ## Code labels, end and thread -/

/-- **A code label's address moves with the code base.** -/
theorem codeOf_shift (lo δ : Nat) (prog : Program) (l : String) :
    codeOf (lo + δ) prog l = (codeOf lo prog l).map (· + δ) :=
  TextTail.labelAddr_shift _ _ l δ prog lo

/-- **A code label of the cells keeps its address with a tail appended.** -/
theorem codeOf_append_of {lo : Nat} {prog : Program} {l : String} {a : Nat} (T : Program)
    (h : codeOf lo prog l = some a) : codeOf lo (prog ++ T) l = some a :=
  TextTail.labelAddr_append_of T h

/-- **A code label not in the cells is the tail's**, laid out from the end
of the cells' code. -/
theorem codeOf_append_none {lo : Nat} {prog : Program} {l : String} (T : Program)
    (h : codeOf lo prog l = none) : codeOf lo (prog ++ T) l = codeOf (codeEnd lo prog) T l :=
  TextTail.labelAddr_append_none T h

/-- **A code label lies at most at the end of the code.** -/
theorem codeOf_le {lo : Nat} {prog : Program} {l : String} {a : Nat} (h : codeOf lo prog l = some a) :
    a ≤ codeEnd lo prog :=
  TextTail.labelAddr_le h

/-- **The end of the code moves with the code base.** -/
theorem codeEnd_shift (lo δ : Nat) (prog : Program) : codeEnd (lo + δ) prog = codeEnd lo prog + δ := by
  simp only [codeEnd]; omega

/-- **The end of the code with a tail appended**: the tail's bytes after
the cells' end. -/
theorem codeEnd_append (lo : Nat) (prog T : Program) : codeEnd lo (prog ++ T) = codeEnd (codeEnd lo prog) T := by
  simp only [codeEnd, List.map_append, List.sum_append, Nat.add_assoc]

/-- **The loaded thread's machine state does not see the tail**: registers,
private memory and pc are those of the thread of the cells alone (only the
executable and its end differ). -/
theorem threadAt_append_st (E : Entry) (base : Nat) (prog T : Program) (syms : List (String × Nat)) :
    (threadAt E base (prog ++ T) syms).st = (threadAt E base prog syms).st :=
  rfl

/-! ## Option lists -/

/-- `mapM` into `Option` keeps its result under a function agreeing on
every value the first returns. -/
theorem mapM_some_mono {α β : Type} {f g : α → Option β} (hfg : ∀ x y, f x = some y → g x = some y) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → xs.mapM g = some ys
  | [], _, h => by simpa using h
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h ⊢
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    exact ⟨y, hfg x y hy, ys', mapM_some_mono hfg hys, rfl⟩

/-- `mapM` into `Option` of a function mapped by `h`: the results mapped by
`h`. -/
theorem mapM_map {α β : Type} {f g : α → Option β} {h : β → β} :
    ∀ {xs : List α}, (∀ x ∈ xs, g x = (f x).map h) → xs.mapM g = (xs.mapM f).map (List.map h)
  | [], _ => rfl
  | x :: xs, hg => by
    have ih := mapM_map (xs := xs) fun y hy => hg y (List.mem_cons_of_mem x hy)
    rw [List.mapM_cons, List.mapM_cons, hg x (List.mem_cons_self ..), ih]
    cases f x <;> cases xs.mapM f <;> rfl

/-! ## The phase table -/

/-- A range's bounds keep their values under a resolver agreeing on every
label the first resolves. -/
theorem resolve_mono {code code' : String → Option Nat} (hc : ∀ l a, code l = some a → code' l = some a)
    {r : PhRange} {x : Nat × Nat} (h : r.resolve code = some x) : r.resolve code' = some x := by
  unfold PhRange.resolve at h ⊢
  split at h
  · rename_i a b ha hb; rw [hc _ _ ha, hc _ _ hb]; exact h
  · cases h

/-- **The phase table keeps its value** under a resolver agreeing on every
label the first resolves. -/
theorem phTabBy_mono {code code' : String → Option Nat} (hc : ∀ l a, code l = some a → code' l = some a)
    {T : PhTab} (h : phTabBy code = some T) : phTabBy code' = some T := by
  have hm : ∀ {xs : List PhRange} {ys : List (Nat × Nat)}, xs.mapM (PhRange.resolve code) = some ys →
      xs.mapM (PhRange.resolve code') = some ys :=
    mapM_some_mono fun _ _ => resolve_mono hc
  simp only [phTabBy, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h ⊢
  obtain ⟨p, hp, l, hl, n, hn, t, ht, rfl⟩ := h
  exact ⟨p, hm hp, l, hm hl, n, hm hn, t, hm ht, rfl⟩

/-- **The phase table of the cells is that of the cells with a tail**, once
every row label resolves in the cells. -/
theorem phTabOf_append_of {lo : Nat} {prog : Program} {T : PhTab} (tl : Program) (h : phTabOf lo prog = some T) :
    phTabOf lo (prog ++ tl) = some T :=
  phTabBy_mono (fun _ _ => codeOf_append_of tl) h

/-- **The phases of the cells are those of the cells with a tail**, once
every row label resolves in the cells. -/
theorem phOf_append_of {lo : Nat} {prog : Program} {T : PhTab} (tl : Program) (h : phTabOf lo prog = some T) :
    phOf lo (prog ++ tl) = phOf lo prog := by
  simp only [phOf, phTabOf_append_of tl h, h]

/-- The table's ranges moved by `δ`. -/
def phTabShift (δ : Nat) (T : PhTab) : PhTab :=
  let sh := fun (r : Nat × Nat) => (r.1 + δ, r.2 + δ)
  ⟨T.p.map sh, T.l.map sh, T.n.map sh, T.t.map sh⟩

/-- A pc moved by `δ` is in the ranges moved by `δ` iff the pc is in the
ranges. -/
theorem inRs_shift (δ : Nat) (rs : List (Nat × Nat)) (pc : Nat) :
    inRs (rs.map fun r => (r.1 + δ, r.2 + δ)) (pc + δ) = inRs rs pc := by
  simp only [inRs, List.any_map]
  congr 1
  funext r
  simp only [Function.comp]
  by_cases h1 : r.1 ≤ pc <;> by_cases h2 : pc < r.2 <;> simp [h1, h2] <;> omega

/-- **The phase of a pc moved by `δ`** in the table moved by `δ`. -/
theorem ph_shift (δ : Nat) (T : PhTab) (pc : Nat) : (phTabShift δ T).ph (pc + δ) = T.ph pc := by
  simp only [phTabShift, PhTab.ph, inRs_shift]

/-- Every range offset of the phase table is at most `38` instructions. -/
theorem phRanges_off : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.o1 ≤ 38 ∧ r.o2 ≤ 38 := by decide

/-- A range resolved at labels moved by `δ` is the range moved by `δ`, when
no label's address with the offset wraps past `2 ^ 64`. -/
theorem resolve_shift {code : String → Option Nat} {δ : Nat}
    (hb : ∀ l a, code l = some a → a + δ + 256 < 2 ^ 64) {r : PhRange} (ho : r.o1 ≤ 38 ∧ r.o2 ≤ 38) :
    r.resolve (fun l => (code l).map (· + δ)) = (r.resolve code).map fun x => (x.1 + δ, x.2 + δ) := by
  unfold PhRange.resolve
  simp only
  cases ha : code r.l1 with
  | none => simp
  | some a =>
    cases hb' : code r.l2 with
    | none => simp
    | some b =>
      have h1 := hb _ _ ha
      have h2 := hb _ _ hb'
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor <;> rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] <;> omega

/-- **The phase table moves with the code base**, when no label's address
with its offset wraps past `2 ^ 64` (the code's end at the moved base, plus
`256`, below `2 ^ 64`). -/
theorem phTabOf_shift (lo δ : Nat) (prog : Program) (hb : codeEnd (lo + δ) prog + 256 < 2 ^ 64) :
    phTabOf (lo + δ) prog = (phTabOf lo prog).map (phTabShift δ) := by
  have hc : ∀ l a, codeOf lo prog l = some a → a + δ + 256 < 2 ^ 64 := fun l a h => by
    have := codeOf_le h; rw [codeEnd_shift] at hb; omega
  have hr : ∀ rs : List PhRange, (∀ r ∈ rs, r.o1 ≤ 38 ∧ r.o2 ≤ 38) →
      rs.mapM (PhRange.resolve (codeOf (lo + δ) prog)) =
        (rs.mapM (PhRange.resolve (codeOf lo prog))).map (List.map fun x => (x.1 + δ, x.2 + δ)) :=
    fun rs ho => mapM_map fun r hr => by
      rw [show codeOf (lo + δ) prog = fun l => (codeOf lo prog l).map (· + δ) from funext (codeOf_shift lo δ prog)]
      exact resolve_shift hc (ho r hr)
  have hP := hr bPR fun r h => phRanges_off r (by simp [h])
  have hL := hr bLR fun r h => phRanges_off r (by simp [h])
  have hN := hr bNR fun r h => phRanges_off r (by simp [h])
  have hT := hr bTR fun r h => phRanges_off r (by simp [h])
  simp only [phTabOf, phTabBy, hP, hL, hN, hT]
  cases bPR.mapM (PhRange.resolve (codeOf lo prog)) <;>
    cases bLR.mapM (PhRange.resolve (codeOf lo prog)) <;>
    cases bNR.mapM (PhRange.resolve (codeOf lo prog)) <;>
    cases bTR.mapM (PhRange.resolve (codeOf lo prog)) <;> rfl

/-- **The phase of a pc moves with the code base**, when no label's
address with its offset wraps past `2 ^ 64`. -/
theorem phOf_shift (lo δ : Nat) (prog : Program) (hb : codeEnd (lo + δ) prog + 256 < 2 ^ 64) (pc : Nat) :
    phOf (lo + δ) prog (pc + δ) = phOf lo prog pc := by
  simp only [phOf, phTabOf_shift lo δ prog hb]
  cases phTabOf lo prog with
  | none => rfl
  | some T => exact ph_shift δ T pc

/-! ## The sites -/

/-- **The sites move with the code base.** -/
theorem sitesOf_shift (lo δ : Nat) (prog : Program) (Λ : Scc.Sem.Layout) :
    sitesOf (lo + δ) prog Λ = (sitesOf lo prog Λ).map (List.map (· + δ)) :=
  mapM_map fun l _ => codeOf_shift lo δ prog l

/-- **The sites of the cells are those of the cells with a tail**, once
every site label resolves in the cells. -/
theorem sitesOf_append_of {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {ss : List Nat} (tl : Program)
    (h : sitesOf lo prog Λ = some ss) : sitesOf lo (prog ++ tl) Λ = some ss :=
  mapM_some_mono (fun _ _ => codeOf_append_of tl) h

/-- **A pc moved by `δ` is off the sites moved by `δ`** iff the pc is off
the sites. -/
theorem okPcOf_shift (lo δ : Nat) (prog : Program) (Λ : Scc.Sem.Layout) (pc : Nat) :
    okPcOf (lo + δ) prog Λ (pc + δ) = okPcOf lo prog Λ pc := by
  simp only [okPcOf, sitesOf_shift]
  cases sitesOf lo prog Λ with
  | none => rfl
  | some ss =>
    simp only [Option.map_some]
    congr 1
    simp only [List.contains_eq_any_beq, List.any_map]
    congr 1
    funext x
    simp only [Function.comp]
    by_cases h : pc = x
    · rw [h, beq_self_eq_true, beq_self_eq_true]
    · have h' : pc + δ ≠ x + δ := fun e => h (by omega)
      rw [beq_false_of_ne h', beq_false_of_ne h]

/-- **The pcs off the sites of the cells are those of the cells with a
tail**, once every site label resolves in the cells. -/
theorem okPcOf_append_of {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {ss : List Nat} (tl : Program)
    (h : sitesOf lo prog Λ = some ss) : okPcOf lo (prog ++ tl) Λ = okPcOf lo prog Λ := by
  funext pc
  simp only [okPcOf, sitesOf_append_of tl h, h]

end Spike.Lib.A64TextTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64TextTail.codeOf_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.codeOf_shift

/-- info: 'Spike.Lib.A64TextTail.codeOf_append_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.codeOf_append_of

/-- info: 'Spike.Lib.A64TextTail.codeOf_append_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.codeOf_append_none

/-- info: 'Spike.Lib.A64TextTail.codeEnd_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.codeEnd_append

/-- info: 'Spike.Lib.A64TextTail.phTabOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.phTabOf_append_of

/-- info: 'Spike.Lib.A64TextTail.phOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.phOf_append_of

/-- info: 'Spike.Lib.A64TextTail.phTabOf_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.phTabOf_shift

/-- info: 'Spike.Lib.A64TextTail.phOf_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.phOf_shift

/-- info: 'Spike.Lib.A64TextTail.sitesOf_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.sitesOf_shift

/-- info: 'Spike.Lib.A64TextTail.sitesOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.sitesOf_append_of

/-- info: 'Spike.Lib.A64TextTail.okPcOf_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.okPcOf_shift

/-- info: 'Spike.Lib.A64TextTail.okPcOf_append_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64TextTail.okPcOf_append_of
