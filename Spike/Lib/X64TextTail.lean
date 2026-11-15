/-
**Code laid out at another base, or with a tail appended** (x86-64; shared
by the linked proofs of post-pass texts): the granule pass leaves the
pre-pass cells unchanged and appends a tail (a `.zero` filler, `.Lgw0:`, one
descriptor word, `scc_text_end:`), and the post-pass executable's code base
moves. These are the facts of the canonical loader's layout functions
(`Scc/Sem/Target.lean`, `Scc/Sem/TargetX64.lean`) under both changes, from
the ISA-neutral `labelAddr` facts (`Spike/Lib/TextTail.lean`).

- `codeLabel_shift`: a label's address moves with the base;
- `codeLabel_append_of`: a label of the cells keeps its address with a tail
  appended (first occurrence);
- `codeLabel_append_none`: a label not in the cells is the tail's, laid out
  from the cells' end;
- `codeEnd_shift`, `codeEnd_append`: the end of the code under both;
- `threadAt_append_st`: the loaded thread's machine state does not see the
  tail;
- `codeLabel_none_of`, `codeLabel_tail`: cells naming no label hold none; a
  label other than the moved end label and the tail's is where it was.
-/
import Scc.Sem.TargetX64
import Spike.Lib.TextTail

namespace Spike.Lib.X64TextTail

open Scc.Sem Scc.Sem.X64
open Spike.Lib.TextTail (labelAddr_shift labelAddr_append_of labelAddr_append_none)

/-- **A code label's address moves with the code base.** -/
theorem codeLabel_shift (lo δ : Nat) (cells : List (Directive × Nat)) (l : String) :
    codeLabel (lo + δ) cells l = (codeLabel lo cells l).map (· + δ) :=
  labelAddr_shift _ _ l δ cells lo

/-- **A code label of the cells keeps its address with a tail appended.** -/
theorem codeLabel_append_of {lo : Nat} {cells : List (Directive × Nat)} {l : String} {a : Nat}
    (T : List (Directive × Nat)) (h : codeLabel lo cells l = some a) : codeLabel lo (cells ++ T) l = some a :=
  labelAddr_append_of T h

/-- **A code label not in the cells is the tail's**, laid out from the end
of the cells' code. -/
theorem codeLabel_append_none {lo : Nat} {cells : List (Directive × Nat)} {l : String}
    (T : List (Directive × Nat)) (h : codeLabel lo cells l = none) :
    codeLabel lo (cells ++ T) l = codeLabel (codeEnd lo cells) T l :=
  labelAddr_append_none T h

/-- **The end of the code moves with the code base.** -/
theorem codeEnd_shift (lo δ : Nat) (cells : List (Directive × Nat)) :
    codeEnd (lo + δ) cells = codeEnd lo cells + δ := by
  simp only [codeEnd]; omega

/-- **The end of the code with a tail appended**: the tail's bytes after
the cells' end. -/
theorem codeEnd_append (lo : Nat) (cells T : List (Directive × Nat)) :
    codeEnd lo (cells ++ T) = codeEnd (codeEnd lo cells) T := by
  simp only [codeEnd, List.map_append, List.sum_append, Nat.add_assoc]

/-- **The loaded thread's machine state does not see the tail**: registers,
private memory and pc are those of the thread of the cells alone (only the
executable and its end differ). -/
theorem threadAt_append_st (E : Entry) (base : Nat) (cells T : List (Directive × Nat))
    (syms : List (String × Nat)) : (threadAt E base (cells ++ T) syms).st = (threadAt E base cells syms).st :=
  rfl

/-- **Cells naming no label `l` hold no code label `l`.** -/
theorem codeLabel_none_of {l : String} : ∀ {b : Nat} {T : List (Directive × Nat)},
    (∀ dz ∈ T, dz.1 ≠ .label l) → codeLabel b T l = none
  | _, [], _ => rfl
  | b, (d, z) :: T, h => by
    have hd : labelName d ≠ some l := by
      cases d with
      | label l' =>
        intro he; cases he; exact h _ List.mem_cons_self rfl
      | _ => nofun
    show (if labelName d = some l then some b else codeLabel (b + z) T l) = none
    rw [if_neg hd]
    exact codeLabel_none_of fun dz hdz => h dz (List.mem_cons_of_mem _ hdz)

/-- **A code label other than the moved end label and the tail's** is at the
same address in the cells closed by the end label `te` and in the cells
followed by the tail `T`. -/
theorem codeLabel_tail {lo : Nat} {P T : List (Directive × Nat)} {te l : String} (hl : l ≠ te)
    (hT : ∀ dz ∈ T, dz.1 ≠ .label l) :
    codeLabel lo (P ++ [(.label te, 0)]) l = codeLabel lo (P ++ T) l := by
  cases h : codeLabel lo P l with
  | some a => rw [codeLabel_append_of _ h, codeLabel_append_of _ h]
  | none =>
    rw [codeLabel_append_none _ h, codeLabel_append_none _ h, codeLabel_none_of hT, codeLabel_none_of]
    intro dz hdz
    simp only [List.mem_singleton] at hdz
    subst hdz
    intro he; cases he; exact hl rfl

end Spike.Lib.X64TextTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64TextTail.codeLabel_shift' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64TextTail.codeLabel_shift

/-- info: 'Spike.Lib.X64TextTail.codeLabel_append_of' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64TextTail.codeLabel_append_of

/-- info: 'Spike.Lib.X64TextTail.codeLabel_append_none' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64TextTail.codeLabel_append_none

/-- info: 'Spike.Lib.X64TextTail.codeEnd_append' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64TextTail.codeEnd_append

/-- info: 'Spike.Lib.X64TextTail.codeLabel_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64TextTail.codeLabel_tail
