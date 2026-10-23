/-
**The emitted body's placement, from the function's context** (AArch64).

`bodyIn prog cx l k insts ret`: a closed Boolean that walks a lowered
body's instructions (`Scc.Lower.Inv.lower0`'s `addChk` sequence, then the
return of `ret`), keeping a running instruction offset `k` after the label
`l`. For each instruction it emits the construct's directives from the
context `cx` (`getOp`, `addChecked`, the slot store; the return's
`getOp ++ leave ++ [ret]`) and checks each one with `blockAt` at its offset.
`bodyCode_of` turns the check into `BodyCode` in any valid layout. The
check is discharged per program by `decide +kernel`. It reads only the
listing's instruction run after `l`, independent of how `--blocks` groups
it.
-/
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.Checks
import Spike.Lib.A64CodeSegs

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}

/-- **`bodyIn` gives the body's code** in any valid layout of `prog`. -/
theorem bodyCode_of (hp : Lays exe prog) (hend : endPc = endOf exe prog) {cx : FnCtx} {l : Label} :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (ws : List Scc.IR.Operand), bodyIn prog cx l k is ws = true →
      BodyCode cx (CdOf exe endPc) ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) is ws := by
  intro is
  induction is with
  | nil =>
    intro k ws h
    match ws, h with
    | [w], h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg] at h
        exact ⟨lw, hg, code_of hp hend h rfl⟩
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro k ws h
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.ok la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        refine ⟨la, lb, off, ha, hb, hd, code_of hp hend h1 rfl,
          code_of hp hend h2 (ofNat4_add _ _ _), ?_⟩
        have := ih _ ws h3
        rwa [ofNat4_succ, ofNat4_add] at this
    all_goals simp [bodyIn] at h

/-- The code predicate of a body's blocks: the code at `pc`, and `blk` one
of `S`'s blocks at its offset after `l`. -/
def CdIn (exe : _root_.Executable) (endPc : Int64) (l : Label) (S : List (Nat × List Directive)) (pc : Int64)
    (blk : List Directive) : Prop :=
  CdOf exe endPc pc blk ∧ ∃ j, pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * j) ∧ (j, blk) ∈ S

/-- **`bodyIn` gives the body's code with its blocks' offsets**: `BodyCode`
at every block of `bodyBlks` among `S`'s. -/
theorem bodyCode_in (hp : Lays exe prog) (hend : endPc = endOf exe prog) {cx : FnCtx} {l : Label}
    {S : List (Nat × List Directive)} :
    ∀ (is : List Scc.IR.Inst) (k : Nat) (ws : List Scc.IR.Operand), bodyIn prog cx l k is ws = true →
      (∀ x ∈ bodyBlks cx k is ws, x ∈ S) →
      BodyCode cx (CdIn exe endPc l S) ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) is ws := by
  intro is
  induction is with
  | nil =>
    intro k ws h hS
    match ws, h with
    | [w], h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg] at h
        exact ⟨lw, hg, code_of hp hend h rfl, k, rfl, hS _ (by simp [bodyBlks, hg])⟩
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro k ws h hS
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.ok la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨h1, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd, List.mem_cons] at hS
        refine ⟨la, lb, off, ha, hb, hd, ⟨code_of hp hend h1 rfl, k, rfl, hS _ (.inl rfl)⟩,
          ⟨code_of hp hend h2 (ofNat4_add _ _ _), _, (ofNat4_add _ _ _).symm, hS _ (.inr (.inl rfl))⟩, ?_⟩
        have := ih _ ws h3 fun x hx => hS x (.inr (.inr hx))
        rwa [ofNat4_succ, ofNat4_add] at this
    all_goals simp [bodyIn] at h

/-- **`bodyIn` gives the body's code at its blocks** (`InBody`). -/
theorem bodyCode_inBody (hp : Lays exe prog) (hend : endPc = endOf exe prog) {cx : FnCtx} {l : Label}
    {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} (h : bodyIn prog cx l 0 is ws = true) :
    BodyCode cx (CdIn exe endPc l (bodyBlks cx 0 is ws)) ((_root_.Executable.labels exe).label l) is ws := by
  have := bodyCode_in (S := bodyBlks cx 0 is ws) hp hend is 0 ws h fun _ hx => hx
  rwa [ofNat4_zero] at this

end Code

end Spike.Lib.LowerA64
