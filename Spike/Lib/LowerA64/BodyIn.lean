/-
**The emitted body's placement, from the function's context** (AArch64).

`bodyIn prog cx L n o insts ret`: a closed Boolean that walks a lowered
body's instructions (`Scc.Lower.Inv.lower0`'s `addChk` sequence, then the
return of `ret`), keeping the current label `L` (the body's, then each
fresh label `retL cx n`, P5) and the running instruction offset `o` after
it. For each instruction it emits the construct's directives from the
context `cx` (`getOp`, `addChecked`, the slot store; the return's
`getOp ++ leave`, then `[ret]` after its label) and checks each one with
`blockAt` at its offset, each fresh label right after the code before it
(`labelGap`). `bodyCode_in` turns the check into `BodyCode` in any valid
layout (the return's code across its label, `cd_ret`), `bodyCode_of`
without the blocks' offsets. The
check is discharged per program by `decide +kernel`. It reads only the
listing's instruction run after `l`, independent of how `--blocks` groups
it.
-/
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.Checks
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64CodeAcross

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}

/-- `4 * (e + o)` instructions after `l` is `o` after `L`, `4 * e` after `l`. -/
private theorem pc_split {a b : Int64} {e o : Nat} (h : b = a + Int64.ofNat (4 * e)) :
    a + Int64.ofNat (4 * (e + o)) = b + Int64.ofNat (4 * o) := by
  rw [h, Int64.add_assoc, ← Int64.ofNat_add, Nat.mul_add]

private theorem pc_add (x : Int64) (a b : Nat) :
    x + Int64.ofNat (4 * (a + b)) = x + Int64.ofNat (4 * a) + Int64.ofNat (4 * b) := by
  rw [Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]

/-- **The return's code across its label**: the load and the frame exit
`o` instructions after `L`, `[ret]` at the return site's label right after
them, are the return's code. -/
theorem cd_ret {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {cx : FnCtx} {L m : Label}
    {o : Nat} {lw : List Item} (h1 : blockAt prog L o (tearDirs cx lw) = true)
    (hg : labelGap prog L m (o + (tearDirs cx lw).length) = true) (h2 : blockAt prog m 0 (directives [ret]) = true) :
    CdOf exe endPc ((_root_.Executable.labels exe).label L + Int64.ofNat (4 * o)) (directives (lw ++ cx.leave ++ [ret])) :=
  fun _ hs hn => by
    rw [directives_append]
    exact Spike.Lib.A64.codeAt_across hp hs (hn.trans hend) h1 hg h2

/-- The code predicate of a body's blocks: the code at `pc`, and `blk` one
of `S`'s blocks at its offset after `l`. -/
def CdIn (exe : _root_.Executable) (endPc : Int64) (l : Label) (S : List (Nat × List Directive)) (pc : Int64)
    (blk : List Directive) : Prop :=
  CdOf exe endPc pc blk ∧ ∃ j, pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * j) ∧ (j, blk) ∈ S

/-- **`bodyIn` gives the body's code with its blocks' offsets**: `BodyCode`
at every block of `bodyBlks` among `S`'s, from the current label `L`, `e`
instructions after `l`, `o` instructions into `L`'s run, the next
instruction numbered `n`. -/
theorem bodyCode_in {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {cx : FnCtx} {l : Label}
    {S : List (Nat × List Directive)} :
    ∀ (is : List Scc.IR.Inst) (L : Label) (n e o : Nat) (ws : List Scc.IR.Operand),
      bodyIn prog cx L n o is ws = true →
      (_root_.Executable.labels exe).label L = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * e) →
      (∀ x ∈ bodyBlks cx (e + o) is ws, x ∈ S) →
      BodyCode cx (CdIn exe endPc l S) ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * (e + o))) is ws := by
  intro is
  induction is with
  | nil =>
    intro L n e o ws h hL hS
    match ws, h with
    | [w], h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg, Bool.and_eq_true] at h
        obtain ⟨⟨h1, hgap⟩, h2⟩ := h
        rw [pc_split hL]
        exact ⟨lw, hg, cd_ret hp hend h1 hgap h2, e + o, pc_split hL |>.symm,
          hS _ (by simp [bodyBlks, hg])⟩
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro L n e o ws h hL hS
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.ok la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨h1, hgap⟩, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd, List.mem_cons] at hS
        have hR := label_labelGap hp hgap
        have hR' : (_root_.Executable.labels exe).label (retL cx n) =
            (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (e + o + (addDirs cx la lb).length)) := by
          rw [hR, ← pc_split hL]; simp only [Nat.add_assoc]
        refine ⟨la, lb, off, ha, hb, hd, ⟨code_of hp hend h1 (pc_split hL).symm, e + o, rfl, hS _ (.inl rfl)⟩,
          ⟨code_of hp hend h2 ?_, _, ?_, hS _ (.inr (.inl rfl))⟩, ?_⟩
        · rw [ofNat4_zero, hR', pc_add]; rfl
        · exact (pc_add _ _ _).symm
        · have := ih (retL cx n) (n + 1) (e + o + (addDirs cx la lb).length) 1 ws h3 hR'
            fun x hx => hS x (.inr (.inr hx))
          rw [pc_add, pc_add] at this
          exact this
    all_goals simp [bodyIn] at h

/-- **Every block of `bodyBlks` is in the code** at its offset after `l`:
from the current label `L`, `e` instructions after `l`, `o` instructions
into `L`'s run (the return's block across its label by `cd_ret`). -/
theorem cdOf_bodyBlks {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {cx : FnCtx}
    {l : Label} :
    ∀ (is : List Scc.IR.Inst) (L : Label) (n e o : Nat) (ws : List Scc.IR.Operand) {j : Nat} {blk : List Directive},
      bodyIn prog cx L n o is ws = true →
      (_root_.Executable.labels exe).label L = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * e) →
      (j, blk) ∈ bodyBlks cx (e + o) is ws →
      CdOf exe endPc ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * j)) blk := by
  intro is
  induction is with
  | nil =>
    intro L n e o ws j blk h hL hm
    match ws, h with
    | [w], h =>
      cases hg : cx.getOp .X0 w with
      | error e => simp [bodyIn, hg] at h
      | ok lw =>
        simp only [bodyIn, hg, Bool.and_eq_true] at h
        obtain ⟨⟨h1, hgap⟩, h2⟩ := h
        simp only [bodyBlks, hg, List.mem_singleton, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        rw [pc_split hL]
        exact cd_ret hp hend h1 hgap h2
    | [], h => simp [bodyIn] at h
    | _ :: _ :: _, h => simp [bodyIn] at h
  | cons i is ih =>
    intro L n e o ws j blk h hL hm
    cases i
    case addChk d a b =>
      cases ha : cx.getOp .X9 a <;> cases hb : cx.getOp .X10 b <;> cases hd : cx.slotOff d <;>
        simp only [bodyIn, ha, hb, hd, reduceCtorEq] at h
      case ok.ok.ok la lb off =>
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨h1, hgap⟩, h2⟩, h3⟩ := h
        simp only [bodyBlks, ha, hb, hd] at hm
        have hR := label_labelGap hp hgap
        have hR' : (_root_.Executable.labels exe).label (retL cx n) =
            (_root_.Executable.labels exe).label l + Int64.ofNat (4 * (e + o + (addDirs cx la lb).length)) := by
          rw [hR, ← pc_split hL]; simp only [Nat.add_assoc]
        rcases List.mem_cons.mp hm with hm | hm
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
          exact code_of hp hend h1 (pc_split hL).symm
        rcases List.mem_cons.mp hm with hm | hm
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
          exact code_of hp hend h2 (by rw [ofNat4_zero, hR'])
        · exact ih _ _ _ _ ws h3 hR' hm
    all_goals simp [bodyIn] at h

/-- **`bodyIn` gives the body's code at its blocks** (`InBody`). -/
theorem bodyCode_inBody {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {cx : FnCtx} {l : Label}
    {n : Nat} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} (h : bodyIn prog cx l n 0 is ws = true) :
    BodyCode cx (CdIn exe endPc l (bodyBlks cx 0 is ws)) ((_root_.Executable.labels exe).label l) is ws := by
  have := bodyCode_in (S := bodyBlks cx 0 is ws) hp hend is l n 0 0 ws h (ofNat4_zero _).symm fun _ hx => hx
  rwa [ofNat4_zero] at this

/-- `BodyCode` under a weaker code predicate. -/
theorem BodyCode.mono {cx : FnCtx} {Cd Cd' : Int64 → List Directive → Prop} (hm : ∀ pc blk, Cd pc blk → Cd' pc blk) :
    ∀ {pc : Int64} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand}, BodyCode cx Cd pc is ws → BodyCode cx Cd' pc is ws
  | _, [], [_], ⟨l, hg, hc⟩ => ⟨l, hg, hm _ _ hc⟩
  | _, .addChk .. :: _, _, ⟨la, lb, off, ha, hb, hd, h1, h2, hr⟩ => ⟨la, lb, off, ha, hb, hd, hm _ _ h1, hm _ _ h2, BodyCode.mono hm hr⟩

/-- **`bodyIn` gives the body's code** in any valid layout of `prog`. -/
theorem bodyCode_of {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) {cx : FnCtx} {l : Label}
    {n : Nat} {is : List Scc.IR.Inst} {ws : List Scc.IR.Operand} (h : bodyIn prog cx l n 0 is ws = true) :
    BodyCode cx (CdOf exe endPc) ((_root_.Executable.labels exe).label l) is ws :=
  BodyCode.mono (fun _ _ hc => hc.1) (bodyCode_inBody hp hend h)

end Code

end Spike.Lib.LowerA64
