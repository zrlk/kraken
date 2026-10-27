/-
**`CodeC2`'s arms** (AArch64): the code of a checked `+`, a saturating `-`,
an `if` and a `ret` of any number of words in a block of `CodeC2`, the
`Accepted2` twins of `Spike/Lib/LowerA64/BodyC.lean`'s `codeC_addChk`,
`codeC_subSat`, `codeC_br` and `codeC_ret`.

- `retLoads`, `term_retN_inv`: a `ret`'s terminator code is its words'
  loads into `x0`, `x1`, … (`retLoads`), the frame's exit and `ret`.
- `codeC2_addChk`, `codeC2_subSat`, `codeC2_br`, `codeC2_ret`, `codeC2_retN`.
-/
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.LowerA64.BlocksC2Code

namespace Spike.Lib.LowerA64

open Kraken Kraken.AArch64.Parser
open Scc.Emit.A64 Scc.Lower.InvA64

set_option linter.unusedSimpArgs false

/-! ## A `ret`'s terminator code -/

theorem forIn_retLoads (cx : FnCtx) :
    ∀ (ps : List (Scc.IR.Operand × XReg)) (out : List Item),
      (forIn (m := Except String) ps out fun (x : Scc.IR.Operand × XReg) (r : List Item) => do
          let l ← cx.getOp x.2 x.1
          pure (ForInStep.yield (r ++ l))) = (retLoads cx ps).map (out ++ ·)
  | [], out => by simp [retLoads, pure, Except.pure, Except.map]
  | (v, r) :: ps, out => by
    rw [List.forIn_cons]
    cases hv : cx.getOp r v with
    | error e => simp [hv, retLoads, bind, Except.bind, Except.map]
    | ok l =>
      have ih := forIn_retLoads cx ps (out ++ l)
      simp only [hv, retLoads, bind, Except.bind, pure, Except.pure] at ih ⊢
      rw [ih]
      cases retLoads cx ps <;> simp [Except.map]

/-- **A `ret`'s terminator code**: at most `maxRets` words, their loads
into `x0`, `x1`, … (`retLoads`), the frame's exit and `ret`. -/
theorem term_retN_inv {cx : FnCtx} {k : Nat} {vs : List Scc.IR.Operand} {c2 : List Item}
    (h : cx.term k (.ret vs) = .ok c2) :
    vs.length ≤ Scc.IR.maxRets ∧ ∃ ls, retLoads cx (vs.zip argRegs) = .ok ls ∧ c2 = ls ++ cx.leave ++ [ret] := by
  simp only [FnCtx.term] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · rename_i hl
    rw [forIn_retLoads] at h
    cases hr : retLoads cx (vs.zip argRegs) with
    | error e => simp [hr, Except.map, bind, Except.bind] at h
    | ok ls =>
      simp [hr, Except.map, bind, Except.bind, pure, Except.pure] at h
      exact ⟨by omega, ls, rfl, by rw [← h, List.append_assoc]⟩

/-! ## `CodeC2`'s arms -/

section Arms

variable {cx : FnCtx} {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}

/-- **A checked `+`'s code** in `CodeC2`: the add's block, then the store's,
then the rest. -/
theorem codeC2_addChk (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {k : Nat} {pc : Int64} {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {is : List Scc.IR.Inst} {tm : Scc.IR.Term}
    (h : CodeC2 cx Cd Bl k pc (.addChk d a b :: is) tm) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      SubCd Cd pc (addDirs cx la lb) ∧ SubCd Cd (pc + Int64.ofNat (4 * (addDirs cx la lb).length)) (strDirs off) ∧
      CodeC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (addDirs cx la lb).length) + 4) is tm := by
  rcases h with ⟨-, l, hl, hc, hrest⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩
  · obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_addChk_inv hf h1 hl
    rw [hds] at hc hrest
    refine ⟨la, lb, off, ha, hb, hd, SubCd.left hc, SubCd.right hc, ?_⟩
    rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hrest
    exact hrest
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he

/-- **A saturating `-`'s code** in `CodeC2`: the subtraction's block, then
the store's, then the rest. -/
theorem codeC2_subSat (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {k : Nat} {pc : Int64} {d : Scc.IR.Reg}
    {a b : Scc.IR.Operand} {is : List Scc.IR.Inst} {tm : Scc.IR.Term}
    (h : CodeC2 cx Cd Bl k pc (.subSat d a b :: is) tm) :
    ∃ la lb off, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧ cx.slotOff d = .ok off ∧
      SubCd Cd pc (subDirs la lb) ∧ SubCd Cd (pc + Int64.ofNat (4 * (subDirs la lb).length)) (strDirs off) ∧
      CodeC2 cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (subDirs la lb).length) + 4) is tm := by
  rcases h with ⟨-, l, hl, hc, hrest⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩
  · obtain ⟨la, lb, off, ha, hb, hd, hds⟩ := inst_subSat_inv hf h1 hl
    rw [hds] at hc hrest
    refine ⟨la, lb, off, ha, hb, hd, SubCd.left hc, SubCd.right hc, ?_⟩
    rw [List.length_append, show (strDirs off).length = 1 from rfl, add_ofNat_four_succ] at hrest
    exact hrest
  · cases he
  · simp [Spike.Lib.LowerShape.newBufCall] at he
  · cases he

/-- **An `if`'s code** in `CodeC2`: the compare-and-branch's block, then the
`b` to the `else` label. -/
theorem codeC2_br {k : Nat} {pc : Int64} {a b : Scc.IR.Operand} {t f : Scc.IR.Label}
    (h : CodeC2 cx Cd Bl k pc [] (.br .eq a b t f)) :
    ∃ la lb T Fl, cx.getOp .X9 a = .ok la ∧ cx.getOp .X10 b = .ok lb ∧
      cx.blockLabel t = .ok T ∧ cx.blockLabel f = .ok Fl ∧ SubCd Cd pc (brDirs la lb T) ∧
      SubCd Cd (pc + Int64.ofNat (4 * (brDirs la lb T).length)) (jmpDirs Fl) :=
  codeC_br (Bl := Bl) h

/-- **A one-word `ret`'s code** in `CodeC2`: the word's load, the frame's
exit, `ret`. -/
theorem codeC2_ret {k : Nat} {pc : Int64} {w : Scc.IR.Operand} (h : CodeC2 cx Cd Bl k pc [] (.ret [w])) :
    ∃ l, cx.getOp .X0 w = .ok l ∧ SubCd Cd pc (directives (l ++ cx.leave ++ [ret])) :=
  codeC_ret (Bl := Bl) h

/-- **A `ret`'s code** in `CodeC2`, of any number of words: at most
`maxRets`, their loads into `x0`, `x1`, … (`retLoads`), the frame's exit,
`ret`. -/
theorem codeC2_retN {k : Nat} {pc : Int64} {ws : List Scc.IR.Operand} (h : CodeC2 cx Cd Bl k pc [] (.ret ws)) :
    ws.length ≤ Scc.IR.maxRets ∧ ∃ ls, retLoads cx (ws.zip argRegs) = .ok ls ∧
      SubCd Cd pc (directives (ls ++ cx.leave ++ [ret])) := by
  rcases h with h | ⟨l, hl, hc⟩
  · cases h
  · obtain ⟨hn, ls, hr, rfl⟩ := term_retN_inv hl
    exact ⟨hn, ls, hr, SubCd.whole hc⟩

end Arms

/-- info: 'Spike.Lib.LowerA64.codeC2_retN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms codeC2_retN

end Spike.Lib.LowerA64
