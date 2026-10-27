/-
**The shape of `lowerC2`'s blocks** (ISA-neutral): the instructions and
terminators the closed form `lowerC2` (`Spike/Lib/LowerShapeC2.lean`) emits,
the `Accepted2` twin of `Spike/Lib/LowerShapeC1.lean`'s `InstC`/`TermC`/
`BlockC`/`ResC`, read by each ISA's `codeC2_of_seg`.

- `InstC2`: checked `+`, saturating `-`, a one-result one-argument user
  call, `newBuf`'s call of the allocator (`newBufCall`), the `xchg`'s plain
  64-bit load and store (`xchgLoad`, `xchgStore`), and the output extern's
  block (`printInsts`: a 32-bit zero extension, an add, a multiply by 8, an
  unsigned-min `select`, the `print` call).
- `TermC2`: a `ret` of any number of words, an `if`'s `br .eq`.
- `BlockC2`, `ResC2`: a block, a closed form of that shape.
- `lowerC2_resC2`: `lowerC2` emits only `InstC2` instructions and `TermC2`
  terminators.
-/
import Spike.Lib.LowerShapeC2

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv

/-! ## The instructions and terminators -/

/-- **The instructions `lowerC2` emits.** -/
inductive InstC2 : Inst → Prop
  | addChk (d : Reg) (p q : Operand) : InstC2 (.addChk d p q)
  | subSat (d : Reg) (p q : Operand) : InstC2 (.subSat d p q)
  | call (d : Reg) (g : String) (w : Operand) : InstC2 (.call [d] (Names.user g) [w])
  | newBuf (p : Reg) (h : Nat) (kv : UInt64) (u : Operand) : InstC2 (newBufCall p h kv u)
  | load (d : Reg) (a : Addr) : InstC2 (xchgLoad d a)
  | store (a : Addr) (w : Operand) : InstC2 (xchgStore a w)
  | ext (d : Reg) (o : Operand) : InstC2 (.ext false .w32 d o)
  | add (d : Reg) (b : Operand) (s : Reg) : InstC2 (.bin .add d b (.reg s))
  | mul8 (d : Reg) (m : Operand) : InstC2 (.bin .mul d m (imm 8))
  | minU (d : Reg) (c : Operand) (s : Reg) : InstC2 (.select .ult d c (.reg s) c (.reg s))
  | print (a0 a1 : Operand) : InstC2 (.call [] Names.print [a0, a1])

/-- **The terminators `lowerC2` emits**: a `ret` of any number of words and
an `if`'s `br .eq`. -/
inductive TermC2 : Term → Prop
  | ret (ws : List Operand) : TermC2 (.ret ws)
  | br (p q : Operand) (t f : Label) : TermC2 (.br .eq p q t f)

/-- A block of `lowerC2`'s shape. -/
def BlockC2 (b : Block) : Prop := (∀ i ∈ b.insts, InstC2 i) ∧ TermC2 b.term

/-- A closed form of `lowerC2`'s shape: the open block's instructions and
terminator, and every later block. -/
def ResC2 (r : Res2) : Prop :=
  (∀ i ∈ r.insts, InstC2 i) ∧ TermC2 r.term ∧ ∀ b ∈ r.blocks, BlockC2 b

/-- **The output extern's block is of `InstC2`.** -/
theorem printInsts_instC2 (n : Nat) (b o m c : Operand) : ∀ i ∈ printInsts n b o m c, InstC2 i := by
  intro i hi
  simp only [printInsts, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact .ext _ _
  · exact .add _ _ _
  · exact .mul8 _ _
  · exact .minU _ _ _
  · exact .print _ _

/-- A closed form with instructions `is` before its open block's. -/
theorem ResC2.cons {r : Res2} (h : ResC2 r) {is : List Inst} (hi : ∀ i ∈ is, InstC2 i) :
    ResC2 { r with insts := is ++ r.insts } :=
  ⟨fun i hm => (List.mem_append.mp hm).elim (hi i) (h.1 i), h.2.1, h.2.2⟩

/-- **`lowerC2` emits only `InstC2` instructions and `TermC2` terminators.** -/
theorem lowerC2_resC2 (cx : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (l : Label) (k : Nat) (r : Res2),
      lowerC2 cx env n l k e = some r → ResC2 r := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n l k r hr
    cases op with
    | add a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_add_inv hr
      exact (ih _ _ _ _ r' hr').cons (is := [_]) (by simpa using InstC2.addChk _ _ _)
    | sub a b =>
      obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_sub_inv hr
      exact (ih _ _ _ _ r' hr').cons (is := [_]) (by simpa using InstC2.subSat _ _ _)
    | call g is a ts =>
      rcases lowerC2_call_inv hr with ⟨_, _, _, r', -, -, -, -, hr', rfl⟩ |
        ⟨_, _, _, _, _, _, _, r', -, -, -, -, hr', rfl⟩
      · exact (ih _ _ _ _ r' hr').cons (is := [_]) (by simpa using InstC2.call _ _ _)
      · exact (ih _ _ _ _ r' hr').cons (printInsts_instC2 _ _ _ _ _)
    | newBuf c τ =>
      obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, hr', rfl⟩ := lowerC2_newBuf_inv hr
      exact (ih _ _ _ _ r' hr').cons (is := [_]) (by simpa using InstC2.newBuf _ _ _ _)
    | xchgAt b i v =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, hr', rfl⟩ :=
        lowerC2_xchg_inv hr
      exact (ih _ _ _ _ r' hr').cons (is := [_, _]) (by
        simp only [List.mem_cons, List.mem_nil_iff, or_false]
        rintro i (rfl | rfl)
        · exact .load _ _
        · exact .store _ _)
    | _ =>
      first
      | (obtain ⟨_, _, _, _, r', -, -, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         exact (ih _ _ _ _ r' hr'))
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, -, -, -, hr'⟩ := lowerC2_split_inv hr
    exact ih _ _ _ _ _ hr'
  | unpack a i x e ih =>
    intro env n l k r hr
    obtain ⟨_, _, -, hr'⟩ := lowerC2_unpack_inv hr
    exact ih _ _ _ _ _ hr'
  | ifeq a b yes no ihy ihn =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    have hy' := ihy _ _ _ _ _ hy
    have hn' := ihn _ _ _ _ _ hn
    refine ⟨by simp, .br _ _ _ _, ?_⟩
    intro b hb
    simp only [List.mem_append, List.mem_cons] at hb
    rcases hb with (rfl | hb) | rfl | hb
    · exact ⟨hy'.1, hy'.2.1⟩
    · exact hy'.2.2 b hb
    · exact ⟨hn'.1, hn'.2.1⟩
    · exact hn'.2.2 b hb
  | ret a =>
    intro env n l k r hr
    obtain ⟨_, _, -, rfl⟩ := lowerC2_ret_inv hr
    exact ⟨by simp, .ret _, by simp⟩
  | _ => intro env n l k r hr; simp [lowerC2] at hr

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerShape.lowerC2_resC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms lowerC2_resC2

end Spike.Lib.LowerShape
