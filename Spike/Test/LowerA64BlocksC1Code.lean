import Spike.Lib.LowerA64.BlocksC1Code

/-!
# The code predicate of an `Accepted1` block with calls on AArch64

`Spike/Lib/LowerA64/BlocksC1Code.lean` at work: `CodeC`'s arms unfolded on
an `unreachable`, a `ret`, a non-call instruction and a one-word user call.
-/

namespace Spike.Test.LowerA64BlocksC1Code

open Kraken.AArch64.Parser
open Scc.Emit.A64
open Spike.Lib.LowerA64

variable (cx : FnCtx) (Cd : Int64 → List Directive → Prop) (Bl : Int64 → Label → Nat → Prop)

/-- `unreachable` makes no claim. -/
example (k : Nat) (pc : Int64) : CodeC cx Cd Bl k pc [] .unreachable := Or.inl rfl

/-- A `ret`'s code at `pc`. -/
example (k : Nat) (pc : Int64) (w : Scc.IR.Operand) (l : List Item) (h : cx.term k (.ret [w]) = .ok l)
    (hc : Cd pc (directives l)) : CodeC cx Cd Bl k pc [] (.ret [w]) := Or.inr ⟨l, h, hc⟩

/-- The thread-pointer read numbered `k`, then the block's rest from `k + 1`. -/
example (k : Nat) (pc : Int64) (d : Scc.IR.Reg) (l : List Item) (is : List Scc.IR.Inst) (tm : Scc.IR.Term)
    (h : cx.inst k (.getTp d) = .ok l) (hc : Cd pc (directives l))
    (hr : CodeC cx Cd Bl (k + 1) (pc + Int64.ofNat (4 * (directives l).length)) is tm) :
    CodeC cx Cd Bl k pc (.getTp d :: is) tm := Or.inl ⟨rfl, l, h, hc, hr⟩

/-- A one-word user call numbered `k`: the argument's load, the `bl` with
return label `spK` (`Bl _ _ k`), the result's store. -/
example (k : Nat) (pc : Int64) (d : Scc.IR.Reg) (g : String) (w : Scc.IR.Operand) (lw ls : List Item)
    (tm : Scc.IR.Term) (hw : cx.getOp .X0 w = .ok lw) (hs : cx.setReg d .X0 = .ok ls)
    (h1 : Cd pc (directives lw))
    (h2 : Bl (pc + Int64.ofNat (4 * (directives lw).length)) (Scc.Lower.Names.user g) k)
    (h3 : Cd (pc + Int64.ofNat (4 * (directives lw).length) + 4) (directives ls))
    (hr : CodeC cx Cd Bl (k + 1)
      (pc + Int64.ofNat (4 * (directives lw).length) + 4 + Int64.ofNat (4 * (directives ls).length)) [] tm) :
    CodeC cx Cd Bl k pc [.call [d] (Scc.Lower.Names.user g) [w]] tm :=
  Or.inr ⟨d, g, w, lw, ls, rfl, hw, hs, h1, h2, h3, hr⟩

/-- `codeC_of_seg` on a call-free `ret` block right after its label: its code
at `CdC` from the label's address. -/
example {prog : List Directive} {okPc : Nat → Bool} {ph : Nat → Nat} {lab : Label → Int64} {ra : Int64}
    (hm : cx.maps = true)
    (hgap : ∀ a b n, Scc.Cert.Rt.A64.labelGap prog a b n = true → lab b = lab a + Int64.ofNat (4 * n))
    (w : Scc.IR.Operand) (hw : Spike.Lib.LowerShape.OpOk w) (k : Nat) (l : Label) (c2 : List Item)
    (zs : List Directive) (ht : cx.term k (.ret [w]) = .ok c2)
    (hseg : Scc.Cert.Code1A64.segIn prog l (directives c2 ++ zs) = true)
    (hph : ∀ r ∈ Scc.Cert.Ph1A64.runsAux l [] (directives c2 ++ zs),
      Scc.Cert.Ph1A64.runPhB okPc ph lab (lab r.1) ra r.2 = true)
    (hrl : ∀ r ∈ Scc.Cert.Ph1A64.runsAux l [] (directives c2 ++ zs),
      ph (lab r.1).toBitVec.toNat = ph ra.toBitVec.toNat) :
    CodeC cx (CdC prog okPc ph lab ra) (BlC prog okPc ph lab cx ra) k (lab l) [] (.ret [w]) := by
  have := codeC_of_seg (frames := none) hm hgap (.ret w hw) [] k l [] c2 [] zs (by simp) rfl ht
    (by simpa using hseg) rfl (by simpa using hph) (by simpa using hrl)
  simpa using this

/-- Only the bracket's abort block has the stack abort's call: a call
block's instructions do not. -/
example (lcx : Scc.Lower.Ctx) (n : Nat) (g : String) (w : Scc.IR.Operand) (t : Scc.IR.Term)
    (hg : Spike.Lib.LowerCall.Callee lcx g) (hw : Spike.Lib.LowerShape.OpOk w) (ht : t ≠ .unreachable) :
    ∀ i ∈ (Spike.Lib.LowerCall.callBlk n g w [] t).insts, i ≠ abortI :=
  ne_abortI_of_callBlk (.call n g w [] t hg hw (by simp [Spike.Lib.LowerCall.NoCall])) ht

/-- …and the abort block's is one. -/
example (n : Nat) : abortI ∈ (Scc.Lower.Inv.deepBlock n).insts := by simp [Scc.Lower.Inv.deepBlock]

/-- info: 'Spike.Lib.LowerA64.cdOf_blC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.cdOf_blC

/-- info: 'Spike.Lib.LowerA64.blC_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Spike.Lib.LowerA64.blC_ph

end Spike.Test.LowerA64BlocksC1Code
