/-
**The setup block's result type** (ISA-free): in an `Accepted2` program
whose `main` takes the setup result `ty` (`setupOf p = some ty`), every
compiled block named `rodata` returns `ty` (`decl2` checks it with
`setup2`).

- `rodata_retTy_of_accepted2`: a block of `p` named `rodata` returns `ty`;
- `rodata_retTy_compiled2`: the same at a compiled block's index (the
  `hret` premise of the setup bottom keys' `hbot` on both ISAs).
-/
import Spike.Lib.LowerProgC2Core

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower

/-- **A block named `rodata` returns the setup result** in an `Accepted2`
program with a setup block. -/
theorem rodata_retTy_of_accepted2 {p : Prog} (hp : Accepted2 p = true) {ty : Ty} (hty : setupOf p = some ty)
    {d : Decl} (hd : d ∈ p) (hn : d.name = "rodata") : d.retTy = ty := by
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  obtain ⟨E, hE⟩ := decl2_of_decls2 hds d hd
  have hpe : isPrintExt d = false := by simp [isPrintExt, hn]
  have hnl : (hasPrint p && "rodata" == "printL") = false := by simp
  have hmr : ("rodata" == "main") = false := by decide
  simp only [decl2, hpe, hn, hnl, hty, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE
  simp only [hmr, Bool.false_eq_true, ↓reduceIte] at hE
  unfold setup2 at hE
  simp only [Bool.and_eq_true, beq_iff_eq] at hE
  exact hE.1.1.1.2

/-- **A compiled block named `rodata` returns the setup result**, at its
index in `compiled2 p`. -/
theorem rodata_retTy_compiled2 {p : Prog} (hp : Accepted2 p = true) {ty : Ty} (hty : setupOf p = some ty)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata") : d.retTy = ty :=
  rodata_retTy_of_accepted2 hp hty (List.mem_filter.1 (List.mem_of_getElem? hd)).1 hn

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.rodata_retTy_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.rodata_retTy_of_accepted2

/-- info: 'Spike.Lib.LowerNode.rodata_retTy_compiled2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.rodata_retTy_compiled2
