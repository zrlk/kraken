import WeakCore.TermScope
import WeakCore.TermWrapDefs

/-! # TermScopeW: the interim scope rule A1 (`ProgScopeOKW`)

No `sum`, `iex`, `refine` or `tex` node whose values carry a word or token key, in any type the
checker infers for the program (every bound variable, by `checkW`, a pass over the unchanged
checker functions `checkOp`/`Cx.use`/`instantiate`), nor in signatures; type arguments (`call`,
`tail`) and type-package witnesses (`packT`) carry none.  Literal `word`/`word2` components (word
units, read by `VRes`) stay allowed.  `ProgScopeOKW p = ProgScopeOK p && ProgWrapOK p`.
Typing-aware (inferred types, `inl[τ] w`), and type variables bound by `mu`
answer with the `mu`'s own keys (`VRR .mu` pushes the `mu` itself).
-/

namespace TermScope

open CoreLang CoreTerm

/-- (A1) Every code block: `wrapOK` signature, and its body passes `checkW` from `checkDecl`'s
context. -/
def declWrapOK (p : Prog) (d : Decl) : Bool :=
  wrapOK d.argTy && wrapOK d.retTy &&
  (checkW p { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
              ke := d.tparams.reverse.map some } d.body matches .ok _)

def ProgWrapOK (p : Prog) : Bool := p.all (declWrapOK p)

/-- **The program scope check with A1** (interim scope): `ProgScopeOK` and `ProgWrapOK`. -/
def ProgScopeOKW (p : Prog) : Bool := ProgScopeOK p && ProgWrapOK p

theorem ProgScopeOKW.scope {p : Prog} (h : ProgScopeOKW p = true) : ProgScopeOK p = true :=
  (Bool.and_eq_true _ _ ▸ h).1

theorem ProgScopeOKW.wrap {p : Prog} (h : ProgScopeOKW p = true) : ProgWrapOK p = true :=
  (Bool.and_eq_true _ _ ▸ h).2

end TermScope
