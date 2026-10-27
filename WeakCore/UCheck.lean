/-
# UCheck — UnElab's typing: `checkU`, and T1 (typing preservation)

`checkU p cx k e` is the core checker applied to the elaboration, unfolded over nested terms: an
operand is checked by `checkArg` — its nested operands left to right, then the core rule `checkOp` for the
operation bound to its temporary `tmp k'` — and a term by the core rule of its head on the atoms (`check`), with
its subterms elaborated.  It is not an independent type system: the core tracks affinity, torn reads and index
binders by variable name, so there is no finer judgement to give.

**T1** `checkU_elab : checkU p cx k e = check p cx (elabT k e)`: an equation, for every `p`, `cx`, `k`, `e`.  So an
UnElab program is accepted exactly when its `.w` is (`checkProgU_elab`).
-/
import WeakCore.UnElab
open CoreLang CoreTerm UnElab

namespace UCheck

/-- One elaborated `let`, as the checker takes it. -/
def stepB (p : Prog) (cx : Cx) (b : String × Op) : M Cx := checkOp p cx b.1 b.2

mutual
/-- An operand: its nested operands, then the rule of its operation under its temporary. -/
def checkArg (p : Prog) (cx : Cx) (k : Nat) : UArg → M Cx
  | .at _ => pure cx
  | .op h args => do
      let cx ← checkArgs p cx k args
      checkOp p cx (tmp (elabArgs k args).2.2) (setAts h (elabArgs k args).2.1)

/-- Operands, left to right. -/
def checkArgs (p : Prog) (cx : Cx) (k : Nat) : List UArg → M Cx
  | [] => pure cx
  | a :: rest => do
      let cx ← checkArg p cx k a
      checkArgs p cx (elabArg k a).2.2 rest
end

/-- **UnElab's typing.**  The `let` spine is followed by `checkU`; every other head is the core rule on the
operands' atoms, with its subterms elaborated. -/
def checkU (p : Prog) (cx : Cx) (k : Nat) : UExpr → M Unit
  | .let_ x h args e => do
      let cx ← checkArgs p cx k args
      let r := elabArgs k args
      let cx ← checkOp p cx (binder x r.2.2).1 (setAts h r.2.1)
      checkU p cx (binder x r.2.2).2 e
  | .split a pp q e => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (destr r.2.2 r.2.1 (.pair pp q) fun j => elabT j e)
  | .unpack a i x e => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.unpack r.2.1 i x (elabT r.2.2 e))
  | .unpackT a al x e => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.unpackT r.2.1 al x (elabT r.2.2 e))
  | .region a rn pn tn e => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.region r.2.1 rn pn tn (elabT r.2.2 e))
  | .openPub a rn pn cn e => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.openPub r.2.1 rn pn cn (elabT r.2.2 e))
  | .case a x e₁ y e₂ => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.case r.2.1 x (elabT r.2.2 e₁) y (elabT r.2.2 e₂))
  | .ifnull a e₁ x e₂ => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.ifnull r.2.1 (elabT r.2.2 e₁) x (elabT r.2.2 e₂))
  | .parity a kn ev od => do
      let cx ← checkArg p cx k a
      let r := elabArg k a
      check p cx (.parity r.2.1 kn (elabT r.2.2 ev) (elabT r.2.2 od))
  | .ifeq a b yes no => do
      let cx ← checkArgs p cx k [a, b]
      let r := elabArgs k [a, b]
      check p cx (.ifeq (r.2.1.getD 0 .unit) (r.2.1.getD 1 .unit) (elabT r.2.2 yes) (elabT r.2.2 no))
  | .cas acq rel w e v t ok fail => do
      let cx ← checkArgs p cx k [w, e, v]
      let r := elabArgs k [w, e, v]
      let g (i : Nat) : At := r.2.1.getD i .unit
      check p cx (.cas acq rel (g 0) (g 1) (g 2) t (elabT r.2.2 ok) (elabT r.2.2 fail))
  | .casp acq rel w e0 e1 v0 v1 t ok fail => do
      let cx ← checkArgs p cx k [w, e0, e1, v0, v1]
      let r := elabArgs k [w, e0, e1, v0, v1]
      let g (i : Nat) : At := r.2.1.getD i .unit
      check p cx (.casp acq rel (g 0) (g 1) (g 2) (g 3) (g 4) t (elabT r.2.2 ok) (elabT r.2.2 fail))
  | .ret a => do
      let cx ← checkArg p cx k a
      check p cx (.ret (elabArg k a).2.1)
  | .tail f is a ts => do
      let cx ← checkArg p cx k a
      check p cx (.tail f is (elabArg k a).2.1 ts)

/-! ## T1 -/

/-- The checker on a block of lets: the lets in order, then the rest. -/
theorem check_lets (p : Prog) (cx : Cx) (ls : List (String × Op)) (e : Expr) :
    check p cx (lets ls e) = ls.foldlM (stepB p) cx >>= fun cx => check p cx e := by
  induction ls generalizing cx with
  | nil => simp [lets]
  | cons b ls ih =>
      simp only [lets, check, List.foldlM_cons, stepB, bind_assoc]
      congr 1; funext cx'; exact ih cx'

mutual
theorem checkArg_fold (p : Prog) (cx : Cx) (k : Nat) (a : UArg) :
    checkArg p cx k a = (elabArg k a).1.foldlM (stepB p) cx := by
  match a with
  | .at _ => simp [checkArg, elabArg]
  | .op h args =>
      simp only [checkArg, elabArg, List.foldlM_append, checkArgs_fold p cx k args, List.foldlM_cons,
        List.foldlM_nil, stepB, bind_pure]

theorem checkArgs_fold (p : Prog) (cx : Cx) (k : Nat) (as : List UArg) :
    checkArgs p cx k as = (elabArgs k as).1.foldlM (stepB p) cx := by
  match as with
  | [] => simp [checkArgs, elabArgs]
  | a :: rest =>
      simp only [checkArgs, elabArgs, List.foldlM_append, checkArg_fold p cx k a]
      congr 1; funext cx'; exact checkArgs_fold p cx' _ rest
end

/-- **T1, typing preservation**: UnElab's typing is the core checker on the elaboration. -/
theorem checkU_elab (p : Prog) (cx : Cx) (k : Nat) (e : UExpr) : checkU p cx k e = check p cx (elabT k e) := by
  induction e generalizing cx k with
  | let_ x h args e ih =>
      simp only [checkU, elabT, check_lets, checkArgs_fold, check]
      congr 1; funext cx'; congr 1; funext cx''; exact ih cx'' _
  | ifeq a b yes no _ _ => simp only [checkU, elabT, check_lets, checkArgs_fold]
  | cas acq rel w e v t ok fail _ _ => simp only [checkU, elabT, check_lets, checkArgs_fold]
  | casp acq rel w e0 e1 v0 v1 t ok fail _ _ => simp only [checkU, elabT, check_lets, checkArgs_fold]
  | _ => simp only [checkU, elabT, check_lets, checkArg_fold]

/-! ## Code blocks and programs -/

/-- `checkDecl` with its body check abstracted (pinned to the core's `checkDecl` by `checkDecl_with`, so it
cannot drift from it). -/
def checkDeclWith (p : Prog) (body : Cx → M Unit) (d : Decl) : M Unit := do
  let nt := d.tparams.length
  if !d.argTy.wf nt d.idx.length || !d.retTy.wf nt d.idx.length then
    throw s!"{d.name}: signature is not well formed"
  if !d.argTy.scTop || d.retTy.secondClass then
    throw s!"{d.name}: a second-class capability may be passed, not returned or stored"
  body { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
         ke := d.tparams.reverse.map some }
  -- the kind rules; no rule mentions a decl by name (`isDev` is by KIND)
  let isDev : String → Bool := fun f => ((p.find? (·.name == f)).map (·.kind == .device)).getD false
  if d.kind == .device && !(devCells d.argTy).all devCellOK then
    throw s!"{d.name}: a device function may only be given cells of plain bits, protocol words or word pairs"
  if d.kind != .device && !exprNoDevOnly isDev d.body then
    throw s!"{d.name}: device externs and device functions may be used only inside a device function"
  if !exprNoDevFnptr isDev d.body then
    throw s!"{d.name}: a device function cannot be taken as a value"
  match d.kind with
  | .restricted _ _ =>
      throw s!"{d.name}: restricted functions are not supported yet (fuel and stack budgets are not checked)"
  | _ => pure ()

theorem checkDecl_with (p : Prog) (d : Decl) : checkDecl p d = checkDeclWith p (fun cx => check p cx d.body) d := rfl

/-- A code block: the core's signature checks, then `checkU` on the body (counter 0). -/
def checkDeclU (p : Prog) (d : UDecl) : M Unit := checkDeclWith p (fun cx => checkU p cx 0 d.body) (elabDecl d)

/-- A program: every block, against the elaborated program (the checker reads other blocks only through
`Prog.find?`, for signatures and `fnptr`, which `elabProg` leaves unchanged). -/
def checkProgU (U : UProg) : M Unit := U.forM (checkDeclU (elabProg U))

theorem checkDeclU_elab (p : Prog) (d : UDecl) : checkDeclU p d = checkDecl p (elabDecl d) := by
  simp only [checkDeclU, checkDecl_with, checkU_elab]; rfl

theorem forM_map_elab (p : Prog) (U : UProg) :
    U.forM (checkDeclU p) = (U.map elabDecl).forM (checkDecl p) := by
  induction U with
  | nil => rfl
  | cons d U ih =>
    show (do checkDeclU p d; U.forM (checkDeclU p)) = (do checkDecl p (elabDecl d); (U.map elabDecl).forM (checkDecl p))
    rw [checkDeclU_elab, ih]

/-- **T1 for programs**: an UnElab program is accepted exactly when its elaboration is. -/
theorem checkProgU_elab (U : UProg) : checkProgU U = checkProg (elabProg U) := by
  simp only [checkProgU, checkProg, forM_map_elab]; rfl

theorem checkProgU_ok {U : UProg} (h : checkProgU U = .ok ()) : checkProg (elabProg U) = .ok () := by
  rw [← checkProgU_elab]; exact h

/-! ## Rule 4's lint: `ret f(args)` of a declared block -/

/-- The blocks called as `ret f(args)` in a term (a call followed by `ret`: a stack frame per call). -/
def retCalls : UExpr → List String
  | .let_ _ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e
  | .openPub _ _ _ _ e => retCalls e
  | .case _ _ e1 _ e2 | .ifnull _ e1 _ e2 | .parity _ _ e1 e2 | .ifeq _ _ e1 e2
  | .cas _ _ _ _ _ _ e1 e2 | .casp _ _ _ _ _ _ _ _ e1 e2 => retCalls e1 ++ retCalls e2
  | .ret (.op (.call f _ _ _) _) => [f]
  | _ => []

/-- `sce`'s warnings: one per `ret f(args)` where `f` is a declared block. -/
def retCallLint (blocks : List String) (U : UProg) : List String :=
  U.flatMap fun d => ((retCalls d.body).filter blocks.contains).map fun f =>
    s!"in {d.name}: `ret {f}(…)` returns after a call (a stack frame per call): did you mean `tail {f}(args)`?"

#print axioms check_lets
#print axioms checkArg_fold
#print axioms checkArgs_fold
#print axioms checkU_elab
#print axioms checkDecl_with
#print axioms checkDeclU_elab
#print axioms checkProgU_elab
#print axioms checkProgU_ok

end UCheck
