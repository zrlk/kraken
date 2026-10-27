/-
# UnElab — the non-ANF surface language: AST and elaboration to the core

UnElab is the core language with nesting: wherever a core operation takes an atom (`At`), UnElab takes an
*operand* (`UArg`), which is an atom or a nested operation.  Types, kinds, protocols, index terms and every
operation are the core's (`CoreTerm.Op`, unchanged).  The meaning of an UnElab program is its elaboration
`elabProg`: ANF conversion with fresh temporaries `%k` (printed `«%k»`), operands evaluated left to right,
innermost first (the design notes).

* `UArg.op head args`: `head` is a core `Op` whose atom positions are holes; `args` fills them, in the order
  `TermScope.opAts` lists them (`setAts`).
* Anonymous binders (a nested operation, `let _ = …`, the hidden pairs of a pattern) are `none`/`UPat.pair` and
  are named `tmp k` by one counter per block, consumed in evaluation order; branches restart from the same `k`.
  User-named binders never consume it.
* `embed : Expr → UExpr` (atoms only, named binders) with `elabT k (embed e) = e` (`elabT_embed`): an internal
  lemma (starts, T2), not a user-facing promise.

Nothing here is trusted: an elaborated program is judged by the core checker (`checkProg`, `ProgScopeOKW`).
-/
import WeakCore.TermScope
open CoreLang CoreTerm

namespace UnElab

/-! ## The AST -/

/-- An operand: an atom, or a nested operation (`head`'s atom positions are holes, filled by `args` in
`TermScope.opAts` order). -/
inductive UArg
  | at (a : At)
  | op (head : Op) (args : List UArg)

/-- A `let` pattern: a name (`some x`), `_` (`none`), or a pair; `(p1, p2, p3)` is `pair p1 (pair p2 p3)`. -/
inductive UPat
  | bind (x : Option String)
  | pair (p q : UPat)
  deriving DecidableEq, Repr

/-- UnElab terms: the core's `Expr` with operands for atoms.  `let x = a` (an atom) is `let_ x (.atom _) [.at a]`;
`let pat = ARG` with `pat` a name is a `let_`; with `pat` a pair it is `split`. -/
inductive UExpr
  | let_ (x : Option String) (head : Op) (args : List UArg) (e : UExpr)
  | split (a : UArg) (p q : UPat) (e : UExpr)
  | unpack (a : UArg) (i x : String) (e : UExpr)
  | unpackT (a : UArg) (α x : String) (e : UExpr)
  | region (a : UArg) (r p t : String) (e : UExpr)
  | openPub (a : UArg) (r p c : String) (e : UExpr)
  | case (a : UArg) (x : String) (e₁ : UExpr) (y : String) (e₂ : UExpr)
  | ifnull (a : UArg) (isNull : UExpr) (x : String) (nonNull : UExpr)
  | parity (a : UArg) (k : String) (even odd : UExpr)
  | ifeq (a b : UArg) (yes no : UExpr)
  | cas (acq rel : Bool) (w e v : UArg) (t : String) (ok fail : UExpr)
  | casp (acq rel : Bool) (w e0 e1 v0 v1 : UArg) (t : String) (ok fail : UExpr)
  | ret (a : UArg)
  | tail (f : String) (is : List String) (a : UArg) (ts : List Ty)

structure UDecl where
  name    : String
  tparams : List Kind := []
  idx     : List String
  arg     : String
  argTy   : Ty
  retTy   : Ty
  body    : UExpr
  /-- (M1, T2) The decl kind (copied to and from the core `Decl`). -/
  kind    : DeclKind := .plain

abbrev UProg := List UDecl

/-! ## Filling an operation's atom positions -/

/-- The `k`-th temporary, `%k` (printed `«%k»`; UnElab's parser refuses names beginning with `%`). -/
def tmp (k : Nat) : String := "%" ++ toString k

/-- `o` with its atom positions (in `TermScope.opAts` order) replaced by `as`; missing ones are `()`.  For
`validate`, a non-variable leaves the name unchanged; for `store … with t`, the token is the third atom.
Arity is not checked here: missing atoms become `()` and extra ones are dropped.  The parser gives every nested
operation exactly `(opAts h).length` operands (`UElabTest` checks this over the libraries and EM0). -/
def setAts (o : Op) (as : List At) : Op :=
  let g (i : Nat) : At := as.getD i .unit
  match o with
  | .atom _ => .atom (g 0)
  | .pair _ _ => .pair (g 0) (g 1)
  | .inl t _ => .inl t (g 0)
  | .inr t _ => .inr t (g 0)
  | .add _ _ => .add (g 0) (g 1)
  | .sub _ _ => .sub (g 0) (g 1)
  | .new _ => .new (g 0)
  | .null μ t => .null μ t
  | .fold _ t => .fold (g 0) t
  | .publish _ => .publish (g 0)
  | .intoRgn r _ => .intoRgn r (g 0)
  | .newBuf _ t => .newBuf (g 0) t
  | .idx _ _ => .idx (g 0) (g 1)
  | .bufInit _ _ _ => .bufInit (g 0) (g 1) (g 2)
  | .fld i _ => .fld i (g 0)
  | .load acq _ => .load acq (g 0)
  | .store rel _ _ tok => .store rel (g 0) (g 1) (tok.map fun _ => g 2)
  | .fence f => .fence f
  | .mkWord r P _ _ => .mkWord r P (g 0) (g 1)
  | .pack _ w t => .pack (g 0) w t
  | .packT _ σ t => .packT (g 0) σ t
  | .validate y => match g 0 with
      | .var z => .validate z
      | _ => .validate y
  | .call f is _ ts => .call f is (g 0) ts
  | .spawn f _ T ts => .spawn f (g 0) T ts
  | .ext n _ => .ext n (g 0)
  | .borrow c _ => .borrow c (g 0)
  | .endBorrow _ => .endBorrow (g 0)
  | .xchg _ _ => .xchg (g 0) (g 1)
  | .fnptr f => .fnptr f
  | .callc _ _ => .callc (g 0) (g 1)
  | .rem _ _ => .rem (g 0) (g 1)
  | .nameI _ => .nameI (g 0)
  | .xchgAt _ _ _ => .xchgAt (g 0) (g 1) (g 2)
  | .loadAt _ _ => .loadAt (g 0) (g 1)
  | .bits o _ _ => .bits o (g 0) (g 1)
  | .bit1 o _ => .bit1 o (g 0)
  | .vmatch _ _ _ => .vmatch (g 0) (g 1) (g 2)
  | .band _ _ => .band (g 0) (g 1)
  | .zero t => .zero t
  | .loadAtF _ _ p => .loadAtF (g 0) (g 1) p
  | .xchgAtF _ _ p _ => .xchgAtF (g 0) (g 1) p (g 2)
  | .freeze _ => .freeze (g 0)
  | .cvt sg w _ => .cvt sg w (g 0)
  | .toInt _ => .toInt (g 0)
  | .asLanes sg w _ => .asLanes sg w (g 0)
  | .fop o _ _ => .fop o (g 0) (g 1)
  | .fcmp o _ _ => .fcmp o (g 0) (g 1)
  | .fop1 o _ => .fop1 o (g 0)
  | .lane _ _ => .lane (g 0) (g 1)
  | .setLane _ _ _ => .setLane (g 0) (g 1) (g 2)
  | .ldl _ _ => .ldl (g 0) (g 1)
  | .stl _ _ _ => .stl (g 0) (g 1) (g 2)
  | .ldlw _ _ _ => .ldlw (g 0) (g 1) (g 2)
  | .stlw _ _ _ _ => .stlw (g 0) (g 1) (g 2) (g 3)
  | .mkWord2 r P _ _ _ => .mkWord2 r P (g 0) (g 1) (g 2)
  | .ldp acq _ n0 n1 => .ldp acq (g 0) n0 n1
  | .stp rel _ _ _ _ => .stp rel (g 0) (g 1) (g 2) (g 3)
  | .mkEPair r P _ _ => .mkEPair r P (g 0) (g 1)
  | .mkTicket r N P _ _ => .mkTicket r N P (g 0) (g 1)
  | .claim _ _ => .claim (g 0) (g 1)
  | .fetch o acq rel _ _ => .fetch o acq rel (g 0) (g 1)

theorem setAts_opAts (o : Op) : setAts o (TermScope.opAts o) = o := by
  cases o with
  | store rel a v tok => cases tok <;> rfl
  | _ => rfl

/-! ## Elaboration (ANF conversion) -/

mutual
/-- An operand: the lets it needs (post-order, left to right), its atom, and the next counter. -/
def elabArg (k : Nat) : UArg → List (String × Op) × At × Nat
  | .at a => ([], a, k)
  | .op h args =>
      let r := elabArgs k args
      (r.1 ++ [(tmp r.2.2, setAts h r.2.1)], .var (tmp r.2.2), r.2.2 + 1)

/-- Operands, left to right. -/
def elabArgs (k : Nat) : List UArg → List (String × Op) × List At × Nat
  | [] => ([], [], k)
  | a :: rest =>
      let r := elabArg k a
      let s := elabArgs r.2.2 rest
      (r.1 ++ s.1, r.2.1 :: s.2.1, s.2.2)
end

/-- A binder: the user's name, or the next temporary. -/
def binder : Option String → Nat → String × Nat
  | some x, k => (x, k)
  | none, k => (tmp k, k + 1)

/-- The binder a pattern position gets: its name, or a temporary (`_`, or a nested pair). -/
def patBinder : UPat → Nat → String × Nat
  | .bind o, k => binder o k
  | .pair _ _, k => (tmp k, k + 1)

/-- Destructure `s` by the pattern: for a pair `(p, q)`, the binders of `p` then `q`, one `split`, then `p`'s
sub-pattern, then `q`'s (depth first, left first); `c j` is the continuation at counter `j`. -/
def destr (k : Nat) (s : At) : UPat → (Nat → Expr) → Expr
  | .bind _, c => c k
  | .pair p q, c =>
      let b1 := patBinder p k
      let b2 := patBinder q b1.2
      .split s b1.1 b2.1 (destr b2.2 (.var b1.1) p fun j => destr j (.var b2.1) q c)

/-- Elaborate a term at counter `k`: operands first (lets), then the head; branches restart from the same
counter. -/
def elabT (k : Nat) : UExpr → Expr
  | .let_ x h args e =>
      let r := elabArgs k args
      let b := binder x r.2.2
      lets r.1 (.let_ b.1 (setAts h r.2.1) (elabT b.2 e))
  | .split a p q e =>
      let r := elabArg k a
      lets r.1 (destr r.2.2 r.2.1 (.pair p q) fun j => elabT j e)
  | .unpack a i x e =>
      let r := elabArg k a
      lets r.1 (.unpack r.2.1 i x (elabT r.2.2 e))
  | .unpackT a al x e =>
      let r := elabArg k a
      lets r.1 (.unpackT r.2.1 al x (elabT r.2.2 e))
  | .region a rn pn tn e =>
      let r := elabArg k a
      lets r.1 (.region r.2.1 rn pn tn (elabT r.2.2 e))
  | .openPub a rn pn cn e =>
      let r := elabArg k a
      lets r.1 (.openPub r.2.1 rn pn cn (elabT r.2.2 e))
  | .case a x e₁ y e₂ =>
      let r := elabArg k a
      lets r.1 (.case r.2.1 x (elabT r.2.2 e₁) y (elabT r.2.2 e₂))
  | .ifnull a e₁ x e₂ =>
      let r := elabArg k a
      lets r.1 (.ifnull r.2.1 (elabT r.2.2 e₁) x (elabT r.2.2 e₂))
  | .parity a kn ev od =>
      let r := elabArg k a
      lets r.1 (.parity r.2.1 kn (elabT r.2.2 ev) (elabT r.2.2 od))
  | .ifeq a b yes no =>
      let r := elabArgs k [a, b]
      lets r.1 (.ifeq (r.2.1.getD 0 .unit) (r.2.1.getD 1 .unit) (elabT r.2.2 yes) (elabT r.2.2 no))
  | .cas acq rel w e v t ok fail =>
      let r := elabArgs k [w, e, v]
      let g (i : Nat) : At := r.2.1.getD i .unit
      lets r.1 (.cas acq rel (g 0) (g 1) (g 2) t (elabT r.2.2 ok) (elabT r.2.2 fail))
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      let r := elabArgs k [w, e0, e1, v0, v1]
      let g (i : Nat) : At := r.2.1.getD i .unit
      lets r.1 (.casp acq rel (g 0) (g 1) (g 2) (g 3) (g 4) t (elabT r.2.2 ok) (elabT r.2.2 fail))
  | .ret a =>
      let r := elabArg k a
      lets r.1 (.ret r.2.1)
  | .tail f is a ts =>
      let r := elabArg k a
      lets r.1 (.tail f is r.2.1 ts)

def elabDecl (d : UDecl) : Decl :=
  { name := d.name, tparams := d.tparams, idx := d.idx, arg := d.arg, argTy := d.argTy, retTy := d.retTy,
    body := elabT 0 d.body, kind := d.kind }

def elabProg (U : UProg) : Prog := U.map elabDecl

/-! ## Embedding the core (internal) -/

def embed : Expr → UExpr
  | .let_ x op e => .let_ (some x) op ((TermScope.opAts op).map .at) (embed e)
  | .split a x y e => .split (.at a) (.bind (some x)) (.bind (some y)) (embed e)
  | .unpack a i x e => .unpack (.at a) i x (embed e)
  | .unpackT a al x e => .unpackT (.at a) al x (embed e)
  | .region a r p t e => .region (.at a) r p t (embed e)
  | .openPub a r p c e => .openPub (.at a) r p c (embed e)
  | .case a x e₁ y e₂ => .case (.at a) x (embed e₁) y (embed e₂)
  | .ifnull a e₁ x e₂ => .ifnull (.at a) (embed e₁) x (embed e₂)
  | .parity a k ev od => .parity (.at a) k (embed ev) (embed od)
  | .ifeq a b yes no => .ifeq (.at a) (.at b) (embed yes) (embed no)
  | .cas acq rel w e v t ok fail => .cas acq rel (.at w) (.at e) (.at v) t (embed ok) (embed fail)
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      .casp acq rel (.at w) (.at e0) (.at e1) (.at v0) (.at v1) t (embed ok) (embed fail)
  | .ret a => .ret (.at a)
  | .tail f is a ts => .tail f is (.at a) ts

def embedDecl (d : Decl) : UDecl :=
  { name := d.name, tparams := d.tparams, idx := d.idx, arg := d.arg, argTy := d.argTy, retTy := d.retTy,
    body := embed d.body, kind := d.kind }

def embedProg (p : Prog) : UProg := p.map embedDecl

theorem elabArgs_ats (k : Nat) (as : List At) : elabArgs k (as.map .at) = ([], as, k) := by
  induction as generalizing k with
  | nil => rfl
  | cons a as ih => simp [elabArgs, elabArg, ih]

theorem elabT_embed (k : Nat) (e : Expr) : elabT k (embed e) = e := by
  induction e generalizing k with
  | let_ x op e ih => simp [embed, elabT, elabArgs_ats, binder, lets, setAts_opAts, ih]
  | split a x y e ih => simp [embed, elabT, elabArg, destr, patBinder, binder, lets, ih]
  | ret a => rfl
  | tail f is a ts => rfl
  | ifeq a b yes no ih1 ih2 => simp [embed, elabT, elabArgs, elabArg, lets, ih1, ih2]
  | cas acq rel w e v t ok fail ih1 ih2 => simp [embed, elabT, elabArgs, elabArg, lets, ih1, ih2]
  | casp acq rel w e0 e1 v0 v1 t ok fail ih1 ih2 => simp [embed, elabT, elabArgs, elabArg, lets, ih1, ih2]
  | _ => simp_all [embed, elabT, elabArg, lets]

theorem elabDecl_embedDecl (d : Decl) : elabDecl (embedDecl d) = d := by
  cases d; simp [elabDecl, embedDecl, elabT_embed]

theorem elabProg_embedProg (p : Prog) : elabProg (embedProg p) = p := by
  induction p with
  | nil => rfl
  | cons d p ih => simp [elabProg, embedProg, elabDecl_embedDecl] at *; exact ih

/-! ## Reserved names (hygiene by reservation) -/

/-- Names beginning with `%` are the elaborator's; UnElab's parser refuses them. -/
def reserved (s : String) : Bool := s.startsWith "%"

def okAt : At → Bool
  | .var x => !reserved x
  | _ => true

/-- The names a head binds or names as variables outside its atom positions (`ldp … as (k0, k1)`) are not
reserved.  (`validate y`'s `y` is an atom position, filled from the operands; names inside a head — `intoRgn r`,
`fnptr f` — are the user's too, but bind nothing.) -/
def noResHead : Op → Bool
  | .ldp _ _ n0 n1 => !reserved n0 && !reserved n1
  | .validate y => !reserved y
  | _ => true

mutual
/-- An operand's names are not reserved: its atoms, and (nested) its head's names and its operands'. -/
def noResArg : UArg → Bool
  | .at a => okAt a
  | .op h args => noResHead h && noResArgs args
def noResArgs : List UArg → Bool
  | [] => true
  | a :: r => noResArg a && noResArgs r
end

def noResPat : UPat → Bool
  | .bind (some x) => !reserved x
  | .bind none => true
  | .pair p q => noResPat p && noResPat q

/-- No user-written name (binder or variable) is reserved. -/
def noReservedE : UExpr → Bool
  | .let_ x h args e => noResPat (.bind x) && noResHead h && noResArgs args && noReservedE e
  | .split a p q e => noResArg a && noResPat p && noResPat q && noReservedE e
  | .unpack a i x e => noResArg a && !reserved i && !reserved x && noReservedE e
  | .unpackT a al x e => noResArg a && !reserved al && !reserved x && noReservedE e
  | .region a r p t e => noResArg a && !reserved r && !reserved p && !reserved t && noReservedE e
  | .openPub a r p c e => noResArg a && !reserved r && !reserved p && !reserved c && noReservedE e
  | .case a x e₁ y e₂ => noResArg a && !reserved x && !reserved y && noReservedE e₁ && noReservedE e₂
  | .ifnull a e₁ x e₂ => noResArg a && !reserved x && noReservedE e₁ && noReservedE e₂
  | .parity a k ev od => noResArg a && !reserved k && noReservedE ev && noReservedE od
  | .ifeq a b yes no => noResArg a && noResArg b && noReservedE yes && noReservedE no
  | .cas _ _ w e v t ok fail =>
      noResArgs [w, e, v] && !reserved t && noReservedE ok && noReservedE fail
  | .casp _ _ w e0 e1 v0 v1 t ok fail =>
      noResArgs [w, e0, e1, v0, v1] && !reserved t && noReservedE ok && noReservedE fail
  | .ret a => noResArg a
  | .tail _ _ a _ => noResArg a

def noReserved (U : UProg) : Bool :=
  U.all fun d => !reserved d.arg && noReservedE d.body

/-! ## Pinned behaviour -/

-- `let (w, cnt, j) = a`: `split a w %0; split %0 cnt j` (one counter, the hidden pair first).
#guard match elabT 0 (.split (.at (.var "a")) (.bind (some "w")) (.pair (.bind (some "cnt")) (.bind (some "j")))
                 (.ret (.at (.var "w")))) with
  | .split (.var "a") "w" "%0" (.split (.var "%0") "cnt" "j" (.ret (.var "w"))) => true
  | _ => false
-- `let ((s, mv), n) = a`: `split a %0 n; split %0 s mv`.
#guard match elabT 0 (.split (.at (.var "a")) (.pair (.bind (some "s")) (.bind (some "mv"))) (.bind (some "n"))
                 (.ret (.at .unit))) with
  | .split (.var "a") "%0" "n" (.split (.var "%0") "s" "mv" (.ret .unit)) => true
  | _ => false
-- `tail emit8(w, cnt1, j + 1)` at counter 6: `%6 = j + 1; %7 = (cnt1, %6); %8 = (w, %7)`, innermost first.
#guard match elabT 6 (.tail "emit8" [] (.op (.pair .unit .unit) [.at (.var "w"),
                   .op (.pair .unit .unit) [.at (.var "cnt1"), .op (.add .unit .unit) [.at (.var "j"), .at (.lit 1)]]]) []) with
  | .let_ "%6" (.add (.var "j") (.lit 1)) (.let_ "%7" (.pair (.var "cnt1") (.var "%6"))
      (.let_ "%8" (.pair (.var "w") (.var "%7")) (.tail "emit8" [] (.var "%8") []))) => true
  | _ => false
-- `let _ = e` consumes the counter; branches restart from the same counter.
#guard match elabT 0 (.let_ none (.load false .unit) [.op (.fld 0 .unit) [.at (.var "m")]]
          (.ifeq (.op (.load true .unit) [.at (.var "c")]) (.at (.lit 1))
            (.let_ none (.atom .unit) [.at .unit] (.ret (.at .unit))) (.let_ none (.atom .unit) [.at .unit] (.ret (.at .unit))))) with
  | .let_ "%0" (.fld 0 (.var "m")) (.let_ "%1" (.load false (.var "%0"))
      (.let_ "%2" (.load true (.var "c")) (.ifeq (.var "%2") (.lit 1)
        (.let_ "%3" (.atom .unit) (.ret .unit)) (.let_ "%3" (.atom .unit) (.ret .unit))))) => true
  | _ => false
-- `validate (load d)`: the temporary is validated.
#guard match elabT 0 (.let_ (some "y") (.validate "") [.op (.load false .unit) [.at (.var "d")]] (.ret (.at (.var "y")))) with
  | .let_ "%0" (.load false (.var "d")) (.let_ "y" (.validate "%0") (.ret (.var "y"))) => true
  | _ => false

-- A nested head's names are checked too: `ret (ldp acq w as («%0», k))` is not hygienic.
#guard !noReservedE (.ret (.op (.ldp true .unit "%0" "k") [.at (.var "w")]))
#guard noReservedE (.ret (.op (.ldp true .unit "j" "k") [.at (.var "w")]))

#print axioms setAts_opAts
#print axioms elabArgs_ats
#print axioms elabT_embed
#print axioms elabDecl_embedDecl
#print axioms elabProg_embedProg

end UnElab
