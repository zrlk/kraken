import WeakCore.TermRun

/-! # TermBufDefs: the (d′) R1 buffer-scope check

`bufNeed top ke τ`: may a piece of a value of `τ`, other than an exempt top-level protocol word,
carry a resource?  `none`: yes, from a token, share, own handle, a non-exempt word, or a locally
bound non-`copy` type variable.  `some L`: only through the free type variables in `L` (each with
whether it occurs at the top, where a word substituted for it stays exempt).  `bufNeed top ke τ =
some []` is the r4 check `bufResIn top ke τ = false`.

`ProgBufOK`: every `newBuf τ` passes once the declaration's *buffer-used* type parameters
(`BufUsed`) are taken as resource-free, and every call or tail call passes, at a callee's
buffer-used parameter, a type argument passing the same check.  `BufUsed` is the least fixpoint,
computed by iteration and checked closed.  `InitBufOK`: the initial threads' terms and frames pass
with no type parameter.
-/

namespace TermBufDefs
open CoreLang CoreTerm TermRun

/-- Both parts pass: their needs together. -/
def oapp {α : Type} : Option (List α) → Option (List α) → Option (List α)
  | some a, some b => some (a ++ b)
  | _, _ => none

/-- Out of a binder: its variable (index 0) must not be needed; the rest shift down. -/
def downN (L : List (Nat × Bool)) : Option (List (Nat × Bool)) :=
  if L.any (fun x => x.1 == 0) then none else some (L.map fun x => (x.1 - 1, x.2))

/-- (d′, R1) **The needs of a buffer element type** (see the module doc). -/
def bufNeed (top : Bool) (ke : KEnv) : Ty → Option (List (Nat × Bool))
  | .word _ P     => if top && !P.ghost then some [] else none
  | .word2 _ _    => if top then some [] else none
  | .epair _ _    => none
  | .tok _ _      => none
  | .share _      => none
  | .tok2 _ _ _ _ => none
  | .tokE _ _ _   => none
  | .ptr .own _   => none
  | .ptrOpt .own _ => none
  | .loc .own _   => none
  | .prod a b     => oapp (bufNeed top ke a) (bufNeed top ke b)
  | .array _ t    => bufNeed top ke t
  | .mu t         => (bufNeed false (none :: ke) t).bind downN
  | .sum a b      => oapp (bufNeed false ke a) (bufNeed false ke b)
  | .refine t _   => bufNeed false ke t
  | .iex t        => bufNeed false ke t
  | .iall t       => bufNeed false ke t
  | .tex κ t      => (bufNeed false (some κ :: ke) t).bind downN
  | .tvar k       => if ke.ask k true (·.copy) then some [] else some [(k, top)]
  | _             => some []

/-- Needs at the declaration's parameters: under `dep` `unpackT`s (whose variables, of the
weakest kind, may not be needed), a parameter index below `nT`. -/
def mapNeed (dep nT : Nat) (L : List (Nat × Bool)) : Option (List (Nat × Bool)) :=
  L.foldr (fun x acc => acc.bind fun a =>
    if dep ≤ x.1 ∧ x.1 - dep < nT then some ((x.1 - dep, x.2) :: a) else none) (some [])

/-- A call's type arguments at the callee's buffer-used parameters `Uf` (`σs[k] = ts[n-1-k]`). -/
def argNeed (Uf : List (Nat × Bool)) (nT : Nat) (ke : KEnv) (dep : Nat) (ts : List Ty) :
    Option (List (Nat × Bool)) :=
  Uf.foldr (fun x acc => oapp acc <|
    if x.1 < ts.length then
      match ts[ts.length - 1 - x.1]? with
      | some σ => (bufNeed x.2 ke σ).bind (mapNeed dep nT)
      | none => none
    else none) (some [])

/-- The buffer-used parameters of `f` in table `T` (the first entry, as `find?`). -/
def look (T : List (String × List (Nat × Bool))) (f : String) : List (Nat × Bool) :=
  ((T.find? (·.1 == f)).map (·.2)).getD []

/-- An operation's needs. -/
def opNeed (T : List (String × List (Nat × Bool))) (nT : Nat) (ke : KEnv) (dep : Nat) : Op →
    Option (List (Nat × Bool))
  | .newBuf _ τ => (bufNeed true ke τ).bind (mapNeed dep nT)
  | .call f _ _ ts => argNeed (look T f) nT ke dep ts
  | _ => some []

/-- (d′, R1) **An expression's needs**; `ke` grows at `unpackT` by the weakest kind. -/
def bufWalk (T : List (String × List (Nat × Bool))) (nT : Nat) : KEnv → Nat → Expr →
    Option (List (Nat × Bool))
  | ke, dep, .let_ _ op e => oapp (opNeed T nT ke dep op) (bufWalk T nT ke dep e)
  | ke, dep, .split _ _ _ e => bufWalk T nT ke dep e
  | ke, dep, .unpack _ _ _ e => bufWalk T nT ke dep e
  | ke, dep, .unpackT _ _ _ e => bufWalk T nT (some Kind.top :: ke) (dep + 1) e
  | ke, dep, .region _ _ _ _ e => bufWalk T nT ke dep e
  | ke, dep, .openPub _ _ _ _ e => bufWalk T nT ke dep e
  | ke, dep, .case _ _ e₁ _ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | ke, dep, .ifnull _ e₁ _ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | ke, dep, .parity _ _ e₁ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | ke, dep, .ifeq _ _ e₁ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | ke, dep, .cas _ _ _ _ _ _ e₁ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | ke, dep, .casp _ _ _ _ _ _ _ _ e₁ e₂ => oapp (bufWalk T nT ke dep e₁) (bufWalk T nT ke dep e₂)
  | _, _, .ret _ => some []
  | ke, dep, .tail f _ _ ts => argNeed (look T f) nT ke dep ts

/-- A declaration's needs, at its type parameters. -/
def declNeed (T : List (String × List (Nat × Bool))) (d : Decl) : Option (List (Nat × Bool)) :=
  bufWalk T d.tparams.length (d.tparams.reverse.map some) 0 d.body

/-- One round: every declaration's needs, joined to the table's. -/
def bufRound (p : Prog) (T : List (String × List (Nat × Bool))) :
    Option (List (String × List (Nat × Bool))) :=
  p.mapM fun d => (declNeed T d).map fun L => (d.name, (look T d.name ++ L).eraseDups)

/-- `n` rounds from `T`. -/
def bufIter (p : Prog) : Nat → List (String × List (Nat × Bool)) → Option (List (String × List (Nat × Bool)))
  | 0, T => some T
  | n + 1, T => (bufRound p T).bind (bufIter p n)

/-- The `BufUsed` table: enough rounds to saturate (each round adds an entry or is stable). -/
def bufTable (p : Prog) : Option (List (String × List (Nat × Bool))) :=
  bufIter p ((p.map fun d => 2 * d.tparams.length).sum + 1) []

/-- The table is closed: every declaration passes with its needs in the table. -/
def bufClosed (p : Prog) (T : List (String × List (Nat × Bool))) : Bool :=
  p.all fun d => match declNeed T d with
    | some L => L.all fun x => (look T d.name).contains x
    | none => false

/-- (d′, R1) **The program passes the buffer-scope check.** -/
def ProgBufOK (p : Prog) : Bool :=
  match bufTable p with
  | some T => bufClosed p T
  | none => false

/-- (d′, R1) **The initial threads pass**: their terms and frames, with no type parameter. -/
def InitBufOK (p : Prog) (c0 : Cfg) : Bool :=
  match bufTable p with
  | some T => c0.ths.all fun th => bufWalk T 0 [] 0 th.term == some [] &&
      th.stack.all fun fr => bufWalk T 0 [] 0 fr.body == some []
  | none => false

end TermBufDefs
