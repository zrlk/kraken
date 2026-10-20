/-
# Scope — the index variables in scope at each point of a code block

Index variables inside code are mostly bound syntactically (`unpack`,
`region`, `openPub`, `parity`, `rem`/`band`/`nameI`), but two binders depend on
types: loading a *protocol word* binds a fresh index (`CoreTerm.checkOp`,
`.load`), and the false branch of an `if` may bind one (`CoreTerm.noCx`).  A
tool that reads or writes code as text (the parser and printer in
`Syntax.lean`, the formatter in `CoreUtils.lean`) must know exactly which
index names are in scope, or de Bruijn indices in types written inside code
mean the wrong thing.

`branches p cx e` gives the checker's context for each immediate subterm of
`e`, computed with the checker's own functions (`checkOp`, `Cx.use`, `Cx.bind`,
`Cx.push`, `intIdx`, `noCx`, `lendCx`, …), line for line as `CoreTerm.check`
does.  It looks only at `e`'s head (the operation, the binder names), never at
the subterms, so a parser can ask before it has read them.  Where the
checker would fail (an ill-typed prefix, an unknown callee), the context is
`none`, and a client falls back to the syntactic rule: after a `load` or in an
`else`, earlier index names cannot be used.

Nothing here is trusted.  A client that used a wrong context would only
produce a different program, which the checker then judges as written.

Build: LEAN_PATH=build lean -o build/Scope.olean Scope.lean
(after CoreTerm.olean)
-/
import WeakCore.CoreTerm
open CoreLang CoreTerm

namespace Scope

/-- The checker's starting context for a code block (as `checkDecl`). -/
def start (d : Decl) : Cx :=
  { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
    ke := d.tparams.reverse.map some }

/-- A placeholder subterm: `branches` never looks at subterms. -/
def hole : Expr := .ret .unit

/-- The checker's context for each immediate subterm of `e`, in order (`let`:
the body; `case`/`ifnull`/`if`/`cas`/`parity`: both branches; `ret`/`tail`:
none).  `none` where the checker would fail before reaching that subterm. -/
def branches (p : Prog) (cx : Cx) : Expr → List (Option Cx)
  | .let_ x op _ => [(checkOp p cx x op).toOption]
  | .split a x y _ => [Except.toOption do
      let (t, cx) ← cx.use a
      match t with
      | .prod u v => do let cx ← cx.bind x u; cx.bind y v
      | _ => throw ""]
  | .unpack a i x _ => [Except.toOption do
      let (t, cx) ← cx.use a
      match t with
      | .iex b => (cx.push i).bind x b
      | _ => throw ""]
  | .unpackT a _ x _ => [Except.toOption do
      let (t, cx) ← cx.use a
      match t with
      | .tex κ b => if !b.guardT 0 then throw "" else (cx.pushT κ).bind x b
      | _ => throw ""]
  | .region a rn pn tn _ => [Except.toOption do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          cx.bind tn (.tok (.var 0) none)
      | .refine (.loc .own (.array n u)) (.ini k) => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0))
          cx.bind tn (.tok (.var 0) none)
      | _ => throw ""]
  | .openPub a rn pn cn _ => [Except.toOption do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .pub u => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          cx.bind cn (.cap .pub (.var 0))
      | _ => throw ""]
  | .case a x _ y _ =>
      match cx.use a with
      | .ok (.sum u v, cx) => [(cx.bind x u).toOption, (cx.bind y v).toOption]
      | _ => [none, none]
  | .ifnull a _ y _ =>
      match cx.use a with
      | .ok (.ptrOpt μ u, cx) => [some cx, (cx.bind y (.ptr μ u)).toOption]
      | _ => [none, none]
  | .parity a k _ _ =>
      match intIdx cx a with
      | .ok i =>
          match (cx.norm i).bind Lin.asVar? with
          | some v =>
              let cx := cx.push k
              [some { cx with facts := (v + 1, .smul 2 (.var 0)) :: cx.facts },
               some { cx with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: cx.facts }]
          | none => [none, none]
      | .error _ => [none, none]
  | .ifeq a b _ _ =>
      if plainEq cx a b then [some cx, some cx]
      else
        match intIdx cx a, intIdx cx b with
        | .ok i, .ok j =>
            match cx.norm i, cx.norm j with
            | some ni, some nj =>
                let yes : Option Cx :=
                  if ni == nj then some cx
                  else match ni.asVar?, nj.asVar? with
                    | some v, _ =>
                        if nj.mentions v then none
                        else some { cx with facts := (v, nj.toIdx) :: cx.facts }
                    | _, some v =>
                        if ni.mentions v then none
                        else some { cx with facts := (v, ni.toIdx) :: cx.facts }
                    | _, _ =>
                        match zeroVar ni nj with
                        | some u => some { cx with facts := (u, .lit 0) :: cx.facts }
                        | none => none
                -- The checker reaches `no` only if `yes` checked.
                [yes, yes.map fun _ => noCx cx ni nj]
            | _, _ => [none, none]
        | _, _ => [none, none]
  | .cas acq rel w e v t _ _ =>
      match cx.peek w with
      | .error _ => [none, none]
      | .ok tw =>
      match wordOf tw with
      | none =>
          -- Both branches run after `use v`: `ok` with `t : Unit` bound.
          let after : Option Cx := Except.toOption do
            let u ← casCellTy cx tw
            if u.rawWords != some 1 then throw ""
            let _ ← cx.peek e
            let (_, cx) ← cx.use v
            pure cx
          let ok := after.bind fun c => (c.bind t .unit).toOption
          [ok, ok.bind fun _ => after]
      | some (r, P) =>
          let ok : Option Cx := Except.toOption do
            let i ← intIdx cx e
            let j ← intIdx cx v
            let (c, k) ← classifyM cx P i
            let (c', k') ← classifyM cx P j
            if P.epoch then cx.bind t (.tokE r (.word P) j)
            else
              let cl' ← clauseM P c'
              if cl'.holds then lendCx cx acq rel r (shareMove P c k c' k') t
              else
                let cx' ← cx.bind t (.tok r (some (P, j)))
                pure (if monotone P then { cx' with unsealed := r :: cx'.unsealed } else cx')
          [ok, ok.map fun _ => cx]
  | .casp acq _ w e0 e1 v0 v1 t _ _ =>
      match cx.peek w with
      | .error _ => [none, none]
      | .ok tw =>
      match word2Of tw with
      | none =>
          match epairOf tw with
          | none => [none, none]
          | some (r, P) =>
              -- The epoch-fenced write binds `t : Unit` when a token of the new epoch is live.
              let ok : Option Cx := Except.toOption do
                let j0 ← intIdx cx v0
                if !cx.hasTokE r P j0 then throw ""
                cx.bind t .unit
              [ok, ok.map fun _ => cx]
      | some (r, P) =>
          let ok : Option Cx := Except.toOption do
            let i0 ← intIdx cx e0
            let i1 ← intIdx cx e1
            let j0 ← intIdx cx v0
            let j1 ← intIdx cx v1
            let (c, k0, k1) ← classify2M cx P i0 i1
            let (c', k0', k1') ← classify2M cx P j0 j1
            let cl ← clause2M P c
            let cl' ← clause2M P c'
            if !cl.holds || !pstep2 P c k0 k1 c' k0' k1' then throw ""
            if cl'.holds then
              if bump2 P k0 k0' then
                if !acq then throw ""
                cx.bind t (.tokE r (.pair P) j0)
              else cx.bind t .unit
            else if !acq then throw ""
            else cx.bind t (.tok2 r P j0 j1)
          [ok, ok.map fun _ => cx]
  | .ret _ => []
  | .tail _ _ _ _ => []

/-- The number of immediate subterms. -/
def arity : Expr → Nat
  | .let_ .. | .split .. | .unpack .. | .unpackT .. | .region .. | .openPub .. => 1
  | .case .. | .ifnull .. | .parity .. | .ifeq .. | .cas .. | .casp .. => 2
  | .ret _ | .tail .. => 0

/-- `branches` from a context that may be unknown. -/
def branchesO (p : Prog) : Option Cx → Expr → List (Option Cx)
  | some cx, e => branches p cx e
  | none, e => List.replicate (arity e) none

/-- The `i`th branch context (`none` if unknown). -/
def nth (p : Prog) (cx : Option Cx) (e : Expr) (i : Nat) : Option Cx :=
  ((branchesO p cx e)[i]?).getD none

/-- Does a walk from `d`'s start follow the checker to every `ret`/`tail`?
(True of every code block the checker accepts: a test that `branches` covers
the checker, used in `#guard`s over the libraries.) -/
partial def covers (p : Prog) (d : Decl) : Bool :=
  let rec go (cx : Cx) (e : Expr) : Bool :=
    let subs : List Expr := match e with
      | .let_ _ _ b | .split _ _ _ b | .unpack _ _ _ b | .unpackT _ _ _ b | .region _ _ _ _ b
      | .openPub _ _ _ _ b => [b]
      | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂
      | .cas _ _ _ _ _ _ e₁ e₂ | .casp _ _ _ _ _ _ _ _ e₁ e₂ => [e₁, e₂]
      | .ret _ | .tail _ _ _ _ => []
    let bs := branches p cx e
    bs.length == subs.length &&
      (bs.zip subs).all fun (c, s) => match c with
        | some c => go c s
        | none => false
  go (start d) d.body

-- Every library code block is followed to the end.
#guard mutexLib.all (covers mutexLib ·)
#guard seqLib.all (covers seqLib ·)
#guard (queueLib .int).all (covers (queueLib .int) ·)
#guard (claimLib .int).all (covers (claimLib .int) ·)
#guard polyQueueLib.all (covers polyQueueLib ·)
#guard pcLib.all (covers pcLib ·)

end Scope
