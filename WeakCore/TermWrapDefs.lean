import WeakCore.CoreTerm

/-! # TermWrapDefs: the A1 checker's definitions (moved, A1 checker invariant)

The interim scope rule A1's type tests and its typing-aware pass `checkW`, moved verbatim from
`TermScopeW` (and `opTys` from `TermScope`) so that the thread invariant (`TermSound`) can pin a
frame's context by `checkW`.  `ProgScopeOKW` stays in `TermScopeW`.
-/

namespace TermScope

open CoreLang CoreTerm

/-- The type annotations of an operation. -/
def opTys : Op → List Ty
  | .inl τ _ | .inr τ _ | .null _ τ | .fold _ τ | .newBuf _ τ | .pack _ _ τ | .zero τ => [τ]
  | .packT _ σ τ => [σ, τ]
  | .call _ _ _ ts => ts
  | .spawn _ _ T ts => T :: ts
  | _ => []

/-- (A1) `call`'s type arguments and `packT`'s witness are `argOK`; every annotation `wrapOK`. -/
def opArgOK : Op → Bool
  | .call _ _ _ ts => ts.all argOK
  | .spawn _ _ T ts => wrapOK T && ts.all argOK
  | .packT _ σ τ => argOK σ && wrapOK τ
  | op => (opTys op).all wrapOK

/-- (A1) **The typing-aware pass**: `CoreTerm.check`, verbatim (same checker functions), with
every `let`-bound type `wrapOK`, `opArgOK` at every operation and `tail`'s type arguments
`argOK`.  (The other binders are components of a checked type, or fixed token/unit types.) -/
def checkW (p : Prog) (cx : Cx) : Expr → M Unit
  | .let_ x op e => do
      if !opArgOK op then throw "A1: a type argument or witness carries a key"
      let cx ← checkOp p cx x op
      match cx.vars.find? (·.1 == x) with
      | some (_, t, _) => if !wrapOK t then throw s!"A1: {x} has a key-carrying wrapper type"
      | none => pure ()
      checkW p cx e
  | .split a x y e => do
      let (t, cx) ← cx.use a
      match t with
      | .prod u v => do
          let cx ← cx.bind x u
          let cx ← cx.bind y v
          checkW p cx e
      | _ => throw "split needs a pair"
  | .unpack a i x e => do
      let (t, cx) ← cx.use a
      match t with
      | .iex b => do
          let cx ← (cx.push i).bind x b
          checkW p cx e
      | _ => throw "unpack needs an index existential"
  | .unpackT a _ x e => do
      let (t, cx) ← cx.use a
      match t with
      | .tex κ b => do
          if !b.guardT 0 then
            throw "unpack: the package's variable must occur only under a reference"
          let cx ← (cx.pushT κ).bind x b
          checkW p cx e
      | _ => throw "unpack at a type needs a type existential"
  | .region a rn pn tn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u => do
          -- D1: a region cell is a published cell whose writes the token gates,
          -- so its type is shareable (no `own` inside) and opening it fences.
          if !rgnCellOK cx.ke u then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          checkW p cx e
      | .refine (.loc .own (.array n u)) (.ini k) => do
          -- An own buffer can be opened as a region directly: the region's
          -- pointer is the buffer's locative, its initialized prefix fixed.
          if !rgnCellOK cx.ke (.array n u) then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          let cx := cx.push rn
          let cx ← cx.bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          checkW p cx e
      | _ => throw "region needs an own reference or an own buffer"
  | .openPub a rn pn cn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .pub u => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind cn (.cap .pub (.var 0))
          checkW p cx e
      | _ => throw "openPub needs a pub reference"
  | .case a x e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .sum u v => do
          checkW p (← cx.bind x u) e₁
          checkW p (← cx.bind y v) e₂
      | _ => throw "case needs a sum"
  | .ifnull a e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .ptrOpt μ u => do
          checkW p cx e₁
          checkW p (← cx.bind y (.ptr μ u)) e₂
      | _ => throw "ifnull needs a nullable reference"
  | .parity a k ev od => do
      let i ← intIdx cx a
      let v ← match (cx.norm i).bind Lin.asVar? with
        | some v => pure v
        | none => throw "parity: the index is not a free variable, so there is nothing to refine"
      let cx := cx.push k
      checkW p { cx with facts := (v + 1, .smul 2 (.var 0)) :: cx.facts } ev
      checkW p { cx with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: cx.facts } od
  | .ifeq a b yes no =>
      if plainEq cx a b then do checkW p cx yes; checkW p cx no
      else do
      let i ← intIdx cx a
      let j ← intIdx cx b
      match cx.norm i, cx.norm j with
      | some ni, some nj =>
          if ni == nj then checkW p cx yes
          else
            match ni.asVar?, nj.asVar? with
            | some v, _ =>
                if nj.mentions v then throw "ifeq: cannot record the equality"
                checkW p { cx with facts := (v, nj.toIdx) :: cx.facts } yes
            | _, some v =>
                if ni.mentions v then throw "ifeq: cannot record the equality"
                checkW p { cx with facts := (v, ni.toIdx) :: cx.facts } yes
            | _, _ =>
                match zeroVar ni nj with
                | some u => checkW p { cx with facts := (u, .lit 0) :: cx.facts } yes
                | none => throw "ifeq: cannot record the equality"
          checkW p (noCx cx ni nj) no
      | _, _ => throw "ifeq: index outside the decidable fragment"
  | .cas acq rel w e v t ok fail => do
      let tw ← cx.peek w
      match wordOf tw with
      | none =>
          -- A plain `pub` cell: compare-and-swap one word.  No region, no token:
          -- the cell's type is invariant, so success and failure both leave it
          -- well typed, and the expected value is compared, not duplicated.
          let u ← casCellTy cx tw
          if u.rawWords != some 1 then throw "cas needs a one-word cell (§3.5)"
          if affine cx.ke u then throw "cas would duplicate an affine value"
          let te ← cx.peek e
          let (tv, cx) ← cx.use v
          if !sub cx te u then throw "cas: the expected value does not have the cell's type"
          if !sub cx tv u then throw "cas: the new value does not have the cell's type"
          if Ty.sensitiveIn cx.ke u && !(acq && rel) then
            throw "cas: a view-sensitive type needs acq and rel (§3.8)"
          checkW p (← cx.bind t .unit) ok
          checkW p cx fail
      | some (r, P) =>
      if P.epoch then
        -- An epoch counter: `cas e -> e + 1` enters epoch `e + 1` and yields
        -- its token, never the region (the counter has no held state).
        if !acq then throw "entering an epoch needs acq"
        let i ← intIdx cx e
        let j ← intIdx cx v
        let (c, k) ← classifyM cx P i
        let (c', k') ← classifyM cx P j
        if !pstep P c k c' k' then throw "not a transition of the protocol"
        checkW p (← cx.bind t (.tokE r (.word P) j)) ok
        checkW p cx fail
      else
        if P.ghost then throw "cas on a ghost word: it has no runtime value"
        let i ← intIdx cx e
        let j ← intIdx cx v
        let (c, k) ← classifyM cx P i
        let (c', k') ← classifyM cx P j
        let cl ← clauseM P c
        let cl' ← clauseM P c'
        if !cl.holds then throw "cas from a held state: the holder stores instead"
        if !pstep P c k c' k' then throw "not a transition of the protocol"
        if cl'.holds then
          checkW p (← lendCx cx acq rel r (shareMove P c k c' k') t) ok
        else
          if P.lends.contains c || P.lendsDown.contains c then
            throw "taking the region from a lending state: shares are out"
          if !acq then throw "taking the region needs acq"
          let cx' ← cx.bind t (.tok r (some (P, j)))
          let cx' := if monotone P then { cx' with unsealed := r :: cx'.unsealed } else cx'
          checkW p cx' ok
        checkW p cx fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail => do
      let tw ← cx.peek w
      match word2Of tw with
      | none =>
        match epairOf tw with
        | none => throw "casp needs a reference to a protocol pair"
        | some (r, P) =>
          -- The epoch-fenced write: the new epoch must be the one a live epoch
          -- token names, and the write publishes (`rel`).  The compare is the
          -- fence: a re-stamp by a later epoch makes a stale writer's expected
          -- pair wrong, and a stale pair that lands still names its epoch.
          if !rel then throw "an epoch-fenced write needs rel"
          let _ ← intIdx cx e0
          let _ ← intIdx cx e1
          let j0 ← intIdx cx v0
          let _ ← intIdx cx v1
          if !cx.hasTokE r P j0 then throw "an epoch-fenced write needs the epoch token of its new epoch"
          checkW p (← cx.bind t .unit) ok
          checkW p cx fail
      | some (r, P) =>
      let i0 ← intIdx cx e0
      let i1 ← intIdx cx e1
      let j0 ← intIdx cx v0
      let j1 ← intIdx cx v1
      let (c, k0, k1) ← classify2M cx P i0 i1
      let (c', k0', k1') ← classify2M cx P j0 j1
      let cl ← clause2M P c
      let cl' ← clause2M P c'
      if !cl.holds then throw "casp from a held state: the holder stores instead"
      if !pstep2 P c k0 k1 c' k0' k1' then throw "not a transition of the pair protocol"
      if cl'.holds then
        if bump2 P k0 k0' then
          -- An epoch pair's move that bumps the epoch issues the new epoch's token.
          if !acq then throw "entering an epoch needs acq"
          checkW p (← cx.bind t (.tokE r (.pair P) j0)) ok
        else
          -- Between shared states nothing changes hands (a pair lends no shares).
          checkW p (← cx.bind t .unit) ok
      else
        if !acq then throw "taking the region needs acq"
        checkW p (← cx.bind t (.tok2 r P j0 j1)) ok
      checkW p cx fail
  | .ret a => do
      let (t, cx) ← cx.use a
      noLeak cx t
      noDrop cx
      if !sub cx t cx.ret then throw "ret: the value does not have the return type"
  | .tail f is a ts => do
      if !ts.all argOK then throw "A1: a tail type argument carries a key"
      let d ← p.find f
      let (at_, rt) ← instantiate cx d is ts
      let (t, cx) ← cx.use a
      noLeak cx t
      noDrop cx
      if !sub cx t at_ then throw s!"tail call {f}: argument type mismatch"
      if !sub cx rt cx.ret then throw s!"tail call {f}: return type mismatch"


end TermScope
