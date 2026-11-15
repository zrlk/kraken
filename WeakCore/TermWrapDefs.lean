import WeakCore.CoreTerm

/-! # TermWrapDefs: the A1 checker's definitions (moved, A1 checker invariant)

The interim scope rule A1's type tests and its typing-aware pass `checkW`, moved verbatim from
`TermScopeW` (and `opTys` from `TermScope`) so that the thread invariant (`TermSound`) can pin a
frame's context by `checkW`.  `ProgScopeOKW` stays in `TermScopeW`.
-/

namespace TermC1

open CoreLang CoreTerm

/-- A region payload: coupled. Affine payloads are admitted; the region `xchg` guards protect them. -/
def rgnPay (ke : KEnv) (u : Ty) : Bool := Ty.coupledOKIn ke u

/-- `t` carries no key (token, share or word) anywhere: not bare, not under a product, sum, reference,
array or binder.  Code pointers, capabilities and opaque values carry none.  A type variable must be
copy-kinded (a `μ`-bound one stands for the recursive type and is checked by recursion).  An `own`
reference does not occur here: `adapt` has turned it into a region reference. -/
def keyFreeIn (ke : KEnv) : Ty → Bool
  | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ | .word _ _ | .word2 _ _ => false
  | .prod a b | .sum a b => keyFreeIn ke a && keyFreeIn ke b
  | .array _ t | .ptr _ t | .ptrOpt _ t | .loc _ t | .refine t _ | .iex t | .iall t => keyFreeIn ke t
  | .tex κ t       => keyFreeIn (some κ :: ke) t
  | .mu t          => keyFreeIn (none :: ke) t
  | .tvar k        => ke.ask k true (·.copy)
  | _              => true

def keyFree (ke : KEnv) (t : Ty) : Bool := keyFreeIn ke t

/-- The region and cell type of a region-cell reference (not a protocol word). -/
def rgnCellAt (cx : Cx) (a : At) : Option (Idx × Ty) :=
  match cx.peek a with
  | .ok t => if (wordOf t).isNone then (match cellOf t with | some (.rgn r, u) => some (r, u) | _ => none) else none
  | .error _ => none

/-- A live token for `r`, compared syntactically: `Cx.hasTok`
with `eqI` replaced by `==`, so no fact can equate a token's region with another index.
Used by the view-sensitive region `xchg` check. -/
def hasTok1 (cx : Cx) (r : Idx) : Bool :=
  cx.vars.any fun (_, t, b) => b && match tokRgn t with
    | some s => r == s
    | none => false

/-- The syntactic token test implies `Cx.hasTok` (`==` implies `eqI`). -/
theorem hasTok1_hasTok {cx : Cx} {r : Idx} (h : hasTok1 cx r = true) : cx.hasTok r = true := by
  unfold hasTok1 at h; unfold Cx.hasTok
  obtain ⟨⟨x, t, b⟩, hm, he⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨(x, t, b), hm, ?_⟩
  dsimp only at he ⊢
  cases hs : tokRgn t with
  | none => simp [hs] at he
  | some s =>
    simp only [hs, Bool.and_eq_true] at he ⊢
    exact ⟨he.1, by unfold Cx.eqI; simp [he.2]⟩

def ruleA (cx : Cx) : Op → Bool
  | .load _ a => match rgnCellAt cx a with
      | some (r, u) => cx.opaqueOK u && u.arrFree && !affine cx.ke (adapt r u)
      | none => true
  | _ => true

/-- (FLD e) The payload type a `publish` or `intoRgn` atom points at must be `drf1`: no region
locative (and no `iall`) inside a published or region cell's type.  Non-reference forms pass (the
typing rule refuses them). -/
@[simp] def pubPayDrf (cx : Cx) (a : At) : Bool :=
  match cx.peek a with
  | .ok (.ptr _ u) => drf1 u
  | .ok (.refine (.loc _ u) _) => drf1 u
  | _ => true

/-- (FLD e) `pubPayDrf` at a `publish` or `intoRgn`; every other operation passes. -/
@[simp] def pubOpDrf (cx : Cx) : Op → Bool
  | .publish a => pubPayDrf cx a
  | .intoRgn _ a => pubPayDrf cx a
  | _ => true

end TermC1

namespace TermScope

open CoreLang CoreTerm

/-- The type annotations of an operation. -/
def opTys : Op → List Ty
  | .inl τ _ | .inr τ _ | .null _ τ | .fold _ τ | .newBuf _ τ | .pack _ _ τ | .zero τ => [τ]
  | .packT _ σ τ => [σ, τ]
  | .call _ _ _ ts => ts
  | .spawn _ _ T ts => T :: ts
  | .spawnI _ _ _ _ ts => ts
  | .isTy _ τ => [τ]
  | _ => []

/-- (A1) `call`'s type arguments and `packT`'s witness are `argOK`; every annotation `wrapOK`. -/
def opArgOK : Op → Bool
  | .call _ _ _ ts => ts.all argOK
  | .spawn _ _ T ts => wrapOK T && ts.all argOK
  | .spawnI _ _ _ T ts => wrapOK T && ts.all argOK
  | .packT _ σ τ => argOK σ && wrapOK τ
  | op => (opTys op).all wrapOK

/-- Is `x` the atom's variable? -/
def freeA (x : String) : At → Bool
  | .var y => x == y
  | _ => false

/-- The atoms an operation reads (`validate`'s variable included). -/
def opAts : Op → List At
  | .atom a => [a]
  | .pair a b => [a, b]
  | .inl _ a => [a]
  | .inr _ a => [a]
  | .add a b => [a, b]
  | .sub a b => [a, b]
  | .new a _ => [a]
  | .null _ _ => []
  | .fold a _ => [a]
  | .publish a => [a]
  | .intoRgn _ a => [a]
  | .newBuf n _ => [n]
  | .idx b i => [b, i]
  | .bufInit b i v => [b, i, v]
  | .fld _ a => [a]
  | .load _ a => [a]
  | .store _ a v tok => [a, v] ++ tok.toList
  | .fence _ => []
  | .mkWord _ _ v tok => [v, tok]
  | .pack a _ _ => [a]
  | .packT a _ _ => [a]
  | .validate y => [.var y]
  | .call _ _ a _ => [a]
  | .spawn _ a _ _ => [a]
  | .spawnI _ _ a _ _ => [a]
  | .ext _ a => [a]
  | .borrow _ t => [t]
  | .endBorrow t => [t]
  | .xchg a v => [a, v]
  | .fnptr _ => []
  | .callc f a => [f, a]
  | .rem a n => [a, n]
  | .nameI a => [a]
  | .xchgAt b i v => [b, i, v]
  | .loadAt b i => [b, i]
  | .bits _ a b => [a, b]
  | .bit1 _ a => [a]
  | .vmatch lo hi b => [lo, hi, b]
  | .band a m => [a, m]
  | .zero _ => []
  | .loadAtF b i _ => [b, i]
  | .xchgAtF b i _ v => [b, i, v]
  | .freeze t => [t]
  | .cvt _ _ a => [a]
  | .toInt a => [a]
  | .asLanes _ _ a => [a]
  | .fop _ a b => [a, b]
  | .fcmp _ a b => [a, b]
  | .fop1 _ a => [a]
  | .lane a j => [a, j]
  | .setLane a j v => [a, j, v]
  | .ldl b i => [b, i]
  | .stl b i v => [b, i, v]
  | .ldlw b wi j => [b, wi, j]
  | .stlw b wi j v => [b, wi, j, v]
  | .mkWord2 _ _ v0 v1 tok => [v0, v1, tok]
  | .ldp _ a _ _ => [a]
  | .stp _ a v0 v1 tok => [a, v0, v1, tok]
  | .mkEPair _ _ v0 v1 => [v0, v1]
  | .mkTicket _ _ _ v tok => [v, tok]
  | .claim a tok => [a, tok]
  | .fetch _ _ _ a v => [a, v]
  | .isTy a _ => [a]

/-- Does `x` occur free in the term?  Binders are exactly the variables the
runtime pushes on the environment (`tstep`). -/
def freeB (x : String) : Expr → Bool
  | .let_ y op e => (opAts op).any (freeA x) || (x != y && freeB x e)
  | .split a y z e => freeA x a || (x != y && x != z && freeB x e)
  | .unpack a _ y e => freeA x a || (x != y && freeB x e)
  | .unpackT a _ y e => freeA x a || (x != y && freeB x e)
  | .region a _ p t e => freeA x a || (x != p && x != t && freeB x e)
  | .openPub a _ p c e => freeA x a || (x != p && x != c && freeB x e)
  | .case a y e₁ z e₂ => freeA x a || (x != y && freeB x e₁) || (x != z && freeB x e₂)
  | .ifnull a e₁ y e₂ => freeA x a || freeB x e₁ || (x != y && freeB x e₂)
  | .parity a _ e₁ e₂ => freeA x a || freeB x e₁ || freeB x e₂
  | .ifeq a b e₁ e₂ => freeA x a || freeA x b || freeB x e₁ || freeB x e₂
  | .cas _ _ w e v t ok fail => freeA x w || freeA x e || freeA x v || (x != t && freeB x ok) || freeB x fail
  | .casp _ _ w e0 e1 v0 v1 t ok fail => freeA x w || freeA x e0 || freeA x e1 || freeA x v0 || freeA x v1 ||
      (x != t && freeB x ok) || freeB x fail
  | .ret a => freeA x a
  | .tail _ _ a _ => freeA x a

open TermC1 in
/-- (A1) **The typing-aware pass**: `CoreTerm.check`, verbatim (same checker functions), with
every `let`-bound type `wrapOK`, `opArgOK` at every operation and `tail`'s type arguments
`argOK`.  (The other binders are components of a checked type, or fixed token/unit types.) -/
def checkW (p : Prog) (cx : Cx) : Expr → M Unit
  | .let_ x op e => do
      if !opArgOK op then throw "A1: a type argument or witness carries a key"
      if !ruleA cx op then
        throw "c1: torn read of a region cell whose type can never be validated (layout depends on an unpacked type, array by value, or an affine payload)"
      -- c1 (a coupled payload at intoRgn; the region-xchg guards at xchg)
      -- c1 (FLD e): a published or region cell's type is drf1
      if !pubOpDrf cx op then throw "c1: a published or region cell's type must not hold a region locative (drf1)"
      match op with
      | .intoRgn _ a0 =>
          match cx.peek a0 with
          | .ok (.ptr .own u0) => if !rgnPay cx.ke u0 then throw "c1: intoRgn payload not coupled"
          | .ok _ => throw "c1: intoRgn buffer form is outside c1"
          | .error _ => pure ()
      | .xchg a0 _ =>
          match cx.peek a0 with
          | .ok ta => match cellOf ta with
              | some (.rgn r, u) =>
                  -- an affine payload only under a held token of the region (`Cx.hasTok`, up to the index facts);
                  -- an unsealed token is refused by the observable-state check below
                  -- a later proof of exclusive region use must key on the region's value, not its name: this check compares indices up to the index facts
                  if affine cx.ke (adapt r u) && !cx.hasTok r then
                    throw "c1: region xchg of an affine payload needs a held token of the region"
                  if affine cx.ke (adapt r u) && !keyFree cx.ke (adapt r u) then
                    throw "c1: region xchg of an affine payload with a key (token, share or word)"
                  if cx.hasTok r && !cx.sealedR r then
                    throw "c1: region xchg under a token taken from an observable state before fence st (§4.4 rule 7)"
                  if Ty.sensitiveIn cx.ke (adapt r u) && !hasTok1 cx r then
                    throw "c1: region xchg of a view-sensitive payload needs a held token"
              | _ => pure ()
          | .error _ => pure ()
      | _ => pure ()
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
          -- c1 (e1)
          if !Ty.coupledOKIn cx.ke u then throw "c1 (e1): region payload not coupledOK"
          -- c1 (FLD e)
          if !drf1 u then throw "c1: a published or region cell's type must not hold a region locative (drf1)"
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          checkW p cx e
      | .refine (.loc .own (.array n u)) (.ini k) => do
          -- An own buffer can be opened as a region directly: the region's
          -- pointer is the buffer's locative, its initialized prefix fixed.
          if !rgnCellOK cx.ke (.array n u) then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          -- c1 (e1; live region buffers out)
          if !Ty.coupledOKIn cx.ke (.array n u) then throw "c1 (e1): region buffer payload not coupledOK"
          if freeB pn e then throw "c1: live region buffers are outside c1"
          -- c1 (FLD e)
          if !drf1 (.array n u) then throw "c1: a published or region cell's type must not hold a region locative (drf1)"
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
