import WeakCore.TermScope
import WeakCore.TermWrapDefs

/-! # TermC1Defs: region c1, the language-side definitions under new names

New definitions only, alongside the old ones; nothing here is used by any existing definition, premise
or theorem.  When the change is adopted the old names are redirected to these and the
parallel copies are deleted.

* `drf1` (T1): `drf` with the region arms by plain recursion (`.ptr _ t`, `.ptrOpt _ t`, `.loc μ t`).
* `opOK1`/`allOK1`/`ProgScopeOK1` (T2): `opOK`/`allOK`/`ProgScopeOK` with `drf1`, `.intoRgn` admitted
  (h2) and the `region` binder unrestricted (b1).
* `capFree`, `rgnPay` (g1): a live region payload is coupled, copyable and capability-free.
* `monoSaw`, `rgnCellAt`, `rgnOpOK1` (i1): region-cell loads only with a tok/share witness and no
  ordered observation of a monotone word in scope; stores only with the sealed token and a copyable
  cell type; `xchg`/`fetch` banned (and `cas` in `checkW1`).
* `checkW1` (T3): `TermScope.checkW` (TermWrapDefs L32–246) copied with exactly four insertions
  (marked `c1`): `rgnOpOK1` + `rgnPay` at `intoRgn` (operation arm), e1 `coupledOK` + live `rgnPay` at
  `region`, the same at the buffer `region` (live buffers out), and no `cas` at a region cell.
* `declWrapOK1`/`ProgWrapOK1`/`ProgScopeOKW1`: `TermScopeW`'s, over `checkW1`/`ProgScopeOK1`.
-/

namespace TermC1

open CoreLang CoreTerm TermScope

/-- (T1, c1) `drf` with the region-reference arms by plain recursion. -/
def drf1 : Ty → Bool
  | .prod a b => drf1 a && drf1 b
  | .sum a b => drf1 a && drf1 b
  | .code a b => drf1 a && drf1 b
  | .array _ t => drf1 t
  | .ptr _ t => drf1 t
  | .ptrOpt _ t => drf1 t
  | .loc μ t => drfM μ && drf1 t
  | .mu t => drf1 t
  | .tex _ t => drf1 t
  | .iall _ => false
  | .iex t => drf1 t
  | .refine t _ => drf1 t
  | _ => true

/-- (T2, c1, h2) `opOK` over `drf1`, with `.intoRgn` admitted. -/
def opOK1 : Op → Bool
  | .validate _ => false
  | .mkTicket _ _ _ _ _ | .claim _ _ => false
  | .null μ τ => drfM μ && drf1 τ
  | op => (opTys op).all drf1

/-- (T2, c1, b1) `allOK` over `opOK1`; the `region` binder is unrestricted. -/
def allOK1 : Expr → Bool
  | .let_ _ op e => opOK1 op && allOK1 e
  | .split _ _ _ e => allOK1 e
  | .unpack _ _ _ e => allOK1 e
  | .unpackT _ _ _ e => allOK1 e
  | .region _ _ _ _ e => allOK1 e
  | .openPub _ _ p _ e => !freeB p e && allOK1 e
  | .case _ _ e₁ _ e₂ => allOK1 e₁ && allOK1 e₂
  | .ifnull _ e₁ _ e₂ => allOK1 e₁ && allOK1 e₂
  | .parity _ _ e₁ e₂ => allOK1 e₁ && allOK1 e₂
  | .ifeq _ _ e₁ e₂ => allOK1 e₁ && allOK1 e₂
  | .cas _ _ _ _ _ _ ok fail => allOK1 ok && allOK1 fail
  | .casp _ _ _ _ _ _ _ _ ok fail => allOK1 ok && allOK1 fail
  | .ret _ => true
  | .tail _ _ _ ts => ts.all drf1

/-- (T2, c1) `ProgScopeOK` over `drf1`/`allOK1`. -/
def ProgScopeOK1 (p : Prog) : Bool := p.all fun d => drf1 d.argTy && drf1 d.retTy && allOK1 d.body

/-- (g1) No capability component (outside nothing: also under references). -/
def capFree : Ty → Bool
  | .cap _ _ => false
  | .prod a b | .sum a b | .code a b => capFree a && capFree b
  | .array _ t | .ptr _ t | .ptrOpt _ t | .loc _ t | .mu t | .tex _ t | .iall t | .iex t | .refine t _ => capFree t
  | _ => true

/-- (g1) A live region payload: coupled, copyable, capability-free. -/
def rgnPay (ke : KEnv) (u : Ty) : Bool := Ty.coupledOKIn ke u && !affine ke u && capFree u

/-- The region and cell type of a region-cell reference (not a protocol word). -/
def rgnCellAt (cx : Cx) (a : At) : Option (Idx × Ty) :=
  match cx.peek a with
  | .ok t => if (wordOf t).isNone then (match cellOf t with | some (.rgn r, u) => some (r, u) | _ => none) else none
  | .error _ => none

/-- An ordered observation of a monotone protocol word: `TornLic`'s saws/find/wordOf/monotone
conjuncts (CoreTyping L1186–89).  Its absence refutes `TornLic cx r w s` for every `r`, `w`, `s`
(`TermC1.noMonoSaw_not_tornLic`). -/
def monoSaw (cx : Cx) : String × Idx × Bool → Bool
  | (w, _, o) => o && match cx.find w with
    | .ok (t, _) => match wordOf t with
      | some (_, P) => monotone P
      | none => false
    | .error _ => false

/-- (i1) Region-cell accesses, positive form: a load only with a tok/share witness and no
`monoSaw`; a store only with the sealed token and a copyable cell type; `xchg`/`fetch` banned. -/
def rgnOpOK1 (cx : Cx) : Op → Bool
  | .load _ a => match rgnCellAt cx a with
      | some (r, _) => (cx.hasTok r || cx.hasShare r) && !cx.saws.any (monoSaw cx)
      | none => true
  | .store _ a _ _ => match rgnCellAt cx a with
      | some (r, u) => cx.hasTok r && cx.sealedR r && !affine cx.ke u
      | none => true
  | .xchg a _ => (rgnCellAt cx a).isNone
  | .fetch _ _ _ a _ => (rgnCellAt cx a).isNone
  | _ => true

/-- (T3, c1) `TermScope.checkW` (TermWrapDefs L32–246, 34 self-references renamed) with four insertions, each marked `-- c1`.
Parallel copy: deleted when the change is adopted, where `checkW` takes this text. -/
def checkW1 (p : Prog) (cx : Cx) : Expr → M Unit
  | .let_ x op e => do
      if !opArgOK op then throw "A1: a type argument or witness carries a key"
      -- c1 (i1; h2/g1 at intoRgn)
      if !rgnOpOK1 cx op then throw "c1: region-cell access outside tok/share load or sealed-tok store"
      match op with
      | .intoRgn _ a0 =>
          match cx.peek a0 with
          | .ok (.ptr .own u0) => if !rgnPay cx.ke u0 then throw "c1: intoRgn payload not coupled/copyable/cap-free"
          | .ok _ => throw "c1: intoRgn buffer form is outside c1"
          | .error _ => pure ()
      | _ => pure ()
      let cx ← checkOp p cx x op
      match cx.vars.find? (·.1 == x) with
      | some (_, t, _) => if !wrapOK t then throw s!"A1: {x} has a key-carrying wrapper type"
      | none => pure ()
      checkW1 p cx e
  | .split a x y e => do
      let (t, cx) ← cx.use a
      match t with
      | .prod u v => do
          let cx ← cx.bind x u
          let cx ← cx.bind y v
          checkW1 p cx e
      | _ => throw "split needs a pair"
  | .unpack a i x e => do
      let (t, cx) ← cx.use a
      match t with
      | .iex b => do
          let cx ← (cx.push i).bind x b
          checkW1 p cx e
      | _ => throw "unpack needs an index existential"
  | .unpackT a _ x e => do
      let (t, cx) ← cx.use a
      match t with
      | .tex κ b => do
          if !b.guardT 0 then
            throw "unpack: the package's variable must occur only under a reference"
          let cx ← (cx.pushT κ).bind x b
          checkW1 p cx e
      | _ => throw "unpack at a type needs a type existential"
  | .region a rn pn tn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u => do
          -- D1: a region cell is a published cell whose writes the token gates,
          -- so its type is shareable (no `own` inside) and opening it fences.
          if !rgnCellOK cx.ke u then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          -- c1 (e1; g1 for a live binder)
          if !Ty.coupledOKIn cx.ke u then throw "c1 (e1): region payload not coupledOK"
          if freeB pn e && !rgnPay cx.ke u then throw "c1: live region payload not copyable/cap-free"
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          checkW1 p cx e
      | .refine (.loc .own (.array n u)) (.ini k) => do
          -- An own buffer can be opened as a region directly: the region's
          -- pointer is the buffer's locative, its initialized prefix fixed.
          if !rgnCellOK cx.ke (.array n u) then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          -- c1 (e1; live region buffers out)
          if !Ty.coupledOKIn cx.ke (.array n u) then throw "c1 (e1): region buffer payload not coupledOK"
          if freeB pn e then throw "c1: live region buffers are outside c1"
          let cx := cx.push rn
          let cx ← cx.bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          checkW1 p cx e
      | _ => throw "region needs an own reference or an own buffer"
  | .openPub a rn pn cn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .pub u => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind cn (.cap .pub (.var 0))
          checkW1 p cx e
      | _ => throw "openPub needs a pub reference"
  | .case a x e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .sum u v => do
          checkW1 p (← cx.bind x u) e₁
          checkW1 p (← cx.bind y v) e₂
      | _ => throw "case needs a sum"
  | .ifnull a e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .ptrOpt μ u => do
          checkW1 p cx e₁
          checkW1 p (← cx.bind y (.ptr μ u)) e₂
      | _ => throw "ifnull needs a nullable reference"
  | .parity a k ev od => do
      let i ← intIdx cx a
      let v ← match (cx.norm i).bind Lin.asVar? with
        | some v => pure v
        | none => throw "parity: the index is not a free variable, so there is nothing to refine"
      let cx := cx.push k
      checkW1 p { cx with facts := (v + 1, .smul 2 (.var 0)) :: cx.facts } ev
      checkW1 p { cx with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: cx.facts } od
  | .ifeq a b yes no =>
      if plainEq cx a b then do checkW1 p cx yes; checkW1 p cx no
      else do
      let i ← intIdx cx a
      let j ← intIdx cx b
      match cx.norm i, cx.norm j with
      | some ni, some nj =>
          if ni == nj then checkW1 p cx yes
          else
            match ni.asVar?, nj.asVar? with
            | some v, _ =>
                if nj.mentions v then throw "ifeq: cannot record the equality"
                checkW1 p { cx with facts := (v, nj.toIdx) :: cx.facts } yes
            | _, some v =>
                if ni.mentions v then throw "ifeq: cannot record the equality"
                checkW1 p { cx with facts := (v, ni.toIdx) :: cx.facts } yes
            | _, _ =>
                match zeroVar ni nj with
                | some u => checkW1 p { cx with facts := (u, .lit 0) :: cx.facts } yes
                | none => throw "ifeq: cannot record the equality"
          checkW1 p (noCx cx ni nj) no
      | _, _ => throw "ifeq: index outside the decidable fragment"
  | .cas acq rel w e v t ok fail => do
      let tw ← cx.peek w
      -- c1 (i1): no cas at a region cell
      if wordOf tw == none && (cellOf tw matches some (.rgn _, _)) then throw "c1: cas at a region cell"
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
          checkW1 p (← cx.bind t .unit) ok
          checkW1 p cx fail
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
        checkW1 p (← cx.bind t (.tokE r (.word P) j)) ok
        checkW1 p cx fail
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
          checkW1 p (← lendCx cx acq rel r (shareMove P c k c' k') t) ok
        else
          if P.lends.contains c || P.lendsDown.contains c then
            throw "taking the region from a lending state: shares are out"
          if !acq then throw "taking the region needs acq"
          let cx' ← cx.bind t (.tok r (some (P, j)))
          let cx' := if monotone P then { cx' with unsealed := r :: cx'.unsealed } else cx'
          checkW1 p cx' ok
        checkW1 p cx fail
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
          checkW1 p (← cx.bind t .unit) ok
          checkW1 p cx fail
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
          checkW1 p (← cx.bind t (.tokE r (.pair P) j0)) ok
        else
          -- Between shared states nothing changes hands (a pair lends no shares).
          checkW1 p (← cx.bind t .unit) ok
      else
        if !acq then throw "taking the region needs acq"
        checkW1 p (← cx.bind t (.tok2 r P j0 j1)) ok
      checkW1 p cx fail
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



/-- (c1) `TermScope.declWrapOK` over `checkW1`. -/
def declWrapOK1 (p : Prog) (d : Decl) : Bool :=
  wrapOK d.argTy && wrapOK d.retTy &&
  (checkW1 p { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
               ke := d.tparams.reverse.map some } d.body matches .ok _)

def ProgWrapOK1 (p : Prog) : Bool := p.all (declWrapOK1 p)

/-- (c1) **The program scope check with A1 under c1**: `ProgScopeOK1` and `ProgWrapOK1`. -/
def ProgScopeOKW1 (p : Prog) : Bool := ProgScopeOK1 p && ProgWrapOK1 p

theorem ProgScopeOKW1.scope {p : Prog} (h : ProgScopeOKW1 p = true) : ProgScopeOK1 p = true :=
  (Bool.and_eq_true _ _ ▸ h).1

theorem ProgScopeOKW1.wrap {p : Prog} (h : ProgScopeOKW1 p = true) : ProgWrapOK1 p = true :=
  (Bool.and_eq_true _ _ ▸ h).2

end TermC1

#print axioms TermC1.ProgScopeOKW1.scope
#print axioms TermC1.ProgScopeOKW1.wrap
