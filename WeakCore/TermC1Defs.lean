import WeakCore.TermScope
import WeakCore.TermWrapDefs

/-! # TermC1Defs: region c1, the language-side definitions under new names

New definitions only, alongside the old ones; nothing here is used by any existing definition, premise
or theorem.  When the c1 definitions replace the old ones, the old names are redirected to these and the
parallel copies are deleted.

* `drf1` (T1): `drf` with the region arms by plain recursion (`.ptr _ t`, `.ptrOpt _ t`, `.loc μ t`).
* `opOK1`/`allOK1`/`ProgScopeOK1` (T2): `opOK`/`allOK`/`ProgScopeOK` with `drf1`, `.intoRgn` admitted
  (h2) and the `region` binder unrestricted (b1).
* `rgnPay` (g1): an `intoRgn` payload is coupled; affine payloads are admitted.  Capabilities are not excluded. A held capability licenses region-cell access through base typing; capability values stored as region payloads are inert.
  Region `xchg` of an affine payload requires a held token of the region (base `Cx.hasTok`, up to index equality); that the token is sealed comes from the observable-state refusal below, not from this check. A view-sensitive payload requires a held token of syntactically the same region (§3.8). And, exactly as for a store, there is no region `xchg` under a token (base `Cx.hasTok`, up to index equality) taken from an observable state before `fence st` (CoreTerm:1860-1864). Affine values may enter region cells (`intoRgn`, `region`); dropping a region with an affine payload inside discards it, it does not duplicate it. They leave only through such a token holder's `xchg`: loads and `cas` refuse affine types, a torn read is refused by layout (ruleA) and its `validate` separately refuses affine types, and a region has no end in the core. An affine region `xchg` payload carries no key, at any depth.
* `rgnCellAt`: the region and cell type of a region-cell reference. Region-cell accesses are base typing's.
* `checkW1` (T3): `TermScope.checkW` (TermWrapDefs) copied with exactly four insertions
  (marked `c1`): `rgnPay` at `intoRgn` (operation arm), e1 `coupledOK` at
  `region`, the same at the buffer `region` (live buffers out), and the region `xchg` guard (affine only under a held token, up to index equality, and with no key; not under an unsealed token; view-sensitive only under a syntactic held token).
* `declWrapOK1`/`ProgWrapOK1`/`ProgScopeOKW1`: `TermScopeW`'s, over `checkW1`/`ProgScopeOK1`.
-/

namespace TermC1

open CoreLang CoreTerm TermScope

/-- (T2, c1, h2) `opOK` over `drf1`, with `.intoRgn` admitted; and `opShareOK` (spawn type arguments only). -/
def opOK1 : Op → Bool
  | .validate _ => false
  | .mkTicket _ _ _ _ _ | .claim _ _ => false
  | .null μ τ => drfM μ && drf1 τ
  | op => (opTys op).all drf1 && opShareOK op

/-- (T2, c1, b1) `allOK` over `opOK1`; the `region` and `openPub` binders are unrestricted. -/
def allOK1 : Expr → Bool
  | .let_ _ op e => opOK1 op && allOK1 e
  | .split _ _ _ e => allOK1 e
  | .unpack _ _ _ e => allOK1 e
  | .unpackT _ _ _ e => allOK1 e
  | .region _ _ _ _ e => allOK1 e
  | .openPub _ _ p _ e => allOK1 e
  | .case _ _ e₁ _ e₂ => allOK1 e₁ && allOK1 e₂
  | .ifnull _ e₁ _ e₂ => allOK1 e₁ && allOK1 e₂
  | .parity _ _ e₁ e₂ => allOK1 e₁ && allOK1 e₂
  | .ifeq _ _ e₁ e₂ => allOK1 e₁ && allOK1 e₂
  | .cas _ _ _ _ _ _ ok fail => allOK1 ok && allOK1 fail
  | .casp _ _ _ _ _ _ _ _ ok fail => allOK1 ok && allOK1 fail
  | .ret _ => true
  | .tail _ _ _ ts => ts.all drf1 && ts.all TermSound.rgnFree

/-- (T2, c1) `ProgScopeOK` over `drf1`/`allOK1`. -/
def ProgScopeOK1 (p : Prog) : Bool := p.all fun d => drf1 d.argTy && drf1 d.retTy && allOK1 d.body

/-- (T3, c1; alias) `TermScope.checkW` carries the c1 text since the switch (M11); one checker. -/
abbrev checkW1 (p : Prog) (cx : Cx) : Expr → M Unit := TermScope.checkW p cx

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

/-! ### (D9 condition (2), (b)) PubCpl1's fallback form, stated here for the frame-invariant restatement.
Not used by any definition above; PubCpl1 (TermC1Inv) reads it there. -/

/-- No shallow `loc (rgn _)` (recursing as `rgnFree`'s structural arms). -/
def noLocRgn : Ty → Bool
  | .loc (.rgn _) _ => false
  | .prod a b | .sum a b => noLocRgn a && noLocRgn b
  | .array _ t | .mu t | .tex _ t | .iall t | .iex t | .refine t _ => noLocRgn t
  | _ => true

/-- PubCpl1's frontier-cell conjunct, fallback form: `noOwnIn ∧ noIallV ∧ noLocRgn`. -/
def pubCellFB (ke : KEnv) (T : Ty) : Bool := Ty.noOwnIn ke T && TermTv.noIallV T && noLocRgn T

theorem opOK1_share {op : Op} (h : opOK1 op = true) : opShareOK op = true := by
  unfold opOK1 at h
  split at h
  · cases h
  · cases h
  · cases h
  · rfl
  · exact (Bool.and_eq_true _ _ ▸ h).2

/-- A spawn admitted by `opOK1` moves no second-class type argument (N2 δ: the value itself may be
second-class). -/
theorem opShareOK_spawn {f a T ts} (h : opShareOK (.spawn f a T ts) = true) :
    ∀ t ∈ ts, t.secondClass = false := by
  simp only [opShareOK, Bool.and_eq_true, List.all_eq_true] at h
  exact fun t ht => by simpa using h.2 t ht

theorem opOK1_spawn {f a T ts} (h : opOK1 (.spawn f a T ts) = true) :
    ∀ t ∈ ts, t.secondClass = false :=
  opShareOK_spawn (opOK1_share h)

theorem allOK1_tail_rgnFree {f is a ts} (h : allOK1 (.tail f is a ts) = true) :
    ∀ t ∈ ts, TermSound.rgnFree t = true := by
  simp only [allOK1, Bool.and_eq_true] at h; exact fun t ht => List.all_eq_true.1 h.2 t ht

end TermC1

/-! ### unit `#guard`s for the D9 (a′) rule -/
section ShareRuleGuards
open CoreLang CoreTerm TermC1
-- a region pointer is drf1.
#guard drf1 (.ptr (.rgn (.lit 0)) .int) = true
-- a share packT at a region-ref witness is admitted at opOK1, as is a non-share one
#guard opOK1 (.packT (.var "x") (.ptr (.rgn (.lit 0)) .int) (.tex { share := true } (.tvar 0))) = true
#guard opOK1 (.packT (.var "x") (.ptr (.rgn (.lit 0)) .int) (.tex {} (.tvar 0))) = true
#guard opOK1 (.packT (.var "x") (.ptr .pub .int) (.tex { share := true } (.tvar 0))) = true
#guard opOK1 (.packT (.var "x") (.ptr .pub (.ptr (.rgn (.lit 0)) .int)) (.tex { share := true } (.tvar 0))) = true
-- r-simple at spawn / tail; a region-ref type argument is admitted at call
#guard opOK1 (.call "f" [] (.var "x") [.ptr (.rgn (.lit 0)) .int]) = true
#guard opOK1 (.call "f" [] (.var "x") [.int]) = true
#guard opOK1 (.spawn "f" (.var "x") .int [.ptr (.rgn (.lit 0)) .int]) = false
-- spawn scope (N2 δ): a second-class value is admitted at spawn; a second-class type argument is refused
#guard opOK1 (.spawn "f" (.var "x") (.tex {} (.cap .bor (.var 0))) []) = true
#guard opOK1 (.spawn "f" (.var "x") (.cap .rd (.lit 0)) []) = true
#guard opOK1 (.spawn "f" (.var "x") .int [.cap .bor (.lit 0)]) = false
#guard opOK1 (.spawn "f" (.var "x") (.cap .pub (.lit 0)) [.cap .frz (.lit 0)]) = true
#guard opOK1 (.spawn "f" (.var "x") .int [.int]) = true
#guard allOK1 (.tail "f" [] (.var "x") [.ptr (.rgn (.lit 0)) .int]) = false
#guard allOK1 (.tail "f" [] (.var "x") [.ptr .pub .int]) = true
-- syntactic token arms: a token for `s` with the fact `r = s` licenses no access at `r` (eqI would)
#guard Cx.hasTok { ret := .unit, inames := ["s", "r"], facts := [(1, .var 0)], vars := [("p", .ptr (.rgn (.var 1)) .int, true), ("t", .tok (.var 0) none, true)] } (.var 1) = true
#guard hasTok1 { ret := .unit, inames := ["s", "r"], facts := [(1, .var 0)], vars := [("p", .ptr (.rgn (.var 1)) .int, true), ("t", .tok (.var 0) none, true)] } (.var 1) = false
-- admitsIn rejects repacking an opaque non-share α into a share package
#guard admitsIn { ret := .int, ke := [some {}], opq := [0] } { share := true } (.tvar 0) = false
-- (b) fallback form: noIallV alone is not enough (D13FB example), pubCellFB rejects loc rgn
#guard TermTv.noIallV (.loc (.rgn (.lit 0)) .int) = true
#guard pubCellFB [] (.loc (.rgn (.lit 0)) .int) = false
#guard pubCellFB [] (.ptr (.rgn (.lit 0)) .int) = true
end ShareRuleGuards

#print axioms TermC1.opOK1_share
#print axioms TermC1.allOK1_tail_rgnFree
#print axioms TermC1.opShareOK_spawn
#print axioms TermC1.opOK1_spawn
#print axioms TermC1.hasTok1_hasTok
#print axioms TermC1.ProgScopeOKW1.scope
#print axioms TermC1.ProgScopeOKW1.wrap
