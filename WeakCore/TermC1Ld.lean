import WeakCore.TermC1Lem
import WeakCore.TermAdaptPW

/-! # TermC1Ld: `load` and `store` at region cells (G4)

Under c1 a region reference is held to the `pub` clause (`ModeOK1`), so a region-cell load or store
is a `pub` one: `tstepM_loadCell` / `tstepM_storeCell` (TermStep, any mode whose clause gives a
`pub`-like frontier).  Today's `VR` has no frontier at `.rgn` (`ModeOK .rgn _ = True`); the lemmas
here take it as the explicit hypothesis `hmo`, which the switch discharges from
`VR` with `ModeOK1`.

The bound type is `adapt r u`; the cell's type is `noOwnIn` (pre-state `PubCpl`, at the frontier
`hmo` gives), so `adapt r u = u` (`rgn_adapt`).  A `loadCap`/`storeCap` derivation at a region cell
takes the same route; `loadTorn` is refuted by `rgnOpOK1` (`noMonoSaw_not_tornLic`).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `adapt` keeps `arrFree` (it changes reference modes only). -/
theorem arrFree_adapt : ∀ (u : Ty) (r : Idx), (adapt r u).arrFree = u.arrFree := by
  intro u
  induction u with
  | ptr μ t _ => intro r; cases μ <;> rfl
  | ptrOpt μ t _ => intro r; cases μ <;> rfl
  | loc μ t _ => intro r; cases μ <;> rfl
  | prod a b iha ihb => intro r; simp only [adapt, Ty.arrFree, iha, ihb]
  | sum a b iha ihb => intro r; simp only [adapt, Ty.arrFree, iha, ihb]
  | array i t ih => intro r; simp only [adapt, Ty.arrFree]
  | iex t ih => intro r; simp only [adapt, Ty.arrFree, ih]
  | iall t ih => intro r; simp only [adapt, Ty.arrFree, ih]
  | tex κ t ih => intro r; simp only [adapt, Ty.arrFree, ih]
  | refine t ψ ih => intro r; simp only [adapt, Ty.arrFree, ih]
  | mu t ih => intro r; simp only [adapt, Ty.arrFree, ih]
  | _ => intro r; rfl

/-- `adapt` is the identity on a type whose closure is `noOwn`. -/
theorem adapt_cl (ρ : Nat → Nat) (W : Nat → Ty) (r : Idx) :
    ∀ (t : Ty) (ke : KEnv) (c d : Nat), Ty.noOwnIn ke (cl ρ W c d t) = true → adapt r t = t := by
  intro t
  induction t generalizing r with
  | prod a b iha ihb =>
      intro ke c d h
      simp only [cl, Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, iha r ke c d h.1, ihb r ke c d h.2]
  | sum a b iha ihb =>
      intro ke c d h
      simp only [cl, Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, iha r ke c d h.1, ihb r ke c d h.2]
  | array i t ih => intro ke c d h; simp only [cl, Ty.noOwnIn] at h; simp only [adapt, ih r ke c d h]
  | iex t ih => intro ke c d h; simp only [cl, Ty.noOwnIn] at h; simp only [adapt, ih _ ke c (d + 1) h]
  | iall t ih => intro ke c d h; simp only [cl, Ty.noOwnIn] at h; simp only [adapt, ih _ ke c (d + 1) h]
  | refine t ψ ih => intro ke c d h; simp only [cl, Ty.noOwnIn] at h; simp only [adapt, ih r ke c d h]
  | mu t ih => intro ke c d h; simp only [cl, Ty.noOwnIn] at h; simp only [adapt, ih r _ (c + 1) d h]
  | tex κ t ih =>
      intro ke c d h
      simp only [cl, Ty.noOwnIn, Bool.and_eq_true] at h
      simp only [adapt, ih r _ (c + 1) d h.2]
  | ptr μ t _ => intro ke c d h; cases μ <;> simp_all [cl, clM, Ty.noOwnIn, adapt]
  | ptrOpt μ t _ => intro ke c d h; cases μ <;> simp_all [cl, clM, Ty.noOwnIn, adapt]
  | loc μ t _ => intro ke c d h; cases μ <;> simp_all [cl, clM, Ty.noOwnIn, adapt]
  | _ => intro ke c d h; simp [adapt]

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}

/-- **S15's hypothesis turns into `hV`**: `ModeOK1` at a region mode is `ModeOK` at `pub`. -/
theorem rgnV {a : At} {r : Idx}
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) :
    ∀ rt pw ad c, evalAt th.env a = some (rt, [pw]) → pw.val = .loc ad 0 → η.sto ad.label = some c →
      ModeOK η.tid η.pfr η.seen (.rgn r) ad.label c [pw] → ModeOK η.tid η.pfr η.seen .pub ad.label c [pw] :=
  fun rt pw ad c he hw hs _ => hmo rt [pw] ad c he (by simp [hw]) hs

/-- **The bound type at a region cell is the payload** (`adapt r u = u`): the cell has a
frontier (`hmo`), so pre-state `PubCpl` makes its type `noOwn`, hence the component the reference
targets (`cell_target`, `noOwn_AtOff`), the payload's closure. -/
theorem rgn_adaptT {K : TEnv → List Word → Prop} {a : At} {t : Ty} {r : Idx} {u : Ty} {g : G} {s : St}
    (hi : FInv ρ η th.σs K cx th.env) (hpk : cx.peek a = .ok t) (hcl : cellOf t = some (.rgn r, u))
    (hm : MemInv g (CE η) s)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws)
    (hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u)) :
    adapt r u = u := by
  obtain ⟨rt, ws, hea, hv, -⟩ := peek_VR hi.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, -, -⟩ := cell_target hcl hnb hv
  obtain ⟨f, hf, -⟩ := hmo rt ws ad c hea hws hsto
  exact adapt_cl ρ η.wit r u [] 0 0 (noOwn_AtOff hat (MemInv_noOwnT hm hsto hf))

/-- `rgn_adaptT` at a region pointer: `VR`'s `accs` conjunct rules out an array target. -/
theorem rgn_adapt {K : TEnv → List Word → Prop} {a : At} {r : Idx} {u : Ty} {g : G} {s : St}
    (hi : FInv ρ η th.σs K cx th.env) (hpk : cx.peek a = .ok (.ptr (.rgn r) u))
    (hm : MemInv g (CE η) s)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) :
    adapt r u = u := by
  obtain ⟨rt, ws, -, hv, -⟩ := peek_VR hi.2.1 hpk
  simp only [VR] at hv
  obtain ⟨_, c, -, -, -, hcty, -, hacc⟩ := hv
  exact rgn_adaptT hi hpk rfl hm hmo (Fd_noarr (by rw [← Fd_accs hcty]; exact hacc))

/-- `rgn_adaptT` at a region locative `load`: the bound `adapt r u` is `arrFree` (`bind`), so the
payload's closure is, and no array is its fold. -/
theorem rgnLoc_adaptL {K : TEnv → List Word → Prop} {a : At} {r : Idx} {u : Ty} {g : G} {s : St}
    (hi : FInv ρ η th.σs K cx th.env) (hpk : cx.peek a = .ok (.loc (.rgn r) u))
    (hm : MemInv g (CE η) s)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) :
    (adapt r u).arrFree = true → adapt r u = u := fun haf =>
  rgn_adaptT hi hpk rfl hm hmo (fun n e hF => by
    have h := Fd_arrFree hF (arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (by rw [← arrFree_adapt u r]; exact haf))
    simp [Ty.arrFree] at h)

/-- A value stored at a region locative at type `adapt r u` has a layout, so the payload's closure
has one (`mr_cl_adapt`: `adapt` is invisible to `wc`). -/
theorem accs_rgnSub {K : TEnv → List Word → Prop} {a v : At} {r : Idx} {u tv : Ty} {c₁ : Cx}
    (hi : FInv ρ η th.σs K cx th.env) (htv : TvOK cx) (hpk : cx.peek a = .ok (.loc (.rgn r) u))
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv (adapt r u)) :
    accs (cl ρ η.wit 0 0 u) ≠ none := by
  obtain ⟨-, rv, wsv, -, -, hlv⟩ := use_FInv hu hi
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK (adapt r u) = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length (adapt r u) = true := by
    rw [tb_adapt]; exact tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc (.rgn r) u) = some (.rgn r, u))
  have hw : wc (close th.σs (adapt r u)) ≠ none := (Lay_canon hsub hlv).2.2.2.1
  rw [wc_of_sig (sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)),
    ← TermAdaptPW.mr_wc (TermAdaptPW.mr_cl_adapt ρ η.wit u r 0 0 (fun k hk => absurd hk (Nat.not_lt_zero k)))] at hw
  exact fun h => hw (by simp [wc, h])

/-- `rgn_adaptT` at a region locative `store` at type `adapt r u` (`accs_rgnSub`). -/
theorem rgnLoc_adaptS {K : TEnv → List Word → Prop} {a v : At} {r : Idx} {u : Ty} {g : G} {s : St}
    (hi : FInv ρ η th.σs K cx th.env) (htv : TvOK cx) (hpk : cx.peek a = .ok (.loc (.rgn r) u))
    (hm : MemInv g (CE η) s)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) :
    ∀ tv c₁, cx.use v = .ok (tv, c₁) → SubS c₁ tv (adapt r u) → adapt r u = u :=
  fun _ _ hu hsub => rgn_adaptT hi hpk rfl hm hmo (Fd_noarr (accs_rgnSub hi htv hpk hu hsub))

end


/-- **The typing facts of a region-cell `load`** (`loadRgn`, or `loadCap` rerouted; pointer or
locative): a copyable payload and the binding at it; `loadTorn` is refuted by `rgnOpOK1`. -/
theorem rgnLoad_facts {p : Prog} {cx c' : Cx} {x : String} {acq : Bool} {a : At} {t : Ty} {r : Idx} {u : Ty}
    (hop : OpT p cx x (.load acq a) c') (hpk : cx.peek a = .ok t) (hcl : cellOf t = some (.rgn r, u))
    (hnw : wordOf t = none) (hrop : rgnOpOK1 cx (.load acq a) = true)
    (had : (adapt r u).arrFree = true → adapt r u = u) : affine cx.ke u = false ∧ cx.bind x u = .ok c' := by
  have hrc : rgnCellAt cx a = some (r, u) := by simp [rgnCellAt, hpk, hnw, hcl]
  cases hop with
  | loadWord hp hw _ _ => rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadOwn hp _ hc _ _ => rw [hpk] at hp; cases hp; rw [hcl] at hc; simp at hc
  | loadPub hp _ hc _ _ _ => rw [hpk] at hp; cases hp; rw [hcl] at hc; simp at hc
  | loadRgn hp _ hc _ haf hb =>
      rw [hpk] at hp; cases hp
      rw [hcl] at hc; simp only [Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      rw [had (bind_arrFree hb)] at haf hb; exact ⟨haf, hb⟩
  | loadCap hp _ hc _ _ haf hb =>
      rw [hpk] at hp; cases hp
      rw [hcl] at hc; simp only [Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      rw [had (bind_arrFree hb)] at haf hb; exact ⟨haf, hb⟩
  | loadTorn _ _ _ htl _ _ => exact absurd htl ((rgnOpOK1_load hrop hrc).2 _ _ _)

/-- The `SubS c₁ tv u ∨ SubS c₁ tv (adapt r u)` premise of `storeRgn`/`storeCap`, collapsed. -/
theorem rgnSub {cx c₁ : Cx} {v : At} {r : Idx} {u tv : Ty}
    (had : ∀ tv c₁, cx.use v = .ok (tv, c₁) → SubS c₁ tv (adapt r u) → adapt r u = u)
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv u ∨ SubS c₁ tv (adapt r u)) : SubS c₁ tv u := by
  rcases hsub with h | h
  · exact h
  · rw [had _ _ hu h] at h; exact h

/-- **The typing facts of a region-cell `store`** (`storeRgn`, or `storeCap` rerouted; pointer or
locative): the stored value's use, its subtype of the payload, and the binding. -/
theorem rgnStore_facts {p : Prog} {cx c' : Cx} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {r : Idx} {u : Ty}
    (hop : OpT p cx x (.store rel a v tok) c') (hpk : cx.peek a = .ok t) (hcl : cellOf t = some (.rgn r, u))
    (hnw : wordOf t = none)
    (had : ∀ tv c₁, cx.use v = .ok (tv, c₁) → SubS c₁ tv (adapt r u) → adapt r u = u) :
    ∃ tv c₁, cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x .unit = .ok c' := by
  cases hop with
  | storeWordGive hp hw => rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeOwn hp _ hc => rw [hpk] at hp; cases hp; rw [hcl] at hc; simp at hc
  | storePub hp _ hc => rw [hpk] at hp; cases hp; rw [hcl] at hc; simp at hc
  | storeRgn hp _ hc _ hu _ hsub hb =>
      rw [hpk] at hp; cases hp
      rw [hcl] at hc; simp only [Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨_, _, hu, rgnSub had hu hsub, hb⟩
  | storeCap hp _ hc _ hu _ _ hsub hb =>
      rw [hpk] at hp; cases hp
      rw [hcl] at hc; simp only [Option.some.injEq, Prod.mk.injEq, Mode.rgn.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨_, _, hu, rgnSub had hu hsub, hb⟩

section
variable {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
  {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {r : Idx} {u : Ty} {e : Expr} {Rf Rs H : Res}

/-- **(G4) `load` through a region reference, thread layer**: a `pub` load (`tstepM_loadCell`). -/
theorem tstepM_loadRgn1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMF p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  obtain ⟨haf, hb⟩ := rgnLoad_facts hop hpk rfl hnw hrop (fun _ => rgn_adapt hi hpk hm hmo)
  exact tstepM_loadCell (hDy := hDy) hterm hpk haf hb he (OpT_TvOK hP hop htv) (OpT_retSk hop) hi hE htv hm hRP hPS (rgnV hmo)

/-- **(G4) `load` through a region reference, with resources**: `tstepMR_loadCell`. -/
theorem tstepMR_loadRgn1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMK p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop0 he0 =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  obtain ⟨haf, hb⟩ := rgnLoad_facts hop hpk rfl hnw hrop (fun _ => rgn_adapt hi.1 hpk hm hmo)
  exact tstepMR_loadCell (hDy := hDy) hterm hpk haf hb he hck (OpT_TvOK hP hop htv) (OpT_retSk hop) hi hE htv hm hH hRP hPS (rgnV hmo)

/-- **(G4) `load` through a region reference, with credits**: nothing minted, credits kept. -/
theorem tstepMC_loadRgn1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  mc_liftA hm hC (tstepMR_loadRgn1 (hDy := hDy) hterm hP hpk hnw hT hCk hi hE htv hm hH hRP hPS hrop hmo)

/-- **(G4) `store` through a region reference, thread layer**: a `pub` store (`tstepM_storeCell`). -/
theorem tstepM_storeRgn1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMF p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  obtain ⟨tv, c₁, hu, hsub, hb⟩ := rgnStore_facts hop hpk rfl hnw (fun _ _ _ _ => rgn_adapt hi hpk hm hmo)
  exact tstepM_storeCell (hDy := hDy) (hterm := hterm) (hpk := hpk) (hu := hu) (hsub := hsub) (hb := hb) (he := he)
    (htv' := OpT_TvOK hP hop htv) (hRk := OpT_retSk hop) (hi := hi) (hE := hE) (htv := htv) (hm := hm)
    (hRP := hRP) (hPS := hPS) (hV := rgnV hmo)

/-- **(G4) `store` through a region reference, with resources**: `tstepMR_storeCell`. -/
theorem tstepMR_storeRgn1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X, ThInvMPLX p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧ Tot + H' + X ≤ Rf + Rs + H := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop0 he0 =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  obtain ⟨tv, c₁, hu, hsub, hb⟩ := rgnStore_facts hop hpk rfl hnw (fun _ _ _ _ => rgn_adapt hi.1 hpk hm hmo)
  exact tstepMR_storeCell (hDy := hDy) (hterm := hterm) (hpk := hpk) (hnw := hnw) (hu := hu) (hsub := hsub) (hb := hb)
    (he := he) (hck := hck) (htv' := OpT_TvOK hP hop htv) (hRk := OpT_retSk hop) (hi := hi) (hE := hE)
    (htv := htv) (hm := hm) (hH := hH) (hia := hia) (hdw := hdw) (hfo := hfo) (hRP := hRP) (hPS := hPS)
    (hV := rgnV hmo)

/-- **(G4) `store` through a region reference, with credits**: nothing minted, credits kept. -/
theorem tstepMC_storeRgn1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr (.rgn r) u)) (hnw : wordOf (Ty.ptr (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ Tot H' C F,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  mc_liftPLX hC (tstepMR_storeRgn1 (hDy := hDy) hterm hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS hmo)


/-- **(G4) `load` through a region locative, thread layer**: a `pub` load (`tstepM_loadCellLoc`). -/
theorem tstepM_loadRgnLoc1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMF p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  obtain ⟨haf, hb⟩ := rgnLoad_facts hop hpk rfl hnw hrop (rgnLoc_adaptL hi hpk hm hmo)
  exact tstepM_loadCellLoc (hDy := hDy) hterm hpk haf hb he (OpT_TvOK hP hop htv) (OpT_retSk hop) hi hE htv hm hRP hPS (fun h => by cases h) (rgnV hmo)

/-- **(G4) `load` through a region locative, with resources**: `tstepMR_loadCellLoc`. -/
theorem tstepMR_loadRgnLoc1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMK p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧ Tot + H' ≤ Rf + Rs + H := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop0 he0 =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  obtain ⟨haf, hb⟩ := rgnLoad_facts hop hpk rfl hnw hrop (rgnLoc_adaptL hi.1 hpk hm hmo)
  exact tstepMR_loadCellLoc (hDy := hDy) hterm hpk haf hb he hck (OpT_TvOK hP hop htv) (OpT_retSk hop) hi hE htv hm hH hRP hPS (fun h => by cases h) (rgnV hmo)

/-- **(G4) `load` through a region locative, with credits**: nothing minted, credits kept. -/
theorem tstepMC_loadRgnLoc1 {acq : Bool}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hrop : rgnOpOK1 cx (.load acq a) = true)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  mc_liftA hm hC (tstepMR_loadRgnLoc1 (hDy := hDy) hterm hP hpk hnw hT hCk hi hE htv hm hH hRP hPS hrop hmo)

/-- **(G4) `store` through a region locative, thread layer**: a `pub` store (`tstepM_storeCellLoc`). -/
theorem tstepM_storeRgnLoc1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMF p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  obtain ⟨tv, c₁, hu, hsub, hb⟩ := rgnStore_facts hop hpk rfl hnw (rgnLoc_adaptS hi htv hpk hm hmo)
  exact tstepM_storeCellLoc (hDy := hDy) (hterm := hterm) (hpk := hpk) (hu := hu) (hsub := hsub) (hb := hb) (he := he)
    (htv' := OpT_TvOK hP hop htv) (hRk := OpT_retSk hop) (hi := hi) (hE := hE) (htv := htv) (hm := hm)
    (hRP := hRP) (hPS := hPS) (hμ := fun h => by cases h) (hV := rgnV hmo)

/-- **(G4) `store` through a region locative, with resources**: `tstepMR_storeCellLoc`. -/
theorem tstepMR_storeRgnLoc1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H' X, ThInvMPLX p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' X ∧ Tot + H' + X ≤ Rf + Rs + H := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop0 he0 =>
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  obtain ⟨tv, c₁, hu, hsub, hb⟩ := rgnStore_facts hop hpk rfl hnw (rgnLoc_adaptS hi.1 htv hpk hm hmo)
  exact tstepMR_storeCellLoc (hDy := hDy) (hterm := hterm) (hpk := hpk) (hnw := hnw) (hu := hu) (hsub := hsub) (hb := hb)
    (he := he) (hck := hck) (htv' := OpT_TvOK hP hop htv) (hRk := OpT_retSk hop) (hi := hi) (hE := hE)
    (htv := htv) (hm := hm) (hH := hH) (hia := hia) (hdw := hdw) (hfo := hfo) (hRP := hRP) (hPS := hPS)
    (hμ := fun h => by cases h) (hV := rgnV hmo)

/-- **(G4) `store` through a region locative, with credits**: nothing minted, credits kept. -/
theorem tstepMC_storeRgnLoc1 {rel : Bool} {v : At} {tok : Option At}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc (.rgn r) u)) (hnw : wordOf (Ty.loc (.rgn r) u) = none)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    {cr db : Ts → Res} (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hmo : ∀ rt ws ad c, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      η.sto ad.label = some c → ModeOK1 η.tid η.pfr η.seen (.rgn r) ad.label c ws) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ∃ Tot H' C F,
      ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  mc_liftPLX hC (tstepMR_storeRgnLoc1 (hDy := hDy) hterm hP hpk hnw hT hCk hi hE htv hm hH hia hdw hfo hRP hPS hmo)
end

end TermC1

#print axioms TermC1.arrFree_adapt
#print axioms TermC1.adapt_cl
#print axioms TermC1.rgnV
#print axioms TermC1.rgn_adaptT
#print axioms TermC1.rgn_adapt
#print axioms TermC1.rgnLoc_adaptL
#print axioms TermC1.accs_rgnSub
#print axioms TermC1.rgnLoc_adaptS
#print axioms TermC1.rgnLoad_facts
#print axioms TermC1.rgnSub
#print axioms TermC1.rgnStore_facts
#print axioms TermC1.tstepM_loadRgn1
#print axioms TermC1.tstepMR_loadRgn1
#print axioms TermC1.tstepMC_loadRgn1
#print axioms TermC1.tstepM_storeRgn1
#print axioms TermC1.tstepMR_storeRgn1
#print axioms TermC1.tstepMC_storeRgn1
#print axioms TermC1.tstepM_loadRgnLoc1
#print axioms TermC1.tstepMR_loadRgnLoc1
#print axioms TermC1.tstepMC_loadRgnLoc1
#print axioms TermC1.tstepM_storeRgnLoc1
#print axioms TermC1.tstepMR_storeRgnLoc1
#print axioms TermC1.tstepMC_storeRgnLoc1
