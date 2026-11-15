import WeakCore.EtaFD
import WeakCore.ContIV
import WeakCore.WinPremises
import WeakCore.BornW
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaW** (B12 on (R′)): `NoHoldPubN` at every certified configuration of a window from a `SysInvN`
start, from `noHold_eta` (EtaN).  The holder premises `hPH`/`hPT`/`hm0`, `hbf`, `hlab`, `hnp` and the non-fresh oracle are
discharged here (SysInvN, ThSysAt, the x-free lineage EtaF, the ♭ ownership chain); the remaining inputs are
the NAMED window temporaries `WinTmp`:

* (`contB`, ContB at the cut, is DISCHARGED: ContIV `contB_of` from the base `MemInv` + `hinv.rle` + D1.)
* (`contE`, ContE at the adversarial typing, is DISCHARGED: ContIV `contE_of` from the WinAnte `MemInv`.)
* (`sup0`, `∃ b, FreshSup P b (CE η)`, is DROPPED: never consumed.  The plan parameter `P` went with it.)
* (`rini0`, the `FreshLP` rini clause at `CE η`, is DISCHARGED: read from W's `FreshLP` inside `MemInv`.)
* (`scal`, W's `ScalIni Eg` clause, is DISCHARGED: `hinv.scalIni` at the SysInvN base.)
  At an anchor it is an input `hscS` of `win_gen` (base: `hinv.scalIni`; post-promise: `ScalFlat.scalIni_egP`);
* (`oFresh`, the oracle at a fresh label of the window, is DISCHARGED: BornW `oFresh_of`, ownXLe_born.)

`win_gen` separates the window start / anchor (`cS`, `Cut Eg i S`: `WinTmpA`; `hscS`) from the
`SysInvN` base (`c`, `Cut Eg0 i S0`: `contB`); conjunct 2 of `CertWinPNX` (EtaCertWinSnd) uses it at
`cS := promise c j a v w`, `Eg := EgP …`. -/
/-! # EtaFence (ported from the EtaFence draft): the three fencing operations (`publish`, `region`, `intoRgn`) use their
argument as an own pointer or own buffer locative; the facts the window proof reads off a publish
hold at every fencing term. -/

namespace EtaFence
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermOwnX2

/-- A fencing term at argument `a`: `publish a`, `region a …`, or `intoRgn r a`. -/
def FenceAt (t : Expr) (a : At) : Prop :=
  (∃ y e, t = .let_ y (.publish a) e) ∨ (∃ rn pn tn e, t = .region a rn pn tn e) ∨
    (∃ y r e, t = .let_ y (.intoRgn r a) e)

/-- `cx` uses `a` as an own pointer or an own buffer locative. -/
def OwnUse (cx : Cx) (a : At) : Prop :=
  (∃ u c₁, cx.use a = .ok (.ptr .own u, c₁)) ∨
    ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁)

theorem fenceAt_publish {y : String} {a : At} {e : Expr} : FenceAt (.let_ y (.publish a) e) a := .inl ⟨y, e, rfl⟩
theorem fenceAt_region {a : At} {rn pn tn : String} {e : Expr} : FenceAt (.region a rn pn tn e) a :=
  .inr (.inl ⟨rn, pn, tn, e, rfl⟩)
theorem fenceAt_intoRgn {y r : String} {a : At} {e : Expr} : FenceAt (.let_ y (.intoRgn r a) e) a :=
  .inr (.inr ⟨y, r, e, rfl⟩)

/-- A typed fencing term uses its argument as own. -/
theorem fence_use {p : Prog} {cx : Cx} {t : Expr} {a : At} (hT : Typed p cx t) (hf : FenceAt t a) : OwnUse cx a := by
  rcases hf with ⟨y, e, rfl⟩ | ⟨rn, pn, tn, e, rfl⟩ | ⟨y, r, e, rfl⟩
  · cases hT with
    | let_ hop _ =>
      cases hop with
      | publish hu _ _ => exact .inl ⟨_, _, hu⟩
      | publishBuf hu _ _ => exact .inr ⟨_, _, _, _, hu⟩
  · cases hT with
    | region hu _ _ _ _ => exact .inl ⟨_, _, hu⟩
    | regionBuf hu _ _ _ _ => exact .inr ⟨_, _, _, _, hu⟩
  · cases hT with
    | let_ hop _ =>
      cases hop with
      | intoRgn _ hu _ _ => exact .inl ⟨_, _, hu⟩
      | intoRgnBuf _ hu _ _ => exact .inr ⟨_, _, _, _, hu⟩

/-- (`publish_own_cell` at every fencing term) The fenced cell is an own cell of the typing env. -/
theorem fence_own_cell {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {a : At}
    {rt : Ty} {ws : List Word} {ad : WeakMem.Address}
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hf : FenceAt th.term a) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ∃ c, η.sto ad.label = some c ∧ c.owner = some η.tid := by
  rcases fence_use hT hf with ⟨u, c₁, hu⟩ | ⟨n, k, u, c₁, hu⟩
  · obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
    subst hws'
    exact ⟨c, hsto, hmode⟩
  · obtain ⟨-, rb, wsb, hea', hvb, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
      subst hws'
      exact ⟨c, hsto, hmode⟩


/-! ## ♭ twins (the window proof's lemmas, at every fencing term) -/

open TermCert TermFul TermGlob TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
  TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (`publish_own_cellB` / `publish_own_cellKD`, any `K`) The fenced cell is an own cell of the ♭ typing env. -/
theorem fence_own_cellK {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {a : At}
    {rt : Ty} {ws : List Word} {ad : Address} {K : TEnv → List Word → Prop}
    (hT : Typed p cx th.term) (hi : FInvB glb gnum gi ρ η th.σs K cx th.env)
    (hf : FenceAt th.term a) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ∃ c, η.sto ad.label = some c ∧ c.owner = some η.tid := by
  rcases fence_use hT hf with ⟨u, c₁, hu⟩ | ⟨n, k, u, c₁, hu⟩
  · obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
    subst hws'
    exact ⟨c, hsto, hmode⟩
  · obtain ⟨-, rb, wsb, hea', hvb, -⟩ := use_FInvB (bkG := False) hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VRF, VRb2] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
      subst hws'
      exact ⟨c, hsto, hmode⟩

/-- (`EtaN.pub_sto`) The fenced cell exists at the N-typing env. -/
theorem fence_sto {p : Prog} {E : TEnv} {th : TTh} {a : At} {rt : Ty} {ws : List Word}
    {ad : Address} (hT1 : ThInvEBN glb gnum gi p E th) (hf : FenceAt th.term a)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) : E.sto ad.label ≠ none := by
  obtain ⟨ρ, η, cx, rfl, hE, ⟨hT, -⟩, htv, hi, -⟩ := hT1
  obtain ⟨cl, hcl, -⟩ := fence_own_cellK hT hi hf hea hws
  show η.sto ad.label ≠ none
  rw [hcl]; exact Option.some_ne_none _

/-- (`EtaW.own_pub_ne`) A thread with no own-count at `x` is not fencing `x`. -/
theorem own_fence_ne {p : Prog} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {th : TTh} {x : AllocLabel}
    {a : At} {rt : Ty} {ws : List Word} {ad : Address}
    (hE : EnvOKB p η) (hTy : Typed p cx th.term)
    (hFI : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf)
    (h0 : Rf (.own x) = 0) (hf : FenceAt th.term a) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ad.label ≠ x := by
  rcases fence_use hTy hf with ⟨u, c₁, hu⟩ | ⟨n, k, u, c₁, hu⟩
  · exact use_own_neB hu hFI hE (Or.inl ⟨_, rfl⟩) h0 hea hws
  · exact use_own_neB hu hFI hE (Or.inr ⟨_, _, _, rfl⟩) h0 hea hws

/-- (`EtaO.not_bufInitL_pub`) A fencing term is not a buffer initialisation. -/
theorem not_bufInitL_fence {th : TTh} {a : At} {l : AllocLabel} (hf : FenceAt th.term a) : ¬ BufInitL th l := by
  rintro ⟨x1, bb, ib, v, e1, rt, ws, ad, h1, -, -, -⟩
  rcases hf with ⟨y, e, h⟩ | ⟨rn, pn, tn, e, h⟩ | ⟨y, r, e, h⟩ <;> rw [h] at h1 <;> cases h1

/-- (`FlatWinStart.solo_pub_split`) The run split at a fencing term. -/
theorem solo_fence_split {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c1 c1a : Cfg}
    (h : Solo p k arch i c1 c1a) : ∀ {th1 : TTh} {a : At},
    c1.ths[i]? = some th1 → FenceAt th1.term a →
    (∃ tha, c1a.ths[i]? = some tha ∧ tha.term = th1.term ∧ tha.env = th1.env) ∨
    ∃ c1p thp c1', Solo p k arch i c1 c1p ∧ c1p.ths[i]? = some thp ∧ thp.term = th1.term ∧
      thp.env = th1.env ∧ c1' ∈ threadSteps p k arch c1p i ∧ Solo p k arch i c1' c1a := by
  induction h with
  | refl c => intro th1 _ hth _; exact Or.inl ⟨th1, hth, rfl, rfl⟩
  | thread hs hrest _ =>
      intro th1 _ hth _
      exact Or.inr ⟨_, th1, _, .refl _, hth, rfl, rfl, hs, hrest⟩
  | prom a' v w hw hrest ih =>
      intro th1 a hth hf
      rcases ih (FlatWinStart.promise_ths hth) hf with ⟨tha, h1, h2, h3⟩ | ⟨c1p, thp, c1', h1, h2, h3, h4, h5, h6⟩
      · exact Or.inl ⟨tha, h1, h2, h3⟩
      · exact Or.inr ⟨c1p, thp, c1', .prom a' v w hw h1, h2, h3, h4, h5, h6⟩
  | ext hs hrest _ =>
      intro th1 a hth hf
      exfalso
      obtain ⟨th', x, n, a', e', -, -, -, hth', ht', -⟩ := extSteps_elim hs
      rw [hth] at hth'; cases hth'
      rcases hf with ⟨y, e, h⟩ | ⟨rn, pn, tn, e, h⟩ | ⟨y, r, e, h⟩ <;> rw [h] at ht' <;> cases ht'

/-- (`BornW.ownXLeB_of_U`) At a fencing term of `x` the U bound is the ♭ bound. -/
theorem ownXLeB_of_U_fence {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c : Cfg} {th1 : TTh} {a : At} {rt : Ty} {ws : List Word} {ad : Address}
    (h : OwnXLeBU p k arch E0 i x 0 c) (hth1 : c.ths[i]? = some th1)
    (hf : FenceAt th1.term a) (hea : evalAt th1.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) (hx : ad.label = x) : OwnXLeB p k arch E0 i x 1 c := by
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, -, hle, hX, hA, hTyE, hRc, -, hR⟩ := h
  rw [hth1] at hth
  cases hth
  have hT0 := hT
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hTy, htv, hi, -, -⟩ := hT0
  obtain ⟨cl, hcl, -⟩ := fence_own_cellK hTy.1 (finv_ofB htv hi) hf hea hws
  have hsx : E.sto x ≠ none := by
    rw [← hCE, ← hx]
    show η.sto ad.label ≠ none
    rw [hcl]; exact Option.some_ne_none _
  rw [bornBit_some hsx] at hle
  exact ⟨th1, E, Tot, HP, hth1, hT, hm, hP, hb, hn, hsx, by omega, hX, hA, hTyE, hRc, fun h1 => absurd h1 (by decide), hR⟩

/-- (`EtaDyFr.pub_splitFD`) A fenced label is a base-cut cell or a fresh label of the window. -/
theorem fence_splitFD {p : Prog} {k : Promises.Knobs} {arch : Arch} {lb nn : Nat} {E0 : TEnv} {n0 i : Nat} {c1 : Cfg}
    {th1 : TTh} {a : At} {rt : Ty} {ws : List Word} {ad : Address}
    (hI : EtaDyFr.EtaFD p k arch lb nn E0 n0 i c1) (hth1 : c1.ths[i]? = some th1) (hf : FenceAt th1.term a)
    (hea : evalAt th1.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0]) :
    E0.sto ad.label ≠ none ∨ ∃ j, n0 ≤ j ∧ ad.label = freshLabel lb nn i j := by
  obtain ⟨th, E, hth, ⟨ρ, η, cx, hCE, -, hT, -, hi, -⟩, -, -, -, -, -, -, hf', -⟩ := hI
  rw [hth1] at hth
  cases hth
  obtain ⟨cl, hcl, -⟩ := fence_own_cellK hT.1 hi hf hea hws
  rcases hf' ad.label with h | h
  · left
    rw [← h, ← hCE]
    show η.sto ad.label ≠ none
    rw [hcl]; exact fun h0 => by cases h0
  · exact .inr h

/-! ## ♭ window chain at every fencing term (ShadowWinChain twins) -/
section
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The shadow fence step of `x` at count 1 (`tgt_publish1S`'s statement at any fencing term). -/
def TgtFenceS (p : Prog) : Prop :=
  ∀ {g : G} {x : AllocLabel} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs HP : Res} {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} {a : At},
    SrcB p g x 1 mem pairs th ρ η cx Rf Rs HP → FenceAt th.term a →
    evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g'] → ad.label = x → PwSkel →
    ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvREB g.lbase g.n g.i p E r.2.2 Tot ∧
      MemInvB g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldPB E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
      E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ 0 ∧
      TermOwnX2.Flat.AnchStepB g th (CE η) E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧
      TyOKE { g with tys := tysUpd g.tys th r.2.2 } E ∧ RecFresh { g with tys := tysUpd g.tys th r.2.2 } g.i r.2.2.nalloc ∧
      E.ini = (CE η).ini ∧ E.rini = (CE η).rini

/-- `TgtFenceS`, discharged: `tgt_publish1S` and the twins `tgt_region1S` / `tgt_into1S` (ShadowPubStep). -/
theorem tgtFence_of {p : Prog} (hP : ProgT p) : TgtFenceS p := by
  intro g x mem pairs th ρ η cx Rf Rs HP rt ws ad g' a hS hf hea hws hxl hPS
  rcases hf with ⟨y, e, h⟩ | ⟨rn, pn, tn, e, h⟩ | ⟨y, r, e, h⟩
  · exact tgt_publish1S hP hS h hea hws hxl hPS
  · exact tgt_region1S hP hS h hea hws hxl hPS
  · exact tgt_into1S hP hS h hea hws hxl hPS

/-- (`ownXPub1S` at any fencing term) -/
theorem ownXFence1S [WrIniCB] {p : Prog} [ProgRetIall p] (hP : ProgT p) {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {x : AllocLabel} (hPS : PwSkel) (htgt : TgtFenceS p) {E0 : TEnv} {c0 c0' : Cfg} {th : TTh} {a : At}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat}
    (hth : c0.ths[i]? = some th) (hsc : ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c0)
    (hI : TermOwnX2.Flat.OwnXLeB p k arch E0 i x 1 c0)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc : Certified p k arch c0' i)
    (hf : FenceAt th.term a) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∃ η1 : TEnv, EnvOKB p η1 ∧ MemInvB (gOf p k arch c0 i) (CE η1) (stOf c0.mem c0.pairs th) ∧
      ExtB E0 (CE η1) ∧ (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      TermOwnX2.Flat.OwnXLeB p k arch (reAncB E0 (CE η1) x) i x 0 c0' := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hFI, rfl, hRP, hDy⟩, hm, hH, hbf, hnie, hsto, hle, hx0, hA, hTy, hRc, -, hR⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hFp := TermOwnX2.Flat.finv_ofB htv hFI
  have hS : SrcB p (gOf p k arch c0 i) x 1 c0.mem c0.pairs th ρ η cx Rf Rs HP :=
    ⟨rfl, Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)), hE, hT.1, hT.2, htv, hFI, hm, hH, hbf, hnie, hsto, hle,
      hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hFp, PAx_of_step hs hc hth, hRP, hDy, hTy, hRc⟩
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', Tot', HP', hT', hm', hH', hnie', hsto', hle', hAS, hTy', hRc', hEi, hEr⟩ :=
    htgt hS hf hea hws hxl hPS r hr hpa
  obtain ⟨hx', hA'⟩ := hAS.1 E0 hx0 hA hm.2.2.2.1.old hm' (TermOwnX2.Flat.wrHypB hE hT.1 htv hFp hm hS.sc (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr)
  refine ⟨η, hE, hm, hx0, hsto, hR hR0, r.2.2, E', Tot', HP', e3, (by rw [(threadSteps_lbase hs).1, threadSteps_n hs]; exact hT'), ?_, ?_, by rw [gOf_thread hs]; exact hbf, hnie', hsto', hle', ?_, ?_, ?_, ?_, ?_,
    fun _ => hAS.2.2 (hR hR0)⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hH'
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := hx'
    refine ⟨a1, a2, a3, a4, a5, fun l => ?_, a7, a8, a9, a10, a11, fun l => ?_⟩
    · show (if l = x then (CE η).ini x else E0.ini l) ≤ E'.ini l
      by_cases h : l = x
      · subst h; rw [if_pos rfl, hEi]; exact Nat.le_refl _
      · rw [if_neg h]; exact a6 l
    · show (if l = x then (CE η).rini x else E0.rini l) ≤ E'.rini l
      by_cases h : l = x
      · subst h; rw [if_pos rfl, hEr]; exact Nat.le_refl _
      · rw [if_neg h]; exact a12 l
  · rw [e1, e2]
    obtain ⟨b1, b2⟩ := hA'
    refine ⟨fun l hl => ?_, b2⟩
    show E'.ini l ≤ max (if l = x then (CE η).ini x else E0.ini l) (E'.rini l)
    by_cases h : l = x
    · subst h; rw [if_pos rfl, hEi]; exact Nat.le_max_left _ _
    · rw [if_neg h]; exact b1 l hl
  · rw [gOf_thread hs]; exact TyOKE_mono (TermTyped.tysOf_thread hs hth e3 hRc) hTy'
  · rw [gOf_thread hs]
    exact RecFresh_sub (g := { gOf p k arch c0 i with tys := tysUpd (gOf p k arch c0 i).tys th r.2.2 })
      (g' := { gOf p k arch c0 i with tys := tysOf c0' }) (TermTyped.tysOf_thread hs hth e3 hRc) rfl rfl hRc'
  · intro _
    show E'.rini x ≤ (if x = x then (CE η).rini x else E0.rini x)
    rw [if_pos rfl, hEr]; exact Nat.le_refl _
/-- (`ownXLe_pub_chainS` at any fencing term) -/
theorem ownXLe_fence_chainS [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c c1 c1' c2 : Cfg} {th : TTh} {a : At}
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (htgt : TgtFenceS p)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : TermOwnX2.Flat.OwnXLeB p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (h1 : Solo p k arch i c c1)
    (hs : c1' ∈ threadSteps p k arch c1 i) (hth : c1.ths[i]? = some th) (hf : FenceAt th.term a)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∃ η1 : TEnv, EnvOKB p η1 ∧ MemInvB (gOf p k arch c1 i) (CE η1) (stOf c1.mem c1.pairs th) ∧
      ExtB E0 (CE η1) ∧ (CE η1).sto x ≠ none ∧ (∀ l, (CE η1).rini l ≤ (CE η1).ini l) ∧
      TermOwnX2.Flat.OwnXLeB p k arch (reAncB E0 (CE η1) x) i x 0 c2 := by
  have hc1' : Certified p k arch c1' i := certified_back h2 hc2
  have hc1 : Certified p k arch c1 i := certified_back (.thread hs h2) hc2
  have hI1 := ownXLe_runAllS hP hPS hSub hSig hQ hvI h0 hTA h1 hc1
  obtain ⟨η1, hE1, hm1, hX1, hs1, hr1, hI1'⟩ :=
    ownXFence1S hP hPS htgt hth (hQ c1 h1 hc1) (TermViewInv.viewInv_solo hvI h1) hI1 hs hc1' hf hea hws hx hR0
  exact ⟨η1, hE1, hm1, hX1, hs1, hr1, ownXLe_runAllS hP hPS hSub hSig (fun c0 h3 h4 => hQ c0 (solo_trans h1 (.thread hs h3)) h4)
    (TermViewInv.viewInv_thread (TermViewInv.viewInv_solo hvI h1) hs) hI1'
    (TermTyped.tidAt_thread hs (TermTyped.tidAt_solo h1 hTA)) h2 hc2⟩

end

/-! ## The window oracle and NoHold at every fencing term -/
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open CertWinProof

/-- (`BornW.OFresh` at every fencing term) -/
def OFreshF (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) (th : TTh) : Prop :=
  ∀ c1 th1 (a : At) (rt : Ty) (ws : List Word) (ad : Address) (j : Nat),
    Solo p k arch i c c1 → Certified p k arch c1 i → c1.ths[i]? = some th1 →
    FenceAt th1.term a → evalAt th1.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
    th.nalloc ≤ j → ad.label = freshLabel c.lbase c.n i j →
    ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th0, c0.ths[i]? = some th0 → ¬ BufInitL th0 ad.label

/-- (`EtaO.eta_oracle` at every fencing term) -/
theorem eta_oracle_fence [WrIniCB] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs}
    {arch : Arch} {E0 : TEnv} {i : Nat} {c c1 : Cfg} {th1 : TTh} {a : At}
    {rt : Ty} {ws : List Word} {ad : Address} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (htgt : TgtFenceS p)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAtB p i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLeB p k arch E0 i ad.label 1 c) (hTA : TermTyped.TidAt i c E0) (hsolo : Solo p k arch i c c1)
    (hth1 : c1.ths[i]? = some th1) (hf : FenceAt th1.term a)
    (hea : evalAt th1.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad 0])
    (hR0 : ∀ l, E0.rini l ≤ E0.ini l) :
    ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th →
      ¬ BufInitL th ad.label := by
  intro c0 h2 hc0 th hth
  rcases solo_fence_split h2 hth1 hf with ⟨tha, h1, h3, -⟩ |
    ⟨c1p, thp, c1', h1, h3, h4, h5, h6, h7⟩
  · have hee : tha = th := Option.some.inj (h1.symm.trans hth)
    rw [← hee]
    exact not_bufInitL_fence (by rw [h3]; exact hf)
  · have hea' : evalAt thp.env a = some (rt, ws) := by rw [h5]; exact hea
    obtain ⟨η1, -, -, -, -, -, hI⟩ := ownXLe_fence_chainS hP hPS hSub hSig htgt hQ hvI h0 hTA
      (solo_trans hsolo h1) h6 h3 (by rw [h4]; exact hf) hea' hws rfl h7 hc0 hR0
    obtain ⟨th', hth', ρ, η, cx, Rf, Rs, hE, hTy, hFI, hz⟩ := OwnXLeB.rf_zero hI
    have hee : th' = th := Option.some.inj (hth'.symm.trans hth)
    rw [← hee]
    exact not_bufInitL_ofB hE hTy hFI hz

/-- (`BornW.oFresh_of` at every fencing term) -/
theorem oFresh_fence {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) (htgt : TgtFenceS p) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hrs : TermScope.RunScopeI c) (hvI : TermViewInv.ViewInv c) (hK : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg i S)) :
    OFreshF p k arch i c th := by
  intro c1 th1 a rt ws ad j hsolo hc1 hth1 hf hea hws hj hjl
  have hPS := TermMain.pwSkel_ok
  have hSub := TermMain.pwSubS_ok
  have hSig := TermMain.pwSig_ok
  have hTA := TermMain.tidAt_cut hinv i S
  have hQ := TermCertScope.Flat.scopeAtB_solo (i := i) (k := k) (arch := arch) hps hrs
  have h0 := ownXLeBU_start hinv hth hS hj hK
  have h1 := ownXLe_runAllSU hP hPS hSub hSig hQ hvI h0 hTA hsolo hc1
  have h2 := ownXLeB_of_U_fence h1 hth1 hf hea hws hjl
  exact eta_oracle_fence hP hPS hSub hSig htgt (fun c0 h hc => hQ c0 (solo_trans hsolo h) hc)
    (TermViewInv.viewInv_solo hvI hsolo) (by rw [hjl]; exact h2) (TermTyped.tidAt_solo hsolo hTA) (.refl _) hth1 hf hea hws hinv.rle

/-- (`EtaN.noHold_eta` at every fencing term) -/
theorem noHold_eta_fence {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS)
    (hSig : PwSig) (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Eg : GEnv}
    {S : AllocLabel → Prop} {i : Nat} {c c1 : Cfg} {th th1 : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {a : At} {rt : Ty} {ws : List Word} {ad : Address}
    (hth : c.ths[i]? = some th) (hsolo : Solo p k arch i c c1) (hc1 : Certified p k arch c1 i)
    (hth1 : c1.ths[i]? = some th1)
    (hrs : TermScope.RunScopeI c) (hvI : TermViewInv.ViewInv c) (hTA : TermTyped.TidAt i c (Cut Eg i S))
    (hPH : TermPredHold.PredHoldG Eg c) (hPT : TermMain.PromTyAOK Eg c)
    (hm0 : MemInv (gOf p k arch c i) (Cut Eg i S) (stOf c.mem c.pairs th))
    (hE : EnvOK p η) (hT : TermSound.TypedK p η cx th1.term) (htv : TvOK cx)
    (hF : FInv ρ η th1.σs (Resume p th1.stack) cx th1.env)
    (hm : MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1))
    (hExt : Ext (Cut Eg i S) (CE η)) (hA : IniAnch (Cut Eg i S) (CE η))
    (hR : RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1))
    (hf : FenceAt th1.term a) (hea : evalAt th1.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) (hns : ¬ (CE η).seen ad.label)
    (hK : ContE c1.lbase c1.n i p th1 (CE η))
    (hbf : (gOf p k arch c1 i).boxFence = true)
    (hO : ∀ c0, Solo p k arch i c1 c0 → Certified p k arch c0 i → ∀ th, c0.ths[i]? = some th →
      ¬ BufInitL th ad.label)
    (hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0)
    (hnp : ¬ Eg.pubd ad.label)
    (hsc : ScalFlat.ScalIni Eg)
    (hTy : TyOKE (gOf p k arch c1 i) (CE η)) (hDy : DyFr p annNew (progTgts p) η th1.σs th1.term)
    (hRc : RecFresh (gOf p k arch c1 i) i th1.nalloc) :
    NoHold (CE η) (stOf c1.mem c1.pairs th1) ad.label := by
  exact CertWinProof.noHold_eta_sto hP hPS hSub hSig hps hth hsolo hc1 hth1 hrs hvI hTA hPH hPT hm0 hE hT htv hF hm hExt hA hR
    (fence_sto (eta_seed hK hE hT htv hF hDy) hf hea hws) hns hK hbf hO hlab hnp hsc hTy hDy hRc

end
end EtaFence

namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat
  TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat
  TermOwnK3.Flat TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- PubWinSAN's antecedents at a certified configuration `c1` of the window from `c`, anchor `Cut Eg i S`. -/
def WinAnte (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat) (S : AllocLabel → Prop) (c c1 : Cfg)
    (th1 : TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) : Prop :=
  Solo p k arch i c c1 ∧ Certified p k arch c1 i ∧ c1.ths[i]? = some th1 ∧ EnvOK p η ∧ Typed p cx th1.term ∧
    TvOK cx ∧ FInv ρ η th1.σs (Resume p th1.stack) cx th1.env ∧
    MemInv (gOf p k arch c1 i) (CE η) (stOf c1.mem c1.pairs th1) ∧ Ext (Cut Eg i S) (CE η) ∧
    IniAnch (Cut Eg i S) (CE η) ∧ RiniMem (Cut Eg i S) (CE η) (stOf c1.mem c1.pairs th1)

/-- **The anchor temporaries** of a window from `cS` at the anchor `Cut Eg i S` (quantified over `WinAnte`). -/
structure WinTmpA (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat)
    (S : AllocLabel → Prop) (cS : Cfg) : Prop

/-- **The named window temporaries** at a window start `c` (thread `i`, `th`, cut `Cut Eg i S`). -/
structure WinTmp (p : Prog) (k : Promises.Knobs) (arch : Arch) (Eg : GEnv) (i : Nat)
    (S : AllocLabel → Prop) (c : Cfg) (th : TTh) : Prop extends WinTmpA p k arch Eg i S c

/-- A thread with no own-count at `x` is not publishing `x`. -/
theorem own_pub_ne {p : Prog} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {th : TTh} {x : AllocLabel}
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hE : EnvOKB p η) (hTy : Typed p cx th.term) (hFI : FInvRB glb gnum gi ρ η th.σs (ResumeRB glb gnum gi p th.stack Rs) cx th.env Rf)
    (h0 : Rf (.own x) = 0) (hterm : th.term = .let_ y (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ad.label ≠ x := by
  rw [hterm] at hTy
  cases hTy with
  | let_ hop he =>
    cases hop with
    | publish hu hsh hb => exact use_own_neB hu hFI hE (Or.inl ⟨_, rfl⟩) h0 hea hws
    | publishBuf hu hsh hb => exact use_own_neB hu hFI hE (Or.inr ⟨_, _, _, rfl⟩) h0 hea hws

/-- **(B12 core, general anchor)** `NoHoldPubN` at every certified configuration `c1` of a window from `cS`,
anchor `Cut Eg i S`, where the lineage (EtaF), the ♭ chain and the oracle run from a `SysInvN` base `c`
(`Eg0`, `S0`) with `Solo c c1`; `Eg` keeps `Eg0`'s cut cells, adds no `pubd`, and keeps `ini` off `Eg0`'s cells. -/
theorem win_gen {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg0 : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S0 : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg0 Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg0 (Tot i) (HP i) HS (cr i) (db i) S0)
    (hrs : TermScope.RunScopeI c) (hvI : TermViewInv.ViewInv c)
    {cS : Cfg} {thS : TTh} {Eg : GEnv} {S : AllocLabel → Prop} (hW : WinTmpA p k arch Eg i S cS)
    (hthS : cS.ths[i]? = some thS) (hrsS : TermScope.RunScopeI cS) (hvIS : TermViewInv.ViewInv cS)
    (hTAS : TermTyped.TidAt i cS (Cut Eg i S)) (hPHS : TermPredHold.PredHoldG Eg cS)
    (hPTS : TermMain.PromTyAOK Eg cS) (hscS : ScalFlat.ScalIni Eg) (hmS : MemInv (gOf p k arch cS i) (Cut Eg i S) (stOf cS.mem cS.pairs thS))
    (hcut : ∀ l cl, cutSto Eg0 i l = some cl → cutSto Eg i l = some cl)
    (hpub : ∀ l, Eg.pubd l → Eg0.pubd l) (hini : ∀ l, Eg0.sto l = none → Eg.ini l = Eg0.ini l)
    {E0 : TEnv} {c1 : Cfg} (hsolo : Solo p k arch i c c1) (hsoloS : Solo p k arch i cS c1)
    (hc1 : Certified p k arch c1 i) :
    NoHoldPubN p k arch E0 (Cut Eg i S) i c1 := by
  intro th1 hth1 ρ η cx hE hT htv hF hm hExt hA hR hTy hDy _hRP
  -- (c1) the three fencing conjuncts of `PubWinTN` from one fence-generic key
  suffices key : ∀ a rt ws ad, EtaFence.FenceAt th1.term a → evalAt th1.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → ¬ (CE η).seen ad.label → NoHold (CE η) (stOf c1.mem c1.pairs th1) ad.label from
    ⟨fun y a e rt ws ad h => key a rt ws ad (by rw [h]; exact EtaFence.fenceAt_publish),
     fun a r pn tn e rt ws ad h => key a rt ws ad (by rw [h]; exact EtaFence.fenceAt_region),
     fun y r a e rt ws ad h => key a rt ws ad (by rw [h]; exact EtaFence.fenceAt_intoRgn)⟩
  intro a rt ws ad hf hea hws hns
  have htgt : EtaFence.TgtFenceS p := EtaFence.tgtFence_of hP
  have hPS := TermMain.pwSkel_ok
  have hSub := TermMain.pwSubS_ok
  have hSig := TermMain.pwSig_ok
  have hWA : WinAnte p k arch Eg i S cS c1 th1 ρ η cx := ⟨hsoloS, hc1, hth1, hE, hT.1, htv, hF, hm, hExt, hA, hR⟩
  have hTA := TermMain.tidAt_cut hinv i S0
  have hQ := TermCertScope.Flat.scopeAtB_solo (i := i) (k := k) (arch := arch) hps hrs
  have hB0 : FlatAnchor.ContB c.lbase c.n i p th (Cut Eg0 i S0) := ContAnchor.contB_of hth hS.2.2.1 hinv.rle
  -- O1: the lineage (and its `RecFresh`) from the base only: `seedFD` at `c`, `eta_soloFD` to `c1`.
  have hF1 := EtaDyFr.eta_soloFD hP hPS hSub hSig hps hsolo hc1 hrs hTA (EtaDyFr.seedFD hinv hth hS)
  have hRc : RecFresh (gOf p k arch c1 i) i th1.nalloc := by
    obtain ⟨th1', _, hth1', _, _, _, _, _, _, _, _, _, hr⟩ := hF1
    rw [hth1] at hth1'
    cases hth1'
    exact hr
  have hbf1 : (gOf p k arch c1 i).boxFence = true := by
    obtain ⟨_, _, _, _, _, hb, _⟩ := hF1
    exact hb
  rcases EtaFence.fence_splitFD hF1 hth1 hf hea hws with hin | ⟨j, hj, hjl⟩
  · -- the published label is in the base cut: owned by `i`
    obtain ⟨cl, hcl⟩ : ∃ cl, (Cut Eg0 i S0).sto ad.label = some cl := Option.ne_none_iff_exists'.mp hin
    have hEg0 : Eg0.sto ad.label = some cl := (cutSto_some.1 hcl).1
    have hclA : cutSto Eg i ad.label = some cl := hcut _ _ hcl
    have hEg : Eg.sto ad.label = some cl := (cutSto_some.1 hclA).1
    obtain ⟨cl', hcl', ho'⟩ := EtaFence.fence_own_cell hT.1 hF hf hea hws
    have h1 : (CE η).sto ad.label = some cl := hExt.2.2.2.2.1 _ _ hclA
    have h2 : (CE η).tid = i := hExt.2.2.2.1
    have h3 : η.sto ad.label = some cl := h1
    rw [hcl'] at h3
    cases h3
    have ho : cl.owner = some i := by rw [ho']; exact congrArg some h2
    have hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0 :=
      .inl ⟨cl, hEg, ho⟩
    have hnp : ¬ Eg.pubd ad.label := by
      intro hpd
      have hz := ((hinv.ownPub _ (hpub _ hpd)).2 (by rw [hEg0]; exact fun h0 => by cases h0)).1 i th hth
      have h00 := FlatWinStart.ownXLeB_start_le (n := 0) hinv hth hS hEg0 (.inl ho) (Nat.le_of_eq hz) hB0
      have h01 := ownXLe_runAllS hP hPS hSub hSig hQ hvI h00 hTA hsolo hc1
      obtain ⟨th', hth', ρ', η', cx', Rf, Rs, hE', hTy', hFI', hz'⟩ := OwnXLeB.rf_zero h01
      rw [hth1] at hth'
      cases hth'
      exact EtaFence.own_fence_ne hE' hTy' hFI' hz' hf hea hws rfl
    have hO := EtaFence.eta_oracle_fence hP hPS hSub hSig htgt hQ hvI (FlatWinStart.ownXLeB_start hinv hth hS hEg0 (.inl ho) hB0) hTA
      hsolo hth1 hf hea hws hinv.rle
    exact EtaFence.noHold_eta_fence hP hPS hSub hSig hps hthS hsoloS hc1 hth1 hrsS hvIS hTAS hPHS hPTS hmS hE hT htv
      hF hm hExt hA hR hf hea hws hns (ContAnchor.contE_of hth1 hm) hbf1 hO hlab hnp hscS hTy hDy hRc
  · -- the published label is a fresh label of the window
    have hG := hinv.fresh i th hth j hj
    have hjl' : ad.label = freshLabel c.lbase c.n i j := hjl
    have hlab : (∃ cl0, Eg.sto ad.label = some cl0 ∧ cl0.owner = some i) ∨ Eg.ini ad.label = 0 :=
      .inr (by rw [hjl', hini _ hG.1]; exact hG.2.2.1)
    have hnp : ¬ Eg.pubd ad.label := fun hpd =>
      (hinv.ownPub _ (hpub _ hpd)).1 (by rw [hjl']; exact hG.2.2.2.1)
    have hO := EtaFence.oFresh_fence hP hps htgt hinv hth hS hrs hvI hB0 c1 th1 a rt ws ad j hsolo hc1 hth1 hf hea hws hj hjl'
    exact EtaFence.noHold_eta_fence hP hPS hSub hSig hps hthS hsoloS hc1 hth1 hrsS hvIS hTAS hPHS hPTS hmS hE hT htv
      hF hm hExt hA hR hf hea hws hns (ContAnchor.contE_of hth1 hm) hbf1 hO hlab hnp hscS hTy hDy hRc

/-- **(B12 core)** `NoHoldPubN` at every certified configuration of a window from a `SysInvN` start. -/
theorem win_core {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hps : TermScope.ProgScopeOK p = true) {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hrs : TermScope.RunScopeI c) (hvI : TermViewInv.ViewInv c) (hW : WinTmp p k arch Eg i S c th)
    {E0 : TEnv} {c1 : Cfg} (hsolo : Solo p k arch i c c1) (hc1 : Certified p k arch c1 i) :
    NoHoldPubN p k arch E0 (Cut Eg i S) i c1 :=
  win_gen hP hps hinv hth hS hrs hvI hW.toWinTmpA hth hrs hvI (TermMain.tidAt_cut hinv i S)
    hinv.predHold hinv.promTy hinv.scalIni hS.2.2.1 (fun _ _ h => h) (fun _ h => h) (fun _ _ => rfl) hsolo hsolo hc1

/-- **(B12) `CertWinCNX`** from the named window temporaries. -/
theorem certWinC_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hty : ProgT p) (hdy : TermSound.DyClean p) (hsw : TermScope.ProgScopeOKW p = true)
    (A : SpArms p k arch Sp c0)
    (hW : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh}, TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
      ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      WinTmp p k arch Eg i S c th) :
    TermCertScope.CertWinCNX p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r X S hS c1 h1 h2
  obtain ⟨hP, hRI, hCk, -, hvI, -, -⟩ := FlatWinStart.winPrem hty hdy hsw A X S
  haveI := hRI
  haveI := hCk
  exact win_core hP (TermScope.ProgScopeOKW.scope hsw) X.inv X.hth hS (A.runDRF X.run) hvI (hW X S hS) h1 h2

/-- **(B12) `CertWinPNX`, first conjunct** (the pre-promise anchor): the window from `c` through the promise. -/
theorem certWinP1_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {Init : Res}
    {MintOK : Res → Prop} {c0 : Cfg} (hty : ProgT p) (hdy : TermSound.DyClean p) (hsw : TermScope.ProgScopeOKW p = true)
    (A : SpArms p k arch Sp c0)
    (hW : ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      WinTmp p k arch Eg j S c th) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
      {a : Address} {v : WeakMem.Val} {w : Ts}, PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
      ∀ S, ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
      ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
        NoHoldPubN p k arch (Cut Eg j S) (Cut Eg j S) j c1 := by
  intro c Eg Tot HP HS cr db j th a v w X S hS c1 h1 h2
  have hP : ProgT p := hty
  have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope hsw
  haveI : ProgRetIall p := ⟨fun _ hd => TermScope.noIallV_of_drf1L _ (TermScope.drf1L_of_drf1 _ (TermScope.ProgScopeOK.decl hPSc hd).2.1), hdy⟩
  haveI : TermA4.ProgCkWC p := ⟨TermA4.progCkW_of_scopeW hsw, hdy⟩
  exact win_core hP hPSc X.inv X.hth hS (A.runDRF X.run) (A.viewInv X.run) (hW X S hS) (.prom a v w X.hw h1) h2

end CertWinProof
