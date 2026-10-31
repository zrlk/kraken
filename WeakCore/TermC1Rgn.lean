import WeakCore.TermStep
import WeakCore.TermC1Inv

/-! # TermC1Rgn: `region` and `intoRgn` as `publish`

Opening a region publishes its cell, live or dead binder: the runtime step is `publish`'s release fence
(`fenceS .st`, TermRun L1128 / L692–705), and Σ plants the cell's frontier at `vWr` (or keeps an
already planted one) and marks it seen (`pubP`, `pubS`), exactly as `tstepM_publish`.

Stated against today's `MemInv`/`FInv`; the new facts are hypotheses:
* `hcpl`: the payload is `coupledOKIn` (checkW1's region / intoRgn test, `rgnPay`);
* `hsc : PubScope cx a`: the payload is `rgnFree` (today's `PubCpl` conjunct; at the switch `drf1`);
* `hwin`: `NoHold` at the cell (`PubWinTN1e.rgn` / `PubWinTN1e.into`);
* `hPb`: the plant gate `g.pf` at the cell.

New here:
* `PubWinTN1e`: `PubWinTN1` without its live-binder guard. Every region publishes, so the
  certification-window assumption covers every region, dead binders included.
* `RgnPubT1`: the region's cell is published and seen afterwards, from which the fresh region
  reference satisfies `ModeOK1 .rgn` (immediate: the cell is seen).
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `PubWinTN` at the three fencing operations: `publish`; every `region`, live or dead binder,
since every region publishes its cell; `intoRgn`: the cell it moves in. Unseen cells only. -/
def PubWinTN1e (E : TEnv) (s : St) (th : TTh) : Prop :=
  (∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ a r pn tn e rt ws ad, th.term = .region a r pn tn e →
    evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label) ∧
  (∀ x r a e rt ws ad, th.term = .let_ x (.intoRgn r a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label → NoHold E s ad.label)

/-- The publish conjunct of `PubWinTN1e` is `PubWinTN`. -/
theorem PubWinTN1e.pub {E : TEnv} {s : St} {th : TTh} (h : PubWinTN1e E s th) : TermTyped.PubWinTN E s th :=
  h.1

/-- `PubWinTN1e` implies `PubWinTN1` (it drops the live-binder guard). -/
theorem PubWinTN1e.toN1 {E : TEnv} {s : St} {th : TTh} (h : PubWinTN1e E s th) : PubWinTN1 E s th :=
  ⟨h.1, fun a r pn tn e rt ws ad ht _ => h.2.1 a r pn tn e rt ws ad ht, h.2.2⟩

/-- The region conjunct at a `region` term: `NoHold` at an unseen cell, any binder. -/
theorem PubWinTN1e.rgn {E : TEnv} {s : St} {th : TTh} {a : At} {r pn tn : String} {e : Expr}
    (h : PubWinTN1e E s th) (ht : th.term = .region a r pn tn e) :
    ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label →
      NoHold E s ad.label :=
  fun rt ws ad => h.2.1 a r pn tn e rt ws ad ht

/-- The `intoRgn` conjunct at an `intoRgn` term: `NoHold` at an unseen cell. -/
theorem PubWinTN1e.into {E : TEnv} {s : St} {th : TTh} {x r : String} {a : At} {e : Expr}
    (h : PubWinTN1e E s th) (ht : th.term = .let_ x (.intoRgn r a) e) :
    ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → ¬ E.seen ad.label →
      NoHold E s ad.label :=
  fun rt ws ad => h.2.2 x r a e rt ws ad ht

/-- After a step from `th0`: if `th0` opened a region on own cell `ad`, the cell has a frontier
and is seen. -/
def RgnPubT1 (E : TEnv) (th0 : TTh) : Prop :=
  ∀ a rn pn tn e rt ws ad, th0.term = .region a rn pn tn e → evalAt th0.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → E.pfr ad.label ≠ none ∧ E.seen ad.label

/-- `ThInvMF` that also records the region publish. -/
def ThInvMFR1 (p : Prog) (g : G) (E : TEnv) (s : St) (th0 : TTh) (mem : Memory) (pairs : List Ts) (th : TTh) :
    Prop :=
  ∃ E', EFootP g E E' s (stOf mem pairs th) ∧ ThInvE p E' th ∧ MemInv g E' (stOf mem pairs th) ∧
    RgnPubT1 E' th0

theorem ThInvMFR1.toF {p : Prog} {g : G} {E : TEnv} {s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts}
    {th : TTh} (h : ThInvMFR1 p g E s th0 mem pairs th) : ThInvMF p g E s mem pairs th :=
  let ⟨E', h1, h2, h3, _⟩ := h
  ⟨E', h1, h2, h3⟩

/-- After a step from `th0`: if `th0` moved own cell `ad` into a region (`intoRgn`), the cell has
a frontier and is seen. -/
def IntoPubT1 (E : TEnv) (th0 : TTh) : Prop :=
  ∀ x rn a e rt ws ad, th0.term = .let_ x (.intoRgn rn a) e → evalAt th0.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → E.pfr ad.label ≠ none ∧ E.seen ad.label

/-- `ThInvMF` that also records the `intoRgn` publish. -/
def ThInvMFI1 (p : Prog) (g : G) (E : TEnv) (s : St) (th0 : TTh) (mem : Memory) (pairs : List Ts) (th : TTh) :
    Prop :=
  ∃ E', EFootP g E E' s (stOf mem pairs th) ∧ ThInvE p E' th ∧ MemInv g E' (stOf mem pairs th) ∧
    IntoPubT1 E' th0

theorem ThInvMFI1.toF {p : Prog} {g : G} {E : TEnv} {s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts}
    {th : TTh} (h : ThInvMFI1 p g E s th0 mem pairs th) : ThInvMF p g E s mem pairs th :=
  let ⟨E', h1, h2, h3, _⟩ := h
  ⟨E', h1, h2, h3⟩

/-- `RgnPubT1` after a `region` step on the cell `lab`. -/
theorem RgnPubT1.of {E : TEnv} {th : TTh} {a : At} {rn pn tn : String} {e : Expr} {rt : Ty} {ws : List Word}
    {lab : AllocLabel} (hterm : th.term = .region a rn pn tn e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ∀ ad, ws.map (·.val) = [.loc ad 0] → ad.label = lab) (h : E.pfr lab ≠ none ∧ E.seen lab) :
    RgnPubT1 E th := by
  intro a' rn' pn' tn' e' rt' ws' ad' ht' hea' hws'
  rw [hterm] at ht'
  cases ht'
  rw [hea] at hea'
  cases hea'
  rw [hws ad' hws']
  exact h

/-- `IntoPubT1` after an `intoRgn` step on the cell `lab`. -/
theorem IntoPubT1.of {E : TEnv} {th : TTh} {x rn : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word}
    {lab : AllocLabel} (hterm : th.term = .let_ x (.intoRgn rn a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ∀ ad, ws.map (·.val) = [.loc ad 0] → ad.label = lab) (h : E.pfr lab ≠ none ∧ E.seen lab) :
    IntoPubT1 E th := by
  intro x' rn' a' e' rt' ws' ad' ht' hea' hws'
  rw [hterm] at ht'
  cases ht'
  rw [hea] at hea'
  cases hea'
  rw [hws ad' hws']
  exact h

/-- A one-word own handle's label. -/
theorem pwLab {pw : Word} {lab : AllocLabel} {ad : Address} (hpw : pw.val = .loc ⟨lab, 0⟩ 0)
    (h : [pw].map (·.val) = [.loc ad 0]) : ad.label = lab := by
  have h2 : [pw.val] = [.loc ad 0] := h
  rw [hpw] at h2
  cases h2
  rfl

/-- The shared tail of `region` and `intoRgn` on a non-null own cell: publish it (`pubCell_post`)
at `pubEnvAt η lab vWr Rd`, then the frame (`hTh`) and the published-and-seen record (`hPd`). -/
theorem pubStep1 {p : Prog} {g : G} {η : TEnv} {s : St} {lab : AllocLabel} {c : Cell} {Rd : Nat}
    {th0 th' : TTh} {mem' : Memory} {pairs' : List Ts} {Pd : TEnv → TTh → Prop}
    (hE : EnvOK p η) (hm : MemInv g (CE η) s) (hsto : η.sto lab = some c) (hown : c.owner = some η.tid)
    (hR : η.rid ≤ Rd)
    (hF : (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
      Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true)
    (hnh : NoHold (CE η) s lab) (hgp : g.pf lab) (hst : stOf mem' pairs' th' = fenceS s .st)
    (hTh : EnvOK p (pubEnvAt η lab s.vs.vWr Rd) → Ext η (pubEnvAt η lab s.vs.vWr Rd) →
      ThInvE p (CE (pubEnvAt η lab s.vs.vWr Rd)) th')
    (hPd : (CE (pubEnvAt η lab s.vs.vWr Rd)).pfr lab ≠ none ∧ (CE (pubEnvAt η lab s.vs.vWr Rd)).seen lab →
      Pd (CE (pubEnvAt η lab s.vs.vWr Rd)) th0) :
    ∃ E', EFootP g (CE η) E' s (stOf mem' pairs' th') ∧ ThInvE p E' th' ∧ MemInv g E' (stOf mem' pairs' th') ∧
      Pd E' th0 := by
  obtain ⟨hfoot, hx, hmi⟩ := pubCell_post (Rd := Rd) hE hm hsto hown hR hF hnh hgp
  rw [hst]
  exact ⟨_, hfoot, hTh ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩ hx, hmi, hPd (pubEnvAt_seen _ _ _ _)⟩

/-- A published, seen cell satisfies `ModeOK1 .rgn` at any words. -/
theorem ModeOK1_rgn_seen {i : Nat} {P : AllocLabel → Option Ts} {S : AllocLabel → Prop} {r : Idx}
    {l : AllocLabel} {c : Cell} {ws : List Word} (hP : P l ≠ none) (hS : S l) : ModeOK1 i P S (.rgn r) l c ws := by
  cases h : P l with
  | none => exact absurd h hP
  | some f => exact ⟨f, h, Or.inl hS⟩

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}

/-- **P1 + P4 at the thread, `region` on an own pointer**: the step publishes the cell.
The Σ is `pubEnvAt η lab vWr (η.rid + 1)`. -/
theorem tstepM_region1 {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hcpl : ∀ u c₁, (cx.use a = .ok (.ptr .own u, c₁) ∨
      ∃ n k u0, u = .array n u0 ∧ cx.use a = .ok (.refine (.loc .own (.array n u0)) (.ini k), c₁)) →
      Ty.coupledOKIn c₁.ke u = true)
    (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hPb : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → g.pf ad.label) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧
      ∀ r ∈ tstep g mem pairs th, ThInvMFR1 p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  obtain ⟨c, hc, hvc, hk, hcase⟩ := region_step hT0 hi htv (ridNext η)
  cases hT0 with
  | regionBuf hu hrc _ _ _ =>
    obtain ⟨hi1, rb, wsb, hea, hvb, hlb⟩ := use_FInv hu hi
    obtain ⟨μ', u', ψ', rfl⟩ := eskel_eq_refloc (by simpa [close, substTs, skel, rf, etok] using hlb.2.1)
    have hf : FInv (vcons (ridNext η) ρ) η th.σs (Resume p th.stack) c
        ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u') ψ', wsb) :: th.env) := by
      rcases hcase with ⟨μ2, u2, ws2, hea2, hf2⟩ | ⟨μ2, u2, ψ2, ws2, hea2, hf2⟩
      · rw [hea] at hea2; cases hea2
      · rw [hea] at hea2; cases hea2; exact hf2
    simp only [VR] at hvb
    obtain ⟨hv, -⟩ := hvb
    simp only [tstep, hterm, hea]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, -⟩
    · -- a null handle (an empty buffer): only the fence, as today
      have hxb := Ext_bumpR hE.2.1
      refine ⟨CE (bumpR η), EFoot_refl, ⟨_, bumpR η, c, CE_bumpR η, ⟨hE.1, hxb.1, hxb.2.2.2.2.2.2.2.2.2.2.1⟩,
          hc, hvc, FInv_ext hE.2.1 hxb (by simpa [withS] using hf),
          retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_fence hm,
        fun a' rn' pn' tn' e' rt' ws' ad' ht' hea' hws' => ?_⟩
      rw [hterm] at ht'
      cases ht'
      rw [hea] at hea'
      cases hea'
      rw [hnull] at hws'
      simp at hws'
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBuf hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1
        (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      exact pubStep1 (Rd := η.rid + 1) hE hm hsto hown (Nat.le_succ _) hF (hwin _ _ ad hea hws)
        (hPb _ _ ad hea hws) rfl
        (fun hE' hx => ⟨_, _, c, rfl, hE', hc, hvc, FInv_ext hE.2.1 hx (by simpa [withS] using hf),
          retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) (Ext.witEq hx)⟩)
        (RgnPubT1.of hterm hea fun ad' h => by rw [hws] at h; cases h; rfl)
  | region hu hrc _ _ _ =>
  obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, -⟩ := ownPtr_inv hu hi
  have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
  have hf : FInv (vcons (ridNext η) ρ) η th.σs (Resume p th.stack) c
      ((tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env) := by
    rcases hcase with ⟨μ2, u2, ws2, hea2, hf2⟩ | ⟨μ2, u2, ψ2, ws2, hea2, hf2⟩
    · rw [hea] at hea2; cases hea2; exact hf2
    · rw [hea] at hea2; cases hea2
  have hF := pubTyFacts hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
    (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
    (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
  simp only [tstep, hterm, hea]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  exact pubStep1 (Rd := η.rid + 1) hE hm hsto hown (Nat.le_succ _) hF (hwin _ _ ⟨lab, 0⟩ hea hwsv)
    (hPb _ _ ⟨lab, 0⟩ hea hwsv) rfl
    (fun hE' hx => ⟨_, _, c, rfl, hE', hc, hvc, FInv_ext hE.2.1 hx (by simpa [withS] using hf),
      retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) (Ext.witEq hx)⟩)
    (RgnPubT1.of hterm hea fun ad' h => pwLab hpw h)

/-- **P1 + P4 at the thread, `intoRgn` on an own pointer**: `publish` with a region
result. -/
theorem tstepM_intoRgn1 {x rn : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.intoRgn rn a) e) (hP : ProgT p) (hT : Typed p cx th.term)
    (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    (hcpl : ∀ u c₁, (cx.use a = .ok (.ptr .own u, c₁) ∨
      ∃ n k u0, u = .array n u0 ∧ cx.use a = .ok (.refine (.loc .own (.array n u0)) (.ini k), c₁)) →
      Ty.coupledOKIn c₁.ke u = true)
    (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      NoHold (CE η) (stOf mem pairs th) ad.label)
    (hPb : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] → g.pf ad.label) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧
      ∀ r ∈ tstep g mem pairs th, ThInvMFI1 p g (CE η) (stOf mem pairs th) th r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | intoRgnBuf hr hu hrc hb =>
    rename_i c₁ r n k u
    obtain ⟨hi1, μr, nr, ur, ψ, wsb, hea, hvb, hlay⟩ := ownBuf_inv hu hi
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (x, .refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ, wsb) :: th.env }
            (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    have hl := hlay (.rgn r) (.rgn (.lit 0)) (by simp [skelM]) (by simp [modeC, idxC, ofMs])
    simp only [VR] at hvb
    obtain ⟨hv, hir⟩ := hvb
    rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c0, U, hws, hsto, hat, hFU, hmode, hini⟩
    · -- a null handle (an empty buffer): only the fence
      have hvr : VR ρ η (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VR]; exact ⟨Or.inl ⟨hnull, e0, he0⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      refine ⟨CE η, EFoot_refl, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInv hb hi1 hvr hl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_fence hm,
        fun y rn' a' e' rt' ws' ad' ht' hea' hws' => ?_⟩
      rw [hterm] at ht'
      cases ht'
      rw [hea] at hea'
      cases hea'
      rw [hnull] at hws'
      simp at hws'
    · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
      have hown : c0.owner = some η.tid := hmode
      simp only [rgnCellOK, Bool.and_eq_true] at hrc
      have hF := pubTyFactsBuf hi1 hE hm hsto hown (by simpa [tb] using tb_use hu htv) hat
        (hcpl _ _ (.inr ⟨_, _, _, rfl, hu⟩)) hrc.1 (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))
      have hvr : VR ρ (pubEnvAt η ad.label (stOf mem pairs th).vs.vWr η.rid) (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          (shp (.refine (.loc (.rgn (.lit 0)) (.array nr ur)) ψ)) wsb := by
        simp only [VR]
        exact ⟨Or.inr ⟨ad, c0, _, hws, hsto, hat, .refl, trivial, IniAt_mono (modeIni_le_ini _ _ _) hini⟩,
          IniR_mono (TEnv.selIni_le_ini η _) hir⟩
      exact pubStep1 (Rd := η.rid) hE hm hsto hown (Nat.le_refl _) hF (hwin _ _ ad hea hws)
        (hPb _ _ ad hea hws) rfl
        (fun hE' hx => ⟨ρ, _, c', rfl, hE', he, htv', bind_FInv hb (FInv_ext hE.2.1 hx hi1) hvr hl,
          retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩)
        (IntoPubT1.of hterm hea fun ad' h => by rw [hws] at h; cases h; rfl)
  | intoRgn hr hu hrc hb =>
  rename_i c₁ r u
  obtain ⟨hi1, lab, c0, pw, μr, ru, hea, hpw, hsto, hcty, hown, hacc, hl⟩ := ownPtr_inv hu hi
  have hwsv : [pw].map (·.val) = [.loc ⟨lab, 0⟩ 0] := by simp [hpw]
  have hF := pubTyFacts hi1 hE (by simpa [tb] using tb_use hu htv) hcty hacc (hcpl _ _ (.inl hu))
    (by simp only [rgnCellOK, Bool.and_eq_true] at hrc; exact hrc.1)
    (hsc _ (use_cases hu).1 _ _ (Or.inl rfl))
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
        withS { th with term := e, env := (x, .ptr (.rgn (.lit 0)) ru, [pw]) :: th.env }
          (fenceS (stOf mem pairs th) .st))] := by
    simp only [tstep, hterm, evalOp, hea]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : VR ρ (pubEnvAt η lab (stOf mem pairs th).vs.vWr η.rid) (.ptr (.rgn r) u) (shp (.ptr (.rgn (.lit 0)) ru)) [pw] := by
    simp only [VR]
    exact ⟨⟨lab, 0⟩, c0, hwsv, rfl, hsto, hcty, trivial, hacc⟩
  have hlay : Lay th.σs (.ptr (.rgn r) u) (.ptr (.rgn (.lit 0)) ru) [pw] :=
    Lay_ptr_remode hl (by simp [skelM]) (by simp [modeC, idxC, ofMs])
  exact pubStep1 (Rd := η.rid) hE hm hsto hown (Nat.le_refl _) hF (hwin _ _ ⟨lab, 0⟩ hea hwsv)
    (hPb _ _ ⟨lab, 0⟩ hea hwsv) rfl
    (fun hE' hx => ⟨ρ, _, c', rfl, hE', he, htv', bind_FInv hb (FInv_ext hE.2.1 hx hi1) hvr hlay,
      retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩)
    (IntoPubT1.of hterm hea fun ad' h => pwLab hpw h)

end

end TermC1

#print axioms TermC1.PubWinTN1e.pub
#print axioms TermC1.PubWinTN1e.toN1
#print axioms TermC1.PubWinTN1e.rgn
#print axioms TermC1.PubWinTN1e.into
#print axioms TermC1.ThInvMFR1.toF
#print axioms TermC1.ModeOK1_rgn_seen
#print axioms TermC1.RgnPubT1.of
#print axioms TermC1.IntoPubT1.of
#print axioms TermC1.pwLab
#print axioms TermC1.pubStep1
#print axioms TermC1.tstepM_region1
#print axioms TermC1.ThInvMFI1.toF
#print axioms TermC1.tstepM_intoRgn1
