import WeakCore.NLayer
import WeakCore.StackResFree
import WeakCore.WinPubSplit
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
/-! **EtaL**: the η lineage on the internal
RetPw-free layer N.  Part 1: the cap step on N (port of W `cap_pres`/`tstep_cap`), the `ResumeB → ResumeBN`
weakening, and the seed. -/
namespace CertWinProof
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermOwnX2.Flat
  TermOwnK4.Flat
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ### The cap step on N (W TermStep:33481 `cap_pres`, :33535 `tstep_cap`, ported to ♭) -/

theorem VarsOKB_firstOK {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {vars : List (String × Ty × Bool)} {env : Env}
    (h : VarsOKB ρ η σs vars env) : VarsOKB ρ η σs (vars.filter (Cx.firstOK vars)) env :=
  fun x e he => h x e (find_firstOK vars x e he)

theorem cap_presB {p : Prog} {cx c' : Cx} {x : String} {op : Op} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty}
    {K : TEnv → List Word → Prop} {env : Env} {g : G} {s s' : St} {rt : Ty} {ws : List Word}
    (hT : OpT p cx x op c') (hA : CapOp op) (hncl : ∀ a tk, op ≠ .claim a tk)
    (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (hr : (s', rt, ws) ∈ evalOp g env σs s op) :
    FInvB g.lbase g.n g.i ρ η σs K c' ((x, rt, ws) :: env) := by
  cases hT <;> simp only [CapOp] at hA
  case borrow c₁ y c a t t' r hva hpk hlo hu hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have hay : a = .var y := by cases a <;> simp [varOf, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hva ⊢ <;> exact hva
    subst hay
    have htk : (∃ q st, t = .tok q st) ∨ (∃ q P i j, t = .tok2 q P i j) ∨ ∃ q, t = .share q := by
      cases t <;> simp [lendOf, throw, throwThe, MonadExceptOf.throw] at hlo <;> simp
    have haf : affine cx.ke t = true := by
      rcases htk with ⟨q, st, rfl⟩ | ⟨q, P, i, j, rfl⟩ | ⟨q, rfl⟩ <;> simp [affine, Ty.affineIn]
    obtain ⟨hp, hc⟩ := use_cases hu
    rw [hpk] at hp
    simp only [Except.ok.injEq] at hp
    subst hp
    rcases hc with ⟨hna, -⟩ | ⟨y', hy', rfl⟩
    · rw [haf] at hna; cases hna
    · simp only [At.var.injEq] at hy'
      subst hy'
      have hi1 := (use_FInvB (bkG := False) hu hi).1
      have hfr : FInvB g.lbase g.n g.i ρ η σs K { cx with vars := cx.vars.map (markU y), lent := y :: cx.lent } env :=
        ⟨hi1.1, hi1.2.1, hi1.2.2⟩
      exact bind_FInvB hb hfr (by simp [VRF, VRb2]) (Lay_cap σs c r)
  case freeze c₁ a r hu hsr hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    exact bind_FInvB hb (use_FInvB (bkG := False) hu hi).1 (by simp [VRF, VRb2]) (Lay_cap σs .frz r)
  case endBorrow y a hva hy hb =>
    simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    obtain ⟨F, hceq, hF⟩ := endCx_eq cx y
    rw [hceq] at hb
    have hv : VarsOKB ρ η σs ((cx.vars.filter (Cx.firstOK cx.vars)).map F) env :=
      VarsOK_flagsB F (fun e => ⟨(hF e).1, (hF e).2.1⟩) (VarsOKB_firstOK hi.2.1)
    have hfr : FInvB g.lbase g.n g.i ρ η σs K
          { cx with
          lent := cx.lent.erase y
          vars := (cx.vars.filter (Cx.firstOK cx.vars)).map F } env :=
      ⟨hi.1, hv, hi.2.2⟩
    exact bind_FInvB hb hfr (by simp [VRF, VRb2]) (Lay_unitT σs)
  case claim => exact absurd rfl (hncl _ _)

/-- **The cap step on N**: same state, typed at the same environment. -/
theorem tstep_capBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} (hP : ProgT p) (hc : CapT th.term)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeBN g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ThInvEBN g.lbase g.n g.i p (CE η) r.2.2 ∧ Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  obtain ⟨x, op, e, hterm, hA, hncl⟩ := capT_inv hc
  have hsame := same_let (g := g) (mem := mem) (pairs := pairs) hterm
    (fun f is a ts h => by subst h; simp [CapOp] at hA) (fun f a h => by subst h; simp [CapOp] at hA)
    (fun r hr => same_of_eq (cap_state hA r hr))
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      have key := tstep_capOp (g := g) (mem := mem) (pairs := pairs) hterm hA
      refine ⟨?_, fun r hr => ⟨?_, hsame r hr⟩⟩
      · rw [key]; cases op <;> simp only [CapOp] at hA <;> simp [evalOp]
      · rw [key] at hr
        simp only [List.mem_map] at hr
        obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := hr
        exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, cap_presB hop hA hncl hi hm, retPwN_true, hDy.letW hterm rfl⟩

/-! ### `ResumeB → ResumeBN` (drop the pubWords clauses) -/

theorem RetOKB_monoK {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {ret : Ty} {K K' : TEnv → List Word → Prop}
    (hK : ∀ E ws, K E ws → K' E ws) (h : RetOKB glb gnum gi ρ η σs ret K) : RetOKB glb gnum gi ρ η σs ret K' :=
  fun η' hx hS ws hv hl => hK _ _ (h η' hx hS ws hv hl)

theorem FInvB_monoK {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K K' : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} (hK : ∀ E ws, K E ws → K' E ws) (h : FInvB glb gnum gi ρ η σs K cx env) : FInvB glb gnum gi ρ η σs K' cx env := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, RetOKB_monoK hK h3, h4⟩

theorem ResumeB_toN {p : Prog} : ∀ (st : List Frame) (E : TEnv) (ws : List Word), ResumeB glb gnum gi p st E ws → ResumeBN glb gnum gi p st E ws
  | [], _, _, _ => trivial
  | f :: rest, _, _, ⟨ρ, η, c, hCE, hE, hT, hv, hF, _, hDy⟩ =>
      ⟨ρ, η, c, hCE, hE, hT, hv, FInvB_monoK (ResumeB_toN rest) hF, fun _ _ _ _ => trivial, hDy⟩

/-- The seed's continuation hypothesis (AnchorFrameTyping `ContB`'s resource-free twin; discharged by
`ContAnchor.contE_of` (ContIV, via `contE_f4`)). -/
def ContE (lb n i : Nat) (p : Prog) (th : TTh) (E : TEnv) : Prop :=
  ∀ (ρ : Nat → Nat) (η : TEnv) (cx : Cx), CE η = E → EnvOK p η →
    RetOK ρ η th.σs cx.ret (Resume p th.stack) → RetOKB lb n i ρ (FlatAnchor.flat η) th.σs cx.ret (ResumeB lb n i p th.stack)

/-- **(L1) The seed**: W's adversarial typing (PubWinSAN's antecedents) gives the N thread invariant at the same
environment, given `ContE`. -/
theorem eta_seed {p : Prog} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} (hK : ContE glb gnum gi p th (CE η))
    (hE : EnvOK p η) (hT : Typed p cx th.term) (htv : TvOK cx) (hF : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    ThInvEBN glb gnum gi p (CE η) th := by
  obtain ⟨h1, h2, -, h4⟩ := FlatAnchor.FInvB_flat (glb := glb) (gnum := gnum) (gi := gi) hE.2.1 hF
  exact ⟨ρ, FlatAnchor.flat η, cx, FlatAnchor.CE_flat η, FlatAnchor.EnvOKB_flat hE, hT, htv,
    ⟨h1, h2, RetOKB_monoK (ResumeB_toN th.stack) (hK ρ η cx rfl hE hF.2.2.1), h4⟩, retPwN_true, hDy⟩

end CertWinProof
