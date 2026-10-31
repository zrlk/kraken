/-
G1a: the step's footprint with `FreshArr` — a fresh array cell of the step's witness comes from
`newBuf`, with the element type closed at the witness.  The allocating steps (`new`, `newBuf`,
`inl`, `inr`, `case`) by the strengthened step lemmas of `TermStep` (`tstepM_newA`,
`tstepM_newBufA`, `tstepM_inlTS`, `tstepM_inrTS`, `tstepM_caseTS`); every other step keeps the
allocation count (`TermNallocF.tstep_nallocEq`), so it has no fresh label.
-/
import WeakCore.TermPubW
import WeakCore.TermNallocF

namespace TermStep
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermNallocF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (G1) A step that keeps the allocation count has no fresh label. -/
theorem FreshArr_vac {g : G} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {E' : TEnv} {r : Memory × List Ts × TTh}
    (hn : r.2.2.nalloc = th.nalloc) : FreshArr g ρ η th E' r := by
  intro l c N u hf
  obtain ⟨j, hj, hj2, -⟩ := hf
  omega

/-- (G1) `ThInvMFW` with `FreshArr` of its witness, for the old thread `th0`. -/
def ThInvMFWA (p : Prog) (g : G) (ρ : Nat → Nat) (η : TEnv) (th0 : TTh) (E : TEnv) (s : St) (mem : Memory)
    (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', FreshArr g ρ η th0 E' (mem, pairs, th) ∧ EFootW g E E' s (stOf mem pairs th) ∧ ThInvE p E' th ∧
    MemInv g E' (stOf mem pairs th)

theorem ThInvMFA.weakA {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {th0 : TTh} {E : TEnv} {s : St}
    {mem : Memory} {pairs : List Ts} {th : TTh} (h : ThInvMFA p g ρ η th0 E s mem pairs th) :
    ThInvMFWA p g ρ η th0 E s mem pairs th :=
  let ⟨E', fa, hf, h1, h2⟩ := h
  ⟨E', fa, hf.weak, h1, h2⟩

theorem ThInvMFWA.toW {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {th0 : TTh} {E : TEnv} {s : St}
    {mem : Memory} {pairs : List Ts} {th : TTh} (h : ThInvMFWA p g ρ η th0 E s mem pairs th) :
    ThInvMFW p g E s mem pairs th :=
  let ⟨E', _, hf, h1, h2⟩ := h
  ⟨E', hf, h1, h2⟩


/-- (G1) **`tstepMF_stepW` with `FreshArr`.** -/
theorem tstepMF_stepWFA {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFWA p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have gen : NotAllocT th.term → tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFWA p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
    fun hna =>
      let h := tstepMF_stepW (hDy := hDy) (hZ := hZ) (hPb := hPb) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hRP hPS hSub hSig hTy
      ⟨h.1, fun r hr hpa =>
        let ⟨E', h1, h2, h3⟩ := h.2 r hr hpa
        ⟨E', FreshArr_vac (tstep_nallocEq hr hna), h1, h2, h3⟩⟩
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | inl =>
        have h := tstepM_inlTS (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
        exact ⟨h.1, fun r hr hpa => ((h.2 r hr hpa).toA hm).weakA⟩
    | inr =>
        have h := tstepM_inrTS (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
        exact ⟨h.1, fun r hr hpa => ((h.2 r hr hpa).toA hm).weakA⟩
    | new =>
        have h := tstepM_newA (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
        exact ⟨h.1, fun r hr _ => (h.2 r hr).weakA⟩
    | newBuf =>
        have h := tstepM_newBufA (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
        exact ⟨h.1, fun r hr _ => (h.2 r hr).weakA⟩
    | _ => exact gen (by rw [ht]; unfold NotAllocT; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intros; intro h; cases h))
  | case =>
      have h := tstepM_caseTS (hDy := hDy) (hbf := hbf) ht hn hT hi hE htv hm hpx hRP hPS
      exact ⟨h.1, fun r hr hpa => ((h.2 r hr hpa).toA hm).weakA⟩
  | _ => exact gen (by rw [ht]; unfold NotAllocT; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intros; intro h; cases h))

/-- (G1) **`tstep_footprintW` with `FreshArr`**: the hypotheses of `tstep_footprintW`; the
witness also satisfies `FreshArr` for the old thread. -/
theorem tstep_footprintWFA {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT3 (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hZ : ∀ l, BufInitOn th l → ¬ g.zf l := by exact fun _ _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ FreshArr g ρ η th E' r := by
  rcases hsc with hsc | ⟨-, hc⟩
  case inr =>
    have k := tstep_cap (hDy := hDy) (g := g) (mem := mem) (pairs := pairs) hP hc hT hi hE htv hRP hPS
    refine ⟨k.1, fun r hr _ => ?_⟩
    have hF : FootW g (CE η) (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) :=
      ⟨(EFoot.weak EFoot_refl), fun l hl => fresh_blank hm hl⟩
    exact ⟨CE η, hF, FootW_ext hF, (k.2 r hr).1, MemInv_same hm (k.2 r hr).2, FreshArr_eq hm fun _ => rfl⟩
  have h := tstepMF_stepWFA (hDy := hDy) (hZ := hZ) (hPb := hPb) (hbf := hbf) hP hp hn hnd hsc hT hi hE htv hm hpx hwin hRP hPS hSub hSig hTy
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', fa, hF, h1, h2⟩ := h.2 r hr hpa
  have hF' : FootW g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact FootW_ext hF'
  exact ⟨E', hF', hx, h1, h2, fa⟩

end TermStep

#print axioms TermStep.FreshArr_vac
#print axioms TermStep.ThInvMFA.weakA
#print axioms TermStep.ThInvMFWA.toW
#print axioms TermStep.tstepMF_stepWFA
#print axioms TermStep.tstep_footprintWFA
