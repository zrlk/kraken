import WeakCore.TermStep
import WeakCore.TermNoHold

/-!
# TermBiiS (BII): one typed-run thread step at a `bufInit`, with the count it leaves

* `tstep_footprintB`: `tstep_footprint` at a `bufInit`, exposing `BufInitBump` (from
  `TermStep.tstepM_bufInitB`; mirror of `tstep_footprintP`).
* `xfz_threadB`: `xfz_thread` at a `bufInit`, with `BufInitBump` (via `TermNoHold.xfz_of_foot`).
-/

namespace TermBiiS

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermCert TermGlob TermTyped TermNoHold
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **`tstep_footprint` at a `bufInit`**: the footprint's environment counts the written slot. -/
theorem tstep_footprintB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel)
    {x : String} {b i v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b i v) e) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ BufInitBump th b i E' := by
  have h := tstepM_bufInitB (hDy := hDy) hterm hP hT hi hE htv hm hZ hRP hPS
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', hF, h1, h2, hB⟩ := h.2 r hr hpa
  have hF' : Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact Foot_ext hF'
  exact ⟨E', hF', hx, h1, h2, hB⟩

/-- **`xfz_thread` at a `bufInit`**, with the count the step leaves (`BufInitBump`) and `Ext E E'`. -/
theorem xfz_threadB {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {E0 E Eu Ea : TEnv} {n0 v0 na0 : Nat}
    {Z W : AllocLabel → Prop} {H : AllocLabel → Nat → Ts → Prop} {c0 c0' : Cfg} {th : TTh} [ProgRetIall p] [TermTyped.WrIniC]
    (hP : ProgT p) (hsc0 : TermTyped.ScopeAt p i c0) (hvI0 : TermViewInv.ViewInv c0)
    (hth : c0.ths[i]? = some th) (hx : Ext E0 E) (hTE : ThInvE p E th)
    (hm : MemInv (gOf p k arch c0 i) E (stOf c0.mem c0.pairs th)) (hSC : StoClo E)
    (hbo : (gOf p k arch c0 i).boxFence = true) (hfb : FrBound E0 n0 v0 E)
    (hfr : TermTyped.FrRunA E0 n0 v0 E (stOf c0.mem c0.pairs th) Ea Eu) (hna : na0 ≤ th.nalloc)
    (hfresh : FreshRun (gOf p k arch c0 i) E0 na0 E) (hIL : TermTyped.IniLoc Z E0 E)
    (hIH : TermTyped.IniHeld H E0 E th.vs.vWr)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc0' : Certified p k arch c0' i)
    (hPS : PwSkel)
    (hZW : ∀ l, BufInitOn th l → Z l ∨ W l → False)
    (hHr : ∀ l o τ, (c0.mem.size ≤ τ ∨ (τ ∈ th.promises ∧ ∃ m, c0.mem[τ]? = some m ∧ m.loc = ⟨l, o⟩)) →
      H l o τ)
    {x : String} {b ib v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b ib v) e) :
    ∃ th' E' s s', c0'.ths[i]? = some th' ∧
      Foot { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
        pf := fun l => TermOwnG0Defs.PubAt th l } E E' s s' ∧
      (∀ l, TermOwnG0Defs.PubAt th l → E'.pfr l ≠ none) ∧
      (∀ l, TermOwnG0Defs.PubAt th l → th'.vs.vWr = th.vs.vWr) ∧
      Ext E0 E' ∧ ThInvE p E' th' ∧ MemInv (gOf p k arch c0' i) E' (stOf c0'.mem c0'.pairs th') ∧
      StoClo E' ∧ (gOf p k arch c0' i).boxFence = true ∧ FrBound E0 n0 v0 E' ∧
      TermTyped.FrRunA E0 n0 v0 E' (stOf c0'.mem c0'.pairs th') Ea Eu ∧ na0 ≤ th'.nalloc ∧
      FreshRun (gOf p k arch c0' i) E0 na0 E' ∧ TermTyped.IniLoc Z E0 E' ∧
      TermTyped.IniHeld H E0 E' th'.vs.vWr ∧ BufInitBump th b ib E' ∧ Ext E E' := by
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, hrp, hDy⟩ := hTE
  have hscope := hsc0 th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT htv hi
  have hpub : ∀ l, ¬ TermOwnG0Defs.PubAt th l := fun l ⟨y, a, e', _, _, _, h, _⟩ => by
    rw [hterm] at h; cases h
  have hF := tstep_footprintB (hDy := hDy) (g := { ({ gOf p k arch c0 i with zf := fun l => Z l ∨ W l } : G) with
      pf := fun l => TermOwnG0Defs.PubAt th l }) hP hT hi hE htv hm (ZOK_of_not hZW) hrp hPS hterm
  exact xfz_of_foot (Q := fun _ E' => BufInitBump th b ib E' ∧ Ext (CE η) E') hth hx hSC hbo hfb hfr hna hfresh hIL hIH hs hc0' hHr
    (fun r hr hpa => by
      obtain ⟨E', h1, h2, h3, h4, h5⟩ := hF.2 r hr hpa
      exact ⟨E', h1, h2, h3, h4, fun l hl => absurd hl (hpub l),
        TermTyped.anchR_tstep h1 h4 (TermTyped.bumpIf_of hterm h5) hE hT htv hi hm hscope
          (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI0 (.refl _) hth) hr
          (TermTyped.frRunA_ext hfr hx) hfr.2.1, h5, h2⟩)

end TermBiiS

#print axioms TermBiiS.tstep_footprintB
#print axioms TermBiiS.xfz_threadB
