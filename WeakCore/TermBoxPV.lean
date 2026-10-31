import WeakCore.TermBoxOwn
import WeakCore.TermEnvExt
import WeakCore.TermViewInvH

/-!
# TermBoxPV: box payload views stay below the frontier (box L1, `boxPV`)

Discharges the former `Obligations.boxPVT`.  An old box keeps its payload; a box the step
creates satisfies `TermStep.BoxNewV` (the step's conditional clause, read at the pre-step
environment and state).  The pre-step environment is the post-step one's tail
(`TermEnvExt.tstep_env_ext`: a step that allocates — here, that creates a box at a fresh
label — extends the environment by one binding), and the view facts come from
`TermViewInv.ViewInv` along the run (`TermViewInv.viewInv_run`).
-/

namespace TermBoxPV
open CoreLang CoreTerm TermRun TermSound TermStep TermCut TermSys TermMain
open WeakMem (Memory Address Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`BoxPV` after a thread step** (box L1). `hBV` is the step's `BoxNewV` clause (unfolded),
`hV` the view invariant at the pre-step configuration. -/
theorem boxPV_thread {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hBV : ∀ l B, (CE η).box l = none → E'.box l = some B → ∀ e env0, r.2.2.env = e :: env0 →
      TermViewInv.StV (stOf c.mem c.pairs th) → TermViewInv.EnvV (stOf c.mem c.pairs th).mem.size env0 →
      ∀ w ∈ B.pay, ∀ (a : Address) (g : Nat), w.val = .loc a g → w.view < B.fr)
    (hV : TermViewInv.ViewInv c) (h : TermBoxZ.BoxPV Eg) :
    TermBoxZ.BoxPV (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') := by
  have G := TermInterf.gfoot_of X Y Z
  intro l B hB
  rcases G.2.2.1 l with eb | ⟨hf, hb0, B', hB', -⟩
  · exact h l B (by rw [← eb]; exact hB)
  · have e1 : B' = B := by
      have : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = some B' := hB'
      rw [hB] at this; cases this; rfl
    subst e1
    have hBE : E'.box l = some B' := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post] at hB
      split at hB
      · exact hB
      · contradiction
    have hC0 : (CE η).box l = none := by rw [Y.1]; exact hb0
    have hT := (hV.2 i th X.hth)
    rcases TermEnvExt.tstep_env_ext X.hr with en | ⟨e, he⟩
    · obtain ⟨j, h1, h2, -⟩ := hf
      omega
    · exact hBV l B' hC0 hBE e th.env he ⟨hV.1, hT.2.2⟩ hT.1
end

end TermBoxPV

#print axioms TermBoxPV.boxPV_thread
