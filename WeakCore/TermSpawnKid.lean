import WeakCore.TermSpawnStart
/-!
# TermSpawnKid — the setup result's value at `R0`, and the kids' entry frames

At the setup thread's end (`ret a`, the phantom frame `f0 R0` below), the return clause hands the
result to `f0`, whose `pack` fixes its static type: the result is a value of `R0`.  Bumped to the
setup's release view it is a value of `R0` in every kid's cut.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermSpawnSim

/-- Moving a closed-at-`wf` type's value from a frame view to its thread-wide view. -/
theorem VR_toCE {η : TEnv} (hc : Coh η) {ρ : Nat → Nat} {R0 : Ty} (hR0 : R0.wf 0 0 = true) {S : Shp}
    {ws : List Word} (h : VR ρ η R0 S ws) : VR (fun _ => 0) (CE η) R0 S ws := by
  have a := (VR_close hc ρ R0 [] 0 ρ (fun _ => 0) S ws (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))).1 h
  have b := (VR_close (Coh_CE η) (fun _ => 0) R0 [] 0 (fun _ => 0) (fun _ => 0) S ws (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))).2
  simp only [List.length_nil, TEnv.pre] at a b
  rw [cl_wf (ρ' := fun _ => 0) (W' := (CE η).wit) R0 hR0] at a
  exact b a

/-- **The setup result is a value of `R0`** at the thread-wide view. -/
theorem vr_of_ret {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} {R0 : Ty} {a : At} {rt : Ty}
    {res : List Word} (h : ThInvRE p E (app (f0 R0) th) Tot) (hstk : th.stack = [])
    (hret : th.term = .ret a) (hev : evalAt th.env a = some (rt, res)) (hR0 : R0.wf 0 0 = true) :
    VR (fun _ => 0) E R0 (shp R0) res ∧ Lay [] R0 R0 res := by
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, -, hi, -⟩ := h
  have hterm : (app (f0 R0) th).term = .ret a := hret
  have hT1 := hT.1
  rw [hterm] at hT1
  cases hT1 with
  | ret hu _ hsub =>
      obtain ⟨rt0, ws, R, Rr, hea, -, hl, hvr, hi1, -⟩ := useR hu hi hE.2.2
      have hea' : evalAt th.env a = some (rt0, ws) := hea
      rw [hev] at hea'
      simp only [Option.some.injEq, Prod.mk.injEq] at hea'
      obtain ⟨rfl, rfl⟩ := hea'
      obtain ⟨hs, hl'⟩ := Lay_canon hsub hl
      have hK := hi1.2.1 η (Ext_refl hE.2.1 hE.2.2) res R
        (by rw [← hs]; exact VRR_sub hi1.1.1 hsub _ _ _ hvr) hl'
      have hst : (app (f0 R0) th).stack = [f0 R0] := by simp [app, hstk]
      rw [hst] at hK
      obtain ⟨Rc, Rrest, -, ρ', η', c, hCE', -, hE', hc, -, hf, -⟩ := hK
      simp only [f0] at hc hf
      cases hc.1 with
      | let_ hop _ =>
          cases hop with
          | packT _ _ _ hu' _ hsub' _ =>
              rw [substT_shiftT] at hsub'
              obtain ⟨hF1, rt', ws', hev', hv', hl''⟩ := use_FInv hu' hf.1
              simp [evalAt, lookupE] at hev'
              obtain ⟨rfl, rfl⟩ := hev'
              have hv2 := VR_sub hF1.1 hsub' _ _ hv'
              obtain ⟨hs2, hl2⟩ := Lay_canon hsub' hl''
              have e1 : close [] R0 = R0 := close_tb (tb_of_wf R0 hR0) []
              rw [e1] at hs2 hl2
              rw [hs2] at hv2
              refine ⟨?_, hl2⟩
              have := VR_toCE hE'.2.1 hR0 hv2
              rw [hCE', hCE] at this
              exact this

end TermSpawn
