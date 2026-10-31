import WeakCore.KLayer
/-! The shadow publish on ♭ (`MemInvB`, `VRb2` at flag `False`).  The shadow env changes
only the frontier (`pubP`, W's own); the cell stays unseen.  Ports `MemInv_publishS` and
`publish_{ptr,buf}_remode` (an earlier draft, over W's MemInv/VR) to the ♭ families. -/
namespace FlatShadowPub
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The shadow env: the frontier `publish` would set, nothing else. -/
def shadowEnv (η : TEnv) (l : AllocLabel) (V : Ts) : TEnv := { η with pfr := pubP η l V }

/-- (B3a) Shadow publish keeps `MemInvB` with NO `PubWin`/`NoHold`. -/
theorem MemInv_publishSB {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell}
    (hm : MemInvB g E s) (hsto : E.sto l = some c) (hown : c.owner = some E.tid)
    (hcpl : ∀ b S, SegOf c.ty b S → accs S ≠ none → TearOKB S) (hcT : Ty.coupledOKIn [] c.ty = true)
    (hnT : Ty.noOwnIn [] c.ty = true) (hrT : rgnFree c.ty = true) :
    MemInvB g (shadowEnv E l s.vs.vWr) (fenceS s .st) := by
  cases hpf : E.pfr l with
  | none =>
    refine MemInv_fenceB (MemInv_plantFB (F := s.vs.vWr) hm hsto hown hpf rfl rfl rfl rfl ?_ rfl rfl
      (Or.inl (Nat.le_refl _)) hcpl hcT hnT hrT)
    funext l'
    simp only [shadowEnv, pubP]
    split
    · rename_i he; subst he; simp [hpf]
    · rfl
  | some f =>
    have e : shadowEnv E l s.vs.vWr = E := by
      have e1 : pubP E l s.vs.vWr = E.pfr := by
        funext l'
        simp only [pubP]
        split
        · rename_i he; subst he; simp [hpf]
        · rfl
      simp only [shadowEnv, e1]
    rw [e]
    exact MemInv_fenceB hm

/-- (ShadowPubStep) The `.ptr` publish result (the cell is non-buffer: `accs c.ty ≠ none`). -/
theorem publish_ptr_remodeB {ρ : Nat → Nat} {η : TEnv} {u : Ty} {rt : Shp} {pw : Word} {l : AllocLabel} {V : Ts}
    (h : (VRF False) ρ η (.ptr .own u) rt [pw]) (hl : pw.val = .loc ⟨l, 0⟩ 0) :
    (VRF False) ρ (shadowEnv η l V) (.ptr .pub u) rt [pw] := by
  simp only [VRF, VRb2] at h
  obtain ⟨a, c, hw, ho, hsto, hFd, hmode, hacc⟩ := h
  have ha : a = ⟨l, 0⟩ := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hw
    rw [hl] at hw; cases hw; rfl
  subst ha
  simp only [VRF, VRb2]
  refine ⟨⟨l, 0⟩, c, hw, ho, hsto, hFd, ⟨(η.pfr l).getD V, by simp [shadowEnv, pubP], ?_⟩, hacc⟩
  exact Or.inr (Or.inr ⟨hmode, Or.inr (fun N e h => hacc (by rw [h]; rfl))⟩)

theorem selIni_ownB (η : TEnv) (A : Ty) : η.selIni (.loc .own A) = η.rc := by
  funext l'; simp [TEnv.selIni, TEnv.ownTop, Ty.ownHead, TEnv.rc]

/-- (B3c) The `publishBuf` result. -/
theorem publish_buf_remodeB {ρ : Nat → Nat} {η : TEnv} {n : Idx} {u : Ty} {k : Idx} {rt : Shp} {pw : Word}
    {l : AllocLabel} {V : Ts}
    (h : (VRF False) ρ η (.refine (.loc .own (.array n u)) (.ini k)) rt [pw]) (hl : pw.val = .loc ⟨l, 0⟩ 0) :
    (VRF False) ρ (shadowEnv η l V) (.refine (.loc .pub (.array n u)) (.ini k)) rt [pw] := by
  simp only [VRF, VRb2] at h
  obtain ⟨hv, hir, -⟩ := h
  rw [selIni_ownB] at hir
  have hrc : (shadowEnv η l V).rc = η.rc := rfl
  simp only [VRF, VRb2]
  refine ⟨?_, ?_, fun _ => Or.inr (by rw [hrc]; exact hir)⟩
  · rcases hv with ⟨h0, h1⟩ | ⟨a, c, U, hw, hsto, hat, hFd, hmode, hini⟩
    · exact Or.inl ⟨h0, h1⟩
    · have ha : a = ⟨l, 0⟩ := by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hw
        rw [hl] at hw; cases hw; rfl
      subst ha
      have hrc0 : IniAt η.rc c ⟨l, 0⟩ U := hini
      refine Or.inr ⟨⟨l, 0⟩, c, U, hw, hsto, hat, hFd, ⟨(η.pfr l).getD V, by simp [shadowEnv, pubP], ?_⟩, ?_⟩
      · exact Or.inr (Or.inr ⟨hmode, Or.inr hrc0⟩)
      · exact IniAt_monoAt (TEnv.rc_le_ini η l) hrc0
  · have hsel : (shadowEnv η l V).selIni (.loc .pub (.array n u)) = η.ini := by
      funext l'; simp [TEnv.selIni, TEnv.ownTop, Ty.ownHead, shadowEnv]
    rw [hsel]
    simp only [IniR] at hir ⊢
    exact fun a ha => Nat.le_trans (hir a ha) (TEnv.rc_le_ini η a.label)

theorem envShrink_pubS (η : TEnv) (lab : AllocLabel) (V : Ts) :
    TermOwnK4.EnvShrink (CE η) (CE (η.withStoB η.sto η.ini (pubP η lab V))) := by
  refine ⟨rfl, rfl, ⟨rfl, fun _ _ h => h, fun _ => Nat.le_refl _, fun l f h => pubP_mono η lab V l f h,
    fun _ _ h => h, fun _ => Nat.le_refl _⟩, rfl, rfl, rfl, fun l h => ?_⟩
  show η.pfr l = none
  have h' : pubP η lab V l = none := h
  simp only [pubP] at h'
  split at h'
  · cases h'
  · exact h'

end FlatShadowPub
