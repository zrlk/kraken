import WeakCore.TermSpawnEntry
/-!
# TermSpawnArg — a kid's argument is a value of its type at the kid's cut
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermSpawnSim

theorem noOR_of_aff : ∀ (T : Ty) (ke : KEnv), Ty.affineIn ke T = false → rgnFree T = true → noOR T = true
  | .ptr μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.affineIn, rgnFree, noOR]
  | .ptrOpt μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.affineIn, rgnFree, noOR]
  | .loc μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.affineIn, rgnFree, noOR]
  | .prod a b, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR, Bool.and_eq_true, Bool.or_eq_false_iff] at h1 h2 ⊢
      exact ⟨noOR_of_aff a ke h1.1 h2.1, noOR_of_aff b ke h1.2 h2.2⟩
  | .sum a b, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR, Bool.and_eq_true, Bool.or_eq_false_iff] at h1 h2 ⊢
      exact ⟨noOR_of_aff a ke h1.1 h2.1, noOR_of_aff b ke h1.2 h2.2⟩
  | .array _ t, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t ke h1 h2
  | .mu t, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t _ h1 h2
  | .tex κ t, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t _ h1 h2
  | .iall t, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t ke h1 h2
  | .iex t, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t ke h1 h2
  | .refine t _, ke, h1, h2 => by
      simp only [Ty.affineIn, rgnFree, noOR] at h1 h2 ⊢; exact noOR_of_aff t ke h1 h2
  | .intS _, _, _, _ | .int, _, _, _ | .tid, _, _, _ | .fix _ _, _, _, _ | .lanes _ _, _, _, _ | .unit, _, _, _
  | .void, _, _, _ | .share _, _, _, _ | .cap _ _, _, _, _ | .word _ _, _, _, _ | .tok _ _, _, _, _
  | .word2 _ _, _, _, _ | .tok2 _ _ _ _, _, _, _ | .epair _ _, _, _, _ | .tokE _ _ _, _, _, _
  | .tvar _, _, _, _ | .code _ _, _, _, _ => by simp [noOR]

theorem WLe_bumpS (V : Ts) : ∀ ws : List Word, WLe ws (ws.map (bumpW V))
  | [] => WLe_refl []
  | _ :: ws => ⟨⟨rfl, fun _ _ _ => Nat.le_max_left _ _⟩, WLe_bumpS V ws⟩

theorem LocAbove_bumpS (V : Ts) (ws : List Word) : LocAbove V (ws.map (bumpW V)) := by
  intro _ hw _ _ _
  obtain ⟨w', _, rfl⟩ := List.mem_map.1 hw
  exact Nat.le_max_right _ _

theorem Lay_bumpS {σs : List Ty} {t rt : Ty} {ws : List Word} (V : Ts) (h : Lay σs t rt ws) :
    Lay σs t rt (ws.map (bumpW V)) :=
  ⟨ShapeC_vals (WLe_bumpS V ws).vals h.1, h.2.1, h.2.2.1, Valid_vals _ _ _ (WLe_bumpS V ws).vals h.2.2.2.1,
    h.2.2.2.2⟩

/-- The setup result, bumped, at any cut containing the setup's shared part. -/
theorem res_move {Eg Eg2 : GEnv} {S S2 : AllocLabel → Prop} {j : Nat} {V : Ts} {R0 : Ty} {res : List Word}
    (hI : InclS (Cut Eg 0 (fun _ => False)) (Cut Eg2 j S2)) (hS : SeenLE (Cut Eg 0 S) V)
    (hn : noOR R0 = true) (hv : VR (fun _ => 0) (Cut Eg 0 S) R0 (shp R0) res) :
    VR (fun _ => 0) (Cut Eg2 j S2) R0 (shp R0) (res.map (bumpW V)) := by
  have h1 := VR_up _ _ _ _ (WLe_bumpS V res) hv
  have h2 : VR (fun _ => 0) (Cut Eg 0 (fun _ => False)) R0 (shp R0) (res.map (bumpW V)) :=
    VR_unsee V R0 (Cut Eg 0 S) (Cut Eg 0 (fun _ => False)) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
      (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
      (fun _ _ h => h) (LocAbove_bumpS V res) h1 (fun _ => Nat.le_refl _)
  exact VR_transferS R0 (Cut Eg 0 (fun _ => False)) (Cut Eg2 j S2) _ _ _ hn (fun _ _ _ h => h) (fun _ _ _ h => h)
    rfl hI.prog hI.sto hI.ini hI.rini hI.pfr (fun _ h => (h : False).elim) hI.box h2

theorem inclS_Eg0 {p : Prog} {Eg2 : GEnv} {j : Nat} {S2 : AllocLabel → Prop} (hp : Eg2.prog = p) :
    InclS (Cut (TermInit.Eg0 p) 0 TermInit.S0) (Cut Eg2 j S2) :=
  ⟨hp.symm, (fun l c _ hc _ => by rw [TermInit.cut_sto] at hc; cases hc), (fun _ => Nat.zero_le _),
    (fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => Nat.zero_le _)⟩

/-- Constants, bumped, at any cut. -/
theorem const_move {p : Prog} {Eg2 : GEnv} {j : Nat} {S2 : AllocLabel → Prop} {V : Ts} {t : Ty}
    {vals : List WeakMem.Val} (hp : Eg2.prog = p) (hn : noOR t = true) (h : ConstVal p t vals) :
    VR (fun _ => 0) (Cut Eg2 j S2) t (shp t) ((vals.map cst).map (bumpW V)) ∧
      Lay [] t t ((vals.map cst).map (bumpW V)) := by
  have hRL := RLink_of (Coh_CE (Cut (TermInit.Eg0 p) 0 TermInit.S0)) (CohR_CE (Cut (TermInit.Eg0 p) 0 TermInit.S0))
  have hv := VRR_VR t hRL h.1
  have hI := inclS_Eg0 (j := j) (S2 := S2) hp
  have h2 := VR_transferS t (Cut (TermInit.Eg0 p) 0 TermInit.S0) (Cut Eg2 j S2) _ _ _ hn (fun _ _ _ h => h)
    (fun _ _ _ h => h) rfl hI.prog hI.sto hI.ini hI.rini hI.pfr (fun _ h => (h : False).elim) hI.box hv
  exact ⟨VR_up _ _ _ _ (WLe_bumpS V _) h2, Lay_bumpS V h.2⟩

/-- **A kid's argument** is a resource-free laid-out value of its type at any cut containing the setup's
shared part. -/
theorem kid_val {p : Prog} {Eg Eg2 : GEnv} {S S2 : AllocLabel → Prop} {j : Nat} {V : Ts} {R0 : Ty}
    {res : List Word} {kd : Kid} (hp : Eg2.prog = p)
    (hI : InclS (Cut Eg 0 (fun _ => False)) (Cut Eg2 j S2)) (hS : SeenLE (Cut Eg 0 S) V)
    (hres : VR (fun _ => 0) (Cut Eg 0 S) R0 (shp R0) res ∧ Lay [] R0 R0 res) (hok : KidOK p R0 kd) :
    VRR (fun _ => 0) (Cut Eg2 j S2) kd.ty (shp kd.ty)
        (((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW V)) .zero ∧
      Lay [] kd.ty kd.ty (((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW V)) := by
  obtain ⟨ha, htb, hd, -, -, -, -, hc⟩ := hok
  have hn : noOR kd.ty = true := noOR_of_aff _ [] ha (TermScope.rgnFree_of_drf _ hd)
  suffices H : VR (fun _ => 0) (Cut Eg2 j S2) kd.ty (shp kd.ty)
        (((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW V)) ∧
      Lay [] kd.ty kd.ty (((if kd.useRes then res else []) ++ kd.vals.map cst).map (bumpW V)) from
    ⟨VR_VRR_copy_closed htb ha H.1, H.2⟩
  rcases hc with ⟨hu, ⟨hv0, ht⟩ | ⟨τ, ht, hcv⟩⟩ | ⟨hu, hcv⟩
  · rw [hu, hv0, ht]
    simp only [ite_true, List.map_nil, List.append_nil]
    rw [ht] at hn
    exact ⟨res_move hI hS hn hres.1, Lay_bumpS V hres.2⟩
  · rw [hu, ht]
    rw [ht] at hn
    simp only [noOR, Bool.and_eq_true] at hn
    simp only [ite_true, List.map_append]
    have hA := res_move (V := V) hI hS hn.1 hres.1
    have hB := const_move (j := j) (S2 := S2) (V := V) hp hn.2 hcv
    have hLA := Lay_bumpS V hres.2
    refine ⟨VR_prod_mk hA hB.1 rfl ?_, Lay_pair hLA hB.2⟩
    exact wc_of_shape hLA.2.2.1 hLA.1
  · rw [hu]
    simp only [Bool.false_eq_true, ite_false, List.nil_append]
    exact const_move hp hn hcv

end TermSpawn
