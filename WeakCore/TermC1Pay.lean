import WeakCore.TermC1Drf

/-! # TermC1Pay: a region payload stays a region payload under closing

A payload `u` that the checker admits under the kind environment `ke` (`rgnPay ke u`, `drf1 u`)
closes, at witnesses that respect the kinds, to a type that is `coupledOK`, not affine and `drf1`.
The witness premises are `FInv`'s `WitSh`/`WitC` shape (`rgnPay_cl0`), or `Kind.admits` at every
parameter (`rgnPay_cl0_admits`).  Only the witnesses that occur in `u` need `drf1` (`drf1_cl0K`).
Capabilities are not excluded: they license no region-cell access.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound

/-- What `Kind.admits` gives a witness: `coupledOK` under `share`, not affine under `copy`. -/
theorem admits_wit {κ : Kind} {σ : Ty} (h : Kind.admits κ σ = true) :
    (κ.share = true → Ty.coupledOK σ = true) ∧ (κ.copy = true → Ty.affine σ = false) := by
  simp only [Kind.admits, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun hs => ?_, fun hc => ?_⟩
  · have d := h.1.1.1.1.2; simpa [hs] using d
  · have d := h.1.1.2; simpa [hc] using d

/-- **Closing keeps a region payload.** Closing keeps a region payload `coupledOK`, copyable and `drf1`, at closed witnesses
that are `coupledOK` where the kind says `share`, not affine where it says `copy`, and `drf1` where
they occur in the payload. -/
theorem rgnPay_cl0 (ρ : Nat → Nat) {W : Nat → Ty} {ke : KEnv} {u : Ty} (hC : ∀ k, Clo (W k))
    (hS : ∀ k, ke.ask k true (·.share) = true → Ty.coupledOK (W k) = true)
    (hc : ∀ k, ke.ask k true (·.copy) = true → Ty.affine (W k) = false)
    (hD : ∀ k, u.tyMentions k = true → drf1 (W k) = true)
    (hp : rgnPay ke u = true) (hd : drf1 u = true) (ht : tb ke.length u = true) :
    Ty.coupledOK (cl ρ W 0 0 u) = true ∧ Ty.affine (cl ρ W 0 0 u) = false ∧
      drf1 (cl ρ W 0 0 u) = true := by
  simp only [rgnPay, affine, Bool.and_eq_true, Bool.not_eq_true'] at hp
  refine ⟨coupledOK_cl0 ρ W ke hC (fun k _ hk => by simpa [Ty.coupledOK] using hS k hk) hp.1 ht,
    AffineCl.affine_cl0 ρ W ke hC (fun k _ hk => hc k hk) u hp.2 ht, drf1_cl0K ρ hD hd⟩

/-- A property every admitted witness of an `f`-kinded parameter has, and every `μ`-bound
position's witness has, holds wherever `ke.ask k true f` does. -/
theorem wit_of_ask {ke : KEnv} {W : Nat → Ty} {P : Ty → Prop} (f : Kind → Bool)
    (hK : ∀ k κ, ke[k]? = some (some κ) → f κ = true → P (W k))
    (hR : ∀ k, ke[k]? = some none → P (W k)) (k : Nat) (h : ke.ask k true f = true) : P (W k) := by
  unfold KEnv.ask at h
  cases e : ke[k]? with
  | none => rw [e] at h; simp at h
  | some o =>
      cases o with
      | none => exact hR k e
      | some κ => rw [e] at h; exact hK k κ e h

/-- (Static form) The same at witnesses `Kind.admits` admits at every parameter. -/
theorem rgnPay_cl0_admits (ρ : Nat → Nat) {W : Nat → Ty} {ke : KEnv} {u : Ty} (hC : ∀ k, Clo (W k))
    (hK : ∀ k κ, ke[k]? = some (some κ) → Kind.admits κ (W k) = true)
    (hR : ∀ k, ke[k]? = some none → Ty.coupledOK (W k) = true ∧ Ty.affine (W k) = false)
    (hD : ∀ k, u.tyMentions k = true → drf1 (W k) = true)
    (hp : rgnPay ke u = true) (hd : drf1 u = true) (ht : tb ke.length u = true) :
    Ty.coupledOK (cl ρ W 0 0 u) = true ∧ Ty.affine (cl ρ W 0 0 u) = false ∧
      drf1 (cl ρ W 0 0 u) = true :=
  rgnPay_cl0 ρ hC
    (wit_of_ask (W := W) (P := fun σ => Ty.coupledOK σ = true) (·.share) (fun k κ e hs => (admits_wit (hK k κ e)).1 hs) (fun k e => (hR k e).1))
    (wit_of_ask (W := W) (P := fun σ => Ty.affine σ = false) (·.copy) (fun k κ e hc => (admits_wit (hK k κ e)).2 hc) (fun k e => (hR k e).2))
    hD hp hd ht

end TermC1

#print axioms TermC1.admits_wit
#print axioms TermC1.rgnPay_cl0
#print axioms TermC1.wit_of_ask
#print axioms TermC1.rgnPay_cl0_admits
