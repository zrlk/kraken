import WeakCore.TermScopeW
import WeakCore.TermMem

/-! # TermA4R: key-free values carry nothing (D3)

At a type with no `VRR`-keyed leaf outside references (`rcarE env t = false`) and no own or
region reference outside references (`TermCut.noOR`), a value carries no resource:
`vrr_zero_of_rcar` (every resourceful reading is zero), and `VR_VRR_rc` (every plain value has a
resource-free reading; the analogue of `VR_VRR_copy` with `rcar` in place of non-affinity).
-/

namespace TermA4
open CoreLang CoreTerm TermRun TermClose TermSound TermScope

/-- No variable of `η` carries a resource. -/
def RZ (η : TEnv) : Prop :=
  (∀ k S ws R, η.rrs k S ws R → R = .zero) ∧ (∀ k S ws R, η.urrs k S ws R → R = .zero)

theorem RZ_push0 {η : TEnv} (h : RZ η) (s : Ty) : RZ (η.push0 s) := by
  constructor
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk; exact h.1 k S ws R hk
  · intro k S ws R hk
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk; exact h.2 k S ws R hk

theorem RZ_unsee {η : TEnv} (h : RZ η) : RZ η.unsee := ⟨h.2, h.2⟩

/-- **(D3) Key-free values carry nothing.** -/
theorem vrr_zero_of_rcar : ∀ (t : Ty) (env : List Bool) (ρ : Nat → Nat) (η : TEnv) (rt : Shp)
    (ws : List Word) (R : Res), rcarE env t = false → TermCut.noOR t = true → RZ η →
    VRR ρ η t rt ws R → R = .zero
  | .tvar k, _, _, _, _, _, _, _, _, hz, hv => by
      simp only [VRR] at hv
      obtain ⟨w0, -, h⟩ := hv
      exact hz.1 k _ _ _ h
  | .refine t _, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE] at hr; simp only [TermCut.noOR] at hn; simp only [VRR] at hv
      exact vrr_zero_of_rcar t env ρ η rt ws R hr hn hz hv.1
  | .iex b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE] at hr; simp only [TermCut.noOR] at hn; simp only [VRR] at hv
      obtain ⟨n, rb, w, -, hv⟩ := hv
      exact vrr_zero_of_rcar b env _ η rb ws R hr hn hz hv
  | .iall b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE] at hr; simp only [TermCut.noOR] at hn; simp only [VRR] at hv
      exact vrr_zero_of_rcar b env _ η rt ws R hr hn hz (hv 0)
  | .prod a b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE, Bool.or_eq_false_iff] at hr
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      simp only [VRR] at hv
      obtain ⟨ra, rb, -, Ra, Rb, e, hnone, hf⟩ := hv
      cases hw : ra.wc with
      | none => exact hnone hw
      | some n =>
          obtain ⟨-, h1, h2⟩ := hf n hw
          rw [e, vrr_zero_of_rcar a env ρ η ra _ Ra hr.1 hn.1 hz h1,
            vrr_zero_of_rcar b env ρ η rb _ Rb hr.2 hn.2 hz h2, Res.add_zero]
  | .sum a b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE, Bool.or_eq_false_iff] at hr
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      simp only [VRR] at hv
      obtain ⟨n, Ra, Rb, -, ⟨-, x, s, B, -, -, -, -, -, -, hA, hA'⟩ | ⟨j, p, -, h1, h2⟩⟩ := hv
      · by_cases hj : B.tag - s < (armsOf Ra).length
        · cases hb : isBoxed Ra with
          | true => exact vrr_zero_of_rcar a env ρ η _ ws R hr.1 hn.1 hz ((hA hj).1 hb)
          | false =>
              obtain ⟨q, -, -, -, -, hq⟩ := (hA hj).2 hb
              exact vrr_zero_of_rcar a env ρ η.unsee _ q R hr.1 hn.1 (RZ_unsee hz) hq
        · have hj' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hj
          cases hb : isBoxed Rb with
          | true => exact vrr_zero_of_rcar b env ρ η _ ws R hr.2 hn.2 hz ((hA' hj').1 hb)
          | false =>
              obtain ⟨q, -, -, -, -, hq⟩ := (hA' hj').2 hb
              exact vrr_zero_of_rcar b env ρ η.unsee _ q R hr.2 hn.2 (RZ_unsee hz) hq
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, hq⟩ := h1 hj; exact vrr_zero_of_rcar a env ρ η _ q R hr.1 hn.1 hz hq
        · obtain ⟨q, -, hq⟩ := h2 (Nat.le_of_not_lt hj)
          exact vrr_zero_of_rcar b env ρ η _ q R hr.2 hn.2 hz hq
  | .tex κ b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE] at hr; simp only [TermCut.noOR] at hn; simp only [VRR] at hv
      obtain ⟨n, rb, s, -, -, -, hv⟩ := hv
      exact vrr_zero_of_rcar b (false :: env) ρ _ rb ws R hr hn (RZ_push0 hz s) hv
  | .mu b, env, ρ, η, rt, ws, R, hr, hn, hz, hv => by
      simp only [rcarE] at hr; simp only [TermCut.noOR] at hn; simp only [VRR] at hv
      exact vrr_zero_of_rcar b _ ρ _ rt ws R hr hn (RZ_push0 hz _) hv
  | .ptr μ _, _, _, _, _, _, _, _, hn, _, hv => by
      simp only [VRR] at hv; rw [hv.2, TermCut.noOR_ptr hn]; rfl
  | .ptrOpt μ _, _, _, _, _, _, _, _, hn, _, hv => by
      simp only [VRR] at hv; rw [hv.2, TermCut.noOR_ptrOpt hn]; rfl
  | .loc μ _, _, _, _, _, _, _, _, hn, _, hv => by
      simp only [VRR] at hv; rw [hv.2, TermCut.noOR_loc hn]; rfl
  | .unit, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .void, _, _, _, _, _, _, _, _, _, hv => by simp [VRR] at hv
  | .int, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .tid, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .intS _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .fix _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .lanes _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .code _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .array _ _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .cap _ _, _, _, _, _, _, _, _, _, _, hv => by simpa only [VRR] using hv
  | .epair _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; exact hv.2
  | .word _ _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr
  | .word2 _ _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr
  | .tok _ _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr
  | .tok2 _ _ _ _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr
  | .tokE _ _ _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr
  | .share _, _, _, _, _, _, _, hr, _, _, _ => by simp [rcarE] at hr

/-- **(D3, existence) Key-free values exist resource-free**: the analogue of `VR_VRR_copy`, with
`rcarE env t = false` and `noOR t` in place of non-affinity; variables bound below `env.length`
have plain values only as resource-free values. -/
theorem VR_VRR_rc : ∀ (t : Ty) (env : List Bool) (ρ : Nat → Nat) (η : TEnv) (rt : Shp) (ws : List Word),
    rcarE env t = false → TermCut.noOR t = true → tb env.length t = true →
    (∀ k, k < env.length → ∀ S vs, η.rels k S vs → η.rrs k S vs .zero) →
    (∀ k, k < env.length → ∀ S vs, η.urels k S vs → η.urrs k S vs .zero) →
    VR ρ η t rt ws → VRR ρ η t rt ws .zero
  | .tvar k, _, _, _, rt, _, _, _, htb, hr, _, hv => by
      simp only [tb, decide_eq_true_eq] at htb
      simp only [VR, TEnv.get] at hv; simp only [VRR]
      obtain ⟨w0, h0, h⟩ := hv
      exact ⟨w0, h0, hr k htb rt w0 h⟩
  | .refine t _, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE] at hc; simp only [TermCut.noOR] at hn; simp only [tb] at htb
      simp only [VR] at hv; simp only [VRR]
      exact ⟨VR_VRR_rc t env ρ η rt ws hc hn htb hr hu hv.1, hv.2⟩
  | .iex b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE] at hc; simp only [TermCut.noOR] at hn; simp only [tb] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, rb, w, e, hv⟩ := hv
      exact ⟨n, rb, w, e, VR_VRR_rc b env _ η rb ws hc hn htb hr hu hv⟩
  | .iall b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE] at hc; simp only [TermCut.noOR] at hn; simp only [tb] at htb
      simp only [VR] at hv; simp only [VRR]
      exact fun n => VR_VRR_rc b env _ η rt ws hc hn htb hr hu (hv n)
  | .prod a b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE, Bool.or_eq_false_iff] at hc
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      simp only [tb, Bool.and_eq_true] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨ra, rb, e, hf⟩ := hv
      refine ⟨ra, rb, e, .zero, .zero, (Res.zero_add _).symm, fun _ => trivial, fun n hn' => ?_⟩
      obtain ⟨h0, h1, h2⟩ := hf n hn'
      exact ⟨h0, VR_VRR_rc a env ρ η ra _ hc.1 hn.1 htb.1 hr hu h1,
        VR_VRR_rc b env ρ η rb _ hc.2 hn.2 htb.2 hr hu h2⟩
  | .sum a b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE, Bool.or_eq_false_iff] at hc
      simp only [TermCut.noOR, Bool.and_eq_true] at hn
      simp only [tb, Bool.and_eq_true] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, Ra, Rb, e, ⟨hb, x, s, B, hx, ho, hB, hn', hsB, hm, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩⟩ := hv
      · refine ⟨n, Ra, Rb, e, Or.inl ⟨hb, x, s, B, hx, ho, hB, hn', hsB, hm,
          fun hj => ⟨fun eb => VR_VRR_rc a env ρ η _ ws hc.1 hn.1 htb.1 hr hu ((hA hj).1 eb), fun eb => ?_⟩,
          fun hj => ⟨fun eb => VR_VRR_rc b env ρ η _ ws hc.2 hn.2 htb.2 hr hu ((hA' hj).1 eb), fun eb => ?_⟩⟩⟩
        · obtain ⟨q, c1, c2, c3, c4, c5⟩ := (hA hj).2 eb
          exact ⟨q, c1, c2, c3, c4, VR_VRR_rc a env ρ η.unsee _ q hc.1 hn.1 htb.1 hu hu c5⟩
        · obtain ⟨q, c1, c2, c3, c4, c5⟩ := (hA' hj).2 eb
          exact ⟨q, c1, c2, c3, c4, VR_VRR_rc b env ρ η.unsee _ q hc.2 hn.2 htb.2 hu hu c5⟩
      · refine ⟨n, Ra, Rb, e, Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩⟩
        · obtain ⟨q, hq, hv⟩ := h1 hj; exact ⟨q, hq, VR_VRR_rc a env ρ η _ q hc.1 hn.1 htb.1 hr hu hv⟩
        · obtain ⟨q, hq, hv⟩ := h2 hj; exact ⟨q, hq, VR_VRR_rc b env ρ η _ q hc.2 hn.2 htb.2 hr hu hv⟩
  | .tex κ b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE] at hc; simp only [TermCut.noOR] at hn; simp only [tb] at htb
      simp only [VR] at hv; simp only [VRR]
      obtain ⟨n, rb, s, e, hcl, hk, hv⟩ := hv
      refine ⟨n, rb, s, e, hcl, hk, VR_VRR_rc b (false :: env) ρ (η.push0 s) rb ws hc hn
        (by simpa using htb) (fun k hk1 S vs h => ?_) (fun k hk1 S vs h => ?_) hv⟩
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hr k (by simpa using hk1) S vs h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hu k (by simpa using hk1) S vs h
  | .mu b, env, ρ, η, rt, ws, hc, hn, htb, hr, hu, hv => by
      simp only [rcarE] at hc; simp only [TermCut.noOR] at hn; simp only [tb] at htb
      simp only [VR] at hv; simp only [VRR]
      refine VR_VRR_rc b _ ρ _ rt ws hc hn (by simpa using htb)
        (fun k hk1 S vs h => ?_) (fun k hk1 S vs h => ?_) hv
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hr k (by simpa using hk1) S vs h
      · cases k with
        | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
        | succ k =>
            simp [TEnv.push0, TEnv.ins, TEnv.insR] at h ⊢
            exact hu k (by simpa using hk1) S vs h
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .unit, _, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _ => by simp only [VRR]
  | .void, _, _, _, _, _, _, _, _, _, _, hv => by simp [VR] at hv
  | .intS _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .int, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .tid, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .code _ _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, hv => by simp only [VR] at hv; simp only [VRR, and_true]; exact hv
  | .ptr μ _, _, _, _, _, _, _, hn, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; rw [TermCut.noOR_ptr hn]; rfl
  | .ptrOpt μ _, _, _, _, _, _, _, hn, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; rw [TermCut.noOR_ptrOpt hn]; rfl
  | .loc μ _, _, _, _, _, _, _, hn, _, _, _, hv => by
      simp only [VR] at hv; simp only [VRR]; refine ⟨hv, ?_⟩; rw [TermCut.noOR_loc hn]; rfl
  | .word _ _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc
  | .word2 _ _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc
  | .tok _ _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc
  | .tok2 _ _ _ _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc
  | .tokE _ _ _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc
  | .share _, _, _, _, _, _, hc, _, _, _, _, _ => by simp [rcarE] at hc

/-- (D3) A closed key-free value exists resource-free. -/
theorem VR_VRR_rc_closed {s : Ty} (hs : tb 0 s = true) (hc : rcar s = false) (hn : TermCut.noOR s = true)
    {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word} (hv : VR ρ η s rt ws) : VRR ρ η s rt ws .zero :=
  VR_VRR_rc s [] ρ η rt ws hc hn hs (fun _ hk => absurd hk (Nat.not_lt_zero _))
    (fun _ hk => absurd hk (Nat.not_lt_zero _)) hv

end TermA4

#print axioms TermA4.vrr_zero_of_rcar
#print axioms TermA4.VR_VRR_rc
#print axioms TermA4.VR_VRR_rc_closed
