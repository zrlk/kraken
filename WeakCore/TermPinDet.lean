import WeakCore.TermA4R
import WeakCore.TermCkDefs
import WeakCore.TermA4P2
import WeakCore.TermPinAtoms

/-! # TermPinDet (PIN, route D): resources are a function of the words at a `wrapTop` type

Under the interim scope A1 (`ProgScopeOKW`) every cell type is `wrapTop` (`SysInvN.stoW`): the
wrappers `VRR` does not pin (`sum`'s arm, `iex`'s witness, `tex`'s package) wrap only key-free
bodies.
* `vrr_kf`: at a key-free type (`rcarE env t = false`) the resources do not depend on the index
  valuation or the package witnesses (only `ownW` of references is left, a function of the words).
* `vrr_detW`: at a `wrapTop` type, `VRR` is functional (the same words carry the same resources).
-/

namespace TermPinDet
open CoreLang CoreTerm TermRun TermClose TermSound TermScope TermA4 TermStep

/-- `push0` keeps the boxed-sum blocks. -/
theorem box_push0 (η : TEnv) (s : Ty) : (η.push0 s).box = η.box := rfl

/-- `unsee` keeps the boxed-sum blocks. -/
theorem box_unsee (η : TEnv) : η.unsee.box = η.box := rfl

/-- A boxed tier decodes no arm. -/
theorem decodeArm_boxed (as : List Ty) (ws : List Word) : decodeArm .boxed as ws = none := by
  cases ws <;> rfl

/-- **Key-free values: the resources do not depend on the valuation or the witnesses.** -/
theorem vrr_kf : ∀ (t : Ty) (env : List Bool) (ρ ρ' : Nat → Nat) (η η' : TEnv) (rt : Shp)
    (ws : List Word) (R R' : Res), rcarE env t = false → RZ η → RZ η' →
    (∀ l B, η.box l = some B → η'.box l = some B) →
    VRR ρ η t rt ws R → VRR ρ' η' t rt ws R' → R = R'
  | .tvar k, _, _, _, _, _, _, _, _, _, _, hz, hz', _, hv, hv' => by
      simp only [VRR] at hv hv'
      obtain ⟨_, -, h⟩ := hv
      obtain ⟨_, -, h'⟩ := hv'
      rw [hz.1 k _ _ _ h, hz'.1 k _ _ _ h']
  | .refine t _, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE] at hr; simp only [VRR] at hv hv'
      exact vrr_kf t env ρ ρ' η η' rt ws R R' hr hz hz' hb hv.1 hv'.1
  | .iex b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE] at hr; simp only [VRR] at hv hv'
      obtain ⟨n, rb, w, e, hv⟩ := hv
      obtain ⟨n', rb', w', e', hv'⟩ := hv'
      rw [e] at e'; cases e'
      exact vrr_kf b env _ _ η η' rb ws R R' hr hz hz' hb hv hv'
  | .iall b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE] at hr; simp only [VRR] at hv hv'
      exact vrr_kf b env _ _ η η' rt ws R R' hr hz hz' hb (hv 0) (hv' 0)
  | .prod a b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE, Bool.or_eq_false_iff] at hr
      simp only [VRR] at hv hv'
      obtain ⟨ra, rb, e, Ra, Rb, hR, hnone, hf⟩ := hv
      obtain ⟨ra', rb', e', Ra', Rb', hR', hnone', hf'⟩ := hv'
      rw [e] at e'; cases e'
      cases hw : ra.wc with
      | none => rw [hnone hw, hnone' hw]
      | some n =>
          obtain ⟨-, h1, h2⟩ := hf n hw
          obtain ⟨-, h1', h2'⟩ := hf' n hw
          rw [hR, hR', vrr_kf a env ρ ρ' η η' ra _ Ra Ra' hr.1 hz hz' hb h1 h1',
            vrr_kf b env ρ ρ' η η' rb _ Rb Rb' hr.2 hz hz' hb h2 h2']
  | .sum a b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE, Bool.or_eq_false_iff] at hr
      simp only [VRR] at hv hv'
      obtain ⟨n, Ra, Rb, e, hv⟩ := hv
      obtain ⟨n', Ra', Rb', e', hv'⟩ := hv'
      rw [e] at e'; cases e'
      rcases hv with ⟨ht, x, s, B, hx, -, hB, hn, -, -, hA, hA'⟩ | ⟨j, p, hd, h1, h2⟩ <;>
        rcases hv' with ⟨ht', x', s', B', hx', -, hB', hn', -, -, hA2, hA2'⟩ | ⟨j', p', hd', h1', h2'⟩
      · rw [hx] at hx'
        simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hx'
        subst hx'
        rw [hn] at hn'
        simp only [Option.some.injEq, Nat.add_right_cancel_iff] at hn'
        subst hn'
        rw [hb _ _ hB] at hB'; cases hB'
        by_cases hj : B.tag - s < (armsOf Ra).length
        · cases hbx : isBoxed Ra with
          | true => exact vrr_kf a env ρ ρ' η η' _ ws R R' hr.1 hz hz' hb ((hA hj).1 hbx) ((hA2 hj).1 hbx)
          | false =>
              obtain ⟨q, hq, -, -, -, hvq⟩ := (hA hj).2 hbx
              obtain ⟨q', hq', -, -, -, hvq'⟩ := (hA2 hj).2 hbx
              rw [hq] at hq'; cases hq'
              exact vrr_kf a env ρ ρ' η.unsee η'.unsee _ q R R' hr.1 (RZ_unsee hz) (RZ_unsee hz') hb hvq hvq'
        · have hj' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hj
          cases hbx : isBoxed Rb with
          | true => exact vrr_kf b env ρ ρ' η η' _ ws R R' hr.2 hz hz' hb ((hA' hj').1 hbx) ((hA2' hj').1 hbx)
          | false =>
              obtain ⟨q, hq, -, -, -, hvq⟩ := (hA' hj').2 hbx
              obtain ⟨q', hq', -, -, -, hvq'⟩ := (hA2' hj').2 hbx
              rw [hq] at hq'; cases hq'
              exact vrr_kf b env ρ ρ' η.unsee η'.unsee _ q R R' hr.2 (RZ_unsee hz) (RZ_unsee hz') hb hvq hvq'
      · rw [ht, decodeArm_boxed] at hd'; cases hd'
      · rw [ht', decodeArm_boxed] at hd; cases hd
      · rw [hd] at hd'
        simp only [Option.some.injEq, Prod.mk.injEq] at hd'
        obtain ⟨rfl, rfl⟩ := hd'
        by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, hq, hvq⟩ := h1 hj
          obtain ⟨q', hq', hvq'⟩ := h1' hj
          rw [hq] at hq'; cases hq'
          exact vrr_kf a env ρ ρ' η η' _ q R R' hr.1 hz hz' hb hvq hvq'
        · obtain ⟨q, hq, hvq⟩ := h2 (Nat.le_of_not_lt hj)
          obtain ⟨q', hq', hvq'⟩ := h2' (Nat.le_of_not_lt hj)
          rw [hq] at hq'; cases hq'
          exact vrr_kf b env ρ ρ' η η' _ q R R' hr.2 hz hz' hb hvq hvq'
  | .tex κ b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE] at hr; simp only [VRR] at hv hv'
      obtain ⟨n, rb, s, e, -, -, hv⟩ := hv
      obtain ⟨n', rb', s', e', -, -, hv'⟩ := hv'
      rw [e] at e'; cases e'
      exact vrr_kf b (false :: env) ρ ρ' _ _ rb ws R R' hr (RZ_push0 hz s) (RZ_push0 hz' s') hb hv hv'
  | .mu b, env, ρ, ρ', η, η', rt, ws, R, R', hr, hz, hz', hb, hv, hv' => by
      simp only [rcarE] at hr; simp only [VRR] at hv hv'
      exact vrr_kf b _ ρ ρ' _ _ rt ws R R' hr (RZ_push0 hz _) (RZ_push0 hz' _) hb hv hv'
  | .ptr μ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .ptrOpt μ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .loc μ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv, hv']
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, _ => by simp [VRR] at hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .tid, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .code _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv, hv']
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv, hv']
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .word _ _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
  | .word2 _ _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
  | .tok _ _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
  | .share _, _, _, _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [rcarE] at hr
#print axioms vrr_kf

/-- **(route D) `VRR` is functional at a `wrapTop` type**: the same words carry the same resources. -/
theorem vrr_detW : ∀ (t : Ty) (env : List Bool) (ρ : Nat → Nat) (η η' : TEnv) (rt : Shp)
    (ws : List Word) (R R' : Res), wrapTopE env t = true → RZ η → RZ η' →
    (∀ l B, η.box l = some B → η'.box l = some B) →
    VRR ρ η t rt ws R → VRR ρ η' t rt ws R' → R = R'
  | .prod a b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE, Bool.and_eq_true] at hw
      simp only [VRR] at hv hv'
      obtain ⟨ra, rb, e, Ra, Rb, hR, hnone, hf⟩ := hv
      obtain ⟨ra', rb', e', Ra', Rb', hR', hnone', hf'⟩ := hv'
      rw [e] at e'; cases e'
      cases hwc : ra.wc with
      | none => rw [hnone hwc, hnone' hwc]
      | some n =>
          obtain ⟨-, h1, h2⟩ := hf n hwc
          obtain ⟨-, h1', h2'⟩ := hf' n hwc
          rw [hR, hR', vrr_detW a env ρ η η' ra _ Ra Ra' hw.1 hz hz' hb h1 h1',
            vrr_detW b env ρ η η' rb _ Rb Rb' hw.2 hz hz' hb h2 h2']
  | .sum a b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      exact vrr_kf (.sum a b) env ρ ρ η η' rt ws R R'
        (by simp only [rcarE, hw.1.1.1, hw.1.1.2, Bool.or_self]) hz hz' hb hv hv'
  | .iex b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      exact vrr_kf (.iex b) env ρ ρ η η' rt ws R R' (by simpa only [rcarE] using hw.1) hz hz' hb hv hv'
  | .refine t ψ, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      exact vrr_kf (.refine t ψ) env ρ ρ η η' rt ws R R' (by simpa only [rcarE] using hw.1) hz hz' hb hv hv'
  | .tex κ b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      exact vrr_kf (.tex κ b) env ρ ρ η η' rt ws R R' (by simpa only [rcarE] using hw.1) hz hz' hb hv hv'
  | .mu b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE] at hw; simp only [VRR] at hv hv'
      exact vrr_detW b _ ρ _ _ rt ws R R' hw (RZ_push0 hz _) (RZ_push0 hz' _) hb hv hv'
  | .iall b, env, ρ, η, η', rt, ws, R, R', hw, hz, hz', hb, hv, hv' => by
      simp only [wrapTopE] at hw; simp only [VRR] at hv hv'
      exact vrr_detW b env _ η η' rt ws R R' hw hz hz' hb (hv 0) (hv' 0)
  | .tvar k, _, _, _, _, _, _, _, _, _, hz, hz', _, hv, hv' => by
      simp only [VRR] at hv hv'
      obtain ⟨_, -, h⟩ := hv
      obtain ⟨_, -, h'⟩ := hv'
      rw [hz.1 k _ _ _ h, hz'.1 k _ _ _ h']
  | .word r P, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'
      rcases hv.2 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases hv'.2 with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · rw [e1, e2]
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rw [e1, e2]
  | .word2 r P, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by
      simp only [VRR] at hv hv'
      rcases hv.2 with ⟨h1, e1⟩ | ⟨h1, e1⟩ <;> rcases hv'.2 with ⟨h2, e2⟩ | ⟨h2, e2⟩
      · rw [e1, e2]
      · exact absurd h1 h2
      · exact absurd h2 h1
      · rw [e1, e2]
  | .tok _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .share _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .ptr μ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .ptrOpt μ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .loc μ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .unit, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .void, _, _, _, _, _, _, _, _, _, _, _, _, hv, _ => by simp [VRR] at hv
  | .int, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .tid, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .intS _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .fix _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .lanes _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .code _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
  | .array _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .cap _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv, hv']
  | .epair _ _, _, _, _, _, _, _, _, _, _, _, _, _, hv, hv' => by simp only [VRR] at hv hv'; rw [hv.2, hv'.2]
#print axioms vrr_detW

/-! ## Memory values -/

/-- A code value's own view has no resourceful variables. -/
theorem RZ_CE (η : TEnv) : RZ (CE η) :=
  ⟨fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim⟩

/-- **A memory value's resources are a function of its words** at a `wrapTop` type. -/
theorem valOfR_detW {η : TEnv} {T : Ty} {ws : List Word} {R R' : Res} (hw : wrapTop T = true)
    (h : ValOfR η T ws R) (h' : ValOfR η T ws R') : R = R' :=
  vrr_detW T [] _ _ _ _ ws R R' hw (RZ_CE _) (RZ_CE _) (fun _ _ h => h) h.1 h'.1

/-- **A cell's slot list is a function of its words** at a `wrapTop` type. -/
theorem cellR_detW {η : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {Rs Rs' : List Res}
    (hw : wrapTop T = true) (h : CellR η n nr T vals Rs) (h' : CellR η n nr T vals Rs') : Rs = Rs' := by
  rcases h with ⟨hwc, R, hv, rfl⟩ | ⟨N, e, us, hT, hus, hn, hlen, hl, hs⟩ <;>
    rcases h' with ⟨hwc', R', hv', rfl⟩ | ⟨N', e', us', hT', hus', hn', hlen', hl', hs'⟩
  · rw [valOfR_detW hw hv hv']
  · rw [hT'] at hwc; simp [wc, accs] at hwc
  · rw [hT] at hwc'; simp [wc, accs] at hwc'
  · rw [hT] at hT' hw
    simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
    obtain ⟨rfl, rfl⟩ := hT'
    rw [hus] at hus'; cases hus'
    have hwe : wrapTop e = true := by simpa only [wrapTop, wrapTopE] using hw
    apply List.ext_getElem?; intro j
    by_cases hj : j < n
    · have h1 : j < Rs.length := by omega
      have h2 : j < Rs'.length := by omega
      rw [List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
      congr 1
      obtain ⟨z1, v1⟩ := hs j Rs[j] hj (List.getElem?_eq_getElem h1)
      obtain ⟨z2, v2⟩ := hs' j Rs'[j] hj (List.getElem?_eq_getElem h2)
      by_cases hc : j < nr ∨ 0 < nWords us
      · exact valOfR_detW hwe (v1 hc) (v2 hc)
      · rw [z1 (by omega) (by omega), z2 (by omega) (by omega)]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
#print axioms cellR_detW

/-- **An atom split is a function of the words** at a `wrapTop` type (the format of
`TermPinAtoms.VRR_atoms`). -/
theorem atoms_detW (E : TEnv) {T : Ty} {As : List (Nat × Ty)} (hA : TermPinAtoms.AtomL T As) :
    wrapTop T = true → ∀ {ws : List Word} (Rs Rs' : List Res), Rs.length = As.length → Rs'.length = As.length →
      (∀ (k o : Nat) (U : Ty) (Rk : Res), As[k]? = some (o, U) → Rs[k]? = some Rk →
        ∃ n, wc U = some n ∧ VRR (fun _ => 0) (CE E) U (shp U) ((ws.drop o).take n) Rk) →
      (∀ (k o : Nat) (U : Ty) (Rk : Res), As[k]? = some (o, U) → Rs'[k]? = some Rk →
        ∃ n, wc U = some n ∧ VRR (fun _ => 0) (CE E) U (shp U) ((ws.drop o).take n) Rk) →
      Rs = Rs' := by
  induction hA with
  | @atom t _ =>
      intro hw ws Rs Rs' hl hl' h h'
      match Rs, Rs', hl, hl' with
      | [R], [R'], _, _ =>
        obtain ⟨n, hn, hv⟩ := h 0 0 t R rfl rfl
        obtain ⟨n', hn', hv'⟩ := h' 0 0 t R' rfl rfl
        rw [hn] at hn'; obtain rfl := Option.some.inj hn'
        rw [vrr_detW t [] _ _ _ _ _ R R' hw (RZ_CE _) (RZ_CE _) (fun _ _ h => h) hv hv']
  | @prod a b A B us ha _ _ iha ihb =>
      intro hw ws Rs Rs' hl hl' h h'
      simp only [wrapTop, wrapTopE, Bool.and_eq_true] at hw
      simp only [List.length_append, List.length_map] at hl hl'
      have hA : ∀ (Q : List Res), Q.length = A.length + B.length →
          (∀ (k o : Nat) (U : Ty) (Rk : Res), (A ++ B.map (TermPiece.sh (nWords us)))[k]? = some (o, U) →
            Q[k]? = some Rk → ∃ n, wc U = some n ∧ VRR (fun _ => 0) (CE E) U (shp U) ((ws.drop o).take n) Rk) →
          (∀ (k o : Nat) (U : Ty) (Rk : Res), A[k]? = some (o, U) → (Q.take A.length)[k]? = some Rk →
            ∃ n, wc U = some n ∧ VRR (fun _ => 0) (CE E) U (shp U) ((ws.drop o).take n) Rk) ∧
          (∀ (k o : Nat) (U : Ty) (Rk : Res), B[k]? = some (o, U) → (Q.drop A.length)[k]? = some Rk →
            ∃ n, wc U = some n ∧ VRR (fun _ => 0) (CE E) U (shp U) (((ws.drop (nWords us)).drop o).take n) Rk) := by
        intro Q hQ hq
        refine ⟨fun k o U Rk hk hRk => ?_, fun k o U Rk hk hRk => ?_⟩
        · have hkA : k < A.length := by
            rcases Nat.lt_or_ge k A.length with h1 | h1
            · exact h1
            · rw [List.getElem?_eq_none h1] at hk; cases hk
          have hk' : (A ++ B.map (TermPiece.sh (nWords us)))[k]? = some (o, U) := by
            rw [List.getElem?_append_left hkA]; exact hk
          rw [List.getElem?_take_of_lt hkA] at hRk
          exact hq k o U Rk hk' hRk
        · have hk' : (A ++ B.map (TermPiece.sh (nWords us)))[A.length + k]? = some (nWords us + o, U) := by
            rw [List.getElem?_append_right (by omega), List.getElem?_map, Nat.add_sub_cancel_left, hk]; rfl
          rw [List.getElem?_drop] at hRk
          obtain ⟨n, hn, hv⟩ := hq _ _ U Rk hk' hRk
          refine ⟨n, hn, ?_⟩
          rw [List.drop_drop]; exact hv
      obtain ⟨ha1, hb1⟩ := hA Rs hl h
      obtain ⟨ha2, hb2⟩ := hA Rs' hl' h'
      have e1 := iha hw.1 (ws := ws) (Rs.take A.length) (Rs'.take A.length) (by simp; omega) (by simp; omega) ha1 ha2
      have e2 := ihb hw.2 (ws := ws.drop (nWords us)) (Rs.drop A.length) (Rs'.drop A.length) (by simp; omega)
        (by simp; omega) hb1 hb2
      rw [← List.take_append_drop A.length Rs, ← List.take_append_drop A.length Rs', e1, e2]
  | @mu ρ W s L hW hg _ ih =>
      intro hw
      exact ih (wrapTop_unfold hW hw)
#print axioms atoms_detW

/-! ## Non-word atoms of a planted cell: resources independent of the words -/

/-- No `own` reference (`noOwnIn`) and no region reference (`rgnFree`) give `noOR`. -/
theorem noOR_of_noOwnIn : ∀ (t : Ty) (ke : KEnv), Ty.noOwnIn ke t = true → rgnFree t = true → TermCut.noOR t = true
  | .ptr μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, TermCut.noOR]
  | .ptrOpt μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, TermCut.noOR]
  | .loc μ _, _, h1, h2 => by cases μ <;> simp_all [Ty.noOwnIn, rgnFree, TermCut.noOR]
  | .prod a b, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨noOR_of_noOwnIn a ke h1.1 h2.1, noOR_of_noOwnIn b ke h1.2 h2.2⟩
  | .sum a b, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR, Bool.and_eq_true] at h1 h2 ⊢
      exact ⟨noOR_of_noOwnIn a ke h1.1 h2.1, noOR_of_noOwnIn b ke h1.2 h2.2⟩
  | .array _ t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR] at h1 h2 ⊢; exact noOR_of_noOwnIn t ke h1 h2
  | .mu t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR] at h1 h2 ⊢; exact noOR_of_noOwnIn t _ h1 h2
  | .tex κ t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR, Bool.and_eq_true] at h1 h2 ⊢
      exact noOR_of_noOwnIn t _ h1.2 h2
  | .iall t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR] at h1 h2 ⊢; exact noOR_of_noOwnIn t ke h1 h2
  | .iex t, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR] at h1 h2 ⊢; exact noOR_of_noOwnIn t ke h1 h2
  | .refine t _, ke, h1, h2 => by
      simp only [Ty.noOwnIn, rgnFree, TermCut.noOR] at h1 h2 ⊢; exact noOR_of_noOwnIn t ke h1 h2
  | .unit, _, _, _ | .int, _, _, _ | .tid, _, _, _ | .intS _, _, _, _ | .fix _ _, _, _, _ | .lanes _ _, _, _, _
  | .code _ _, _, _, _ | .void, _, _, _ | .tvar _, _, _, _ | .word _ _, _, _, _ | .word2 _ _, _, _, _
  | .epair _ _, _, _, _ | .cap _ _, _, _, _ | .tok _ _, _, _, _ | .tok2 _ _ _ _, _, _, _
  | .tokE _ _ _, _, _, _ | .share _, _, _, _ => rfl
#print axioms noOR_of_noOwnIn

/-- **(route D) A solid non-word atom carries resources independent of its words**: at a `Solid`,
`wrapTop`, `noOR`, `∀`-free type that is neither a non-ghost word nor a two-word unit (the non-word atoms
of a planted cell's slot), any two values carry the same resources. -/
theorem atomR_const {S : Ty} (hs : Solid S) (hw : wrapTop S = true) (hn : TermCut.noOR S = true)
    (hi : TermTv.noIallV S = true) (hg : ∀ r P, S = .word r P → P.ghost = true) (h2 : ∀ r P, S ≠ .word2 r P)
    {ρ : Nat → Nat} {η : TEnv} (hz : RZ η) {rt : Shp} {ws ws' : List Word} {R R' : Res}
    (hv : VRR ρ η S rt ws R) (hv' : VRR ρ η S rt ws' R') : R = R' := by
  have kf : rcar S = false → R = R' := fun hr => by
    rw [vrr_zero_of_rcar S [] ρ η rt ws R hr hn hz hv, vrr_zero_of_rcar S [] ρ η rt ws' R' hr hn hz hv']
  obtain ⟨hp, ha, hm⟩ := hs
  cases S with
  | prod a b => exact absurd rfl (hp a b)
  | array i e => exact absurd rfl (ha i e)
  | mu t => exact absurd rfl (hm t)
  | iall t => simp [TermTv.noIallV] at hi
  | word2 r P => exact absurd rfl (h2 r P)
  | word r P =>
      have hgh := hg r P rfl
      simp only [VRR] at hv hv'
      have nh : ∀ vs, ¬ WordHolds P vs := fun vs h => by rw [h.1] at hgh; cases hgh
      rcases hv.2 with ⟨h1, -⟩ | ⟨-, e1⟩
      · exact absurd h1 (nh _)
      rcases hv'.2 with ⟨h1', -⟩ | ⟨-, e2⟩
      · exact absurd h1' (nh _)
      rw [e1, e2]
  | tok _ _ => simp only [VRR] at hv hv'; rw [hv, hv']
  | tok2 _ _ _ _ => simp only [VRR] at hv hv'; rw [hv, hv']
  | tokE _ _ _ => simp only [VRR] at hv hv'; rw [hv, hv']
  | share _ => simp only [VRR] at hv hv'; rw [hv, hv']
  | sum a b =>
      apply kf
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      simp only [rcar, rcarE, hw.1.1.1, hw.1.1.2, Bool.or_self]
  | iex t =>
      apply kf
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      simpa only [rcar, rcarE] using hw.1
  | refine t ψ =>
      apply kf
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      simpa only [rcar, rcarE] using hw.1
  | tex κ t =>
      apply kf
      simp only [wrapTop, wrapTopE, Bool.and_eq_true, Bool.not_eq_true'] at hw
      simpa only [rcar, rcarE] using hw.1
  | _ => exact kf rfl
#print axioms atomR_const

end TermPinDet
