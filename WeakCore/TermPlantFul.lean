import WeakCore.TermMainDefs
import WeakCore.TermPlantF

/-! # TermPlantFul: `plantFulfil` from a certificate fact (T7)

`plantFulfil` (an own-path op on a frontier cell appends no message) is reduced to two
named per-step facts:

* `OwnKeyT` (typing): the target of an own-path op is one of the stepper's own cells,
  and its own key is in the stepper's frame (the operand's `ownW`);
* `PlantPendT` (stage A, from `certified_pub_vWrLe`): at an own planted cell whose own
  key the stepper still holds (so not yet published: `publish` consumes the handle),
  the stepper keeps, after the step, an outstanding promise whose view is at least its
  new `vWr`.  The certificate must publish the cell before it fulfils the planting
  promise (whose value needs a `pub` pointer to it), and at that publish every
  outstanding promise has view at least `vWr`, which only grows.

Both are stated by the own key, not by the seen set: `EnvAt`'s `S` is not pinned by `TCtx`.

An appending step raises `vWr` to at least the old memory size (`tstep_appUp`), while
every outstanding promise is an old message whose view is below its index
(`promViewLt_run`): no such promise survives.
-/

namespace TermPlantFul
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (typing, per step) The target of an own-path op is an own cell of the stepper, whose
own key is in the stepper's frame. -/
def OwnKeyT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {lab : AllocLabel},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    OwnOpT cx th.term → TermPlant.OpTgt th lab →
    ∃ cl, (CE η).sto lab = some cl ∧ cl.owner = some (CE η).tid ∧ 1 ≤ Rf (.own lab)

/-- (stage A, per step) At an own cell with a frontier whose own key the stepper still
holds, the stepper keeps an outstanding promise with view at least its new `vWr`
(`certified_pub_vWrLe` at the certificate's publish of the cell). -/
def PlantPendT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {lab : AllocLabel} {cl : Cell},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    (CE η).sto lab = some cl → cl.owner = some (CE η).tid → (CE η).pfr lab ≠ none → 1 ≤ Rf (.own lab) →
    ∃ t, t ∈ r.2.2.promises ∧ ∃ m : Msg, r.1[t]? = some m ∧ r.2.2.vs.vWr ≤ m.view

/-- A memory extension no longer than the original is the original. -/
theorem memExt_eq {M M' : Memory} (h : TermCert.MemExt M M') (hs : M'.size ≤ M.size) : M' = M := by
  apply Array.ext_getElem?
  intro t
  cases e : M[t]? with
  | some m => exact h t m e
  | none =>
    have ht : M.size ≤ t := by
      rcases Nat.lt_or_ge t M.size with hlt | hge
      · rw [Array.getElem?_eq_getElem hlt] at e; cases e
      · exact hge
    exact Array.getElem?_eq_none (Nat.le_trans hs ht)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **T7 `plantFulfil`** from `OwnKeyT` and `PlantPendT`. -/
theorem plantFulfil_of (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hS : OwnKeyT p k arch Sp Init MintOK c0)
    (hP : PlantPendT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs) :
    TermPlant.OwnFrOp (CE η) cx th → r.1 = c.mem := by
  rintro ⟨hop, lab, hpf, htg⟩
  obtain ⟨cl, hsto, hown, hns⟩ := hS X Y hop htg
  obtain ⟨t, ht, m, hm, hle⟩ := hP X Y hsto hown hpf hns
  obtain ⟨-, hme, hsub, -, happ⟩ := TermCert.tstep_appUp X.hr
  have ht0 : t ∈ th.promises := hsub t ht
  obtain ⟨m', hm', hv⟩ := TermPlantF.promViewLt_run h0 X.run i th t X.hth ht0
  have hm'' : r.1[t]? = some m' := hme t m' hm'
  rw [hm, Option.some.injEq] at hm''
  have hv' : m.view < t := by rw [hm'']; exact hv
  have htl : t < c.mem.size := TermPlant.lt_size_of_some hm'
  refine memExt_eq hme ?_
  apply Nat.le_of_not_lt
  intro hlt
  have hsz : c.mem.size ≤ r.2.2.vs.vWr := happ hlt
  have hle' : r.2.2.vs.vWr ≤ m.view := hle
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_trans hsz hle') (Nat.lt_trans hv' htl))

end

/-! ## `OwnKeyT` from typing (no new invariant)

The op's address operand has an own reference type (the rule, with `StepScope`
excluding the region-mode `xchg`), so the frame holds it (`HeldOK`): its `VRR`
names an own cell (`ModeOK .own`) and carries its own key (`ownW`). -/

/-- A summand of a key-wise sum is below the sum. -/
theorem sum_ge_mem {R : Res} : ∀ {L : List Res}, R ∈ L → ∀ key, R key ≤ Res.sum L key
  | [], h, _ => by cases h
  | x :: L, h, key => by
    rw [Res.sum_cons, Res.add_apply]
    rcases List.mem_cons.1 h with e | h
    · subst e; exact Nat.le_add_right _ _
    · exact Nat.le_trans (sum_ge_mem h key) (Nat.le_add_left _ _)

/-- An own reference type. -/
def OwnRef (t : Ty) : Prop :=
  (∃ u, t = .ptr .own u) ∨ (∃ u, t = .loc .own u) ∨ ∃ u ψ, t = .refine (.loc .own u) ψ

/-- **A held own reference** names an own cell and carries its key in the frame. -/
theorem ownRef_key {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {env : Env} {Rf : Res} {q : At} {t rt : Ty}
    {w : Word} {ad : Address} {off : Nat}
    (hH : HeldOK ρ η cx env Rf) (hp : cx.peek q = .ok t) (ho : OwnRef t)
    (he : evalAt env q = some (rt, [w])) (hw : w.val = .loc ad off) :
    ∃ cl, η.sto ad.label = some cl ∧ cl.owner = some η.tid ∧ 1 ≤ Rf (.own ad.label) := by
  cases q with
  | lit n =>
    simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at hp; subst hp
    rcases ho with ⟨u, e⟩ | ⟨u, e⟩ | ⟨u, ψ, e⟩ <;> cases e
  | unit =>
    simp only [Cx.peek, pure, Except.pure, Except.ok.injEq] at hp; subst hp
    rcases ho with ⟨u, e⟩ | ⟨u, e⟩ | ⟨u, ψ, e⟩ <;> cases e
  | var y =>
    obtain ⟨-, -, -, Rx, hx, hs⟩ := hH
    have hf := peek_var hp
    obtain ⟨rt', ws, hl, hv⟩ := hx y _ hf (by simp [TermSound.Holds])
    have hl' : lookupE env y = some (rt, [w]) := he
    rw [hl'] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨-, rfl⟩ := hl
    have hmem : Rx y ∈ (cx.vars.filter (Holds cx)).map (fun e => Rx e.1) :=
      List.mem_map.2 ⟨(y, t, true), List.mem_filter.2 ⟨List.mem_of_find?_eq_some hf, by simp [TermSound.Holds]⟩, rfl⟩
    have hle : Rx y (.own ad.label) ≤ Rf (.own ad.label) := Nat.le_trans (sum_ge_mem hmem _) (hs _)
    -- the value's cell and key, from `VRR` at an own reference
    have key : ∀ (a : Address) (c : Cell), [w].map (·.val) = [.loc a 0] → η.sto a.label = some c →
        c.owner = some η.tid → Rx y = ownW .own [w] →
        ∃ cl, η.sto ad.label = some cl ∧ cl.owner = some η.tid ∧ 1 ≤ Rf (.own ad.label) := by
      intro a c hws hsto hown hR
      have hwa : w.val = .loc a 0 := by simpa using hws
      rw [hw] at hwa
      cases hwa
      refine ⟨c, hsto, hown, ?_⟩
      rw [hR, ownW_own_loc hws] at hle
      simpa using hle
    rcases ho with ⟨u, rfl⟩ | ⟨u, rfl⟩ | ⟨u, ψ, rfl⟩
    · obtain ⟨⟨a, c, hws, -, hsto, -, hmode, -⟩, hR⟩ := hv
      exact key a c hws hsto hmode hR
    · obtain ⟨hnl | ⟨a, c, U, hws, hsto, -, -, hmode, -⟩, hR⟩ := hv
      · have : w.val = .null := by simpa using hnl.1
        rw [hw] at this; cases this
      · exact key a c hws hsto hmode hR
    · obtain ⟨⟨hnl | ⟨a, c, U, hws, hsto, -, -, hmode, -⟩, hR⟩, -⟩ := hv
      · have : w.val = .null := by simpa using hnl.1
        rw [hw] at this; cases this
      · exact key a c hws hsto hmode hR

theorem ownRef_bufOf {t u : Ty} {n k : Idx} (h : bufOf t = some (.own, n, u, k)) : OwnRef t := by
  unfold bufOf at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inr (Or.inr ⟨_, _, rfl⟩)
  · cases h

/-- **`OwnKeyT` at a typed frame**: an own-path op's target is an own cell whose key the
frame holds. -/
theorem ownKey_frame {p : Prog} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {th : TTh} {Rf : Res}
    {K : TEnv → Nat → List Word → Res → Prop} {lab : AllocLabel}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hop : OwnOpT cx th.term) (htg : TermPlant.OpTgt th lab) :
    ∃ cl, η.sto lab = some cl ∧ cl.owner = some η.tid ∧ 1 ≤ Rf (.own lab) := by
  obtain ⟨q, rt, w, ad, off, hq, he, hw, rfl⟩ := htg
  have hH := hi.2.2
  have fin : ∀ t, cx.peek q = .ok t → OwnRef t →
      ∃ cl, η.sto ad.label = some cl ∧ cl.owner = some η.tid ∧ 1 ≤ Rf (.own ad.label) :=
    fun t hp ho => ownRef_key hH hp ho he hw
  rcases hop with ⟨x, e, ⟨a, v, ht⟩ | ⟨b, i, v, ht⟩ | ⟨b, i, q', v, ht⟩ | ⟨b, wi, jl, v, ht⟩ | ⟨b, i, v, ht⟩ |
      ⟨b, i, v, ht⟩⟩ | ⟨x, rel, a, v, tok, e, u, ht, ⟨hpk, -⟩ | ⟨hpk, -⟩⟩
  · -- xchg
    rw [ht] at hq hT hsc
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    have hsc' := hsc.resolve_right (by simp only [StepScopeR, OpScopeR]; exact fun h => h)
    cases hT with
    | let_ hop _ =>
    cases hop with
    | xchg hpk hx =>
    cases hx with
    | rgn _ hc => exact absurd hc (hsc' _ hpk _ _)
    | own _ hc =>
      rcases cell_cases hc with rfl | rfl
      · exact fin _ hpk (Or.inl ⟨_, rfl⟩)
      · exact fin _ hpk (Or.inr (Or.inl ⟨_, rfl⟩))
  · -- xchgAt
    rw [ht] at hq hT
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    cases hT with
    | let_ hop _ =>
    cases hop with
    | xchgAt hpk hb => exact fin _ hpk (ownRef_bufOf hb)
  · -- xchgAtF
    rw [ht] at hq hT
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    cases hT with
    | let_ hop _ =>
    cases hop with
    | xchgAtF hpk hb => exact fin _ hpk (ownRef_bufOf hb)
  · -- stlw
    rw [ht] at hq hT
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    cases hT with
    | let_ hop _ =>
    cases hop with
    | stlw hpk hb => exact fin _ hpk (ownRef_bufOf hb)
  · -- stl
    rw [ht] at hq hT
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    cases hT with
    | let_ hop _ =>
    cases hop with
    | stl hpk hb => exact fin _ hpk (ownRef_bufOf hb)
  · -- bufInit: the operand is used by the rule, read before the step
    rw [ht] at hq hT
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    cases hT with
    | let_ hop _ =>
    cases hop with
    | bufInit hu hb => exact fin _ (use_cases hu).1 (ownRef_bufOf hb)
  · -- store through `ptr own`
    rw [ht] at hq
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    exact fin _ hpk (Or.inl ⟨_, rfl⟩)
  · -- store through `loc own`
    rw [ht] at hq
    simp only [TermPlant.opAtom, Option.some.injEq] at hq; subst hq
    exact fin _ hpk (Or.inr (Or.inl ⟨_, rfl⟩))

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`OwnKeyT` discharged** from the scope fact (`Obligations.scope`). -/
theorem ownKeyT_of
    (hsc : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StepScope cx th.term ∨ StepScopeR th.σs cx th.term) :
    OwnKeyT p k arch Sp Init MintOK c0 :=
  by
    intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs lab X Y hop htg
    exact ownKey_frame (η := η) Y.2.2.2.1.1 Y.2.2.2.2.2.1 (hsc X Y) hop htg

end

/-! ## The shared provenance fact `PlantAtT`

At an own cell `lab` of the stepper with a frontier, a window bound `wB` (intended: the
index of the plant promise naming `lab`; any bound if `lab` was published unplanted):

* (A) own provenance: every message at `lab` up to `wB` is an outstanding own promise or
  at most the stepper's coherence there (the cell was private before the plant);
* (B) cross-thread provenance: every foreign promise the stepper's cut sees at `lab` is
  above `wB`;
* (C) while the stepper holds the own key (`lab` unpublished), the plant promise is
  outstanding after the step with view at least the new `vWr` (`certified_pub_vWrLe`
  at the certificate's publish of `lab`).

`PlantPendT` is (C) (`plantPendT_of`); (A)-(C) give `PlantOp`'s `W1`-`W3`. -/

/-- **`PlantAtT`** (stage A, per step): the plant provenance of an own frontier cell. -/
def PlantAtT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {lab : AllocLabel} {cl : Cell},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    (CE η).sto lab = some cl → cl.owner = some (CE η).tid → (CE η).pfr lab ≠ none →
    ∃ wB : Ts,
      (∀ t m, c.mem[t]? = some m → m.loc.label = lab → t ≤ wB → t ∈ th.promises ∨ t ≤ th.vs.coh m.loc) ∧
      (∀ t m, t ∈ FpAt (CE η) ⟨lab, 0⟩ → c.mem[t]? = some m → m.loc.label = lab → wB < t) ∧
      (1 ≤ Rf (.own lab) → ∃ mB : Msg, c.mem[wB]? = some mB ∧ wB ∈ r.2.2.promises ∧ r.2.2.vs.vWr ≤ mB.view)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`PlantPendT` from `PlantAtT`** (its clause (C)). -/
theorem plantPendT_of (hA : PlantAtT p k arch Sp Init MintOK c0) : PlantPendT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs lab cl X Y hsto hown hpf hkey
  obtain ⟨wB, -, -, hC⟩ := hA X Y hsto hown hpf
  obtain ⟨mB, hmB, hwB, hle⟩ := hC hkey
  obtain ⟨-, hme, -, -, -⟩ := TermCert.tstep_appUp X.hr
  exact ⟨wB, hwB, mB, hme wB mB hmB, hle⟩

/-- **`PlantOp` W2 (`WinOwn`)** from `PlantAtT` (A). -/
theorem plantOp_W2 {wB : Ts} {mem : Memory} {th : TTh} {lab : AllocLabel}
    (hA : ∀ t m, mem[t]? = some m → m.loc.label = lab → t ≤ wB → t ∈ th.promises ∨ t ≤ th.vs.coh m.loc) :
    ∀ t m, mem[t]? = some m → m.loc.label = lab → th.vs.coh m.loc < t → t ≤ wB → t ∈ th.promises :=
  fun t m hm hl hc hw => (hA t m hm hl hw).resolve_right (Nat.not_le.2 hc)

/-- **`PlantOp` W1 at the taken step** from `PlantAtT` (C) and `OwnKeyT`: under an own-path op
on `lab`, every promise the step fulfils lies below `wB`. -/
theorem plantOp_W1T (hK : OwnKeyT p k arch Sp Init MintOK c0) (hA : PlantAtT p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {lab : AllocLabel}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hop : OwnOpT cx th.term) (htg : TermPlant.OpTgt th lab) (hpf : (CE η).pfr lab ≠ none) :
    ∃ wB : Ts, (∀ t, t ∈ th.promises → t ∉ r.2.2.promises → t < wB) ∧
      (∀ t m, c.mem[t]? = some m → m.loc.label = lab → th.vs.coh m.loc < t → t ≤ wB → t ∈ th.promises) ∧
      (∀ t m, t ∈ FpAt (CE η) ⟨lab, 0⟩ → c.mem[t]? = some m → m.loc.label = lab → wB < t) := by
  obtain ⟨cl, hsto, hown, hkey⟩ := hK X Y hop htg
  obtain ⟨wB, hAo, hB, hC⟩ := hA X Y hsto hown hpf
  obtain ⟨mB, hmB, hwB, hle⟩ := hC hkey
  obtain ⟨-, hme, hsub, hful, -⟩ := TermCert.tstep_appUp X.hr
  obtain ⟨m', hm', hv⟩ := TermPlantF.promViewLt_run h0 X.run i th wB X.hth (hsub wB hwB)
  rw [hmB, Option.some.injEq] at hm'
  have hv' : mB.view < wB := by rw [hm']; exact hv
  refine ⟨wB, fun t ht hn => ?_, plantOp_W2 hAo, hB⟩
  have h1 : t ≤ r.2.2.vs.vWr := hful t ht hn
  exact Nat.lt_of_le_of_lt (Nat.le_trans h1 hle) hv'

end

end TermPlantFul

#print axioms TermPlantFul.plantFulfil_of
#print axioms TermPlantFul.ownKeyT_of
#print axioms TermPlantFul.plantPendT_of
#print axioms TermPlantFul.plantOp_W1T
