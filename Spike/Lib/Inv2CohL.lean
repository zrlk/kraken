/-
**The location-restricted cover across a thread's own steps** ISA-generic.

`Scc.Sem.stepOne_cohP` for `Spike.Lib.Inv2Core.CohCoversL`: the same
proof, every rule keeping the cover on any location set `L`. A read and a
fence keep memory and promises and raise views; a fulfilment removes its
timestamp from the promises and raises the coherence view of its location
to it; an append adds the message and raises the view there.

- `stepOne_cohL`: one instruction of the thread keeps `CohCoversL … L`;
- `retThread_cohL`: a system call's return keeps it.

The cover on `L` is enough for every read of a word in `L`
(`Scc/Sem/OwnWord.lean` and `Scc/Sem/Rows1Rmw.lean` with `CohCoversP`
replaced by `CohCoversL`, the same proofs):

- `tlatestP_of_readL`, `readSuccs_tlatestL`, `stepOne_load_tlatestL`: a
  read of a word in `L` reads its latest write not promised;
- `OwnInvL … L a v`: `OwnInv` with the restricted cover;
  `stepOne_ownL` (no write of the word), `stepOne_load_ownL`,
  `stepOne_store_ownL`/`stepOne_store_ownOfL`, `stepOne_rmw_ownL`,
  `own_promiseL`;
- `stepOne_rmw_casesL`: `stepOne_rmw_cases` under the restricted cover;
- `ownOk_stepL`: `Consumer1.ownOk_step` under the restricted cover.
-/
import Spike.Lib.Inv2Core
import Spike.Lib.Inv2Rely
import Scc.Sem.OwnWord
import Scc.Sem.Rows1Rmw

namespace Spike.Lib.Inv2Core

open Kraken Kraken.Promising Scc.Sem

/-- The restricted cover across a context step. -/
def CohStepL (L : Loc → Prop) (c c' : Ctx) : Prop :=
  CohCoversL c.views c.prom c.mem L → CohCoversL c'.views c'.prom c'.mem L

theorem CohCoversL.mono' {vs vs' : Views} {prom : List Time} {mem : Memory} {L : Loc → Prop}
    (h : CohCoversL vs prom mem L) (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) : CohCoversL vs' prom mem L :=
  fun k w hk hl hp => Nat.le_trans (h k w hk hl hp) (hle w.loc)

section RulesL
variable (A : Arch) (tid : Nat) (iv : InstrViews) (L : Loc → Prop)

theorem cohStepL_of_eq {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hle : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : CohStepL L c c' := fun h1 => by
  rw [hm, hp]; exact h1.mono' hle

theorem readSuccs_cohL {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : CohStepL L c x.2.2 := by
  obtain ⟨v, -, -, h⟩ := readSuccs_shape A iv hx
  refine cohStepL_of_eq L (by rw [h]) (readSuccs_prom A iv hx) ?_
  intro l'; rw [h]; exact getCoh_le_setCoh _ _ _ _

theorem writeSuccs_cohL {xr : View} {c : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) :
    CohStepL L c c' := by
  intro h1
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, -, rfl⟩ | ⟨-, rfl⟩
  · intro k' w hk hL hp
    show k' ≤ (c.views.setCoh l t).getCoh w.loc
    rw [Views.getCoh_setCoh]
    have hk' : c.mem.get? k' = some w := hk
    by_cases he : k' = t
    · subst he
      rw [hg] at hk'; cases hk'
      simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · have hp' : k' ∉ c.prom := fun hm => hp (by
        show k' ∈ c.prom.erase t
        exact (List.mem_erase_of_ne he).mpr hm)
      have := h1 k' w hk' hL hp'
      split
      · rename_i hl; rw [hl] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this
  · intro k' w hk hL hp
    show k' ≤ (c.views.setCoh l (c.mem.last + 1)).getCoh w.loc
    rw [Views.getCoh_setCoh]
    have hk' : (c.mem.append { loc := l, val := v, tid }).1.get? k' = some w := hk
    by_cases he : k' = c.mem.last + 1
    · subst he
      rw [Memory.get?_append_new] at hk'; cases hk'
      simp only [↓reduceIte]; exact Nat.le_max_right _ _
    · have hold := CohCoversP.get?_append_ne hk' he
      have hp' : k' ∉ c.prom := fun hm => hp (by
        show k' ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
        exact (List.mem_erase_of_ne he).mpr (List.mem_append_left _ hm))
      have := h1 k' w hold hL hp'
      split
      · rename_i hl; rw [hl] at this; exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this

theorem fenceStep_cohL (c : Ctx) (k : FenceKind) : CohStepL L c (fenceStep c k) :=
  cohStepL_of_eq L (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fun l => by cases k <;> exact Nat.le_refl _)

theorem rmwPost_cohL (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) : CohStepL L c (rmwPost A k noRet l c) := by
  refine cohStepL_of_eq L ?_ ?_ ?_ <;> unfold rmwPost <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

theorem runTree_cohL {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → CohStepL L c c' :=
  runTree_preserves A tid iv (CohStepL L) (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h))
    (fun _ _ _ _ _ _ hx => readSuccs_cohL A iv L hx) (fun _ _ _ _ _ _ _ _ _ _ h => writeSuccs_cohL A tid L h)
    (fenceStep_cohL L) (fun _ _ => cohStepL_of_eq L rfl rfl (fun _ => Nat.le_refl _))
    (fun c k noRet l => rmwPost_cohL A L c k noRet l) tree

end RulesL

/-- **One instruction of the thread keeps the restricted cover**, with or
without outstanding promises. -/
theorem stepOne_cohL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversL t.views t.prom mem L) :
    CohCoversL o.thread.views o.thread.prom o.mem L := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hc' := runTree_cohL A tid _ L tree _ st c' hr hc
      obtain ⟨e1, e2⟩ := finishInstr_relKey hth
      have e3 : th.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
      intro k w hk hl hp
      rw [e1] at hp
      have := hc' k w hk hl hp
      unfold Views.getCoh at this ⊢
      rw [e3]; exact this

/-- **A system call's return keeps the restricted cover** (registers and pc
only). -/
theorem retThread_cohL {I : ISA} (K : Kernel.Abi I) {t : Thread I} {mem : Memory} {L : Loc → Prop}
    (hc : CohCoversL t.views t.prom mem L) (r : BitVec 64) :
    CohCoversL (Kernel.retThread K t r).views (Kernel.retThread K t r).prom mem L := by
  rw [retThread_views K t r, Kernel.retThread_prom (K := K) t r]; exact hc

/-! ## Reads under the restricted cover -/

/-- **`tlatestP_of_read` under the restricted cover** of a set holding the
word. -/
theorem tlatestP_of_readL {vs : Views} {prom : List Time} {tm : Memory} {L : Loc → Prop}
    (hc : CohCoversL vs prom tm L) {a t bound : Nat} (hL : L (wordLoc a)) {v : Val}
    (hr : tm.read? (wordLoc a) t = some v) (hw : tm.writeIn (wordLoc a) t bound = false)
    (hb : vs.getCoh (wordLoc a) ≤ bound) (hp : t ∉ prom) : TLatestP tm prom a t := by
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos t with h0 | hpos
    · exact .inl h0
    · have ht0 : t ≠ 0 := by omega
      unfold Memory.read? at hr
      simp only [ht0, ↓reduceIte] at hr
      cases hg : tm.get? t with
      | none => rw [hg] at hr; cases hr
      | some w =>
        rw [hg] at hr
        by_cases hl : w.loc = wordLoc a
        · exact .inr ⟨w, rfl, hl, hp⟩
        · simp [hl] at hr
  · intro k'' w hlt hg hl
    refine Classical.byContradiction fun hnp => ?_
    have hk := hc k'' w hg (hl ▸ hL) hnp
    rw [hl] at hk
    unfold Memory.writeIn at hw
    rw [List.any_eq_false] at hw
    have hlt' : @LT.lt Nat instLTNat t k'' := hlt
    have hk' : @LE.le Nat instLENat k'' (vs.getCoh (wordLoc a)) := hk
    have hb' : @LE.le Nat instLENat (vs.getCoh (wordLoc a)) bound := hb
    have := hw (k'' - t - 1) (List.mem_range.mpr (by omega))
    rw [show t + (k'' - t - 1) + 1 = k'' by omega, hg] at this
    simp [hl] at this

section RulesOwnL
variable (A : Arch) (tid : Nat) (iv : InstrViews) (L : Loc → Prop)

/-- **Kraken's `read` rule reads the latest write not promised** of a word
in `L` under the restricted cover. -/
theorem readSuccs_tlatestL {c : Ctx} {k : LoadKind} {xcl : Bool} {a : Nat} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl (wordLoc a) noRet)
    (hc : CohCoversL c.views c.prom c.mem L) (hL : L (wordLoc a)) :
    TLatestP c.mem c.prom a x.1 ∧ c.mem.read? (wordLoc a) x.1 = some x.2.1 := by
  obtain ⟨t, v, rfl, -, hv, hw, hp⟩ := (mem_readSuccs A).mp hx
  refine ⟨tlatestP_of_readL hc hL hv hw (Nat.le_max_right _ _) ?_, hv⟩
  intro hm
  have : c.prom.contains t = true := List.elem_eq_true_of_mem hm
  rw [this] at hp; cases hp

/-- **A read of the word returns its value** (restricted cover). -/
theorem readSuccs_ownL {c : Ctx} {k : LoadKind} {xcl : Bool} {a : Nat} {noRet : Bool} {v : Val}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl (wordLoc a) noRet)
    (hc : CohCoversL c.views c.prom c.mem L) (hL : L (wordLoc a)) (ho : OwnVal c.mem c.prom a v) :
    x.2.1 = v := by
  obtain ⟨hl, hv⟩ := readSuccs_tlatestL A iv L hx hc hL
  obtain ⟨k', hk', hv'⟩ := ho
  rw [← hk'.unique hl, hv'] at hv
  exact (Option.some.inj hv).symm

end RulesOwnL

/-- **`OwnInv` with the restricted cover**: the cover on `L`, the promises
distinct and messages, and the word at `a` reading as `v`. -/
def OwnInvL (vs : Views) (prom : List Time) (mem : Memory) (L : Loc → Prop) (a : Nat) (v : Val) : Prop :=
  CohCoversL vs prom mem L ∧ prom.Nodup ∧ (∀ p ∈ prom, p ≤ mem.last) ∧ OwnVal mem prom a v

/-- `OwnInv` gives `OwnInvL` on every set. -/
theorem OwnInvL.of_ownInv {vs : Views} {prom : List Time} {mem : Memory} {a : Nat} {v : Val}
    (h : OwnInv vs prom mem a v) (L : Loc → Prop) : OwnInvL vs prom mem L a v :=
  ⟨CohCoversL.of_cohCoversP h.1 L, h.2⟩

/-- **The step invariant**: `OwnInvL … v` kept from `c` to `c'`. -/
def OwnStepL (L : Loc → Prop) (a : Nat) (v : Val) (c c' : Ctx) : Prop :=
  OwnInvL c.views c.prom c.mem L a v → OwnInvL c'.views c'.prom c'.mem L a v

theorem OwnStepL.refl {L : Loc → Prop} {a : Nat} {v : Val} (c : Ctx) : OwnStepL L a v c c := fun h => h

theorem OwnStepL.trans {L : Loc → Prop} {a : Nat} {v : Val} {c₁ c₂ c₃ : Ctx} (h₁ : OwnStepL L a v c₁ c₂)
    (h₂ : OwnStepL L a v c₂ c₃) : OwnStepL L a v c₁ c₃ := fun h => h₂ (h₁ h)

section RulesOwnL2
variable (A : Arch) (tid : Nat) (iv : InstrViews) (L : Loc → Prop)

theorem ownStepL_of_eq {a : Nat} {v : Val} {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hle : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : OwnStepL L a v c c' := fun ⟨h₁, h₂, h₃, h₄⟩ => by
  refine ⟨cohStepL_of_eq L hm hp hle h₁, ?_, ?_, ?_⟩
  · rw [hp]; exact h₂
  · rw [hp, hm]; exact h₃
  · rw [hm, hp]; exact h₄

theorem ownInvL_finish {I : ISA} {a : Nat} {v : Val} {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews}
    {st : I.State} {c : Ctx} {th : Thread I} (hth : th ∈ finishInstr t d iv st c)
    (h : OwnInvL c.views c.prom c.mem L a v) : OwnInvL th.views th.prom c.mem L a v := by
  obtain ⟨e1, e2⟩ := finishInstr_relKey hth
  have e3 : th.views.coh = c.views.coh := by have := congrArg Views.coh e2; exact this
  have he : ∀ l, c.views.getCoh l ≤ th.views.getCoh l := fun l => by
    unfold Views.getCoh; rw [e3]; exact Nat.le_refl _
  rw [e1]
  exact ⟨h.1.mono' he, h.2⟩

theorem readSuccs_ownStepL {a : Nat} {v : Val} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : OwnStepL L a v c x.2.2 := by
  obtain ⟨v', -, -, h⟩ := readSuccs_shape A iv hx
  refine ownStepL_of_eq L (by rw [h]) (readSuccs_prom A iv hx) ?_
  intro l'; rw [h]; exact getCoh_le_setCoh _ _ _ _

/-- **A write elsewhere keeps the word's value** (restricted cover). -/
theorem writeSuccs_ownStepL {a : Nat} {v₀ : Val} {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time} {extra : View}
    (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) (hl : l ≠ wordLoc a) : OwnStepL L a v₀ c c' := by
  intro ⟨h₁, h₂, h₃, ⟨k', ⟨hk1, hk2⟩, hv⟩⟩
  have hc := writeSuccs_cohL A tid L h h₁
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨hc, ?_, ?_, k', ⟨?_, fun k'' w hlt hg' hla => ?_⟩, hv⟩
    · show (c.prom.erase t).Nodup
      exact h₂.erase t
    · show ∀ p ∈ c.prom.erase t, p ≤ c.mem.last
      exact fun p hp => h₃ p (List.mem_of_mem_erase hp)
    · rcases hk1 with h0 | ⟨w, hw, hwl, hp⟩
      · exact .inl h0
      · exact .inr ⟨w, hw, hwl, fun hm => hp (List.mem_of_mem_erase hm)⟩
    · have hg'' : c.mem.get? k'' = some w := hg'
      have hne : k'' ≠ t := by
        rintro rfl; rw [hg] at hg''; cases hg''; exact hl hla
      show k'' ∈ c.prom.erase t
      exact (List.mem_erase_of_ne hne).mpr (hk2 k'' w hlt hg'' hla)
  · have hn : c.mem.last + 1 ∉ c.prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
    have hk'le : k' ≤ c.mem.last := by
      rcases hk1 with h0 | ⟨w, hw, -, -⟩
      · rw [h0]; exact Nat.zero_le _
      · exact Scc.Sem.Memory.le_last_of_get? hw
    have ep : ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)) = c.prom := erase_append_new hn
    refine ⟨hc, ?_, ?_, k', ⟨?_, fun k'' w hlt hg' hla => ?_⟩, ?_⟩
    · show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      rw [ep]; exact h₂
    · show ∀ p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1),
        p ≤ (c.mem.append { loc := l, val := v, tid }).1.last
      rw [ep, Memory.last_append]; exact fun p hp => Nat.le_succ_of_le (h₃ p hp)
    · show k' = 0 ∨ ∃ w, (c.mem.append { loc := l, val := v, tid }).1.get? k' = some w ∧ w.loc = wordLoc a ∧
        k' ∉ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep, Memory.get?_append_le hk'le]; exact hk1
    · have hg'' : (c.mem.append { loc := l, val := v, tid }).1.get? k'' = some w := hg'
      show k'' ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep]
      by_cases he : k'' = c.mem.last + 1
      · subst he; rw [Memory.get?_append_new] at hg''; cases hg''; exact absurd hla hl
      · exact hk2 k'' w hlt (CohCoversP.get?_append_ne hg'' he) hla
    · show (c.mem.append { loc := l, val := v, tid }).1.read? (wordLoc a) k' = some v₀
      rw [read?_append_le hk'le]; exact hv

/-- **A write of `v` to a word in `L` makes it read as `v`** (restricted
cover; `writeSuccs_ownOf`). -/
theorem writeSuccs_ownOfL {a : Nat} {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind}
    {xcl : Bool} {v : Val} {tr : Option Time} {extra : View}
    (h : c' ∈ writeSuccs A tid iv' c k xcl (wordLoc a) v tr extra xr) (hL : L (wordLoc a))
    (h₁ : CohCoversL c.views c.prom c.mem L) (h₂ : c.prom.Nodup) (h₃ : ∀ p ∈ c.prom, p ≤ c.mem.last) :
    OwnInvL c'.views c'.prom c'.mem L a v := by
  have hc := writeSuccs_cohL A tid L h h₁
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, hok, rfl⟩ | ⟨-, rfl⟩
  · have hlt : c.views.getCoh (wordLoc a) < t := by
      unfold Lower.writeOk at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    refine ⟨hc, ?_, ?_, t, ⟨?_, fun k'' w hlt' hg' hla => ?_⟩, ?_⟩
    · show (c.prom.erase t).Nodup
      exact h₂.erase t
    · show ∀ p ∈ c.prom.erase t, p ≤ c.mem.last
      exact fun p hp => h₃ p (List.mem_of_mem_erase hp)
    · exact .inr ⟨_, hg, rfl, h₂.not_mem_erase⟩
    · have hg'' : c.mem.get? k'' = some w := hg'
      show k'' ∈ c.prom.erase t
      refine (List.mem_erase_of_ne (Nat.ne_of_gt hlt')).mpr ?_
      refine Classical.byContradiction fun hp => ?_
      have := h₁ k'' w hg'' (hla ▸ hL) hp
      rw [hla] at this
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this (Nat.lt_trans hlt hlt'))
    · show c.mem.read? (wordLoc a) t = some v
      have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
      simp [Memory.read?, ht0, hg]
  · have hn : c.mem.last + 1 ∉ c.prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
    have ep : ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)) = c.prom := erase_append_new hn
    refine ⟨hc, ?_, ?_, c.mem.last + 1, ⟨?_, fun k'' w hlt hg' _ => ?_⟩, ?_⟩
    · show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      rw [ep]; exact h₂
    · show ∀ p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1),
        p ≤ (c.mem.append { loc := wordLoc a, val := v, tid }).1.last
      rw [ep, Memory.last_append]; exact fun p hp => Nat.le_succ_of_le (h₃ p hp)
    · show c.mem.last + 1 = 0 ∨ ∃ w, (c.mem.append { loc := wordLoc a, val := v, tid }).1.get? (c.mem.last + 1) = some w ∧
        w.loc = wordLoc a ∧ c.mem.last + 1 ∉ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep, Memory.get?_append_new]
      exact .inr ⟨_, rfl, rfl, hn⟩
    · have hg'' : (c.mem.append { loc := wordLoc a, val := v, tid }).1.get? k'' = some w := hg'
      have := Scc.Sem.Memory.le_last_of_get? hg''
      rw [Memory.last_append] at this
      exact absurd (Nat.lt_of_lt_of_le hlt this) (Nat.lt_irrefl _)
    · show (c.mem.append { loc := wordLoc a, val := v, tid }).1.read? (wordLoc a) (c.mem.last + 1) = some v
      simp [Memory.read?, Memory.get?_append_new]

theorem fenceStep_ownStepL {a : Nat} {v : Val} (c : Ctx) (k : FenceKind) : OwnStepL L a v c (fenceStep c k) :=
  ownStepL_of_eq L (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fun l => by cases k <;> exact Nat.le_refl _)

theorem fenceOpt_ownStepL {a : Nat} {v : Val} (c : Ctx) (b : Bool) :
    OwnStepL L a v c (if b then fenceStep c .sy else c) := by
  cases b
  · exact OwnStepL.refl c
  · exact fenceStep_ownStepL L c .sy

theorem rmwPost_ownStepL {a : Nat} {v : Val} (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) :
    OwnStepL L a v c (rmwPost A k noRet l c) := by
  refine ownStepL_of_eq L ?_ ?_ ?_ <;> unfold rmwPost <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

/-- **A run of a tree with no write of the word keeps its value**
(restricted cover). -/
theorem runTree_ownStepL {a : Nat} {v₀ : Val} {σ : Type} (tree : EvTree σ)
    (hW : WriteTree (fun l _ => l ≠ wordLoc a) tree) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → OwnStepL L a v₀ c c' := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact OwnStepL.refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hW i) c s c' h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_ownStepL A iv L hx).trans (ih x.2.1 (hW x.2.1) x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_ownStepL A tid L hc0 hl).trans (ih true (hW true) c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have := ih false (hW false) _ s c' h.2
      exact (ownStepL_of_eq L rfl rfl (fun _ => Nat.le_refl _)).trans this
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (fenceStep_ownStepL L c k).trans (ih () (hW ()) _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree] at h
    have h1 := fenceOpt_ownStepL L (a := a) (v := v₀) c A.rmwFence
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_ownStepL A iv L h2)
    simp only at h
    split at h
    · exact (h12.trans (fenceOpt_ownStepL L _ A.rmwFence)).trans (ih old (hW old) _ s c' h)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact (((h12.trans (writeSuccs_ownStepL A tid L hc3 (hl old new hnew))).trans
        (rmwPost_ownStepL A L c3 k noRet l)).trans (fenceOpt_ownStepL L _ A.rmwFence)).trans (ih old (hW old) _ s c' h)

theorem rmwBump_ownStepL {a : Nat} {v : Val} (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    OwnStepL L a v c (Lower.rmwBump k noRet l c) := by
  refine ownStepL_of_eq L ?_ ?_ ?_ <;> unfold Lower.rmwBump <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

theorem rmwFenceOpt_cohL (c : Ctx) : CohStepL L c (Lower.rmwFenceOpt A c) := by
  unfold Lower.rmwFenceOpt; split
  · exact fenceStep_cohL L c .sy
  · exact id

end RulesOwnL2

/-- **One instruction with no write of the word keeps its value**
(restricted cover). -/
theorem stepOne_ownL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {a : Nat} {v : Val} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hW : WriteTree (fun l _ => l ≠ wordLoc a) tree)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInvL t.views t.prom mem L a v) :
    OwnInvL o.thread.views o.thread.prom o.mem L a v := by
  unfold stepOne at hstep
  rw [hex] at hstep
  have hstep' : _ = outs := Option.some.inj hstep
  subst hstep'
  rw [List.mem_flatMap] at ho
  obtain ⟨r, hr, ho⟩ := ho
  cases r with
  | error m => simp at ho
  | ok q =>
    obtain ⟨st, c'⟩ := q
    simp only [List.mem_map, Except.ok.injEq] at ho
    obtain ⟨th, hth, rfl⟩ := ho
    exact ownInvL_finish L hth (runTree_ownStepL A tid _ L tree hW _ st c' hr hi)

/-- **A load of a word in `L` reads its latest write not promised**
(`stepOne_load_tlatestP` under the restricted cover). -/
theorem stepOne_load_tlatestL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversL t.views t.prom mem L)
    (hL : L (wordLoc a)) :
    o.mem = mem ∧ ∃ ts v, o.thread.st = g v ∧ TLatestP mem t.prom a ts ∧ mem.read? (wordLoc a) ts = some v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_load_iff] at hr
  obtain ⟨ts, v, hx, rfl⟩ := hr
  obtain ⟨hl, hv⟩ := readSuccs_tlatestL A _ L hx hc hL
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    have := congrArg Ctx.mem h; exact this
  exact ⟨hm.trans hmem, ts, v, finishInstr_st hth, hl, hv⟩

/-- **A load of a word in `L` returns its value**, and keeps the
invariant. -/
theorem stepOne_load_ownL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInvL t.views t.prom mem L a v)
    (hL : L (wordLoc a)) :
    o.mem = mem ∧ o.thread.st = g v ∧ OwnInvL o.thread.views o.thread.prom o.mem L a v := by
  obtain ⟨hm, ts, v', hst, hl, hv⟩ := stepOne_load_tlatestL A hex hstep ho hi.1 hL
  obtain ⟨k', hk', hv''⟩ := hi.2.2.2
  rw [← hk'.unique hl, hv''] at hv
  cases hv
  exact ⟨hm, hst, stepOne_ownL A hex (fun _ => trivial) hstep ho hi⟩

/-- **A store of `v` to a word in `L` makes it read as `v`**, whatever it
read as before. -/
theorem stepOne_store_ownOfL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {k : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversL t.views t.prom mem L)
    (hL : L (wordLoc a)) (hn : t.prom.Nodup) (hl : ∀ p ∈ t.prom, p ≤ mem.last) :
    o.thread.st = s ∧ OwnInvL o.thread.views o.thread.prom o.mem L a v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  refine ⟨finishInstr_st hth, ?_⟩
  rw [hm]
  exact ownInvL_finish L hth (writeSuccs_ownOfL A tid L hw hL hc hn hl)

/-- **A store of `v` to a word in `L` makes it read as `v`.** -/
theorem stepOne_store_ownL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {k : StoreKind} {a : Nat} {v₀ v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInvL t.views t.prom mem L a v₀)
    (hL : L (wordLoc a)) :
    o.thread.st = s ∧ OwnInvL o.thread.views o.thread.prom o.mem L a v :=
  stepOne_store_ownOfL A hex hstep ho hi.1 hL hi.2.1 hi.2.2.1

/-- **An RMW of a word in `L` reads its value `v` and makes it read as
`op v`** (restricted cover; `stepOne_rmw_own`). -/
theorem stepOne_rmw_ownL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInvL t.views t.prom mem L a v)
    (hL : L (wordLoc a)) :
    o.thread.st = g v ∧ OwnInvL o.thread.views o.thread.prom o.mem L a ((op v).getD v) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  have hf : ∀ {w : Val} (c : Ctx), OwnStepL L a w c (Lower.rmwFenceOpt A c) :=
    fun c => fenceOpt_ownStepL L c A.rmwFence
  have h0 := hf (Live.TicketStep.ctx0 tid t mem) hi
  have hold : old = v := readSuccs_ownL A _ L hx h0.1 hL h0.2.2.2
  subst hold
  have h1 := readSuccs_ownStepL A _ L hx h0
  refine ⟨finishInstr_st hth, ?_⟩
  rw [hm]
  refine ownInvL_finish L hth ?_
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · rw [hop]
    exact hf c1 h1
  · rw [hop]
    have h2 : OwnInvL c2.views c2.prom c2.mem L a new :=
      writeSuccs_ownOfL A tid L hw hL h1.1 h1.2.1 h1.2.2.1
    exact hf _ (rmwBump_ownStepL L (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true } h2)

/-- **A promise keeps the word's value** (restricted cover). -/
theorem own_promiseL {vs : Views} {prom : List Time} {mem : Memory} {L : Loc → Prop} {a : Nat} {v : Val}
    (h : OwnInvL vs prom mem L a v) (w : Msg) :
    OwnInvL vs (prom ++ [(mem.append w).2]) (mem.append w).1 L a v := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have e2 : (mem.append w).2 = mem.last + 1 := rfl
  have hn : mem.last + 1 ∉ prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
  refine ⟨Spike.Lib.Inv2Rely.CohCoversL.promise h₁ w, ?_, ?_, ownVal_promise h₄ w⟩
  · rw [e2]
    exact List.nodup_append.mpr ⟨h₂, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy => by
      rw [List.mem_singleton] at hy; subst hy; rintro rfl; exact hn hx⟩
  · intro p hp
    rw [Memory.last_append]
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.le_succ_of_le (h₃ p hp)
    · rw [List.mem_singleton] at hp; rw [hp]; exact Nat.le_refl _

/-- **`stepOne_rmw_cases` under the restricted cover** of a set holding the
word. -/
theorem stepOne_rmw_casesL {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {L : Loc → Prop}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversL t.views t.prom mem L)
    (hL : L (wordLoc a)) (hpl : ∀ p ∈ t.prom, p ≤ mem.last) :
    ∃ old tr, o.thread.st = g old ∧ TLatestP mem t.prom a tr ∧ mem.read? (wordLoc a) tr = some old ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom) ∨
       (∃ new, op old = some new ∧
        ((∃ q ∈ t.prom, mem.get? q = some ⟨wordLoc a, new, tid⟩ ∧
            (∃ vs : Views, CohCoversL vs t.prom mem L ∧ vs.getCoh (wordLoc a) < q) ∧
            o.mem = mem ∧ o.thread.prom = t.prom.erase q) ∨
          (o.mem = (mem.append ⟨wordLoc a, new, tid⟩).1 ∧ o.thread.prom = t.prom)))) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  obtain ⟨hm0, hp0⟩ := rmwFenceOpt_mem_prom A
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Ctx)
  have hc0 := rmwFenceOpt_cohL A L
    ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Ctx) hc
  obtain ⟨hl, hv⟩ := readSuccs_tlatestL A _ L hx hc0 hL
  have hc1 := readSuccs_cohL A _ L hx hc0
  have hm1 : c1.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    exact (congrArg Ctx.mem h).trans hm0
  have hp1 : c1.prom = t.prom := (readSuccs_prom A _ hx).trans hp0
  rw [hm0, hp0] at hl
  rw [hm0] at hv
  simp only at hc1
  rw [hm1, hp1] at hc1
  refine ⟨old, tr, finishInstr_st hth, hl, hv, ?_⟩
  rw [(finishInstr_relKey hth).1, hm]
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A c1
    exact .inl ⟨hop, h1.trans hm1, h2.trans hp1⟩
  · refine .inr ⟨new, hop, ?_⟩
    obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A
      (Lower.rmwBump (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true })
    obtain ⟨h3, h4⟩ := rmwBump_mem_prom (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true }
    rw [h1, h3, h2, h4]
    simp only
    rcases (Lower.mem_writeSuccs_iff A tid _).mp hw with ⟨q, hq, hg, hok, rfl⟩ | ⟨-, rfl⟩
    · rw [hp1] at hq
      rw [hm1] at hg
      refine .inl ⟨q, hq, hg, ⟨c1.views, hc1, ?_⟩, hm1, ?_⟩
      · unfold Lower.writeOk at hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
      · show c1.prom.erase q = _
        rw [hp1]
    · refine .inr ⟨?_, ?_⟩
      · show (c1.mem.append _).1 = _
        rw [hm1]
      · show (c1.prom ++ [c1.mem.last + 1]).erase (c1.mem.last + 1) = t.prom
        rw [hm1, hp1]
        exact List.erase_append_singleton_self fun hmem => by
          have h1 : @LE.le Nat instLENat (mem.last + 1) mem.last := hpl _ hmem
          omega

/-- A store's successor state (`finishInstr_st`). -/
theorem stepOne_store_st {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) : o.thread.st = s := by
  obtain ⟨st, c', hr, hth, -⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, -⟩ := hr
  exact finishInstr_st hth

/-- **`Consumer1.ownOk_step` under the restricted cover**: the cover on a
set `C` holding the words owned before the instruction (an RMW reads one)
and after it (a store's fulfilment is above the view of its word). A kept
word needs no cover. -/
theorem ownOk_stepL {I : ISA} {A : Arch} {own : I.State → List (Loc × Val)} {t : Thread I} {tid : Nat}
    {mem : Memory} {C : Loc → Prop} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hT : Consumer1.OwnTree own (own t.st) tree)
    (hc : CohCoversL t.views t.prom mem C) (hn : t.prom.Nodup) (hl : ∀ p ∈ t.prom, p ≤ mem.last)
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) {o : Outcome I}
    (ho : .ok o ∈ outs) (hC : ∀ l w, (l, w) ∈ own t.st → C l) (hC' : ∀ l w, (l, w) ∈ own o.thread.st → C l)
    (h : ExtRows.OwnOk (own t.st) mem t.prom) :
    ExtRows.OwnOk (own o.thread.st) o.mem o.thread.prom := by
  rcases hT with ⟨hQ, hW⟩ | ⟨-, kr, L, V, s', rfl, hL8, hown⟩ | ⟨kr, L, V, s', rfl, hL8, hupd⟩ |
    ⟨k, noRet, L, op, g, rfl, hL8, ⟨v0, hv0⟩, hupd⟩
  · have hq := (stepOne_allInv A hs ho (fun tr he => by rw [hex] at he; cases he; exact hQ)
      ⟨fun _ => trivial, fun _ _ => trivial⟩).1
    rw [hq]
    intro L v hm
    obtain ⟨hL8, hv⟩ := h L v hm
    refine ⟨hL8, (stepOne_ownL A hex (Consumer1.writeTree_mono (fun l w hw he => ?_) hW) hs ho
      ⟨hc, hn, hl, hv⟩).2.2.2⟩
    rw [he, ← ExtRows.loc_wordLoc hL8] at hw
    exact hw v hm
  · have hst := stepOne_store_st A hex hs ho
    have hCL : C L := hC' L V (by rw [hst, hown]; exact List.mem_singleton_self _)
    rw [ExtRows.loc_wordLoc hL8] at hex hCL
    obtain ⟨hst, hi⟩ := stepOne_store_ownOfL A hex hs ho hc hCL hn hl
    rw [hst, hown]
    intro L' v hm
    obtain ⟨rfl, rfl⟩ := List.mem_singleton.mp hm
    exact ⟨hL8, hi.2.2.2⟩
  · have hst := stepOne_store_st A hex hs ho
    have hex' := hex
    rw [ExtRows.loc_wordLoc hL8] at hex'
    rw [hst]
    intro L' w hm
    rcases hupd L' w hm with ⟨rfl, rfl⟩ | ⟨hne, hm'⟩
    · have hCL : C L' := hC' L' w (by rw [hst]; exact hm)
      rw [ExtRows.loc_wordLoc hL8] at hCL
      exact ⟨hL8, (stepOne_store_ownOfL A hex' hs ho hc hCL hn hl).2.2.2.2⟩
    · obtain ⟨hL8', hv⟩ := h L' w hm'
      exact ⟨hL8', (stepOne_ownL A hex
        ⟨fun he => hne ((ExtRows.loc_wordLoc hL8').trans he.symm), fun _ => trivial⟩ hs ho
        ⟨hc, hn, hl, hv⟩).2.2.2⟩
  · have hex' := hex
    rw [ExtRows.loc_wordLoc hL8] at hex'
    obtain ⟨-, hv⟩ := h L v0 hv0
    have hCL : C L := hC L v0 hv0
    rw [ExtRows.loc_wordLoc hL8] at hCL
    obtain ⟨hst, hi⟩ := stepOne_rmw_ownL A hex' hs ho ⟨hc, hn, hl, hv⟩ hCL
    rw [hst]
    intro L' w hm
    rcases hupd v0 hv0 L' w hm with ⟨rfl, rfl⟩ | ⟨hne, hm'⟩
    · exact ⟨hL8, hi.2.2.2⟩
    · obtain ⟨hL8', hv'⟩ := h L' w hm'
      exact ⟨hL8', (stepOne_ownL A hex
        ⟨fun _ _ _ he => hne ((ExtRows.loc_wordLoc hL8').trans he.symm), fun _ => trivial⟩ hs ho
        ⟨hc, hn, hl, hv'⟩).2.2.2⟩

/-- info: 'Spike.Lib.Inv2Core.stepOne_cohL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepOne_cohL

/-- info: 'Spike.Lib.Inv2Core.stepOne_rmw_casesL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepOne_rmw_casesL

/-- info: 'Spike.Lib.Inv2Core.stepOne_rmw_ownL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepOne_rmw_ownL

end Spike.Lib.Inv2Core
