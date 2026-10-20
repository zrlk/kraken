/-
**Prototype.** The take rule at the thread-rule level:
the erasure WP whose **load** nodes may change `(r, g)` (`EvTree.EraseWPRDS`),
its frame (`runTree_eraseWPRDS`, `Erase.npStepRDS`), the rule interface
`ThreadRuleRXGS` and `NPSafeP.of_ruleRXGS`, which gives `NPSafeP G
(K2Scope (model I) AllocIds)`, option (S)'s frame, for which Theorem 1′ is
proved (`theorem1IIPure_F_S`, `theorem1IIPure_Hyb_S`).

## Design

- `RStepG g₀ B r g r' g' cx`: `RStep` whose K2 is scoped to resources whose
  ids are allocated at the **instruction's start** ghost `g₀` (a fixed
  parameter of the WP, so scoped steps compose with no assumption on the
  intermediate ghosts). `RStep.toG` lifts the existing events.
- `EvTree.EraseWPRDS … g₀ …` is `EvTree.EraseWPRD` (write nodes unchanged:
  full-frame `RStep`, or an overtaken context), except at a **load**: given
  erasure at the load's successor, some `(r', g')` with erasure,
  `RStepG g₀` and the continuation's WP. Keeping `(r, g)` is always allowed
  (`EvTree.EraseWPRD.toS`: every existing WP proof is one).
- `EvTree.eraseWPRDS_take`: the node lemma for a load that may take, from
  `Erase.take` (`SLR/TakeRuleErase.lean`) and `Erase.rStepS_take`
  (`SLR/TakeRule.lean`); the rule supplies, per read outcome, the slot, the
  floor bound `x.1 ≤ wfloor` (`AcqStep.le_wfloor` for an acquire load not
  forwarded from the thread's own write) and `g₀.acqTab.length ≤
  g.acqTab.length`.
- `ThreadRuleRXGS G`: `ThreadRuleRXG G` with `wp` an `EraseWPRDS`;
  `ThreadRuleRXG.toS` embeds the existing rules.

Phase-1 limits are unaffected: this file is the old-style (`ThreadRuleRX`)
route only; EnvG has no taking load.

Nothing imports this file.
-/
import Kraken.Promising.SLR.TakeRuleErase
import Kraken.Promising.SLR.NPSafePRule
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## `RStep` with K2 scoped at the instruction's start -/

/-- `RStep` with K2 restricted to resources whose acquire ids are allocated
in `g₀` (the instruction's start ghost). -/
def RStepG (g₀ : Ghost) (B : Time) (r : Res) (g : Ghost) (r' : Res) (g' : Ghost) (cx : Ctx) : Prop :=
  (∀ b, b ≤ B → ∀ ρ, AllocIds g₀ ρ → ∀ x, reachB ρ g' x b → reachB ρ g x b) ∧
    ∀ b, b ≤ B → cx.views.wfloor ≤ b → ∀ x, reachB r' g' x b → reachB r g x b

namespace RStepG

variable {g₀ : Ghost} {B : Time} {r r₁ r₂ r' : Res} {g g₁ g₂ g' : Ghost} {cx cx' : Ctx}

theorem refl (g₀ : Ghost) (B : Time) (r : Res) (g : Ghost) (cx : Ctx) : RStepG g₀ B r g r g cx :=
  ⟨fun _ _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem mono (h : RStepG g₀ B r g r' g' cx) (hf : cx.views.wfloor ≤ cx'.views.wfloor) : RStepG g₀ B r g r' g' cx' :=
  ⟨h.1, fun b hb hb' => h.2 b hb (Nat.le_trans hf hb')⟩

theorem trans (h₁ : RStepG g₀ B r g r₁ g₁ cx) (h₂ : RStepG g₀ B r₁ g₁ r₂ g₂ cx')
    (hf : cx.views.wfloor ≤ cx'.views.wfloor) : RStepG g₀ B r g r₂ g₂ cx' :=
  ⟨fun b hb ρ hρ x h => h₁.1 b hb ρ hρ x (h₂.1 b hb ρ hρ x h),
    fun b hb hb' x h => h₁.2 b hb (Nat.le_trans hf hb') x (h₂.2 b hb hb' x h)⟩

theorem finish (h : RStepG g₀ B r g r' g' cx) {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews}
    {st : I.State} {th : Thread I} (hth : th ∈ finishInstr t d iv st cx) :
    ∀ b, b ≤ B → max th.views.vwNew th.views.vCAP ≤ b → ∀ x, reachB r' g' x b → reachB r g x b := by
  intro b hb hf
  obtain ⟨e1, -, -, e4⟩ := finishInstr_vmono hth
  refine h.2 b hb ?_
  simp only [Views.wfloor] at hf ⊢
  omega_t

end RStepG

theorem RStep.toG {B : Time} {r r' : Res} {g g' : Ghost} {cx : Ctx} (g₀ : Ghost) (h : RStep B r g r' g' cx) :
    RStepG g₀ B r g r' g' cx :=
  ⟨fun b hb ρ _ x hx => h.1 b hb ρ x hx, h.2⟩

/-- A scoped event step (`RStepS`, scope at the current ghost `g`) is an
`RStepG g₀` step once the table has not shrunk since `g₀`. -/
theorem RStepS.toG {B : Time} {r r' : Res} {g₀ g g' : Ghost} {cx : Ctx} (h : RStepS B r g r' g' cx)
    (hlen : g₀.acqTab.length ≤ g.acqTab.length) : RStepG g₀ B r g r' g' cx :=
  ⟨fun b hb ρ hρ x hx => h.2.1 b hb ρ (fun y j hj => Nat.lt_of_lt_of_le (hρ y j hj) hlen) x hx, h.2.2⟩

/-! ## The erasure WP with taking loads -/

/-- **Erasure WP with taking loads**: `EvTree.EraseWPRD` whose load nodes
may change `(r, g)` under erasure, with `RStepG g₀` (`g₀`: the instruction's
start ghost). -/
def _root_.Kraken.Promising.EvTree.EraseWPRDS (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res)
    (T : Nat → Prop) (c : Config I) (t : Thread I) (g₀ : Ghost) {σ : Type} (Post : σ → Res → Ghost → Ctx → Prop) :
    EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l, ErAt rF T c t tid r g x.2.2 →
      ∃ r' g', ErAt rF T c t tid r' g' x.2.2 ∧ RStepG g₀ c.mem.last r g r' g' x.2.2 ∧
        EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret x.2.1) r' g' x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAt rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
        cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
          EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAt rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
            cx'.Overtaken ∨ ∃ r' g', ErAt rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' (rmwAfter A k noRet l cx') ∧
              EvTree.EraseWPRDS A tid iv rF T c t g₀ Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section WPRDS

variable {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
  {t : Thread I} {σ : Type}

/-- **Every `EraseWPRD` proof is an `EraseWPRDS` proof** (loads keep
`(r, g)`). -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRD.toS {Post : σ → Res → Ghost → Ctx → Prop} (g₀ : Ghost)
    (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRD A tid iv rF T c t Post r g cx → tree.EraseWPRDS A tid iv rF T c t g₀ Post r g cx := by
  induction tree with
  | done s => exact fun r g cx h => h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih =>
    exact fun r g cx h x hx E => ⟨r, g, E, RStepG.refl _ _ _ _ _, ih x.2.1 r g x.2.2 (h x hx)⟩
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    rcases h.1 cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    rcases (h x hx).2 new hop cx' hc E hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', E', hR, ih x.2.1 r' g' _ hw⟩

/-- The invariant of `runTree_eraseWPRDS`: memory not shrunk, and `RStepG g₀`
from the start `(r₀, g₀)`. -/
def KAccG (c : Config I) (r₀ : Res) (g₀ : Ghost) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  c.mem.last ≤ cx.mem.last ∧ RStepG g₀ c.mem.last r₀ g₀ r g cx

theorem KAccG.move {r₀ r : Res} {g₀ g : Ghost} {cx cx' : Ctx} (h : KAccG c r₀ g₀ r g cx)
    (hm : cx.mem.last ≤ cx'.mem.last) (hv : cx.VMono cx') : KAccG c r₀ g₀ r g cx' :=
  ⟨Nat.le_trans h.1 hm, h.2.mono hv.wfloor⟩

/-- **The frame with taking loads and dead branches.** -/
theorem runTree_eraseWPRDS {Post : σ → Res → Ghost → Ctx → Prop} (r₀ : Res) (g₀ : Ghost) (tree : EvTree σ) :
    ∀ (r : Res) (g : Ghost) (cx : Ctx) (s : σ) (cx' : Ctx), .ok (s, cx') ∈ runTree A tid iv cx tree →
      ErAt rF T c t tid r g cx → cx.Inv tid → tree.EraseWPRDS A tid iv rF T c t g₀ Post r g cx →
      KAccG c r₀ g₀ r g cx →
      (∃ r' g', ErAt rF T c t tid r' g' cx' ∧ Post s r' g' cx' ∧ RStepG g₀ c.mem.last r₀ g₀ r' g' cx') ∨
        cx'.Overtaken := by
  induction tree with
  | done s0 =>
    intro r g cx s cx' h E _ hw hk
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .inl ⟨r, g, E, hw, hk.2⟩
  | fault m => intro r g cx s cx' h; simp [runTree] at h
  | choose n k ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i r g cx s cx' h E hi (hw i) hk
  | load k xcl l ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    have hv := readSuccs_vmono A iv hx
    obtain ⟨r', g', E', hR, hw'⟩ := hw x hx (E.congr hm hp)
    exact ih x.2.1 r' g' x.2.2 s cx' h E' (readSuccs_inv A tid iv hx hi).1 hw'
      ⟨by rw [hm]; exact hk.1, hk.2.trans hR hv.wfloor⟩
  | store k xcl l v ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      rcases hw.1 c0 hc0 E hi hk.1 with ho | ⟨r', g', E', hR, hw'⟩
      · exact .inr (ho.dord (runTree_dord A tid iv _ c0 s cx' h))
      · obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc0 hi
        have hv := writeSuccs_vmono A tid hc0
        exact ih true r' g' c0 s cx' h E' (writeSuccs_inv A tid _ hc0 hi).1 hw'
          ⟨Nat.le_trans hk.1 hev.last_le, hk.2.trans (hR.toG g₀) hv.wfloor⟩
    · rw [List.mem_ite_nil_right] at h
      have hi' : (xclFailCtx cx l).Inv tid := (hi.of_views (c' := xclFailCtx cx l) rfl rfl rfl).1
      exact ih false r g _ s cx' h.2 (E.congr rfl rfl) hi' (hw.2 h.1)
        (hk.move (Nat.le_refl _) ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
  | fence k ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree] at h
    exact ih () r g _ s cx' h (E.congr (fenceStep_mem cx k) (fenceStep_prom cx k)) (fenceStep_inv tid hi k).1 hw
      (hk.move (by rw [fenceStep_mem]; exact Nat.le_refl _) (fenceStep_vmono cx k))
  | rmw k noRet l op ret ih =>
    intro r g cx s cx' h E hi hw hk
    simp only [runTree] at h
    have hi1 := (fenceOpt_inv tid hi A.rmwFence .sy).1
    obtain ⟨hm1, hp1⟩ := fenceOptCtx_memProm A cx
    change Except.ok (s, cx') ∈ (readSuccs A iv (fenceOptCtx A cx)
      (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet).flatMap _ at h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A iv hx
    have hi2 := (readSuccs_inv A tid iv hx hi1).1
    have E2 : ErAt rF T c t tid r g x.2.2 := E.congr (hm2.trans hm1) (hp2.trans hp1)
    have hv2 : cx.VMono x.2.2 := (fenceOptCtx_vmono A cx).trans (readSuccs_vmono A iv hx)
    have hk2 : KAccG c r₀ g₀ r g x.2.2 := hk.move (by rw [hm2, hm1]; exact Nat.le_refl _) hv2
    obtain ⟨hwn, hws⟩ := hw x hx
    obtain ⟨tr, old, c2⟩ := x
    simp only at h hwn hws E2 hi2 hk2
    split at h
    · next hop =>
      obtain ⟨hm3, hp3⟩ := fenceOptCtx_memProm A c2
      exact ih old r g _ s cx' h (E2.congr hm3 hp3) (fenceOpt_inv tid hi2 A.rmwFence .sy).1 (hwn hop)
        (hk2.move (by rw [hm3]; exact Nat.le_refl _) (fenceOptCtx_vmono A _))
    · next new hop =>
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change Except.ok (s, cx') ∈ runTree A tid iv (rmwAfter A k noRet l c3) (ret old) at h
      rcases hws new hop c3 hc3 E2 hi hk.1 with ho | ⟨r', g', E3, hR, hw3⟩
      · refine .inr (ho.dord ?_)
        refine Ctx.DOrd.trans ?_ (runTree_dord A tid iv _ _ s cx' h)
        unfold rmwAfter
        exact (Ctx.DOrd.rmwPost A c3 k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)
      · obtain ⟨hm4, hp4⟩ := rmwAfter_memProm A k noRet l c3
        have hi3 := (writeSuccs_inv A tid _ hc3 hi2).1
        have hi4 : (rmwAfter A k noRet l c3).Inv tid := by
          unfold rmwAfter
          exact (fenceOpt_inv tid (rmwPost_inv A tid hi3 k noRet l).1 A.rmwFence .sy).1
        obtain ⟨tw, hev⟩ := writeSuccs_writeEv A tid _ hc3 hi2
        have hv := (writeSuccs_vmono A tid hc3).trans (rmwAfter_vmono A k noRet l c3)
        refine ih old r' g' _ s cx' h (E3.congr hm4 hp4) hi4 hw3 ⟨?_, hk2.2.trans (hR.toG g₀) hv.wfloor⟩
        rw [hm4]; exact Nat.le_trans hk2.1 hev.last_le

/-- **The taking load node.** At every read outcome the rule either keeps
`(r, g)` or takes its slot `((l, x.1), ι, R)` of the message read, with the
floor bound and an acquire table not shrunk since `g₀`; it then continues
from the swapped resource and ghost. The taking thread must be exempt from
promise validity (`T tid`, `NPSafe`'s weak erasure). -/
theorem _root_.Kraken.Promising.EvTree.eraseWPRDS_take {g₀ : Ghost} {Post : σ → Res → Ghost → Ctx → Prop}
    {r : Res} {g : Ghost} {cx : Ctx} (hn : tid < c.threads.size) (hT : T tid)
    {k : LoadKind} {xcl : Bool} {l : Loc} {ret : Val → EvTree σ}
    (h : ∀ x ∈ readSuccs A iv cx k xcl l,
      (ret x.2.1).EraseWPRDS A tid iv rF T c t g₀ Post r g x.2.2 ∨
      ∃ (ι : PredId) (R : Res), 1 ≤ r.acq l ι ∧ (⟨(l, x.1), ι, R⟩ : Slot) ∈ g.u ∧
        x.1 ≤ x.2.2.views.wfloor ∧ g₀.acqTab.length ≤ g.acqTab.length ∧
        (ret x.2.1).EraseWPRDS A tid iv rF T c t g₀ Post (takeRes r l ι g.acqTab.length R)
          (takeGhost g l ι x.1) x.2.2) :
    (EvTree.load k xcl l ret).EraseWPRDS A tid iv rF T c t g₀ Post r g cx := by
  intro x hx E
  rcases h x hx with hk | ⟨ι, R, hι, hs, hfl, hlen, hw⟩
  · exact ⟨r, g, E, RStepG.refl _ _ _ _ _, hk⟩
  · have hn' : tid < (c.withThread tid { t with prom := x.2.2.prom } x.2.2.mem).threads.size := by
      rw [Config.withThread_size]; exact hn
    have E' : ErAt rF T c t tid (takeRes r l ι g.acqTab.length R) (takeGhost g l ι x.1) x.2.2 := by
      exact Erase.take E hn' hT hι hs
    have hR := (Erase.rStepS_take (B := c.mem.last) E hι (take_ι_lt E hn' hs hι) hs hfl).toG hlen
    exact ⟨_, _, E', hR, hw⟩

/-- An acquire load not forwarded from the thread's own write gives the
floor bound of `eraseWPRDS_take`. -/
theorem take_floor_acqLoad {cx : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs A iv cx k xcl l) (hk : (A.loadKind k).isAcquire = true)
    (hfw : ∀ f, cx.views.getFwd l = some f → f.time ≠ x.1) : x.1 ≤ x.2.2.views.wfloor :=
  (AcqStep.acqRead hx hk hfw).le_wfloor

end WPRDS

/-- **Erasure and scoped bounded reach across one instruction, with taking
loads and dead branches** (`Erase.npStepRD` for `EraseWPRDS`). -/
theorem Erase.npStepRDS {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {tid : Nat}
    {r : Res} {Post : Thread I → I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hs : NPStepBy A tid c c') (hwf' : c'.WfProm tid)
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF T c t g (Post t) r g (ctx₀ t tid c.mem)) :
    ∃ t t' st r' g' cx', c.threads[tid]? = some t ∧
      t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx' ∧
      c' = c.withThread tid t' cx'.mem ∧ Post t st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' ∧
      RStepG g c.mem.last r g r' g' cx' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hn := lt_size_of_get? ht
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨res, hr, ho⟩ := ho
    cases res with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, cx'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have E0 : ErAt rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAt
        rw [Config.withThread_self c ht]
        exact E
      rcases runTree_eraseWPRDS r g tree r g _ st cx' hr E0 (hinv.ctxInv ht _) (hwp t tree ht hex)
          ⟨Nat.le_refl _, RStepG.refl _ _ _ _ _⟩ with ⟨r', g', E', hpost, hR⟩ | ho
      · exact ⟨t, th, st, r', g', cx', ht, hth, rfl, hpost,
          Erase.withThread_prom E' hn (finishInstr_relKey hth).1, hR⟩
      · exfalso
        have hth' : (c.withThread tid th cx'.mem).threads[tid]? = some th := by
          rw [Config.withThread_get? c th cx'.mem hn, ite_eq_left rfl]
        have h1 := hwf' th hth'
        simp only [Config.withThread] at h1
        rw [ho.finish hth] at h1
        cases h1

/-! ## The rule interface -/

/-- **A rule whose loads may take** (`ThreadRuleRXG G` with `wp` an
`EraseWPRDS` at the instruction's start ghost). -/
structure ThreadRuleRXGS (G : PrepayGuard I) (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop)
    (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostR Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    G A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- Every existing rule is a rule whose loads (never) take. -/
def ThreadRuleRXG.toS {G : PrepayGuard I} {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop}
    {tid : Nat} (R : ThreadRuleRXG G A B tid) : ThreadRuleRXGS G A B tid where
  Inv := R.Inv
  done := R.done
  wp rF t tree h he hg ht hex E hinv hwf hnp :=
    EvTree.EraseWPRD.toS _ tree _ _ _ (R.wp rF t tree h he hg ht hex E hinv hwf hnp)
  prepay := R.prepay

/-- **`NPSafeP` with option (S)'s frame from a rule whose loads may take.**
The induction of `NPSafeP.of_ruleRXG`, with the step from
`Erase.npStepRDS`, whose K2 is scoped to `AllocIds g₁`. -/
theorem NPSafeP.of_ruleRXGS {G : PrepayGuard I} {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop}
    {tid : Nat} (R : ThreadRuleRXGS G A B tid) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost), R.Inv cl c r g →
      NPSafeP (model I) A B tid G (K2Scope (model I) AllocIds) n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafeP]
    exact fun m => NPSafeP.of_ruleRXGS R n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafeP]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hR⟩ := Erase.npStepRDS
        (Post := fun t => WpPostR R.Inv (cl ∧ Erase (setRes rF tid r) g₁ (fun _ => False) c₁) c₁ tid r g₁ t)
        hinv E hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E hinv hwf (hnp t ht))
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', E', hg', ?_, hnew, NPSafeP.of_ruleRXGS R (n + 1) m _ _ r' g' hinv', hacq,
        fun w hw => hown w (written_cx ht (finishInstr_relKey hth).1 hw), hR.1, ?_⟩
      · rintro ts hts ⟨i, ti, hi, htsi⟩
        refine hkeep ts hts ?_
        rw [Config.withThread_get? c₁ t' cx'.mem hn] at hi
        split at hi
        · next he' =>
          subst he'
          cases hi
          exact .inl ((finishInstr_relKey hth).1 ▸ htsi)
        · next he' => exact .inr ⟨i, ti, Ne.symm he', hi, htsi⟩
      · intro b hb hv x hx
        exact hR.finish hth b hb (hv t' ht') x hx
    · obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E hinv hnp hrel
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafeP.of_ruleRXGS R (n + 1) m _ _ r' g' h', hacq,
        fun b hb ρ _ x hx => hk1 b hb ρ x hx, hk2⟩
termination_by n m => (n, m)

/-- **Theorem 1′ for taking rules at the current guard**: `G₀` with option
(S)'s frame, the consumer of `NPSafeP.of_ruleRXGS` for a `ThreadRuleRXGS G₀`
(e.g. `ThreadRuleRX.toG₀.toS` plus taking loads). -/
theorem theorem1IIPure_G₀_S [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPure' (I := I) G₀ G₀ (K2Scope (model I) AllocIds) A fuel :=
  theorem1IIPure' guardOK_G₀ guardOK_G₀ (fun _ _ _ _ _ h => h) k2OK_allocIds A fuel

#print axioms theorem1IIPure_G₀_S
#print axioms runTree_eraseWPRDS
#print axioms EvTree.eraseWPRDS_take
#print axioms Erase.npStepRDS
#print axioms NPSafeP.of_ruleRXGS

end Kraken.Promising.SLR
