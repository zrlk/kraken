/-
**Layer R.** The thread-rule level over an extended
erasure `Erase ∧ X` (`modelX I X`, `SLR/LoadClaimChain.lean`), with loads
that may take (option (S)'s frame), and the ticket dispenser's hand-out
wired into K1/K2.

`SLR/TakeRuleThread.lean` gives `NPSafeP (model I) … (K2Scope AllocIds)` from
a `ThreadRuleRXGS`, whose erasure WP (`EvTree.EraseWPRDS`) carries the existing
`Erase` at every node. A thread of a ticket program must be `NPSafeP` at
`modelT D` (`theorem1IIPureT`, `SLR/LoadClaimFinal.lean`), i.e. keep the
extension `X` across its own steps. Here, generically in `X`:

- `ErAtX X`: `ErAt` together with `X` at the node's configuration;
- `EvTree.EraseWPRDSX X`: `EraseWPRDS` with `ErAtX X` at every node (copy);
  `EvTree.EraseWPRDS.toX` embeds the existing WP when `X` is kept for free
  (`X` constant in the ghost and memory, e.g. `X = ⊤`);
- `runTree_eraseWPRDSX`, `Erase.npStepRDSX`: the frame of one instruction;
- `ThreadRuleRXGSX G X`: `ThreadRuleRXGS G` whose erasures are `Erase ∧ X`;
- **`NPSafeP.of_ruleRXGSX`**: `NPSafeP (modelX I X) … (K2Scope AllocIds)`;
- **`theorem1IIPureX_G₀_S`**: the consumer (`theorem1IIPureX'` at `G₀`, frame
  `K2Scope AllocIds`), for every `X` with a promise law;
- `ThreadRuleRXGSXE` / **`NPSafeP.of_ruleRXGSXE`**: the variant that checks
  `X` only at instruction boundaries (after `finishInstr`, `WpPostRX`), over
  the existing WP `EraseWPRDS`; it needs no `XMem`, so `X` may mention thread
  states (e.g. a per-thread "ticket taken" fact, which a bound on the ticket
  values needs).

Ticket-specific (the dispenser `D`, `SLR/LoadClaim.lean`):

- `RStep.hand`: an RMW's `RStep` followed by the hand-out of `tk n` is an
  `RStep` (K1: `reachB_hand_own`; K2, full: `reachB_hand_frame`).
- `ErAtX` for `X := TicketInv D ∧ Y` (`Y` any memory-only predicate): the
  frame of the dispenser under the take (`TicketInv.take`) is in
  `EnvG/TicketLink.lean`, where the ghost steps are explicit.

Requirement on `X` for the node-level form: it depends on the configuration
only through its memory (`XMem X`), as `ExtLaws.mem`.

**Open:** `TicketInv` alone does not bound the value an
`ldadda` reads, so `EraseT.rmwHand`'s `old.toNat < D.N` and
`fresh_of_atomic`'s `new.toNat = old.toNat + 1` (no wraparound) cannot be
discharged by a per-thread rule: an erased environment may hold a `next`
message of any pure value. A counting extension is needed beside
`TicketInv`.

Nothing imports this file.
-/
import Kraken.Promising.SLR.TakeRuleThread
import Kraken.Promising.SLR.LoadClaimFinal
import Kraken.Promising.SLR.LoadClaimErase

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- `X` depends on the configuration only through its memory. -/
def XMem (X : Ghost → Config I → Prop) : Prop := ∀ g (c c' : Config I), c.mem = c'.mem → X g c → X g c'

theorem Config.withThread_mem' (c : Config I) (tid : Nat) (t : Thread I) (m : Memory) :
    (c.withThread tid t m).mem = m := rfl

/-! ## Erasure with an extension, along an instruction -/

/-- `ErAt` with the extension `X` at the node's configuration. -/
def ErAtX (X : Ghost → Config I → Prop) (rF : Nat → Res) (T : Nat → Prop) (c : Config I) (t : Thread I)
    (tid : Nat) (r : Res) (g : Ghost) (cx : Ctx) : Prop :=
  ErAt rF T c t tid r g cx ∧ X g (c.withThread tid { t with prom := cx.prom } cx.mem)

theorem ErAtX.congr {X : Ghost → Config I → Prop} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
    {t : Thread I} {tid : Nat} {r : Res} {g : Ghost} {cx cx' : Ctx} (h : ErAtX X rF T c t tid r g cx)
    (hm : cx'.mem = cx.mem) (hp : cx'.prom = cx.prom) : ErAtX X rF T c t tid r g cx' := by
  unfold ErAtX ErAt at *; rw [hm, hp]; exact h

theorem ErAtX.erAt {X : Ghost → Config I → Prop} {rF : Nat → Res} {T : Nat → Prop} {c : Config I}
    {t : Thread I} {tid : Nat} {r : Res} {g : Ghost} {cx : Ctx} (h : ErAtX X rF T c t tid r g cx) :
    ErAt rF T c t tid r g cx := h.1

/-- **Erasure WP with taking loads, over `Erase ∧ X`**: `EvTree.EraseWPRDS`
with `ErAtX X` in place of `ErAt` (verbatim otherwise). -/
def _root_.Kraken.Promising.EvTree.EraseWPRDSX (X : Ghost → Config I → Prop) (A : Arch) (tid : Nat)
    (iv : InstrViews) (rF : Nat → Res) (T : Nat → Prop) (c : Config I) (t : Thread I) (g₀ : Ghost) {σ : Type}
    (Post : σ → Res → Ghost → Ctx → Prop) : EvTree σ → Res → Ghost → Ctx → Prop
  | .done s, r, g, cx => Post s r g cx
  | .fault _, _, _, _ => True
  | .choose _ k, r, g, cx => ∀ i, EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (k i) r g cx
  | .load k xcl l ret, r, g, cx => ∀ x ∈ readSuccs A iv cx k xcl l, ErAtX X rF T c t tid r g x.2.2 →
      ∃ r' g', ErAtX X rF T c t tid r' g' x.2.2 ∧ RStepG g₀ c.mem.last r g r' g' x.2.2 ∧
        EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret x.2.1) r' g' x.2.2
  | .store k xcl l v ret, r, g, cx =>
      (∀ cx' ∈ writeSuccs A tid (iv.forStore cx.stores) cx k xcl l v (if xcl then cx.views.xclb.map (·.1) else none) 0 (if xcl then (cx.views.xclb.map (·.2.1)).getD 0 else 0),
        ErAtX X rF T c t tid r g cx → cx.Inv tid → c.mem.last ≤ cx.mem.last →
        cx'.Overtaken ∨ ∃ r' g', ErAtX X rF T c t tid r' g' cx' ∧ RStep c.mem.last r g r' g' cx' ∧
          EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret true) r' g' cx') ∧
      (xcl = true → EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret false) r g (xclFailCtx cx l))
  | .fence k ret, r, g, cx => EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret ()) r g (fenceStep cx k)
  | .rmw k noRet l op ret, r, g, cx =>
      ∀ x ∈ readSuccs A iv (fenceOptCtx A cx) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet,
        (op x.2.1 = none → EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret x.2.1) r g (fenceOptCtx A x.2.2)) ∧
        ∀ new, op x.2.1 = some new →
          ∀ cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0),
            ErAtX X rF T c t tid r g x.2.2 → cx.Inv tid → c.mem.last ≤ cx.mem.last →
            cx'.Overtaken ∨ ∃ r' g', ErAtX X rF T c t tid r' g' cx' ∧
              RStep c.mem.last r g r' g' (rmwAfter A k noRet l cx') ∧
              EvTree.EraseWPRDSX X A tid iv rF T c t g₀ Post (ret x.2.1) r' g' (rmwAfter A k noRet l cx')

section WPRDSX

variable {X : Ghost → Config I → Prop} {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res}
  {T : Nat → Prop} {c : Config I} {t : Thread I} {σ : Type}

/-- **The frame with taking loads and dead branches, over `Erase ∧ X`**
(`runTree_eraseWPRDS`, verbatim with `ErAtX`). -/
theorem runTree_eraseWPRDSX {Post : σ → Res → Ghost → Ctx → Prop} (r₀ : Res) (g₀ : Ghost) (tree : EvTree σ) :
    ∀ (r : Res) (g : Ghost) (cx : Ctx) (s : σ) (cx' : Ctx), .ok (s, cx') ∈ runTree A tid iv cx tree →
      ErAtX X rF T c t tid r g cx → cx.Inv tid → tree.EraseWPRDSX X A tid iv rF T c t g₀ Post r g cx →
      KAccG c r₀ g₀ r g cx →
      (∃ r' g', ErAtX X rF T c t tid r' g' cx' ∧ Post s r' g' cx' ∧ RStepG g₀ c.mem.last r₀ g₀ r' g' cx') ∨
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
    have E2 : ErAtX X rF T c t tid r g x.2.2 := E.congr (hm2.trans hm1) (hp2.trans hp1)
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

/-- **Monotonicity of the WP in its postcondition.** -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRDSX.mono {g₀ : Ghost} {Post Q : σ → Res → Ghost → Ctx → Prop}
    (hPQ : ∀ s r g cx, Post s r g cx → Q s r g cx) (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRDSX X A tid iv rF T c t g₀ Post r g cx → tree.EraseWPRDSX X A tid iv rF T c t g₀ Q r g cx := by
  induction tree with
  | done s => exact fun r g cx h => hPQ s r g cx h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih =>
    intro r g cx h x hx E
    obtain ⟨r', g', E', hR, hw⟩ := h x hx E
    exact ⟨r', g', E', hR, ih x.2.1 r' g' x.2.2 hw⟩
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

/-- **The existing WP is an `EraseWPRDSX` WP for an extension kept by every
ghost and memory** (e.g. `X = ⊤`). -/
theorem _root_.Kraken.Promising.EvTree.EraseWPRDS.toX {g₀ : Ghost} {Post : σ → Res → Ghost → Ctx → Prop}
    (hX : ∀ g (c' : Config I), X g c') (tree : EvTree σ) :
    ∀ r g cx, tree.EraseWPRDS A tid iv rF T c t g₀ Post r g cx → tree.EraseWPRDSX X A tid iv rF T c t g₀ Post r g cx := by
  induction tree with
  | done s => exact fun r g cx h => h
  | fault _ => exact fun _ _ _ _ => trivial
  | choose n k ih => exact fun r g cx h i => ih i r g cx (h i)
  | load k xcl l ret ih =>
    intro r g cx h x hx E
    obtain ⟨r', g', E', hR, hw⟩ := h x hx E.1
    exact ⟨r', g', ⟨E', hX _ _⟩, hR, ih x.2.1 r' g' x.2.2 hw⟩
  | store k xcl l v ret ih =>
    refine fun r g cx h => ⟨fun cx' hc E hi hm => ?_, fun hx => ih false r g _ (h.2 hx)⟩
    rcases h.1 cx' hc E.1 hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', ⟨E', hX _ _⟩, hR, ih true r' g' cx' hw⟩
  | fence k ret ih => exact fun r g cx h => ih () r g _ h
  | rmw k noRet l op ret ih =>
    refine fun r g cx h x hx => ⟨fun hop => ih x.2.1 r g _ ((h x hx).1 hop), fun new hop cx' hc E hi hm => ?_⟩
    rcases (h x hx).2 new hop cx' hc E.1 hi hm with ho | ⟨r', g', E', hR, hw⟩
    · exact .inl ho
    · exact .inr ⟨r', g', ⟨E', hX _ _⟩, hR, ih x.2.1 r' g' _ hw⟩

end WPRDSX

/-- **Erasure with the extension and scoped bounded reach across one
instruction** (`Erase.npStepRDS` over `Erase ∧ X`). -/
theorem Erase.npStepRDSX {X : Ghost → Config I → Prop} (hXm : XMem X) {A : Arch} {rF : Nat → Res} {g : Ghost}
    {T : Nat → Prop} {c c' : Config I} {tid : Nat} {r : Res} {Post : Thread I → I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hX : X g c) (hs : NPStepBy A tid c c')
    (hwf' : c'.WfProm tid)
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWPRDSX X A tid (instrViews t (I.deps t.st)) rF T c t g (Post t) r g (ctx₀ t tid c.mem)) :
    ∃ t t' st r' g' cx', c.threads[tid]? = some t ∧
      t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx' ∧
      c' = c.withThread tid t' cx'.mem ∧ Post t st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' ∧ X g' c' ∧
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
      have E0 : ErAtX X rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAtX ErAt
        rw [Config.withThread_self c ht]
        exact ⟨E, hX⟩
      rcases runTree_eraseWPRDSX r g tree r g _ st cx' hr E0 (hinv.ctxInv ht _) (hwp t tree ht hex)
          ⟨Nat.le_refl _, RStepG.refl _ _ _ _ _⟩ with ⟨r', g', ⟨E', hX'⟩, hpost, hR⟩ | ho
      · exact ⟨t, th, st, r', g', cx', ht, hth, rfl, hpost,
          Erase.withThread_prom E' hn (finishInstr_relKey hth).1, hXm g' (c.withThread tid { t with prom := cx'.prom } cx'.mem) (c.withThread tid th cx'.mem) rfl hX', hR⟩
      · exfalso
        have hth' : (c.withThread tid th cx'.mem).threads[tid]? = some th := by
          rw [Config.withThread_get? c th cx'.mem hn, ite_eq_left rfl]
        have h1 := hwf' th hth'
        simp only [Config.withThread] at h1
        rw [ho.finish hth] at h1
        cases h1

/-! ## The rule interface -/

/-- **A rule whose loads may take, over the extended erasure `Erase ∧ X`**
(`ThreadRuleRXGS G` with `Erase ∧ X` in every erasure hypothesis and
conclusion, and an `EraseWPRDSX X` WP). -/
structure ThreadRuleRXGSX (G : PrepayGuard I) (X : Ghost → Config I → Prop) (A : Arch)
    (B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → X g c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRDSX X A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostR Inv (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ X g c)) c tid r g t) r g
      (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → X g c → c.MachInv →
    (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    G A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ X g' (PromisedBy c tid t₁ w) ∧
      g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ X g c)) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`NPSafeP` over the extended erasure, with option (S)'s frame, from a
rule whose loads may take** (`NPSafeP.of_ruleRXGS` at `modelX I X`). -/
theorem NPSafeP.of_ruleRXGSX' {G : PrepayGuard I} {X : Ghost → Config I → Prop} (hXm : XMem X) {A : Arch}
    {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat} (R : ThreadRuleRXGSX G X A B tid)
    {K : K2Frame (modelX I X)}
    (hK : ∀ g₁ g' B, (∀ b, b ≤ B → ∀ ρ, AllocIds g₁ ρ → ∀ x, reachB ρ g' x b → reachB ρ g₁ x b) → K g₁ g' B) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (modelX I X).R) (g : (modelX I X).Ghost), R.Inv cl c r g →
      NPSafeP (modelX I X) A B tid G K n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafeP]
    exact fun m => NPSafeP.of_ruleRXGSX' hXm R hK n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafeP]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hX', hR⟩ := Erase.npStepRDSX hXm
        (Post := fun t => WpPostR R.Inv (cl ∧ (Erase (setRes rF tid r) g₁ (fun _ => False) c₁ ∧ X g₁ c₁)) c₁ tid
          r g₁ t)
        hinv E.1 E.2 hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E.1 E.2 hinv hwf (hnp t ht))
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', ⟨E', hX'⟩, hg', ?_, hnew, NPSafeP.of_ruleRXGSX' hXm R hK (n + 1) m _ _ r' g' hinv', hacq,
        fun w hw => hown w (written_cx ht (finishInstr_relKey hth).1 hw), hK _ _ _ hR.1, ?_⟩
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
    · obtain ⟨r', g', E', hX', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E.1 E.2 hinv hnp hrel
      exact ⟨r', g', ⟨E', hX'⟩, hg', hpend, hkeep, hnew, NPSafeP.of_ruleRXGSX' hXm R hK (n + 1) m _ _ r' g' h', hacq,
        hK _ _ _ fun b hb ρ _ x hx => hk1 b hb ρ x hx, hk2⟩
termination_by n m => (n, m)

/-- `NPSafeP.of_ruleRXGSX'` at option (S)'s frame `K2Scope AllocIds`. -/
theorem NPSafeP.of_ruleRXGSX {G : PrepayGuard I} {X : Ghost → Config I → Prop} (hXm : XMem X) {A : Arch}
    {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat} (R : ThreadRuleRXGSX G X A B tid)
    (n m : Nat) (cl : Prop) (c : Config I) (r : (modelX I X).R) (g : (modelX I X).Ghost) (h : R.Inv cl c r g) :
    NPSafeP (modelX I X) A B tid G (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSX' hXm R (fun _ _ _ h => h) n m cl c r g h

/-- **Theorem 1′ over `Erase ∧ X` for taking rules at the current guard**
(`theorem1IIPureX'` at `G₀` with option (S)'s frame): the consumer of
`NPSafeP.of_ruleRXGSX`. -/
theorem theorem1IIPureX_G₀_S {X : Ghost → Config I → Prop} {Fresh : Memory → Msg → Prop}
    (hX : XPromiseLaw X Fresh) [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIPureX' (I := I) G₀ G₀ (K2Scope (model I) AllocIds) X Fresh A fuel :=
  theorem1IIPureX' hX guardOK_G₀ guardOK_G₀ (fun _ _ _ _ _ h => h) k2OK_allocIds A fuel

/-! ## Variant: the extension checked at instruction boundaries only

`ErAtX` evaluates `X` at the nodes of an instruction with the thread's state
of the instruction's *start* (`c.withThread tid { t with prom := cx.prom }
cx.mem`). An extension that mentions thread states (e.g. "thread `j` has
taken its ticket", a program-counter fact) does not hold there in general.
`ThreadRuleRXGSXE` asks for `X` only after the instruction, at the actual
`c.withThread tid t' cx'.mem` (`t'` from `finishInstr`), with the existing WP
`EraseWPRDS`; it needs no `XMem`. -/

/-- The post-condition of `ThreadRuleRXGSXE.wp`: `WpPostR` and the extension
after every live `finishInstr` outcome. -/
def WpPostRX (X : Ghost → Config I → Prop) (Inv : Prop → Config I → Res → Ghost → Prop) (cl : Prop) (c : Config I)
    (tid : Nat) (r : Res) (g : Ghost) (t : Thread I) : I.State → Res → Ghost → Ctx → Prop :=
  fun st r' g' cx' => WpPostR Inv cl c tid r g t st r' g' cx' ∧
    ∀ t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx', t'.hasDeadPromise cx'.mem = false →
      X g' (c.withThread tid t' cx'.mem)

/-- **A rule whose loads may take, over `Erase ∧ X`, with `X` at instruction
boundaries** (`ThreadRuleRXGSX` with the existing WP and `X` in its post). -/
structure ThreadRuleRXGSXE (G : PrepayGuard I) (X : Ghost → Config I → Prop) (A : Arch)
    (B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → X g c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRDS A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t g
      (WpPostRX X Inv (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ X g c)) c tid r g t) r g
      (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → X g c → c.MachInv →
    (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    G A tid (c.mem.append { w with tid }).2 { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ X g' (PromisedBy c tid t₁ w) ∧
      g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ (Erase (setRes rF tid r) g (fun _ => False) c ∧ X g c)) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`NPSafeP` over `Erase ∧ X` from a rule checking `X` at instruction
boundaries** (no `XMem`), for any frame `K` implied by option (S)'s. -/
theorem NPSafeP.of_ruleRXGSXE' {G : PrepayGuard I} {X : Ghost → Config I → Prop} {A : Arch}
    {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat} (R : ThreadRuleRXGSXE G X A B tid)
    {K : K2Frame (modelX I X)}
    (hK : ∀ g₁ g' B, (∀ b, b ≤ B → ∀ ρ, AllocIds g₁ ρ → ∀ x, reachB ρ g' x b → reachB ρ g₁ x b) → K g₁ g' B) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (modelX I X).R) (g : (modelX I X).Ghost), R.Inv cl c r g →
      NPSafeP (modelX I X) A B tid G K n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafeP]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafeP]
    exact fun m => NPSafeP.of_ruleRXGSXE' R hK n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafeP]
    intro c₁ g₁ he hg
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, ⟨hpost, hXf⟩, E', hR⟩ := Erase.npStepRDS
        (Post := fun t => WpPostRX X R.Inv (cl ∧ (Erase (setRes rF tid r) g₁ (fun _ => False) c₁ ∧ X g₁ c₁)) c₁ tid
          r g₁ t)
        hinv E.1 hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E.1 E.2 hinv hwf (hnp t ht))
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' := hfin t' hth hdead
      refine ⟨r', g', ⟨E', hXf t' hth hdead⟩, hg', ?_, hnew, NPSafeP.of_ruleRXGSXE' R hK (n + 1) m _ _ r' g' hinv',
        hacq, fun w hw => hown w (written_cx ht (finishInstr_relKey hth).1 hw), hK _ _ _ hR.1, ?_⟩
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
    · obtain ⟨r', g', E', hX', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E.1 E.2 hinv hnp hrel
      exact ⟨r', g', ⟨E', hX'⟩, hg', hpend, hkeep, hnew, NPSafeP.of_ruleRXGSXE' R hK (n + 1) m _ _ r' g' h', hacq,
        hK _ _ _ fun b hb ρ _ x hx => hk1 b hb ρ x hx, hk2⟩
termination_by n m => (n, m)

/-- `NPSafeP.of_ruleRXGSXE'` at option (S)'s frame `K2Scope AllocIds`. -/
theorem NPSafeP.of_ruleRXGSXE {G : PrepayGuard I} {X : Ghost → Config I → Prop} {A : Arch}
    {B : Config I → (modelX I X).R → (modelX I X).Ghost → Prop} {tid : Nat} (R : ThreadRuleRXGSXE G X A B tid)
    (n m : Nat) (cl : Prop) (c : Config I) (r : (modelX I X).R) (g : (modelX I X).Ghost) (h : R.Inv cl c r g) :
    NPSafeP (modelX I X) A B tid G (K2Scope (model I) AllocIds) n m cl c r g :=
  NPSafeP.of_ruleRXGSXE' R (fun _ _ _ h => h) n m cl c r g h

/-- A memory-only extension checked along the nodes gives it at the end: every
`ThreadRuleRXGSX` with `XMem X` whose WP is `EraseWPRDS` plus `X` after is a
`ThreadRuleRXGSXE` (the converse direction of the two interfaces is the
content of `Erase.npStepRDSX`). -/
theorem wpPostRX_of_mem {X : Ghost → Config I → Prop} (hXm : XMem X) {Inv : Prop → Config I → Res → Ghost → Prop}
    {cl : Prop} {c : Config I} {tid : Nat} {r : Res} {g : Ghost} {t : Thread I} {st : I.State} {r' : Res}
    {g' : Ghost} {cx' : Ctx} (h : WpPostR Inv cl c tid r g t st r' g' cx')
    (hX : X g' (c.withThread tid { t with prom := cx'.prom } cx'.mem)) :
    WpPostRX X Inv cl c tid r g t st r' g' cx' :=
  ⟨h, fun t' _ _ => hXm g' (c.withThread tid { t with prom := cx'.prom } cx'.mem) (c.withThread tid t' cx'.mem) rfl hX⟩

/-! ## The hand-out in K1/K2 -/

namespace Dispenser

variable {D : Dispenser}

/-- **An `RStep` followed by the hand-out of `tk n` is an `RStep`** (the
dispenser slot `s₀` of the ghost `g'` after the RMW holds `tk n`, and `ιD` is
an update id of `o` there): K1 by `reachB_hand_own`, full K2 by
`reachB_hand_frame`. -/
theorem RStep.hand {B : Time} {r r' : Res} {g g' : Ghost} {cx : Ctx} (h : RStep B r g r' g' cx) {n : Nat}
    {s₀ : Slot} (h₀ : s₀ ∈ g'.u) (hd : D.IsDisp s₀) (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g'.upd D.o) :
    RStep B r g (r'.op (tok D.o (D.tk n))) (D.handGhost g' n) cx :=
  ⟨fun b hb ρ x hx => h.1 b hb ρ x (reachB_hand_frame h₀ hd h1 hU hx),
    fun b hb hf x hx => h.2 b hb hf x (reachB_hand_own h₀ hd h1 hU hx)⟩

/-- `mayWrite` (the `acqLe` conjunct) across an RMW and the hand-out. -/
theorem mayWrite_hand' {g' : Ghost} {n : Nat} {s₀ : Slot} (h₀ : s₀ ∈ g'.u) (hd : D.IsDisp s₀)
    (h1 : s₀.res.acq D.o (D.tk n) = 1) (hU : D.ιD ∈ g'.upd D.o) {r r' : Res} {g : Ghost}
    (hmw : ∀ x, mayWrite r' g' x → mayWrite r g x) :
    ∀ x, mayWrite (r'.op (tok D.o (D.tk n))) (D.handGhost g' n) x → mayWrite r g x :=
  fun x hx => hmw x (mayWrite_hand h₀ hd h1 hU hx)

end Dispenser

#print axioms runTree_eraseWPRDSX
#print axioms Erase.npStepRDSX
#print axioms NPSafeP.of_ruleRXGSX
#print axioms theorem1IIPureX_G₀_S
#print axioms NPSafeP.of_ruleRXGSXE
#print axioms Dispenser.RStep.hand

end Kraken.Promising.SLR
