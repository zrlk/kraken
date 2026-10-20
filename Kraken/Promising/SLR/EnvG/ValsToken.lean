/-
**Part 2 of 4: the token over `Erase ∧ MemInv G`** (route (c2)). ISA-neutral.

The token runs at `modelX I (MemInvX G)`: its step conjunct *receives*
`MemInv G c₁.mem` with the erasure and must *re-establish* it at the post-step
configuration and at the promised configuration. Both follow from the own
thread's value specification `J` (kept by `EnvExt`, which fixes the own ISA
state) and its tree law `J st → exec st = some tree → tree.AllInv G J`:

- the step: `stepOne_allInv` (`npStepBy_allInv`);
- the promise: the promised message is the first access of the phase-1 tree
  (`relFulfilsLive_firstAccessFA`): a store of a `G` value, or an RMW whose
  read is a message of `c.mem` (not the own promise) mapped by `op` to the
  promised value (**`prepay_val`**).

Main results: **`NPSafeF.of_ruleRXFV`** from a `ThreadRuleRXFV` (`ThreadRuleRXF`
whose `wp`/`prepay` may assume `MemInv G c.mem`), `ThreadRuleRXFV.ofEnvGFCAdjV`.
`prepay_val` uses phase-1 single access (already a limit of the F link).
-/
import Kraken.Promising.SLR.EnvG.ValsLink
import Kraken.Promising.SLR.EnvG.RmwFailChain
import Kraken.Promising.SLR.LoadClaimFinal

namespace Kraken.Promising.SLR.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.Sim Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **The memory-value extension of the erasure**: the configuration's memory
satisfies `MemInv G`. -/
abbrev MemInvX (G : Loc → Val → Prop) : Ghost → Config I → Prop := fun _ c => MemInv G c.mem

/-! ## The prepay value lemma -/

/-- A read answer is not an own promise, and is a message of the memory. -/
theorem readSuccs_notProm {A : Arch} {iv : InstrViews} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.1 ∉ c.prom ∧ x.1 ≤ c.mem.last ∧ c.mem.read? l x.1 = some x.2.1 := by
  have hrd := (Kraken.Promising.readSuccs_read A iv hx).1
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, htr, ht⟩ := hx
  split at ht
  · cases ht
  · rename_i v hv
    by_cases hc : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
        (if A.loadKind k == .acq then c.views.vRel else 0))) (c.views.getCoh l)) || c.prom.contains t) = true
    · rw [ite_eq_left hc] at ht; cases ht
    · rw [ite_eq_right hc] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      simp only [Bool.or_eq_true, not_or, List.contains_iff_mem] at hc
      refine ⟨?_, Nat.lt_succ_iff.mp (List.mem_range.mp htr), hrd⟩
      simpa using hc.2

/-- The first access of an `AllInv G` tree writes a `G` value (store) or maps
`G` values to `G` values (RMW); a context invariant `Φ` is carried over the
fences before it. -/
theorem FirstAccess.allInv {G : Loc → Val → Prop} {S : StoreKind → Bool → Loc → Val → Prop}
    {R : Ctx → RmwKind → Bool → Loc → (Val → Option Val) → Prop} {Φ : Ctx → Prop}
    (hΦ : ∀ cx k, Φ cx → Φ (fenceStep cx k)) {σ : Type} {Q : σ → Prop} :
    ∀ (tree : EvTree σ) (cx : Ctx), FirstAccess S R cx tree → tree.AllInv G Q → Φ cx →
      (∃ k xcl l v, S k xcl l v ∧ G l v) ∨
        (∃ cx' k noRet l op, R cx' k noRet l op ∧ Φ cx' ∧ ∀ old, G l old → ∀ v, op old = some v → G l v)
  | .fence k ret, cx, h, hA, hp => FirstAccess.allInv hΦ (ret ()) (fenceStep cx k) h (hA ()) (hΦ cx k hp)
  | .store k xcl l v _, _, h, hA, _ => .inl ⟨k, xcl, l, v, h, hA.1⟩
  | .rmw k noRet l op _, cx, h, hA, hp => .inr ⟨cx, k, noRet, l, op, h, hp, fun old hg => (hA old hg).1⟩
  | .done _, _, h, _, _ => h.elim
  | .fault _, _, h, _, _ => h.elim
  | .choose _ _, _, h, _, _ => h.elim
  | .load .., _, h, _, _ => h.elim

/-- **The prepay value lemma**: the message promised under a live
fulfilment by a phase-1 tree satisfying `AllInv G` is a `G` value, if the
memory before the promise satisfies `MemInv G`. -/
theorem prepay_val {A : Arch} {tid : Nat} {G : Loc → Val → Prop} {Q : I.State → Prop} {mem : Memory}
    {t₁ : Thread I} {w : Msg}
    (hsh : ∀ tree, I.exec t₁.st = some tree → Phase1ShapeF tree)
    (hJ : ∀ tree, I.exec t₁.st = some tree → tree.AllInv G Q) (hX : MemInv G mem)
    (hrel : { t₁ with prom := t₁.prom ++ [(mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (mem.append { w with tid }).2 (mem.append { w with tid }).1) :
    G w.loc w.val := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hget : (mem.append { w with tid }).1.get? (mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hFA := relFulfilsLive_firstAccessFA (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl rfl
    (hsh tree hex) hrfl
  let P := t₁.prom ++ [(mem.append { w with tid }).2]
  let Φ : Ctx → Prop := fun cx => cx.prom = P ∧ cx.mem = (mem.append { w with tid }).1
  have hΦ : ∀ cx k, Φ cx → Φ (fenceStep cx k) := fun cx k ⟨hp, hm⟩ =>
    ⟨by rw [fenceStep_prom]; exact hp, by rw [fenceStep_mem]; exact hm⟩
  have hA := FirstAccess.allInv (G := G) (Q := Q) hΦ tree _ hFA (hJ tree hex) (show Φ _ from ⟨rfl, rfl⟩)
  rcases hA with
      ⟨_, _, l, v, hS, hG⟩ | ⟨cxN, _, noRet, l, op, hRR, ⟨hp, hm⟩, hG⟩
  · obtain ⟨hl, hv, -⟩ := hS
    subst hl hv; exact hG
  · obtain ⟨hl, -, -, x, hx, hop, -⟩ := hRR
    subst hl
    obtain ⟨hmF, hpF⟩ := fenceOptCtx_memProm (A := A) cxN
    obtain ⟨hnp, hle, hrd⟩ := readSuccs_notProm hx
    rw [hpF, hp] at hnp
    rw [hmF, hm] at hle hrd
    have hne : x.1 ≠ mem.last + 1 :=
      fun e => hnp (List.mem_append_right _ (by rw [e]; exact List.mem_singleton_self _))
    rw [Memory.last_append] at hle
    have hle' : x.1 ≤ mem.last := by omega_t
    rw [(Memory.Prefix.append mem _).read? hle'] at hrd
    exact hG x.2.1 (hX.read? hrd) w.val hop

/-! ## The rule and the token -/

/-- **A `ThreadRuleRXF` whose `wp`/`prepay` may assume `MemInv G` of the
configuration's memory**, with the phase-1 shape of the own tree (for
`prepay_val`) and antitonicity in the closure flag (the token's closure flag
carries the extension). -/
structure ThreadRuleRXFV (A : Arch) (G : Loc → Val → Prop)
    (B : Config I → (modelX I (MemInvX G)).R → (modelX I (MemInvX G)).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  mono : ∀ {cl cl' : Prop} {c : Config I} {r : Res} {g : Ghost}, (cl' → cl) → Inv cl c r g → Inv cl' c r g
  done : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}, Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    cl → c.Done tid → B c r g
  shape : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I),
    Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t →
    Erase (setRes rF tid r) g (fun _ => True) c → (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    ∀ tree, I.exec t.st = some tree → Phase1ShapeF tree
  wp : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g →
    c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → MemInv G c.mem → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostRF Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c₀ r g₀ → EnvExt tid c₀ c → g₀.Le g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid r) g (fun _ => True) c → MemInv G c.mem → c.MachInv →
    (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- The own thread satisfies its value invariant `J`. -/
def OwnJ (tid : Nat) (J : I.State → Prop) (c : Config I) : Prop := ∃ t, c.threads[tid]? = some t ∧ J t.st

/-- `OwnJ` is kept by `EnvExt` (which fixes the own ISA state). -/
theorem OwnJ.envExt {tid : Nat} {J : I.State → Prop} {c c₁ : Config I} (h : OwnJ tid J c) (he : EnvExt tid c c₁) :
    ∀ t, c₁.threads[tid]? = some t → J t.st := by
  obtain ⟨t₀, ht₀, hJ⟩ := h
  obtain ⟨ps, ht₁, -⟩ := he.2.2 t₀ ht₀
  intro t ht
  rw [ht₁] at ht
  cases ht
  exact hJ

/-- **One own instruction step keeps `J` and `MemInv G`** (`stepOne_allInv`). -/
theorem npStepBy_allInv {A : Arch} {tid : Nat} {G : Loc → Val → Prop} {J : I.State → Prop}
    (hJ : ∀ st tree, J st → I.exec st = some tree → tree.AllInv G J) {c c' : Config I}
    (hs : NPStepBy A tid c c') (hJc : ∀ t, c.threads[tid]? = some t → J t.st) (hX : MemInv G c.mem) :
    MemInv G c'.mem ∧ OwnJ tid J c' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hst, ho, heq⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨hJo, hXo⟩ := stepOne_allInv A hst ho (fun tree hex => hJ _ tree (hJc t ht) hex) hX
  refine ⟨hXo, o.thread, ?_, hJo⟩
  rw [Config.withThread_get? c _ _ (lt_size_of_get? ht), ite_eq_left rfl]

/-- **`NPSafeF` over `Erase ∧ MemInv G` from a `ThreadRuleRXFV`** and the own
thread's value specification `J` (its tree law `hJ`). The structure of
`NPSafeF.of_ruleRXF`; the extension is re-established by `npStepBy_allInv`
(step) and `prepay_val` with `MemInv.append` (promise). -/
theorem NPSafeF.of_ruleRXFV {A : Arch} {G : Loc → Val → Prop}
    {B : Config I → (modelX I (MemInvX G)).R → (modelX I (MemInvX G)).Ghost → Prop} {tid : Nat}
    {J : I.State → Prop} (R : ThreadRuleRXFV A G B tid)
    (hJ : ∀ st tree, J st → I.exec st = some tree → tree.AllInv G J) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (modelX I (MemInvX G)).R) (g : (modelX I (MemInvX G)).Ghost),
      R.Inv cl c r g → OwnJ tid J c →
      NPSafeF (modelX I (MemInvX G)) A B tid n m cl c r g
  | 0, _, _, _, _, _, _, _ => by simp [NPSafeF]
  | n + 1, 0, cl, c, r, g, h, hj => by
    rw [NPSafeF]
    exact fun m => NPSafeF.of_ruleRXFV R hJ n m cl c r g h hj
  | n + 1, m + 1, cl, c, r, g, h, hj => by
    rw [NPSafeF]
    intro c₁ g₁ he hg
    have hJ₁ := hj.envExt he
    refine ⟨R.done h he hg, fun rF c' E hs hinv hwf hwf' hnp hful => ?_,
      fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨hX', hj'⟩ := npStepBy_allInv hJ hs hJ₁ E.2
      obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E', hR⟩ := Erase.npStepRD
        (Post := fun t => WpPostRF R.Inv (cl ∧ Erase (setRes rF tid r) g₁ (fun _ => False) c₁) c₁ tid r g₁ t)
        hinv E.1 hs hwf' (fun t tree ht hex => R.wp rF t tree h he hg ht hex E.1 E.2 hinv hwf (hnp t ht))
      have hn := lt_size_of_get? ht
      have ht' : (c₁.withThread tid t' cx'.mem).threads[tid]? = some t' := by
        rw [Config.withThread_get? c₁ t' cx'.mem hn, ite_eq_left rfl]
      rcases hpost with ⟨ts, hts, hpd, hts'⟩ | hpost
      · exact absurd ((finishInstr_relKey hth).1 ▸ hts') (hful t t' ht ht' ts hts hpd)
      obtain ⟨hg', hkeep, hnew, hacq, hown, hfin⟩ := hpost
      have hdead : t'.hasDeadPromise cx'.mem = false := by
        have := hwf' t' ht'
        simpa [Config.withThread] using this
      have hinv' : R.Inv (cl ∧ (Erase (setRes rF tid r) g₁ (fun _ => False) c₁ ∧ MemInv G c₁.mem)) _ r' g' :=
        R.mono (fun hc => ⟨hc.1, hc.2.1⟩) (hfin t' hth hdead)
      refine ⟨r', g', ⟨E', hX'⟩, hg', ?_, hnew, NPSafeF.of_ruleRXFV R hJ (n + 1) m _ _ r' g' hinv' hj', hacq,
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
    · have hGw : G w.loc w.val :=
        prepay_val (R.shape rF t₁ h he hg ht₁ E.1 hnp) (fun tree hex => hJ _ tree (hJ₁ t₁ ht₁) hex) E.2 hrel
      obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        R.prepay rF t₁ w h he hg ht₁ E.1 E.2 hinv hnp hrel
      have hj' : OwnJ tid J (PromisedBy c₁ tid t₁ w) :=
        ⟨{ t₁ with prom := t₁.prom ++ [(c₁.mem.append { w with tid }).2] },
          by rw [Config.withThread_get? c₁ _ _ (lt_size_of_get? ht₁), ite_eq_left rfl], hJ₁ t₁ ht₁⟩
      have h'' : R.Inv (cl ∧ (Erase (setRes rF tid r) g₁ (fun _ => False) c₁ ∧ MemInv G c₁.mem))
          (PromisedBy c₁ tid t₁ w) r' g' := R.mono (fun hc => ⟨hc.1, hc.2.1⟩) h'
      exact ⟨r', g', ⟨E', E.2.append (w := { w with tid }) hGw⟩, hg', hpend, hkeep, hnew,
        NPSafeF.of_ruleRXFV R hJ (n + 1) m _ _ r' g' h'' hj', hacq, hk1, hk2⟩
termination_by n m => (n, m)

/-- **The value rule link**: a `ThreadRuleRXFV` from `LinkHypsFCAdjV`
(`ThreadRuleRXF.ofEnvGFCAdj` over the value-restricted env). -/
def ThreadRuleRXFV.ofEnvGFCAdjV {A : Arch} {tid : Nat} {pl : Plan} {G : Loc → Val → Prop}
    {Q : I.State → State I → Prop} {B : Config I → (modelX I (MemInvX G)).R → (modelX I (MemInvX G)).Ghost → Prop}
    (H : LinkHypsFCAdjV A tid pl G Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRXFV A G B tid where
  Inv := InvGF tid pl Q
  mono hcl h := InvGF.mono_cl hcl h
  done h he hg hcl hd := InvGF.done hB h he hg hcl hd
  shape rF t h he hg ht E hnp tree hex :=
    let ⟨σ, hQ⟩ := InvGF.q_at rF t h he hg ht E hnp
    H.shape _ σ hQ tree hex
  wp rF t tree h he hg ht hex E hX hm _ hnp := InvGF.wpFCAdjV H rF t tree h he hg ht hex E hm hX hnp
  prepay rF t₁ w h he hg ht E _ hm hnp hrel := InvGF.prepayFCAdjV H rF t₁ w h he hg ht E hm hnp hrel

end Kraken.Promising.SLR.EnvG.Vals

#print axioms Kraken.Promising.SLR.EnvG.Vals.NPSafeF.of_ruleRXFV
