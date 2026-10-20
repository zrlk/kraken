/-
Whole-thread environment (`EnvG`): **the rule link**: a `ThreadRuleRX` from a
thread-local invariant `Q` of `EnvG`. ISA-neutral; the AArch64 instance
(`Q` = `Safely (instrStepEnv EnvG)`) is `EnvG/A64Link.lean`.

`Q st σ` relates the thread's ISA state to an `EnvG` state. `LinkHyps`:

- `valid`: the plan is valid;
- `shape`: the thread's trees are phase-1 (`Phase1Shape`: deterministic
  single access, **releases are stores**);
- `link`: every live tree judgment of `EnvG` whose postcondition contains
  `Q` holds of the thread's tree from a `Q`-related env state (for AArch64,
  `exec_treeJLive_of_instrStepEnv'`).

The invariant `InvG` is the core (`CoreAt`: `EnvRel`, pending marks below
`|M|`, the in-flight facts) and `Q` at some env state.

- `InvG.done`: `Q` at a halted thread with no promise gives `B`
  (hypothesis `hB`).
- `InvG.wp`: link theorem 1 without `InflightWritesDead`
  (`treeJ_envG_eraseWPRDS_start`) into `WpPostR`; `PostRel.finish`
  re-establishes `EnvRel` with the new clean flag (`cl`: from `ClAt` without
  a release in flight, from `cl₀` alone with one, `PostS`).
- `InvG.prepay`: the live fulfilment is the tree's first store
  (`relFulfilsLive_firstStore`), permitted at the env state after its fences
  (`TreeJLive.storeOk` through `link`), so `prepayGeneric` applies; a second
  release while one is in flight is impossible (the in-flight tree's store
  is the first release's, and `NoDead` would put the first promise above the
  second).
- `ThreadRuleRX.ofEnvG`, `npSafe_of_envG`: the rule and `NPSafe.of_ruleRX`.
-/
import Kraken.Promising.SLR.EnvG.Phase1
import Kraken.Promising.SLR.EnvG.PrepayRmw

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **The hypotheses of the rule link** for a thread-local invariant `Q` of
`EnvG` (see the module docstring). -/
structure LinkHyps (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1Shape A tree
  link : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- **The rule's invariant**: the core and `Q` at some env state. -/
def InvG (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) (cl : Prop) (c : Config I) (r : Res)
    (g : Ghost) : Prop :=
  ∃ σ t, CoreAt A tid pl cl c r g σ t ∧ Q t.st σ

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`done`**: at a halted thread with no promise, `Q` and `EnvRel` give
`B` (hypothesis `hB`). -/
theorem InvG.done {B : Config I → Res → Ghost → Prop}
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (hcl : cl) (hd : c.Done tid) : B c r g := by
  obtain ⟨σ, t₀, hC, hQ⟩ := h
  obtain ⟨t, ht, hhalt, hprom⟩ := hd
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', -⟩ := hth t₀ hC.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have h1 := hC.rel.ext ⟨hinit, hmsgs, hth⟩ ht (fun ts hts _ => absurd (hprom ▸ hts) List.not_mem_nil)
  exact hB c { t₀ with prom := t₀.prom ++ ps } r g cl σ hQ hhalt hprom (h1.ghostLe hg fun ts hts => absurd (hprom ▸ hts) List.not_mem_nil) hcl

/-- **`wp`**: link theorem 1 into `WpPostR`. -/
theorem InvG.wp (H : LinkHyps A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res)
    (t : Thread I) (tree : EvTree I.State) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c) (hg : g₀.Le g)
    (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvG A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDS (nodeSimS_envG (A := A) (pl := pl) (iv := instrViews t (I.deps t.st))
    (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS) Q) t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envG_eraseWPRDS_start hC.rel (I.deps t.st) hS E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
  refine ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → σ'.cl := by
    cases pf with
    | none => exact fun ⟨h1, h2⟩ => hP.cl ⟨h1, rF, (hr rfl) ▸ h2⟩
    | some _ => exact fun ⟨h1, _⟩ => hcl (by simp) h1
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **The first-store prepay body, generic in the env's store judgment and
in an extension of the erasure**: from the core `hC` (already
transported to `c`), the phase-1 shape and first-store fact of the in-flight
instruction's tree, the env state `σ'` at its first store with its
permission and the side condition `Ex l` (`hJ`, read off the env's
store judgment), and a prepay theorem at that store producing the extension
`Y` after the promise (`hpre`, e.g. `prepayGeneric` with `Y = ⊤`, or the
ticket `prepayGenericTD` with `Y = TX`), the promise keeps the erasure and
`Y`, and the core holds after it with the release in flight. Shared by
`InvG.prepay_of_firstStoreG` (`InvG`) and the ticket link's `InvGTD.prepay`
(`EnvG/TicketRuleLink.lean`). -/
theorem CoreAt.prepay_of_firstStoreGX {Ex : Loc → Prop} {Y : Ghost → Config I → Prop} (hvalid : pl.Valid)
    {cl cl' : Prop} {c : Config I} {r : Res} {g : Ghost} {σ : State I} {t₁ : Thread I} (rF : Nat → Res) (w : Msg)
    (hC : CoreAt A tid pl cl c r g σ t₁) (hcl : cl' → cl) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv) (tree : EvTree I.State)
    (hex : I.exec t₁.st = some tree) (hsh : Phase1Shape A tree)
    (hFS : FirstStore (fun _ _ l v => l = w.loc ∧ v = w.val ∧
      AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
        (c.mem.append { w with tid }).2 l) tree)
    (hJ : ∃ σ' k xcl l v, (l = w.loc ∧ v = w.val ∧
        AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 l) ∧ StoreOk A tid pl σ' k xcl l v ∧ Ex l ∧
      σ'.r = σ.r ∧ σ'.g = σ.g ∧ σ'.snap = σ.snap ∧ WBnd σ'.vs c.mem.last ∧ σ'.cl = σ.cl)
    (hpre : ∀ (σ' : State I) (k : StoreKind) (l : Loc) (v : Val), StoreOk A tid pl σ' k false l v → Ex l →
      AnchorOk tid σ' c g → Erase (setRes rF tid σ'.r) g (fun _ => True) c →
      WriteBound A σ'.vs k l (c.mem.last + 1) →
      ∃ (r' : Res) (g' : Ghost),
        (Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, v, tid⟩) ∧ g.Le g' ∧
          (c.mem.append ⟨l, v, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
          (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, v, tid⟩).2) ∧
          r' = pl.after l v (c.mem.last + 1) σ'.cl σ'.r ∧
          (∀ x, mayWrite r' g' x → mayWrite σ'.r g x) ∧
          (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
          (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
            ∀ x, reachB r' g' x b → reachB σ'.r g x b)) ∧
        Y g' (PromisedBy c tid t₁ ⟨l, v, tid⟩)) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ Y g' (PromisedBy c tid t₁ w) ∧
      g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      CoreAt A tid pl cl' (PromisedBy c tid t₁ w) r' g' σ
        { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  have hn := lt_size_of_get? ht
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      obtain ⟨-, -, l, v, ⟨-, -, habove⟩, hS⟩ := (hFS.and_sok (htree tree hex)).exists
      have hl₁ : l₁ = l := by
        rcases hS with e | e
        · cases e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1
      have hle := hC.pendLe ts₁ h2
      have hne : ts₁ ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
      have := habove ts₁ (List.mem_append_left _ h1) hne _
        (by rw [Memory.get?_append_of_le _ _ _ hle]; exact h3) hl₁
      rw [hts_eq] at this
      omega_t
  -- the env state at the store, and its permission
  obtain ⟨σ', k, xcl, l, v, ⟨hl, hv, habove⟩, hok, hex', hσr, hσg, hσs, hwb, hσc⟩ := hJ
  obtain rfl : xcl = false := hok.1
  subst hl hv
  have hanc : AnchorOk tid σ' c g := ⟨hσs ▸ hC.rel.snap, hσg ▸ hC.rel.ghost, ⟨_, E⟩, hm, hn⟩
  have E0 : Erase (setRes rF tid σ'.r) g (fun _ => True) c := by rw [hσr, ← hr]; exact E
  obtain ⟨r', g', ⟨E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩, hY⟩ :=
    hpre σ' k _ _ hok hex' hanc E0 (hwb.writeBound A k _)
  rw [hσr, ← hr] at hacq hK1
  refine ⟨r', g', E', hY, hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
  -- the invariant after the promise: the release is in flight
  have hExt := EnvExt.promise (tid := tid) (w := w) ht
  have ht' : (PromisedBy c tid t₁ w).threads[tid]? =
      some { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } := by
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have h1 := hC.rel.ext hExt ht' (fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      have := E.pend_le hpd
      rw [h', hts_eq] at this
      omega_t)
  have huniq : ∀ ts ∈ t₁.prom ++ [(c.mem.append { w with tid }).2], ts ∈ g'.pend →
      ts = (c.mem.append { w with tid }).2 := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · rcases hnew ts hpd with h'' | h''
      · exact absurd h'' (hn0 ts h')
      · exact h''
    · exact List.mem_singleton.mp h'
  have hr'' : r' = pl.after w.loc w.val (c.mem.last + 1) σ'.cl σ.r := by rw [hr', hσr]
  refine
    ⟨{ h1 with ghost := h1.ghost.trans hgle,
               res := .inr ⟨_, w.loc, w.val, List.mem_append_right _ (List.mem_singleton_self _), hpend, hget,
                 ⟨σ'.cl, fun h => hσc ▸ h, hr''⟩, huniq⟩,
               cl := fun hc => hC.rel.cl (hcl hc) }, fun ts hpd => ?_, fun ts l' v' hts hpd hget' => ?_⟩
  · show ts ≤ (c.mem.append { w with tid }).1.last
    rw [Memory.last_append]
    rcases hnew ts hpd with h' | h'
    · have := E.pend_le h'; omega_t
    · rw [h', hts_eq]; exact Nat.le_refl _
  · obtain rfl := huniq ts hts hpd
    have e : (⟨l', v', tid⟩ : Msg) = { w with tid } := Option.some.inj (hget'.symm.trans hget)
    simp only [Msg.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    refine ⟨fun tree' hex' => ?_, habove, ?_⟩
    · rw [show tree' = tree from Option.some.inj (hex'.symm.trans hex)]
      exact hFS.singleAccessS (fun _ _ _ _ ⟨e1, e2, _⟩ => .inr (by rw [e1, e2])) hsh.2.singleAccess
    · rw [hr'']; exact pl.after_q_pos hvalid _ _ _ _ _ (hσr ▸ hok.2.1)


/-- **`InvG.prepay` from the first-store fact, generic in the link
hypotheses**: the in-flight instruction's tree has the phase-1
shape (`hsh`) and its first store writes the promised message (`hFS`); of
the link hypotheses only `valid` (`hvalid`) and the store permission
(`hstore`, `LinkHyps.link` at `TreeJLive.storeOk`) are used. Shared by
`InvG.prepay_of_firstStore` (`LinkHyps`), `InvG.prepay_of_firstStore2`
(`LinkHyps2`, `EnvG/MultiRule.lean`) and `InvG.prepay_of_firstStore3`
(`LinkHyps3`, `EnvG/MultiWriteRule.lean`); also
`InvG.prepayT` (`LinkHypsT`), and an instance of
`CoreAt.prepay_of_firstStoreGX` (`Ex = Y = ⊤`, `prepayGeneric`). -/
theorem InvG.prepay_of_firstStoreG (hvalid : pl.Valid)
    (hstore : ∀ st σ tree, Q st σ → I.exec st = some tree → StoreOkAt A tid pl tree σ)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) (tree : EvTree I.State) (hex : I.exec t₁.st = some tree)
    (hsh : Phase1Shape A tree)
    (hFS : FirstStore (fun _ _ l v => l = w.loc ∧ v = w.val ∧
      AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
        (c.mem.append { w with tid }).2 l) tree) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hJ : StoreOkAt A tid pl tree σ := hstore t₁.st σ tree hQ hex
  obtain ⟨σ', k, xcl, l, v, hP, hok, hΦ⟩ :=
    hFS.storeOk (Φ := fun s => s.r = σ.r ∧ s.g = σ.g ∧ s.snap = σ.snap ∧ WBnd s.vs c.mem.last ∧ s.cl = σ.cl)
      (fun s k ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4.fence k, h5⟩) tree σ hJ
      ⟨rfl, rfl, rfl, WBnd.of_viewsLe hC.rel.views, rfl⟩
  obtain ⟨r', g', E', -, hgle, hpend, hkeep, hnew, hCo, hacq, hK2, hK1⟩ :=
    hC.prepay_of_firstStoreGX (Ex := fun _ => True) (Y := fun _ _ => True) hvalid rF w And.left ht E hm tree hex
      hsh hFS ⟨σ', k, xcl, l, v, hP, hok, trivial, hΦ⟩
      (fun σ' k l v hok _ hanc E0 hwb => (prepayGeneric tid pl σ' k l v c g rF t₁ hvalid hok hanc ht E0 hwb).imp
        fun _ => Exists.imp fun _ h => ⟨h, trivial⟩)
  exact ⟨r', g', E', hgle, hpend, hkeep, hnew, ⟨σ, _, hCo, hQ⟩, hacq, hK2, hK1⟩

/-- **`InvG.prepay` from the first-store fact**: the in-flight instruction's
first store writes the promised message. The body of `InvG.prepay` after
`relFulfilsLive_firstStore` (the only use of its `G₀` hypothesis); shared by
`InvG.prepay` and the fence-aware `InvG.prepayHyb` (`EnvG/FenceEnv.lean`). -/
theorem InvG.prepay_of_firstStore (H : LinkHyps A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res}
    {g₀ g : Ghost} (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) (tree : EvTree I.State) (hex : I.exec t₁.st = some tree)
    (hFS : FirstStore (fun _ _ l v => l = w.loc ∧ v = w.val ∧
      AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
        (c.mem.append { w with tid }).2 l) tree) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  have hsh : Phase1Shape A tree := by
    obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
    obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
    exact H.shape _ _ (hst ▸ hQ₀) tree hex
  exact InvG.prepay_of_firstStoreG H.valid
    (fun st σ tree hQ hex => H.link (TreeJLive.storeOk A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial))
    rF t₁ w h he hg ht E hm hnp tree hex hsh hFS

/-- **`prepay`**: the generic prepay theorem at the in-flight instruction's
store. -/
theorem InvG.prepay (H : LinkHyps A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvG A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvG A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh : Phase1Shape A tree := by
    obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
    obtain ⟨hst, -⟩ := hC₀.transport he hg ht hnp E
    exact H.shape _ _ (hst ▸ hQ₀) tree hex
  exact InvG.prepay_of_firstStore H rF t₁ w h he hg ht E hm hnp tree hex
    (relFulfilsLive_firstStore (List.mem_append_right _ (List.mem_singleton_self _)) (Memory.get?_append_last _ _)
      tree _ rfl rfl hsh hrfl)

end Rule

/-- **The rule link**: a `ThreadRuleRX` from a thread-local invariant `Q`
of `EnvG` (`LinkHyps`) and the postcondition at halted threads (`hB`). -/
def ThreadRuleRX.ofEnvG {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvG A tid pl Q
  done h he hg hcl hd := InvG.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvG.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvG.prepay H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the rule link** (`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envG {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHyps A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvG A tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvG H hB) n m cl c r g h

/-! ## The rule link with release-kind RMWs

Additive (option (A)): `LinkHypsR` / `InvGR` / `ThreadRuleRX.ofEnvGR` are
`LinkHyps` / `InvG` / `ThreadRuleRX.ofEnvG` for trees of `Phase1ShapeR`
(release-kind RMWs whose operation never fails), with the core `CoreAtR`.
`LinkHypsR.giveOk` is the give-away side condition of planned-release RMWs
(`RelRmwGiveOk`) at the env's release predicates.

- `InvGR.wp`: `treeJ_envG_eraseWPRDSR_start` (the in-flight RMW fulfils the
  pending promise with its claim, `NodeRel.rmwRelS`).
- `InvGR.prepay`: the live fulfilment is the tree's first access
  (`relFulfilsLive_firstAccess`), permitted at the env state after its fences
  (`TreeJLive.storeOk` / `TreeJLive.rmwOk` through `link`,
  `FirstAccess.accessOk`, carrying the node relation at the unpromised
  context); a store is prepaid by `prepayGeneric`, an RMW by
  `prepayGenericRmw'_of_giveOk` with its read transferred to `ReadAt`
  (`NodeRel.readAt_promised`). -/

/-- **The hypotheses of the rule link with release-kind RMWs**: `LinkHyps`
with `Phase1ShapeR` trees and the give-away side condition. -/
structure LinkHypsR (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree
  giveOk : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel
  link : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

/-- The plain hypotheses with the give-away side condition. -/
theorem LinkHyps.toR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (H : LinkHyps A tid pl Q)
    (hG : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel) : LinkHypsR A tid pl Q :=
  ⟨H.valid, fun st σ hQ tree hex => (H.shape st σ hQ tree hex).toR, hG, H.link⟩

/-- **The rule's invariant with release-kind RMWs**: the core `CoreAtR` and
`Q` at some env state. -/
def InvGR (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) (cl : Prop) (c : Config I) (r : Res)
    (g : Ghost) : Prop :=
  ∃ σ t, CoreAtR tid pl cl c r g σ t ∧ Q t.st σ

section RuleR

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`done`** (`InvG.done`). -/
theorem InvGR.done {B : Config I → Res → Ghost → Prop}
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost} (h : InvGR tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (hcl : cl) (hd : c.Done tid) : B c r g := by
  obtain ⟨σ, t₀, hC, hQ⟩ := h
  obtain ⟨t, ht, hhalt, hprom⟩ := hd
  obtain ⟨hinit, hmsgs, hth⟩ := he
  obtain ⟨ps, ht', -⟩ := hth t₀ hC.rel.ht
  rw [ht] at ht'
  obtain rfl := Option.some.inj ht'
  have h1 := hC.rel.ext ⟨hinit, hmsgs, hth⟩ ht (fun ts hts _ => absurd (hprom ▸ hts) List.not_mem_nil)
  exact hB c { t₀ with prom := t₀.prom ++ ps } r g cl σ hQ hhalt hprom
    (h1.ghostLe hg fun ts hts => absurd (hprom ▸ hts) List.not_mem_nil) hcl

/-- **`wp`** with release-kind RMWs (`InvG.wp`). -/
theorem InvGR.wp (H : LinkHypsR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGR tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvGR tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start (A := A)
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hG : RelRmwGiveOk I pl g.rel := by rw [hC.rel.ghost.rel]; exact H.giveOk _ _ hQ
  have hW := H.link (TreeJLive.eraseWPRDS2 (nodeSimS2_envG (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g) (cl₀ := cl) (rS := r) hS hG) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envG_eraseWPRDSR_start hC.rel (I.deps t.st) hS hG E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
  refine ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → σ'.cl := by
    cases pf with
    | none => exact fun ⟨h1, h2⟩ => hP.cl ⟨h1, rF, (hr rfl) ▸ h2⟩
    | some _ => exact fun ⟨h1, _⟩ => hcl (by simp) h1
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **`prepay` with release-kind RMWs, from the first-access judgments**: the
body of `InvGR.prepay`, for any judgment of the in-flight
tree that yields `StoreOkAt`/`RmwOkAt` at `Q`-states (`LinkHypsR.link` at
`TreeJLive.storeOk`/`rmwOk` for `EnvG`; `LinkHypsTR.link` at
`TreeJLive.storeOkT`/`rmwOkT` for `EnvGT`, `EnvG/TakeRLink.lean`). -/
theorem InvGR.prepay_of_okAt (hvalid : pl.Valid)
    (hshape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → Phase1ShapeR A tree)
    (hgive : ∀ st σ, Q st σ → RelRmwGiveOk I pl σ.g.rel)
    (hok : ∀ st σ tree, Q st σ → I.exec st = some tree → StoreOkAt A tid pl tree σ ∧ RmwOkAt A tid pl tree σ)
    {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGR tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGR tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hn := lt_size_of_get? ht
  obtain ⟨tree, hex, hrfl⟩ := hrel
  have hsh := hshape _ _ hQ tree hex
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hFA := relFulfilsLive_firstAccess (List.mem_append_right _ (List.mem_singleton_self _)) hget tree _ rfl rfl
    hsh hrfl
  -- the tree's single access is the new in-flight release's
  have hSA : SingleAccessS2 (LokS (some (w.loc, w.val))) (SokS (some (w.loc, w.val))) (RokR (some (w.loc, w.val)))
      (LokS (some (w.loc, w.val))) tree :=
    hFA.singleAccessS2 (fun _ _ _ _ ⟨e1, e2, _⟩ => .inr (by rw [e1, e2]))
      (fun _ _ _ _ _ ⟨e1, _, htot, _⟩ => .inr ⟨w.val, by rw [e1], htot⟩) hsh.2.singleAccess
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      have habove : AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 l₁ := by
        rcases (hFA.and_ok (htree tree hex)).exists with ⟨-, -, l, v, ⟨-, -, hab⟩, hS⟩ |
            ⟨_, _, _, l, _, ⟨-, -, -, hab, -⟩, hR⟩
        · rcases hS with e | e
          · cases e
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact hab
        · rcases hR with e | ⟨_, e, -⟩
          · cases e
          · simp only [Option.some.injEq, Prod.mk.injEq] at e
            obtain ⟨rfl, -⟩ := e
            exact hab
      have hle := hC.pendLe ts₁ h2
      have hne : ts₁ ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
      have := habove ts₁ (List.mem_append_left _ h1) hne _
        (by rw [Memory.get?_append_of_le _ _ _ hle]; exact h3) rfl
      rw [hts_eq] at this
      omega_t
  -- the env state at the first access, with the node relation at the unpromised context
  obtain ⟨hJs, hJr⟩ := hok t₁.st σ tree hQ hex
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  let Φ : State I → Ctx → Prop := fun s P => WBnd s.vs c.mem.last ∧ s.cl = σ.cl ∧
    ∃ cxu, NodeRel tid pl (instrViews t₁ (I.deps t₁.st)) rF c t₁ σ.r g cl s r g cxu ∧ P.views = cxu.views ∧
      P.prom = cxu.prom ++ [c.mem.last + 1] ∧ P.mem = (c.mem.append { w with tid }).1
  have hΦ : ∀ s P k, Φ s P → Φ (fenceState s k) (fenceStep P k) := by
    rintro s P k ⟨hb, hcs, cxu, hN, hv, hp, hm'⟩
    exact ⟨hb.fence k, hcs, _, hN.fence k, by rw [fenceStep_views, fenceStep_views, hv],
      by rw [fenceStep_prom, fenceStep_prom, hp], by rw [fenceStep_mem, hm']⟩
  have hG : RelRmwGiveOk I pl σ.g.rel := hgive _ _ hQ
  obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, habove, hq⟩ :
      ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
        (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
        (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
        r' = pl.after w.loc w.val (c.mem.last + 1) σ.cl σ.r ∧
        (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
        (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
        (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
          ∀ x, reachB r' g' x b → reachB σ.r g x b) ∧
        AboveAt (t₁.prom ++ [(c.mem.append { w with tid }).2]) (c.mem.append { w with tid }).1
          (c.mem.append { w with tid }).2 w.loc ∧ 0 < (σ.r.wr w.loc).q := by
    rcases hFA.accessOk hΦ tree σ _ hJs hJr ⟨WBnd.of_viewsLe hC.rel.views, rfl, _, hN0, rfl, rfl, rfl⟩ with
        ⟨s', -, k, xcl, l, v, ⟨hl, hv, hab⟩, hok, hwb, hcs, cxu, hN, -⟩ |
        ⟨s', P', k, l, op, ⟨hl, -, -, hab, x, hx, hop⟩, hok, hwb, hcs, cxu, hN, hv, hp, hm'⟩
    · obtain rfl : xcl = false := hok.1
      subst hl hv
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGeneric tid pl s' k _ _ c g rF t₁ hvalid hok hN.anchorOk ht E0 (hwb.writeBound A k _)
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hab, hN.rv ▸ hok.2.1⟩
    · subst hl
      have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hN.rv, ← hr]; exact E
      have hrd := hN.readAt_promised (w := { w with tid }) hv hp hm' hx
      have hG' : RelRmwGiveOk I pl s'.g.rel := by rw [← hN.ghost.rel, hC.rel.ghost.rel]; exact hG
      obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
        prepayGenericRmw'_of_giveOk hG' hvalid hok hN.anchorOk ht E0 hrd hop (hwb.writeBound A _ _)
      rw [hN.rv, hcs] at hr'
      rw [hN.rv] at hacq hK1
      exact ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1, hab, hN.rv ▸ hok.1⟩
  rw [← hr] at hacq hK1
  refine ⟨r', g', E', hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
  -- the invariant after the promise: the release is in flight
  have hExt := EnvExt.promise (tid := tid) (w := w) ht
  have ht' : (PromisedBy c tid t₁ w).threads[tid]? =
      some { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] } := by
    rw [Config.withThread_get? c _ _ hn, ite_eq_left rfl]
  have h1 := hC.rel.ext hExt ht' (fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · exact h'
    · rw [List.mem_singleton] at h'
      have := E.pend_le hpd
      rw [h', hts_eq] at this
      omega_t)
  have huniq : ∀ ts ∈ t₁.prom ++ [(c.mem.append { w with tid }).2], ts ∈ g'.pend →
      ts = (c.mem.append { w with tid }).2 := fun ts hts hpd => by
    rcases List.mem_append.mp hts with h' | h'
    · rcases hnew ts hpd with h'' | h''
      · exact absurd h'' (hn0 ts h')
      · exact h''
    · exact List.mem_singleton.mp h'
  refine ⟨σ, { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] },
    ⟨{ h1 with ghost := h1.ghost.trans hgle,
               res := .inr ⟨_, w.loc, w.val, List.mem_append_right _ (List.mem_singleton_self _), hpend, hget,
                 ⟨σ.cl, id, hr'⟩, huniq⟩,
               cl := fun hc => hC.rel.cl hc.1 }, fun ts hpd => ?_, fun ts l' v' hts hpd hget' => ?_⟩, hQ⟩
  · show ts ≤ (c.mem.append { w with tid }).1.last
    rw [Memory.last_append]
    rcases hnew ts hpd with h' | h'
    · have := E.pend_le h'; omega_t
    · rw [h', hts_eq]; exact Nat.le_refl _
  · obtain rfl := huniq ts hts hpd
    have e : (⟨l', v', tid⟩ : Msg) = { w with tid } := Option.some.inj (hget'.symm.trans hget)
    simp only [Msg.mk.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    refine ⟨fun tree' hex' => ?_, habove, ?_⟩
    · rw [show tree' = tree from Option.some.inj (hex'.symm.trans hex)]
      exact hSA
    · rw [hr']; exact pl.after_q_pos hvalid _ _ _ _ _ hq

/-- **`prepay`** with release-kind RMWs: the generic prepay theorem at the
in-flight instruction's first access, a store (`prepayGeneric`) or a
release-kind RMW (`prepayGenericRmw'_of_giveOk`). -/
theorem InvGR.prepay (H : LinkHypsR A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGR tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGR tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) :=
  InvGR.prepay_of_okAt H.valid H.shape H.giveOk
    (fun st σ tree hQ hex =>
      ⟨H.link (TreeJLive.storeOk A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial),
        H.link (TreeJLive.rmwOk A tid pl I.State) st σ tree hQ hex (fun _ _ _ => trivial)⟩)
    rF t₁ w h he hg ht E hm hnp hrel

end RuleR

/-! ### Fixing the release predicates

`LinkHypsR.giveOk` is about the env's release predicates `σ.g.rel`, which
every `EnvG` step keeps (`envG_step_rel`: each outcome re-anchors at a ghost
above the old one). So a link for `Q` gives one for `Q` with the predicates
fixed to `rel₀` (`TreeJLive.relFix`, `link_relFix`), where a program-specific
`RelRmwGiveOk I pl rel₀` discharges `giveOk`. -/

/-- **Every `EnvG` step keeps the env's release predicates.** -/
theorem envG_step_rel {A : Arch} {tid : Nat} {pl : Plan} {a : SharedAccess} {σ σ' : State I}
    {ret : a.Ret} (h : (EnvG I A tid pl).step a σ ret σ') : σ'.g.rel = σ.g.rel := by
  cases a with
  | load => exact h.1.ghost.rel
  | store => obtain ⟨-, -, _, _, _, h1, -⟩ := h; exact h1.ghost.rel
  | rmw => obtain ⟨_, _, h1, -⟩ := h; exact h1.ghost.rel
  | fence => cases h; rfl

/-- A live tree judgment of `EnvG` read at env states with release
predicates `rel₀`. -/
def TreeJLive.relFix {A : Arch} {tid : Nat} {pl : Plan} {σT : Type} (J : TreeJLive (EnvG I A tid pl) σT)
    (rel₀ : Loc → Pred) : TreeJLive (EnvG I A tid pl) σT where
  W t s := s.g.rel = rel₀ → J.W t s
  Post st s := s.g.rel = rel₀ → J.Post st s
  done h e := J.done (h e)
  fault _ := J.fault
  choose h e := J.choose fun i => h i e
  load h₁ h₂ e := J.load h₁ fun v g' hs => h₂ v g' hs ((envG_step_rel hs).trans e)
  store h₁ h₂ e := J.store h₁ fun b g' hs => h₂ b g' hs ((envG_step_rel hs).trans e)
  rmw h₁ h₂ e := J.rmw h₁ fun v g' hs => h₂ v g' hs ((envG_step_rel hs).trans e)
  fence h₁ h₂ e := J.fence h₁ fun g' hs => h₂ g' hs ((envG_step_rel hs).trans e)

/-- **A link for `Q` is a link for `Q` with fixed release predicates.** -/
theorem link_relFix {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop} (rel₀ : Loc → Pred)
    (hlink : ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
      (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ) :
    ∀ (J : TreeJLive (EnvG I A tid pl) I.State) st σ tree, (Q st σ ∧ σ.g.rel = rel₀) → I.exec st = some tree →
      (∀ st' σ', (Q st' σ' ∧ σ'.g.rel = rel₀) → J.Post st' σ') → J.W tree σ :=
  fun J st σ tree hQ hex hJ =>
    hlink (J.relFix rel₀) st σ tree hQ.1 hex
      (fun st' σ' hQ' => show (J.relFix rel₀).Post st' σ' from fun e => hJ st' σ' ⟨hQ', e⟩) hQ.2

/-- **The rule link with release-kind RMWs**: a `ThreadRuleRX` from a
thread-local invariant `Q` of `EnvG` (`LinkHypsR`) and the postcondition at
halted threads (`hB`). -/
def ThreadRuleRX.ofEnvGR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvGR tid pl Q
  done h he hg hcl hd := InvGR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGR.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGR.prepay H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the rule link with release-kind RMWs**
(`NPSafe.of_ruleRX`). -/
theorem npSafe_of_envGR {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsR A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGR tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvGR H hB) n m cl c r g h

end Kraken.Promising.SLR.EnvG
