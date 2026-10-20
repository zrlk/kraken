/-
Whole-thread environment: **the rule
link of `EnvGLRV`** (`ThreadRuleRX` from a thread-local invariant of
`EnvGLRV`). ISA-neutral. Additive: `LRRule.lean` at `EnvGLRV`, reusing its
env-free parts (`LRShape`, `CoreAtLR`, `InvGLR`, `InvGLR.done`,
`InvGLR.q_at`, `relFulfilsLive_sokM`).

Changes against `LRRule.lean`:

- `InvGLRV.wp`: the tree runs at the knowledge `cl ∧ Erase (setRes rF tid r)
  g ⊥ c` (`treeJ_envGLRV_eraseWPRDM_start`), so the new knowledge implies the
  env's in both in-flight modes directly from `PostS`.
- `InvGLRV.prepay`: the env's walk to the fulfilling store answers loads by
  `NodeRel.loadLRV` at the knowledge `False` (`storeOkLRV_walk`); the walk's
  state then knows more than the start (`ClAtV` per load), so the in-flight
  relation takes the start's knowledge as the split's, which is sound for
  **whole plan entries** (`LinkHypsLRV.whole`; `RmwOk` asks the same of
  release RMWs).

- `StoreOkAtLRV`, `TreeJLive.storeOkLRV`, `storeOkLRV_walk`;
- `LinkHypsLRV`, `InvGLRV.wp`, `InvGLRV.prepay`;
- `ThreadRuleRX.ofEnvGLRV`, `npSafe_of_envGLRV`, `noFaultRule_ofEnvGLRV_struct`.

Phase-1 limits as `EnvGLR`, plus whole plan entries.
-/
import Kraken.Promising.SLR.EnvG.LRValLink
import Kraken.Promising.SLR.EnvG.LRRule

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- A whole release's virtual resource does not depend on the knowledge. -/
theorem Plan.after_of_whole (pl : Plan) {l : Loc} {v : Val} (hs : pl.Whole l v) (tw : Time) (P P' : Prop)
    (r : Res) : pl.after l v tw P r = pl.after l v tw P' r := by
  unfold Plan.after
  rw [pl.keep_of_whole hs, pl.keep_of_whole hs]

/-! ## The store's permission after the env's loads -/

/-- `StoreOk` at the store of a load-prefix tree, after every `EnvGLRV` load
outcome and fence on the way. -/
def StoreOkAtLRV (A : Arch) (tid : Nat) (pl : Plan) {σ : Type} : EvTree σ → State I → Prop
  | .fence k ret, s => StoreOkAtLRV A tid pl (ret ()) (fenceState s k)
  | .choose _ k, s => ∀ i, StoreOkAtLRV A tid pl (k i) s
  | .load k xcl l ret, s => ∀ v s', LoadOutLRV A tid pl s s' k xcl l v → StoreOkAtLRV A tid pl (ret v) s'
  | .store k xcl l v _, s => StoreOk A tid pl s k xcl l v
  | _, _ => True

/-- **`StoreOkAtLRV` is a live tree judgment of `EnvGLRV`.** -/
def TreeJLive.storeOkLRV (A : Arch) (tid : Nat) (pl : Plan) (σ : Type) : TreeJLive (EnvGLRV I A tid pl) σ where
  W := StoreOkAtLRV A tid pl
  Post _ _ := True
  done _ := trivial
  fault := trivial
  choose h := h
  load _ h := fun v s' hs => h v s' hs
  store hok _ := hok
  rmw _ _ := trivial
  fence _ h := h _ (fenceOut_fenceState _ _)

/-- **The env's walk to the fulfilling store** (`storeOkLR_walk` at
`EnvGLRV`, with the node relation at the knowledge `False`, which makes
`NodeRel.loadLRV`'s clean-erasure hypothesis vacuous). -/
theorem storeOkLRV_walk {A : Arch} {tid : Nat} {pl : Plan} {iv : InstrViews} {rF : Nat → Res} {c : Config I}
    {t : Thread I} {rv₀ : Res} {g₀ : Ghost} {r : Res} {g : Ghost} {ts : Time} {w : Msg} {σ : Type} :
    ∀ (tree : EvTree σ) (s : State I) (P Qc : Ctx),
      NodeRel tid pl iv rF c t rv₀ g₀ False s r g Qc → P.views = Qc.views → P.prom = Qc.prom ++ [ts] →
      P.mem = (Qc.mem.append w).1 → ts = Qc.mem.last + 1 →
      MultiAccessS True (fun _ _ => True) (fun k => ¬ effRelRmw A k) True tree →
      StoreOkAtLRV A tid pl tree s → tree.RelFulfilsLive A tid iv ts P →
      ∃ (s' : State I) (Qc' : Ctx) (k : StoreKind), NodeRel tid pl iv rF c t rv₀ g₀ False s' r g Qc' ∧
        StoreOk A tid pl s' k false w.loc w.val
  | .done _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .fault _, _, _, _, _, _, _, _, _, _, _, h => h.elim
  | .choose _ k, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, ⟨i, h⟩ =>
    storeOkLRV_walk (k i) s P Qc hN hv hp hm hts (hs i) (hok i) h
  | .fence k ret, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, h =>
    storeOkLRV_walk (ret ()) (fenceState s k) (fenceStep P k) (fenceStep Qc k) (hN.fence k)
      (by rw [fenceStep_views, fenceStep_views, hv]) (by rw [fenceStep_prom, fenceStep_prom, hp])
      (by rw [fenceStep_mem, fenceStep_mem, hm]) (by rw [fenceStep_mem]; exact hts) hs hok h
  | .load k xcl l ret, s, P, Qc, hN, hv, hp, hm, hts, hs, hok, ⟨x, hx, h⟩ => by
    obtain ⟨y, hy, e1, e2⟩ := readSuccs_unpromise hv hp hm hts hx
    obtain ⟨s', ho, hN'⟩ := hN.loadLRV (fun hf => hf.elim) hy
    have hvx : x.2.2.views = y.2.2.reset.views := by
      obtain ⟨t1, v1, rfl, -⟩ := (mem_readSuccs A).mp hx
      obtain ⟨t2, v2, rfl, -⟩ := (mem_readSuccs A).mp hy
      simp only at e1 e2
      subst e1 e2
      simp only [Ctx.reset_views, readNext, readPre, hv]
    obtain ⟨hm1, hp1⟩ := readSuccs_memProm A iv hx
    obtain ⟨hm2, hp2⟩ := readSuccs_memProm A iv hy
    exact storeOkLRV_walk (ret x.2.1) s' x.2.2 y.2.2.reset hN' hvx
      (by rw [hp1, hp, Ctx.reset_prom, hp2]) (by rw [hm1, hm, Ctx.reset_mem, hm2])
      (by rw [Ctx.reset_mem, hm2]; exact hts) (hs.2 _) (hok x.2.1 s' (e2 ▸ ho)) h
  | .rmw k _ _ _ ret, _, _, _, _, _, _, _, _, hs, _, ⟨x, _, h⟩ => by
    rcases h with h | ⟨_, _, _, _, h⟩
    · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
    · rcases h with ⟨⟨hk, _⟩, _⟩ | h
      · exact absurd hk hs.1
      · exact (AccessFree.not_relFulfilsLive (ret x.2.1) _ (hs.2 _) h).elim
  | .store k xcl l v ret, s, P, Qc, hN, _, hp, hm, hts, hs, hok, h => by
    rcases h with ⟨c', hc', ⟨⟨-, htc, htc'⟩, hnd⟩ | h⟩ | h
    · have hget : P.mem.get? ts = some w := by rw [hm, hts]; exact Memory.get?_append_last _ _
      obtain ⟨rfl, rfl, -⟩ := fulfil_write_facts (by rw [hp]; exact List.mem_append_right _ (List.mem_singleton_self _))
        hget rfl rfl hc' htc htc' hnd
      obtain rfl : xcl = false := hok.1
      exact ⟨s, Qc, k, hN, hok⟩
    · exact (AccessFree.not_relFulfilsLive (ret true) _ (hs.2 true) h).elim
    · exact (AccessFree.not_relFulfilsLive (ret false) _ (hs.2 false) h).elim

/-! ## The rule -/

/-- **The hypotheses of the `EnvGLRV` rule link**: `LinkHypsLR` at
`EnvGLRV`, plus whole plan entries. -/
structure LinkHypsLRV (A : Arch) (tid : Nat) (pl : Plan) (Q : I.State → State I → Prop) : Prop where
  valid : pl.Valid
  whole : ∀ e ∈ pl.entries, e.split = none
  shape : ∀ st σ, Q st σ → ∀ tree, I.exec st = some tree → LRShape A tree
  link : ∀ (J : TreeJLive (EnvGLRV I A tid pl) I.State) st σ tree, Q st σ → I.exec st = some tree →
    (∀ st' σ', Q st' σ' → J.Post st' σ') → J.W tree σ

section Rule

variable {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}

/-- **`wp`**: link theorem 1 of `EnvGLRV` into `WpPostR`. -/
theorem InvGLRV.wp (H : LinkHypsLRV A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t : Thread I) (tree : EvTree I.State) (h : InvGLR A tid pl Q cl c₀ r g₀)
    (he : EnvExt tid c₀ c) (hg : g₀.Le g) (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree)
    (E : Erase (setRes rF tid r) g (fun _ => True) c) (hm : c.MachInv)
    (hnp : ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) :
    tree.EraseWPRD A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPostR (InvGLR A tid pl Q) (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g
      (ctx₀ t tid c.mem) := by
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t.st σ := hst ▸ hQ₀
  obtain ⟨pf, hS, hsa, hr⟩ := hC.start
  have ha := hsa tree hex (H.shape _ _ hQ tree hex)
  have hW := H.link (TreeJLive.eraseWPRDM (nodeSimLRV_envGLRV (A := A) (pl := pl)
    (iv := instrViews t (I.deps t.st)) (rF := rF) (rv₀ := σ.r) (g₀ := g)
    (cl₀ := cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (rS := r) hS (fun hc => ⟨rF, hc.2⟩)) Q)
    t.st σ tree hQ hex (fun _ _ h => h)
  have hwp := treeJ_envGLRV_eraseWPRDM_start hC.rel (I.deps t.st) hS E hm hW ha
  refine EvTree.EraseWPRD.mono ?_ tree _ _ _ hwp
  rintro st r' g' cx' ⟨σ', hQ', hP, ⟨hg', hkeep, hnew, hacq, hown⟩, hlast, hpd, hcl⟩
  refine ⟨hg', hkeep, hnew, hacq, hown, fun t' ht' _ => ?_⟩
  obtain ⟨cxe, hcx, -⟩ := hP.ctx
  have hE := hP.finish (pl := pl) ht hcx.sim.bnd hcx.sim.ivb (hC.rel.bnd.regs.mono hlast) ht'
  have hcl' : (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) → σ'.cl := by
    cases pf with
    | none => exact fun hc => hP.cl ⟨hc, rF, (hr rfl) ▸ hc.2⟩
    | some _ => exact fun hc => hcl (by simp) hc
  have hprom' : t'.prom = cx'.prom := (finishInstr_relKey ht').1
  refine ⟨σ', t', ⟨{ hE with cl := hcl' }, fun ts hts => ?_, fun ts _ _ hts hpd' _ => ?_⟩, ?_⟩
  · have := E.pend_le (hnew ts hts)
    show ts ≤ cx'.mem.last
    omega_t
  · exact absurd hpd' (hpd ts (hprom' ▸ hts))
  · rw [finishInstr_st ht']; exact hQ'

/-- **`prepay`** (`InvGLR.prepay` at `EnvGLRV`): the split's knowledge is
the start's, sound for whole entries. -/
theorem InvGLRV.prepay (H : LinkHypsLRV A tid pl Q) {cl : Prop} {c₀ c : Config I} {r : Res} {g₀ g : Ghost}
    (rF : Nat → Res) (t₁ : Thread I) (w : Msg) (h : InvGLR A tid pl Q cl c₀ r g₀) (he : EnvExt tid c₀ c)
    (hg : g₀.Le g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid r) g (fun _ => True) c)
    (hm : c.MachInv) (hnp : ∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      InvGLR A tid pl Q (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧
      (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b) := by
  obtain ⟨tree, hex, hrfl⟩ := hrel
  obtain ⟨σ, t₀, hC₀, hQ₀⟩ := h
  obtain ⟨hst, hC⟩ := hC₀.transport he hg ht hnp E
  have hQ : Q t₁.st σ := hst ▸ hQ₀
  have hsh : LRShape A tree := H.shape _ _ hQ tree hex
  have hn := lt_size_of_get? ht
  have hts_eq : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hget : (c.mem.append { w with tid }).1.get? (c.mem.append { w with tid }).2 = some { w with tid } :=
    Memory.get?_append_last _ _
  have hmem : (c.mem.append { w with tid }).2 ∈ t₁.prom ++ [(c.mem.append { w with tid }).2] :=
    List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨-, habove⟩ := relFulfilsLive_sokM (Sok := fun _ _ => True) hmem hget (fun _ hk => hk) tree _ rfl rfl
    hsh.multi hrfl
  -- no release is in flight
  obtain ⟨hr, hn0⟩ : r = σ.r ∧ ∀ ts ∈ t₁.prom, ts ∉ g.pend := by
    rcases hC.rel.res with h' | ⟨ts₁, l₁, v₁, h1, h2, h3, -, -⟩
    · exact h'
    · exfalso
      obtain ⟨htree, -, -⟩ := hC.infl ts₁ l₁ v₁ h1 h2 h3
      obtain ⟨hsok, -⟩ := relFulfilsLive_sokM hmem hget (fun _ hk => absurd hk.1 (by simp)) tree _ rfl rfl
        (htree tree hex) hrfl
      have hl₁ : l₁ = w.loc := by
        rcases hsok with e | ⟨v₀, e⟩
        · cases e
        · simp only [Option.some.injEq, Prod.mk.injEq] at e; exact e.1
      have hle := hC.pendLe ts₁ h2
      have hne : ts₁ ≠ (c.mem.append { w with tid }).2 := by rw [hts_eq]; omega_t
      have := habove ts₁ (List.mem_append_left _ h1) hne _
        (by rw [Memory.get?_append_of_le _ _ _ hle]; exact h3) hl₁
      rw [hts_eq] at this
      omega_t
  -- the env's walk to the store (node relation at knowledge `False`), and its permission
  have hN0 := hC.rel.toNodeRel rF (I.deps t₁.st) E hm
  obtain ⟨s', Qc', k, hN', hok⟩ := storeOkLRV_walk (w := { w with tid }) tree σ
    { views := t₁.views, prom := t₁.prom ++ [(c.mem.append { w with tid }).2], mem := (c.mem.append { w with tid }).1,
      log := [.instr tid (I.showInstr t₁.st)] } _ { hN0 with cl := fun hf => hf.elim } rfl rfl rfl rfl
    hsh.multi (H.link (TreeJLive.storeOkLRV A tid pl I.State) t₁.st σ tree hQ hex (fun _ _ _ => trivial)) hrfl
  have hanc : AnchorOk tid s' c g := hN'.anchorOk
  have hσr : s'.r = σ.r := hN'.rv
  have E0 : Erase (setRes rF tid s'.r) g (fun _ => True) c := by rw [hσr, ← hr]; exact E
  have hwb : WBnd s'.vs c.mem.last := by
    have hv := hN'.ctx.sim.rel.views
    rw [hN'.mem] at hv
    exact WBnd.of_viewsLe hv
  obtain ⟨r', g', E', hgle, hpend, hkeep, hnew, hr', hacq, hK2, hK1⟩ :=
    prepayGeneric tid pl s' k _ _ c g rF t₁ H.valid hok hanc ht E0 (hwb.writeBound A k _)
  rw [hσr, ← hr] at hacq hK1
  refine ⟨r', g', E', hgle, hpend, hkeep, hnew, ?_, hacq, hK2, hK1⟩
  -- the in-flight tree condition
  have hinfl : MultiAccessS True (SokLR (some (w.loc, w.val))) (RokS A (some (w.loc, w.val)))
      (LokS (some (w.loc, w.val))) tree := by
    rcases hsh with hs1 | hs2 | ⟨l₀, hs3⟩
    · have hFS := relFulfilsLive_firstStore hmem hget tree _ rfl rfl hs1 hrfl
      have h1 : SingleAccessS False (SokLR (some (w.loc, w.val))) (RokS A (some (w.loc, w.val)))
          (LokS (some (w.loc, w.val))) tree :=
        hFS.singleAccessS (fun _ _ _ _ ⟨e1, _, _⟩ => .inr ⟨w.val, by rw [e1]⟩) hs1.2.singleAccess
      exact (SingleAccessS.toM False.elim h1).mono (fun _ => trivial) (fun _ _ h => h) (fun _ h => h) id
    · exact absurd hrfl (NoRelWrite.not_relFulfilsLive tree _ hs2.2)
    · have hl₀ := (relFulfilsLive_sokM hmem hget (fun _ h => h.elim) tree _ rfl rfl hs3 hrfl).1
      exact hs3.mono id (fun l' _ hl' => .inr ⟨w.val, by rw [hl', ← hl₀]⟩) (fun _ h => h.elim) (fun h => h.elim)
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
  -- whole entries: the split's knowledge is irrelevant, take the start's
  have hr'' : r' = pl.after w.loc w.val (c.mem.last + 1) σ.cl σ.r := by
    rw [hr', hσr]; exact pl.after_of_whole (Plan.Whole.of_entries H.whole _ _) _ _ _ _
  refine ⟨σ, { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] },
    ⟨{ h1 with ghost := h1.ghost.trans hgle,
               res := .inr ⟨_, w.loc, w.val, hmem, hpend, hget, ⟨σ.cl, id, hr''⟩, huniq⟩,
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
      exact hinfl
    · rw [hr'']; exact pl.after_q_pos H.valid _ _ _ _ _ (hσr ▸ hok.2.1)

end Rule

/-- **The rule link of `EnvGLRV`**: a `ThreadRuleRX` from a thread-local
invariant `Q` of `EnvGLRV` (`LinkHypsLRV`) and the postcondition at halted
threads (`hB`; the invariant is `LRRule.lean`'s `InvGLR`). -/
def ThreadRuleRX.ofEnvGLRV {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLRV A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g) :
    ThreadRuleRX A B tid where
  Inv := InvGLR A tid pl Q
  done h he hg hcl hd := InvGLR.done hB h he hg hcl hd
  wp rF t tree h he hg ht hex E hm _ hnp := InvGLRV.wp H rF t tree h he hg ht hex E hm hnp
  prepay rF t₁ w h he hg ht E hm hnp hrel := InvGLRV.prepay H rF t₁ w h he hg ht E hm hnp hrel

/-- **`NPSafe` from the `EnvGLRV` rule link.** -/
theorem npSafe_of_envGLRV {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLRV A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (n m : Nat) {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (h : InvGLR A tid pl Q cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_ruleRX (ThreadRuleRX.ofEnvGLRV H hB) n m cl c r g h

/-- **The `EnvGLRV` no-fault rule from fault-free trees.** -/
theorem noFaultRule_ofEnvGLRV_struct {A : Arch} {tid : Nat} {pl : Plan} {Q : I.State → State I → Prop}
    {B : Config I → (model I).R → (model I).Ghost → Prop} (H : LinkHypsLRV A tid pl Q)
    (hB : ∀ c t r g cl σ, Q t.st σ → t.halted = true → t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g)
    (HS : ∀ st σ tree, Q st σ → I.exec st = some tree → tree.NoFault) :
    NoFaultRule (ThreadRuleRX.ofEnvGLRV H hB) :=
  NoFaultRule.ofNoFault fun rF t tree h he hg ht hex E _ _ hnp => by
    obtain ⟨σ, hQ⟩ := InvGLR.q_at rF t h he hg ht E hnp
    exact HS t.st σ tree hQ hex

end Kraken.Promising.SLR.EnvG
