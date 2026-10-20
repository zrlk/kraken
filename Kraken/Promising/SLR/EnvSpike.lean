/-
Status: prototype code. This (with `EnvSpikeA64.lean`, `EnvSpikeSwp.lean`)
is the *per-instruction* layer of a whole-thread SLR environment. Its tree
judgment `TreeJ` and the per-ISA simulations of it are reused by `EnvG`
(`EnvG/Live.lean`, `EnvG/RelPureEnv.lean`, `EnvG/MemValsBase.lean`).

Prototype: can the SLR per-instruction obligations
(`EvTree.EraseWPR`) be produced from an environment judgment, the way the invariant environment
produces `EvTree.AllInv` from an `AllEnv (SharedEnv.inv S G)` judgment?

ISA-free part.

- `TreeJ E σ`: an event-tree judgment that an `AllEnv E` judgment transfers
  to node by node (the *laws*: one per event shape, each "the environment
  permits the access and every outcome satisfies the continuation"). The invariant environment's
  `EvTree.AllInv G Q` is one (`TreeJ.allInv`); the per-ISA simulation
  (`EnvSpikeA64.jsim`) is `InvLinkAArch64`'s `isim` with `AllInv` replaced by
  an arbitrary `TreeJ`.
- `SLREnv`: the *per-instruction* SLR environment. Its state is the thread's
  resource, the ghost state and the instruction context `(r, g, cx)`; it is
  parameterised by the instruction's anchor (configuration `c`, thread `t`,
  instruction views `iv`) and by a ghost `Plan` (the angelic choices of
  SLR's write rules: which stores are releases and how a release splits the
  thread's resource). Loads answer from `readSuccs`, fences move the
  context, plain/pure stores and pure RMWs follow `RuleShapes`.
- `TreeJ.eraseWPR`: `EvTree.EraseWPR` at `T = ⊤` is a `TreeJ (SLREnv …)`.

Deliberately not covered: store-exclusive (LL/SC is
deferred: `ok` refuses an exclusive store), releasing RMWs (`rel = true`
RMWs: none in the two lock programs), and `SharedAccess.rmw` has no `noRet`,
so `SLREnv`'s `rmw` answers for both `noRet` values (a weaker, sound
environment; the precise one needs `noRet` in `SharedAccess.rmw`).
-/
import Kraken.SharedEnvInv
import Kraken.Promising.InvLink
import Kraken.Promising.SLR.RuleShapes

namespace Kraken.Promising.SLR.EnvSpike

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## Tree judgments with environment laws -/

/-- An event-tree judgment that an `AllEnv E` judgment transfers to, node by
node, with `Post` at the leaves. The access laws read the footprint of an
access with no declarations (`EvTree.access_empty`). -/
structure TreeJ (E : SharedEnv) (σ : Type) where
  W : EvTree σ → E.State → Prop
  Post : σ → E.State → Prop
  done : ∀ {s g}, Post s g → W (.done s) g
  fault : ∀ {m g}, W (.fault m) g
  choose : ∀ {n : Nat} {k : Fin n → EvTree σ} {g}, (∀ i, W (k i) g) → W (.choose n k) g
  load : ∀ {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {ret : Val → EvTree σ} {g},
    E.ok (.load k xcl addr n) g → (∀ v g', E.step (.load k xcl addr n) g v g' → W (ret v) g') →
      W (.load k xcl ⟨addr, n⟩ ret) g
  store : ∀ {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {ret : Bool → EvTree σ} {g},
    E.ok (.store k xcl addr n v) g → (∀ b g', E.step (.store k xcl addr n v) g b g' → W (ret b) g') →
      W (.store k xcl ⟨addr, n⟩ v ret) g
  rmw : ∀ {k : RmwKind} {noRet : Bool} {addr : BitVec 64} {n : Nat} {op : Val → Option Val}
    {ret : Val → EvTree σ} {g},
    E.ok (.rmw k addr n op) g → (∀ old g', E.step (.rmw k addr n op) g old g' → W (ret old) g') →
      W (.rmw k noRet ⟨addr, n⟩ op ret) g
  fence : ∀ {k : FenceKind} {ret : Unit → EvTree σ} {g},
    E.ok (.fence k) g → (∀ g', E.step (.fence k) g () g' → W (ret ()) g') → W (.fence k ret) g

/-- **The invariant environment's judgment is a `TreeJ`**: `EvTree.AllInv G Q` in `inv S G`. -/
def TreeJ.allInv (S : SharedEnv.Layout) (G : Loc → Val → Prop) {σ : Type} (Q : σ → Prop) :
    TreeJ (SharedEnv.inv S G) σ where
  W t _ := t.AllInv G Q
  Post s _ := Q s
  done h := h
  fault := trivial
  choose h := h
  load _ h := fun v hv => h v () hv
  store hok h := ⟨hok.2, fun b hb => h b () hb⟩
  rmw hok h := fun old hold => ⟨hok.2 old hold, h old () hold⟩
  fence _ h := fun _ => h () trivial

/-- A tree judgment read through `EvTree.map f` (the ISA adapters map the
machine state of the leaves into the ISA state). -/
def TreeJ.comap {E : SharedEnv} {σ τ : Type} (J : TreeJ E τ) (f : σ → τ) : TreeJ E σ where
  W t g := J.W (t.map f) g
  Post s g := J.Post (f s) g
  done h := J.done h
  fault := J.fault
  choose h := J.choose h
  load h₁ h₂ := J.load h₁ h₂
  store h₁ h₂ := J.store h₁ h₂
  rmw h₁ h₂ := J.rmw h₁ h₂
  fence h₁ h₂ := J.fence h₁ h₂

/-! ## The per-instruction SLR environment -/

/-- The angelic choices of SLR's write rules, made up front (an `AllEnv`
environment answers demonically). `rel l v`: a store of `v` to `l` is a
release that attaches slots (otherwise the location's release predicate
must be pure at `v`, `eraseWPR_store_pure`). `split r g l v tw m`: the
resource a release keeps and the resource its slots carry
(`eraseWPR_store_rel`'s `r'` and `R`). -/
structure Plan where
  rel : Loc → Val → Bool
  split : Res → Ghost → Loc → Val → Time → Memory → Res × Res

/-- The state after a non-pending write of the plan: a pure store gains the
message, a release keeps `(split …).1`; the ghost records the write. -/
def Plan.after (pl : Plan) (r : Res) (g : Ghost) (l : Loc) (v : Val) (tw : Time) (m : Memory)
    (ss : List Slot) : Res × Ghost :=
  if pl.rel l v then ((pl.split r g l v tw m).1, storeGhost g l tw true ss)
  else (r.addW l (v, tw), storeGhost g l tw false [])

/-- **The per-instruction SLR environment** of thread `tid`, for the
instruction of thread `t` in configuration `c` with views `iv`, at the
validity-free erasure. State: `(r, g, cx)`.

- load: any `readSuccs` outcome, `(r, g)` unchanged;
- fence: `fenceStep`;
- store (non-exclusive): permitted if the thread may write `l` and either the
  release predicate is pure at `v` (`¬ pl.rel l v`) or the plan's split
  satisfies it (`pl.rel l v`, with the release conditions); outcomes: every
  write event, fulfilling a pending promise (ghost `unpend`) or appending
  (the plan's ghost update, every slot list the erasure allows);
- RMW (pure writes only): `eraseWPR_rmw_pure`'s conditions, for both `noRet`
  readings; outcomes: a failed compare (nothing written), a fulfilled pending
  promise, or the claim of the read message's update slots. -/
def SLREnv (A : Arch) (tid : Nat) (iv : InstrViews) (rF : Nat → Res) (c : Config I) (t : Thread I)
    (pl : Plan) : SharedEnv where
  State := Res × Ghost × Ctx
  ok a s := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v =>
      xcl = false ∧ 0 < (s.1.wr ⟨addr, n⟩).q ∧
      (pl.rel ⟨addr, n⟩ v = false → Pred.Pure (s.2.1.rel ⟨addr, n⟩) v) ∧
      (pl.rel ⟨addr, n⟩ v = true → ∀ cx' tw,
        cx' ∈ writeSuccs A tid (iv.forStore s.2.2.stores) s.2.2 k false ⟨addr, n⟩ v none →
        WriteEv tid s.2.2 cx' ⟨addr, n⟩ v none tw → tw ∉ s.2.1.pend →
        ErAt rF (fun _ => True) c t tid s.1 s.2.1 s.2.2 →
        tw ∉ s.2.2.prom ∧ ¬ s.2.1.Claimed (⟨addr, n⟩, tw) ∧
        (s.2.1.rel ⟨addr, n⟩).P v cx'.mem tw (pl.split s.1 s.2.1 ⟨addr, n⟩ v tw cx'.mem).2 ∧
        (pl.split s.1 s.2.1 ⟨addr, n⟩ v tw cx'.mem).1.op (pl.split s.1 s.2.1 ⟨addr, n⟩ v tw cx'.mem).2 =
          s.1.addW ⟨addr, n⟩ (v, tw))
    | .rmw k addr n op =>
      ∀ noRet, ∀ x ∈ readSuccs A iv (fenceOptCtx A s.2.2)
          (if noRet then .plain else (A.rmwKind k).loadKind) false ⟨addr, n⟩ noRet,
        ∀ new, op x.2.1 = some new → ∀ cx' tw,
        cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
          (x.2.2.loadViews.getLastD 0) →
        WriteEv tid x.2.2 cx' ⟨addr, n⟩ new (some x.1) tw → tw ∉ s.2.1.pend →
        (∀ p ∈ x.2.2.prom, p ∈ s.2.1.pend → ∀ w, x.2.2.mem.get? p = some w → w.loc ≠ ⟨addr, n⟩) ∧
        0 < (s.1.wr ⟨addr, n⟩).q ∧ Pred.Pure (s.2.1.rel ⟨addr, n⟩) new ∧
        (claimedSlots s.2.1 ⟨addr, n⟩ x.1 ≠ [] → x.1 ≤ (rmwAfter A k noRet ⟨addr, n⟩ cx').views.wfloor)
  step a s ret s' := match a, ret with
    | .load k xcl addr n, v =>
      s'.1 = s.1 ∧ s'.2.1 = s.2.1 ∧ ∃ tr, (tr, v, s'.2.2) ∈ readSuccs A iv s.2.2 k xcl ⟨addr, n⟩
    | .fence k, _ => s' = (s.1, s.2.1, fenceStep s.2.2 k)
    | .store k _ addr n v, b =>
      b = true ∧ ∃ tw, s'.2.2 ∈ writeSuccs A tid (iv.forStore s.2.2.stores) s.2.2 k false ⟨addr, n⟩ v none ∧
        WriteEv tid s.2.2 s'.2.2 ⟨addr, n⟩ v none tw ∧
        ((tw ∈ s.2.1.pend ∧ s'.1 = s.1 ∧ s'.2.1 = unpend s.2.1 tw) ∨
         (tw ∉ s.2.1.pend ∧ ∃ ss,
           (pl.rel ⟨addr, n⟩ v = true → ErAt rF (fun _ => True) c t tid s.1 s.2.1 s.2.2 ∧
              SlotsFor s.2.1 (total (setRes rF tid s.1) s.2.1 c).acq ⟨addr, n⟩ tw v s'.2.2.mem ss ∧
              Res.prod (ss.map (·.res)) = (pl.split s.1 s.2.1 ⟨addr, n⟩ v tw s'.2.2.mem).2) ∧
           (s'.1, s'.2.1) = pl.after s.1 s.2.1 ⟨addr, n⟩ v tw s'.2.2.mem ss))
    | .rmw k addr n op, old =>
      ∃ noRet, ∃ x ∈ readSuccs A iv (fenceOptCtx A s.2.2)
          (if noRet then .plain else (A.rmwKind k).loadKind) false ⟨addr, n⟩ noRet,
        x.2.1 = old ∧
        ((op old = none ∧ s' = (s.1, s.2.1, fenceOptCtx A x.2.2)) ∨
         ∃ new, op old = some new ∧ ∃ cx' tw,
          cx' ∈ writeSuccs A tid iv x.2.2 (A.rmwKind k).storeKind true ⟨addr, n⟩ new (some x.1)
            (x.2.2.loadViews.getLastD 0) ∧
          WriteEv tid x.2.2 cx' ⟨addr, n⟩ new (some x.1) tw ∧
          ((tw ∈ s.2.1.pend ∧ s' = (s.1, unpend s.2.1 tw, rmwAfter A k noRet ⟨addr, n⟩ cx')) ∨
           (tw ∉ s.2.1.pend ∧
             s' = ((s.1.op (Res.prod ((claimedSlots s.2.1 ⟨addr, n⟩ x.1).map (·.res)))).addW ⟨addr, n⟩ (new, tw),
               rmwGhost s.2.1 ⟨addr, n⟩ x.1 tw false [], rmwAfter A k noRet ⟨addr, n⟩ cx'))))

/-! ## `EraseWPR` is a tree judgment of `SLREnv` -/

/-- **The laws.** `EvTree.EraseWPR` at the validity-free erasure, with the
postcondition read on the environment state, is a `TreeJ` of `SLREnv`: each
law is one of the generic per-event lemmas (`eraseWPR_load`,
`eraseWPR_fence`, `eraseWPR_store_pure`, `eraseWPR_store_rel`,
`eraseWPR_rmw_pure`). -/
def TreeJ.eraseWPR {A : Arch} {tid : Nat} {iv : InstrViews} {rF : Nat → Res} {c : Config I} {t : Thread I}
    (pl : Plan) (hn : tid < c.threads.size) {σ : Type} (Post : σ → Res × Ghost × Ctx → Prop) :
    TreeJ (SLREnv A tid iv rF c t pl) σ where
  W tr s := tr.EraseWPR A tid iv rF (fun _ => True) c t (fun st r g cx => Post st (r, g, cx)) s.1 s.2.1 s.2.2
  Post := Post
  done h := h
  fault := trivial
  choose h := fun i => h i
  load _ h := EvTree.eraseWPR_load fun x hx => h x.2.1 (_, _, x.2.2) ⟨rfl, rfl, x.1, hx⟩
  fence _ h := EvTree.eraseWPR_fence (h _ rfl)
  store := by
    intro k xcl addr n v ret s hok h
    obtain ⟨r, g, cx⟩ := s
    obtain ⟨rfl, hpos, hpure, hrelok⟩ := hok
    cases hrel : pl.rel ⟨addr, n⟩ v with
    | false =>
      refine EvTree.eraseWPR_store_pure hn hpos (hpure hrel) (fun cx' tw hc hev hpd => ?_)
        (fun cx' tw hc hev hpd => ?_)
      · exact h true (r, unpend g tw, cx') ⟨rfl, tw, hc, hev, .inl ⟨hpd, rfl, rfl⟩⟩
      · exact h true (r.addW ⟨addr, n⟩ (v, tw), storeGhost g ⟨addr, n⟩ tw false [], cx')
          ⟨rfl, tw, hc, hev, .inr ⟨hpd, [], fun h => absurd h (by simp [hrel]),
            by simp [Plan.after, hrel]⟩⟩
    | true =>
      refine EvTree.eraseWPR_store_rel hn hpos (fun cx' tw hc hev hpd => ?_)
        (fun cx' tw hc hev hpd E => ?_)
      · exact h true (r, unpend g tw, cx') ⟨rfl, tw, hc, hev, .inl ⟨hpd, rfl, rfl⟩⟩
      · obtain ⟨hnp, hcl, hP, hop⟩ := hrelok hrel cx' tw hc hev hpd E
        refine ⟨hnp, hcl, _, _, hP, hop, fun ss hss hprod => ?_⟩
        exact h true (_, storeGhost g ⟨addr, n⟩ tw true ss, cx')
          ⟨rfl, tw, hc, hev, .inr ⟨hpd, ss, fun _ => ⟨E, hss, hprod⟩, by simp [Plan.after, hrel]⟩⟩
  rmw := by
    intro k noRet addr n op ret s hok h
    obtain ⟨r, g, cx⟩ := s
    refine EvTree.eraseWPR_rmw_pure hn (fun x hx hop => ?_) (fun x hx new hop cx' tw hc hev hpd => ?_)
      (fun x hx new hop cx' tw hc hev hpd => ?_)
    · exact h x.2.1 _ ⟨noRet, x, hx, rfl, .inl ⟨hop, rfl⟩⟩
    · exact h x.2.1 _ ⟨noRet, x, hx, rfl, .inr ⟨new, hop, cx', tw, hc, hev, .inl ⟨hpd, rfl⟩⟩⟩
    · obtain ⟨hnp, hpos, hpure, htr⟩ := hok noRet x hx new hop cx' tw hc hev hpd
      exact ⟨hnp, hpos, hpure, htr, h x.2.1 _ ⟨noRet, x, hx, rfl, .inr ⟨new, hop, cx', tw, hc, hev, .inr ⟨hpd, rfl⟩⟩⟩⟩

end Kraken.Promising.SLR.EnvSpike
