/-
**The fence-aware purity environment**: the
`RelWritesF` analogue of `SharedEnv.relPure` (`EnvG/RelPureEnv.lean`), for
the cell condition of `theorem1IIPure_of_relWritesF` /
`final_of_relWritesF`. ISA-neutral.

- `SharedEnv.relPureFQ A Q`: state `Bool`, the flag of `EvTree.RelWritesF`
  (a `fence .sy` sets it, other fences keep it, every access clears it). A
  store that is not a release (`A.storeKind k ≠ .rel`) must write a value
  satisfying `Q` unless the flag is set; an RMW write as in `relPureQ`
  (fence bits do not count for RMWs, as in `RelWritesF`). Every outcome is
  possible. `relPureF A rel` is the instance `Q l v = Pred.Pure (rel l) v`.
- `TreeJ.relWritesF`: the tree judgment "`RelWritesF A Q` at the flag, and
  every leaf satisfies `Post` at the flag it is reached with" (`RunsF`).
- `runTree_runsF`: an actual run of a `RunsF` tree from a context that is
  `FenceRel` whenever the flag is set ends in a leaf satisfying `Post` at a
  flag that again implies `FenceRel` of the final context.
- `relWritesF_reach`: a per-thread predicate `J tid st b` that every
  instruction keeps (as `RunsF`), under which every tree is `RelWritesF` at
  the flag `b`, gives a thread-level invariant at every reachable
  configuration: `∃ b, J tid t.st b ∧ (b → t.views.FenceRel)`, and with it
  the `Jinv`/`hJ`/`hcell` of `final_of_relWritesF` (`final_of_relWritesFJ`).

Why a separate environment and not `EnvG`: the cell condition must hold at
every *reachable* configuration, where `EnvG` (whose outcomes need erasure at
the anchor) offers no step; and `EnvG`'s fence bits (`fencedR ∧ fencedW`) are
more permissive than `RelWritesF`'s flag (`dmb ish; str
a; dmb ishst; str b` is fence-released for `EnvG` and for the hardware, not
for `RelWritesF`), so they cannot be read off as `RelWritesF`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnv
import Kraken.Promising.SLR.MpFence

namespace Kraken.SharedEnv

open Kraken.Promising Kraken.Promising.SLR

/-- **The fence-aware purity environment, at a value condition `Q`.** The
state is the `RelWritesF` flag. -/
def relPureFQ (A : Arch) (Q : Loc → Val → Prop) : SharedEnv where
  State := Bool
  ok a b := match a with
    | .load .. => True
    | .store k _ addr n v => A.storeKind k ≠ .rel → b = false → Q ⟨addr, n⟩ v
    | .rmw k addr n op => A.storeKind (A.rmwKind k).storeKind ≠ .rel →
        ∀ old new, op old = some new → Q ⟨addr, n⟩ new
    | .fence _ => True
  step a b _ b' := match a with
    | .fence k => b' = (b || decide (k = .sy))
    | _ => b' = false

/-- **The fence-aware purity environment**: non-release, non-fence-released
writes write values pure for their location's release predicate. -/
abbrev relPureF (A : Arch) (rel : Loc → Pred) : SharedEnv :=
  relPureFQ A fun l v => Pred.Pure (rel l) v

variable {A : Arch} {Q : Loc → Val → Prop}

@[simp] theorem relPureFQ_ok_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {b : (relPureFQ A Q).State} : (relPureFQ A Q).ok (.load k xcl addr n) b ↔ True := Iff.rfl

@[simp] theorem relPureFQ_ok_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val}
    {b : (relPureFQ A Q).State} :
    (relPureFQ A Q).ok (.store k xcl addr n v) b ↔ (A.storeKind k ≠ .rel → b = false → Q ⟨addr, n⟩ v) := Iff.rfl

@[simp] theorem relPureFQ_ok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val}
    {b : (relPureFQ A Q).State} :
    (relPureFQ A Q).ok (.rmw k addr n op) b ↔
      (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q ⟨addr, n⟩ new) := Iff.rfl

@[simp] theorem relPureFQ_ok_fence {k : FenceKind} {b : (relPureFQ A Q).State} :
    (relPureFQ A Q).ok (.fence k) b ↔ True := Iff.rfl

@[simp] theorem relPureFQ_step_fence {k : FenceKind} {b b' : (relPureFQ A Q).State} {u : Unit} :
    (relPureFQ A Q).step (.fence k) b u b' ↔ b' = (b || decide (k = .sy)) := Iff.rfl

@[simp] theorem relPureFQ_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat}
    {b b' : (relPureFQ A Q).State} {v : Val} : (relPureFQ A Q).step (.load k xcl addr n) b v b' ↔ b' = false :=
  Iff.rfl

@[simp] theorem relPureFQ_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val}
    {b b' : (relPureFQ A Q).State} {r : Bool} :
    (relPureFQ A Q).step (.store k xcl addr n v) b r b' ↔ b' = false := Iff.rfl

@[simp] theorem relPureFQ_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val}
    {b b' : (relPureFQ A Q).State} {v : Val} : (relPureFQ A Q).step (.rmw k addr n op) b v b' ↔ b' = false :=
  Iff.rfl

end Kraken.SharedEnv

namespace Kraken.Promising.SLR.EnvSpike

open Kraken Kraken.Promising

/-- **The leaves of a tree at the `RelWritesF` flag**: every leaf satisfies
`Post` at the flag it is reached with (`fence .sy` sets it, other fences
keep it, accesses clear it). -/
def RunsF {σ : Type} (Post : σ → Bool → Prop) : Bool → EvTree σ → Prop
  | b, .done s => Post s b
  | _, .fault _ => True
  | b, .choose _ k => ∀ i, RunsF Post b (k i)
  | _, .load _ _ _ ret => ∀ v, RunsF Post false (ret v)
  | _, .store _ _ _ _ ret => ∀ r, RunsF Post false (ret r)
  | _, .rmw _ _ _ _ ret => ∀ v, RunsF Post false (ret v)
  | b, .fence k ret => RunsF Post (b || decide (k = .sy)) (ret ())

/-- **`RelWritesF` as a tree judgment of `relPureFQ`**: the tree's writes
that are neither release nor fence-released satisfy `Q`, and every leaf
satisfies `Post` at its flag. -/
def TreeJ.relWritesF (A : Arch) (Q : Loc → Val → Prop) {σ : Type} (Post : σ → Bool → Prop) :
    TreeJ (SharedEnv.relPureFQ A Q) σ where
  W t b := t.RelWritesF A Q (b = true) ∧ RunsF Post b t
  Post s b := Post s b
  done h := ⟨trivial, h⟩
  fault := ⟨trivial, trivial⟩
  choose h := ⟨fun i => (h i).1, fun i => (h i).2⟩
  load _ h := ⟨fun v => (h v false rfl).1.mono (fun _ _ x => x) Bool.false_ne_true, fun v => (h v false rfl).2⟩
  store hok h := ⟨⟨fun hk hb => hok hk ((Bool.not_eq_true _).mp hb),
      fun r => (h r false rfl).1.mono (fun _ _ x => x) Bool.false_ne_true⟩, fun r => (h r false rfl).2⟩
  rmw hok h := ⟨⟨hok, fun v => (h v false rfl).1.mono (fun _ _ x => x) Bool.false_ne_true⟩,
    fun v => (h v false rfl).2⟩
  fence _ h := by
    refine ⟨fun ⟨⟩ => EvTree.RelWritesF.mono (fun _ _ x => x) ?_ (h _ rfl).1, (h _ rfl).2⟩
    intro hb
    exact (Bool.or_eq_true_iff.mp hb).imp id of_decide_eq_true

end Kraken.Promising.SLR.EnvSpike

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvSpike

variable {I : ISA}

private theorem mem_of_ite_nilFE {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

/-- **An actual run of a `RunsF` tree ends at a leaf satisfying `Post`**, at
a flag that implies `FenceRel` of the final context, when the start flag
implies it of the start context. -/
theorem runTree_runsF (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {Post : σ → Bool → Prop} :
    ∀ (tree : EvTree σ) (b : Bool) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      RunsF Post b tree → (b = true → c.views.FenceRel) → ∃ b', Post s b' ∧ (b' = true → c'.views.FenceRel)
  | .done _, b, c, s, c', h, hR, hF => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨b, hR, hF⟩
  | .fault _, _, _, _, _, h, _, _ => by simp [runTree] at h
  | .choose _ k, b, c, s, c', h, hR, hF => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_runsF A tid iv (k i) b c s c' h (hR i) hF
  | .load _ _ _ ret, _, _, s, c', h, hR, _ => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, -, h⟩ := h
    exact runTree_runsF A tid iv _ false _ s c' h (hR _) (fun e => absurd e (by simp))
  | .store _ xcl _ _ ret, _, _, s, c', h, hR, _ => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_ite_nilFE h
      rw [List.mem_flatMap] at h
      obtain ⟨c'', -, h⟩ := h
      exact runTree_runsF A tid iv _ false c'' s c' h (hR true) (fun e => absurd e (by simp))
    · split at h
      · exact runTree_runsF A tid iv _ false _ s c' h (hR false) (fun e => absurd e (by simp))
      · simp at h
  | .fence k ret, b, c, s, c', h, hR, hF => by
    simp only [runTree] at h
    refine runTree_runsF A tid iv (ret ()) _ _ s c' h hR fun hb => ?_
    rcases (Bool.or_eq_true_iff.mp hb).imp id of_decide_eq_true with hb | rfl
    · exact fenceStep_fenceRel (hF hb) k
    · exact fenceStep_sy_fenceRel c
  | .rmw k noRet l op ret, _, c, s, c', h, hR, _ => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, -, h⟩ := h
    split at h
    · exact runTree_runsF A tid iv _ false _ s c' h (hR _) (fun e => absurd e (by simp))
    · rw [List.mem_flatMap] at h
      obtain ⟨c'', -, h⟩ := h
      exact runTree_runsF A tid iv _ false _ s c' h (hR _) (fun e => absurd e (by simp))

/-- **One instruction keeps the thread-level invariant**: a step of a thread
whose tree `RunsF` from flag `b` (with `b → FenceRel`) ends at a thread state
satisfying `Post` at a flag implying the new views' `FenceRel`. -/
theorem stepOne_runsF {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Post : I.State → Bool → Prop} {b : Bool}
    (hR : ∀ tree, I.exec t.st = some tree → RunsF Post b tree) (hF : b = true → t.views.FenceRel) :
    ∃ b', Post o.thread.st b' ∧ (b' = true → o.thread.views.FenceRel) := by
  cases hex : I.exec t.st with
  | none => simp [stepOne, hex] at hstep
  | some tree =>
    unfold stepOne at hstep
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
      obtain ⟨b', hP, hF'⟩ := runTree_runsF A tid _ tree b _ st c' hr (hR tree hex) hF
      exact ⟨b', by rw [finishInstr_st hth]; exact hP, fun e => finishInstr_fenceRel hth (hF' e)⟩

/-- **Per-thread fence-aware purity at every reachable configuration.** If
every instruction of thread `tid` from a state satisfying `J tid · b` has a
tree that is `RelWritesF` at the flag `b` and whose leaves satisfy `J tid` at
their flag (`hstep`), and every initial thread state satisfies `J tid · false`
(`h0`), then every thread of every reachable configuration satisfies
`J tid` at a flag implying its views' `FenceRel`. -/
theorem relWritesF_reach [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {Q : Loc → Val → Prop} (J : Nat → I.State → Bool → Prop)
    (hstep : ∀ tid st b tree, J tid st b → I.exec st = some tree →
      tree.RelWritesF A Q (b = true) ∧ RunsF (J tid) b tree)
    (h0 : ∀ tid s, states[tid]? = some s → J tid s false)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) :
    ∀ tid t, c.threads[tid]? = some t → ∃ b, J tid t.st b ∧ (b = true → t.views.FenceRel) := by
  refine threadInv_reachable (J := fun tid t => ∃ b, J tid t.st b ∧ (b = true → t.views.FenceRel))
    (fun tid t mem outs o ⟨b, hJ, hF⟩ hs ho =>
      stepOne_runsF hs ho (fun tree hex => (hstep tid t.st b tree hJ hex).2) hF)
    (fun _ _ _ h => h) (fun tid t ht => ?_) hc
  obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
  exact ⟨false, h0 tid s hs, fun e => absurd e (by simp)⟩

/-- **`final_of_relWritesF` from a per-thread step property**
(`relWritesF_reach`): `Jinv tid t := ∃ b, J tid t.st b ∧ (b → FenceRel)`,
its reachability and the cell condition all come from `hstep` and `h0`. -/
theorem final_of_relWritesFJ [I.LawfulState] (A : Arch) (fuel : Nat) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (J : Nat → I.State → Bool → Prop)
    (hstep : ∀ tid st b tree, J tid st b → I.exec st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (g₀.rel l) v) (b = true) ∧ RunsF (J tid) b tree)
    (h0 : ∀ tid s, states[tid]? = some s → J tid s false)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid (GHyb g₀.rel) (K2Scope (model I) AllocIds) n m True
        (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_relWritesF A fuel hH hE hpend (fun tid t => ∃ b, J tid t.st b ∧ (b = true → t.views.FenceRel))
    (fun _ hc' tid t ht => relWritesF_reach J hstep h0 hc' tid t ht)
    (fun tid t tree ⟨b, hJ, hF⟩ hex => (hstep tid t.st b tree hJ hex).1.mono (fun _ _ x => x) hF) hsafe hc hf hfin

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.final_of_relWritesFJ
