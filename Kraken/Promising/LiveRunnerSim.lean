/-
**Liveness under a state map: a trace-level
simulation, ISA-neutral.**

The existing liveness theorems (`ticket3_x64_live_pf`, `spin_cmpx_live_pf`, …)
are stated for threads without declarations (`decls = {}`): their per-cell
tree lemmas read `exec` through `exec_eq_of_codeAt`. The `.kl` runner's
threads carry declarations. The safety side reached `decls = ds` by reading a
mixed-size access as a fault, which every (∀-path) tree judgment accepts; a
liveness proof needs ∃-facts (enabledness, a read of the last write), so it
needs the *same* tree. This file transfers a liveness statement along a map
`f` of thread states (for declarations: `st ↦ st.noDecls`) that commutes with
`exec` on a step-closed set `G` of states (`ExecSim f G`):

- `runTree_map`, `finishInstr_mapT`, `stepOne_mapT`: one instruction of the
  mapped thread is the instruction of the thread, mapped;
- `runTree_prom_nil`, `stepOne_prom_nil`: an instruction of a thread with no
  outstanding promise leaves none;
- on a promise-free (stuttering) trace whose initial threads are in `G` with
  no promise (`GoodC`), every configuration is `GoodC` (`trace_good`), the
  mapped sequence is a stuttering trace (`mapTrace`), and `PromiseFree`,
  `WeakFair` and `MemFair` hold of it (`mapTrace_promiseFree`,
  `mapTrace_weakFair`, `mapTrace_memFair`);
- **`liveFrom_transfer`**, **`progressFrom_transfer`**: `LiveFrom` /
  `Spin.ProgressFrom` under `WeakFair ∧ MemFair ∧ PromiseFree` at the mapped
  initial configuration gives the same at the original one, for `Waiting` /
  `Done` predicates that read a thread only through the map.

Promise-free fragment only: with promises the transfer would also have to
carry certification (`certify`), which runs a thread alone through future
instructions; not attempted.
-/
import Kraken.Promising.LiveTicketStep
import Kraken.Promising.LiveSpinCommon

namespace Kraken.Promising.Live.RunnerSim

open Kraken Kraken.Promising Kraken.Promising.Live

variable {I : ISA}

/-! ## Maps of threads, outcomes and configurations -/

/-- A thread with its state mapped. -/
def mapT (f : I.State → I.State) (t : Thread I) : Thread I := { t with st := f t.st }

/-- An outcome with its thread mapped. -/
def mapO (f : I.State → I.State) (o : Outcome I) : Outcome I := { o with thread := mapT f o.thread }

/-- A configuration with every thread mapped. -/
def mapC (f : I.State → I.State) (c : Config I) : Config I := { c with threads := c.threads.map (mapT f) }

@[simp] theorem mapT_st (f : I.State → I.State) (t : Thread I) : (mapT f t).st = f t.st := rfl
@[simp] theorem mapT_prom (f : I.State → I.State) (t : Thread I) : (mapT f t).prom = t.prom := rfl
@[simp] theorem mapT_views (f : I.State → I.State) (t : Thread I) : (mapT f t).views = t.views := rfl
@[simp] theorem mapO_thread (f : I.State → I.State) (o : Outcome I) : (mapO f o).thread = mapT f o.thread := rfl
@[simp] theorem mapO_mem (f : I.State → I.State) (o : Outcome I) : (mapO f o).mem = o.mem := rfl
@[simp] theorem mapO_log (f : I.State → I.State) (o : Outcome I) : (mapO f o).log = o.log := rfl
@[simp] theorem mapC_mem (f : I.State → I.State) (c : Config I) : (mapC f c).mem = c.mem := rfl

@[simp] theorem mapC_get? (f : I.State → I.State) (c : Config I) (i : Nat) :
    (mapC f c).threads[i]? = c.threads[i]?.map (mapT f) := by
  simp [mapC]

/-- A thread of the mapped configuration satisfying `P` is a thread whose
map satisfies `P`. -/
theorem exists_mapC (f : I.State → I.State) (c : Config I) (i : Nat) (P : Thread I → Prop) :
    (∃ t, (mapC f c).threads[i]? = some t ∧ P t) ↔ ∃ t, c.threads[i]? = some t ∧ P (mapT f t) := by
  simp only [mapC_get?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨_, ⟨t, ht, rfl⟩, hp⟩; exact ⟨t, ht, hp⟩
  · rintro ⟨t, ht, hp⟩; exact ⟨_, ⟨t, ht, rfl⟩, hp⟩

theorem mapC_withThread (f : I.State → I.State) (c : Config I) (tid : Nat) (t : Thread I) (mem : Memory) :
    mapC f (c.withThread tid t mem) = (mapC f c).withThread tid (mapT f t) mem := by
  simp only [mapC, Config.withThread, Array.set!, Array.map_setIfInBounds]

/-! ## One instruction -/

section Instr

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A run of a mapped tree is the run of the tree, mapped.** -/
theorem runTree_map {σ τ : Type} (f : σ → τ) :
    ∀ (tree : EvTree σ) (c : Ctx),
      runTree A tid iv c (tree.map f) = (runTree A tid iv c tree).map (Except.map fun p => (f p.1, p.2))
  | .done _, _ => rfl
  | .fault _, _ => rfl
  | .choose _ k, c => by
    simp only [runTree, EvTree.map, List.map_flatMap]
    congr 1; funext i; exact runTree_map f (k i) c
  | .load _ _ _ ret, c => by
    simp only [runTree, EvTree.map, List.map_flatMap]
    congr 1; funext x; exact runTree_map f (ret x.2.1) x.2.2
  | .store _ xcl _ _ ret, c => by
    simp only [runTree, EvTree.map, List.map_append, runTree_map f (ret true),
      runTree_map f (ret false)]
    congr 1
    · split <;> (try split) <;> simp [List.map_flatMap]
    · split <;> simp
  | .fence _ ret, c => by
    simp only [runTree, EvTree.map]; exact runTree_map f (ret ()) _
  | .rmw _ _ _ op ret, c => by
    simp only [runTree, EvTree.map, List.map_flatMap]
    congr 1; funext x
    split
    · exact runTree_map f (ret x.2.1) _
    · simp only [List.map_flatMap]
      congr 1; funext c''; exact runTree_map f (ret x.2.1) _

@[simp] theorem setRegView_mapT (f : I.State → I.State) (t : Thread I) (r : I.RegId) (a b : View) :
    (mapT f t).setRegView r a b = mapT f (t.setRegView r a b) := rfl
@[simp] theorem rviewOf_mapT (f : I.State → I.State) (t : Thread I) (r : I.RegId) :
    (mapT f t).rviewOf r = t.rviewOf r := rfl
@[simp] theorem wviewOf_mapT (f : I.State → I.State) (t : Thread I) (r : I.RegId) :
    (mapT f t).wviewOf r = t.wviewOf r := rfl

theorem foldl_mapT {α : Type} (f : I.State → I.State) (F : Thread I → α → Thread I)
    (hF : ∀ t a, F (mapT f t) a = mapT f (F t a)) :
    ∀ (l : List α) (t : Thread I), l.foldl F (mapT f t) = mapT f (l.foldl F t)
  | [], _ => rfl
  | a :: l, t => by simp only [List.foldl_cons, hF]; exact foldl_mapT f F hF l (F t a)

/-- **`finishInstr` at a mapped state is `finishInstr`, mapped.** The
thread's own state is overwritten, so it does not matter. -/
theorem finishInstr_mapT (f : I.State → I.State) (t t' : Thread I) (ht : t'.rview = t.rview)
    (hw : t'.wview = t.wview) (d : InstrDeps I.RegId) (st : I.State) (c : Ctx) :
    finishInstr t' d iv (f st) c = (finishInstr t d iv st c).map (mapT f) := by
  have h0 : ({ t' with st := f st, views := c.views, prom := c.prom } : Thread I) =
      mapT f { t with st, views := c.views, prom := c.prom } := by
    cases t; cases t'; simp_all [mapT]
  simp only [finishInstr]
  rw [h0]
  repeat rw [foldl_mapT]
  all_goals try (intro t a; (try cases a); rfl)
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem mem_ite_nil_left {α : Type} {b : Bool} {L : List α} {x : α} (h : x ∈ (if b then [] else L)) : x ∈ L := by
  cases b <;> simp_all

theorem mem_ite_nil_right {α : Type} {b : Bool} {L : List α} {x : α} (h : x ∈ (if b then L else [])) : x ∈ L := by
  cases b <;> simp_all

theorem fenceStep_prom (c : Ctx) (k : FenceKind) : (fenceStep c k).prom = c.prom := by
  cases k <;> rfl

theorem ite_fence_prom (b : Bool) (c : Ctx) (k : FenceKind) :
    (if b = true then fenceStep c k else c).prom = c.prom := by
  cases b <;> simp [fenceStep_prom]

/-- **An instruction run from a context with no outstanding promise ends
with none**: a write "promises now" and fulfils at once (`writeSuccs_nil`). -/
theorem runTree_prom_nil {σ : Type} : ∀ (tree : EvTree σ) (c : Ctx), c.prom = [] →
    ∀ s c', Except.ok (s, c') ∈ runTree A tid iv c tree → c'.prom = []
  | .done _, c, hp, s, c', h => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    rw [h.2]; exact hp
  | .fault _, _, _, _, _, h => by simp [runTree] at h
  | .choose _ k, c, hp, s, c', h => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_prom_nil (k i) c hp s c' h
  | .load _ _ _ ret, c, hp, s, c', h => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
    refine runTree_prom_nil _ _ ?_ s c' h
    exact hp
  | .store _ xcl _ _ ret, c, hp, s, c', h => by
    simp only [runTree] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨c1, h1, h⟩ := List.mem_flatMap.mp (mem_ite_nil_left h)
      have hw : c1.prom = [] := by
        cases xcl
        · exact (TicketStep.writeSuccs_nil A tid _ hp (.inr h1)).2.1
        · exact (TicketStep.writeSuccs_nil A tid _ hp (.inl h1)).2.1
      exact runTree_prom_nil (ret true) c1 hw s c' h
    · refine runTree_prom_nil _ _ ?_ s c' (mem_ite_nil_right h)
      exact hp
  | .fence _ ret, c, hp, s, c', h => by
    simp only [runTree] at h
    exact runTree_prom_nil (ret ()) _ (by rw [fenceStep_prom]; exact hp) s c' h
  | .rmw _ _ _ op ret, c, hp, s, c', h => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
    have hp0 : (if A.rmwFence = true then fenceStep c .sy else c).prom = [] := by
      rw [ite_fence_prom]; exact hp
    obtain ⟨t, v, e, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    split at h
    · refine runTree_prom_nil _ _ ?_ s c' h
      rw [ite_fence_prom]; exact hp0
    · obtain ⟨c2, h2, h⟩ := List.mem_flatMap.mp h
      have hp2 := (TicketStep.writeSuccs_nil A tid iv (h := .inl h2) (by exact hp0)).2.1
      refine runTree_prom_nil _ _ ?_ s c' h
      rw [ite_fence_prom]
      split <;> exact hp2

/-- **An instruction of a thread with no outstanding promise leaves none.** -/
theorem stepOne_prom_nil (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hp : t.prom = []) (hs : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : o.thread.prom = [] := by
  obtain ⟨tree, c', -, hr, hpr, -⟩ := SLR.stepOne_runK A hs ho
  rw [hpr]
  exact runTree_prom_nil A tid _ tree _ hp _ c' hr

/-- An instruction's views read only the register views. -/
theorem instrViews_mapT (f : I.State → I.State) (t : Thread I) (d : InstrDeps I.RegId) :
    instrViews (mapT f t) d = instrViews t d := rfl

end Instr

/-! ## The simulation hypothesis -/

/-- **`f` commutes with one instruction on the step-closed set `G`**: `exec`
of a mapped state is `exec`, mapped (and the register dependencies and the
instruction's text agree); every leaf of an instruction from `G` is in `G`;
`f` is injective on `G`. For declarations, `f = noDecls` and `G` says the
state runs a fixed executable with declarations `ds` that agree with its
cells (`LiveRunnerX64.lean`). -/
structure ExecSim (f : I.State → I.State) (G : I.State → Prop) : Prop where
  exec : ∀ s, G s → I.exec (f s) = (I.exec s).map (EvTree.map f)
  deps : ∀ s, G s → I.deps (f s) = I.deps s
  showInstr : ∀ s, G s → I.showInstr (f s) = I.showInstr s
  leaves : ∀ s, G s → ∀ tree, I.exec s = some tree → tree.All G
  inj : ∀ s s', G s → G s' → f s = f s' → s = s'

section Sim

variable {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)
include hS

/-- **One instruction of a mapped thread is the instruction, mapped.** -/
theorem stepOne_mapT (A : Arch) {t : Thread I} (hG : G t.st) (tid : Nat) (mem : Memory) :
    stepOne A (mapT f t) tid mem = (stepOne A t tid mem).map (List.map (Except.map (mapO f))) := by
  simp only [stepOne, mapT_st, hS.exec _ hG, hS.deps _ hG, hS.showInstr _ hG, instrViews_mapT]
  cases I.exec t.st with
  | none => rfl
  | some tree =>
    show some _ = some _
    rw [runTree_map, List.flatMap_map, List.map_flatMap]
    simp only [mapT_views, mapT_prom]
    refine congrArg (fun g => some (List.flatMap g _)) (funext fun x => ?_)
    rcases x with m | ⟨st, c'⟩
    · rfl
    · simp only [Except.map, List.map_map]
      rw [finishInstr_mapT _ f t (mapT f t) rfl rfl, List.map_map]
      rfl

/-- A halted mapped thread is a halted thread. -/
theorem halted_mapT {t : Thread I} (hG : G t.st) : (mapT f t).halted = t.halted := by
  simp only [Thread.halted, mapT_st, hS.exec _ hG, Option.isNone_map]

/-- The outcomes of a mapped thread are the mapped outcomes. -/
theorem ok_mem_mapT {A : Arch} {t : Thread I} (hG : G t.st) {tid : Nat} {mem : Memory}
    {outs' : List (Except String (Outcome I))} (hs : stepOne A (mapT f t) tid mem = some outs') {o' : Outcome I}
    (ho : .ok o' ∈ outs') :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o' = mapO f o := by
  rw [stepOne_mapT hS A hG] at hs
  cases h : stepOne A t tid mem with
  | none => rw [h] at hs; cases hs
  | some outs =>
    rw [h] at hs
    obtain rfl := Option.some.inj hs
    obtain ⟨x, hx, e⟩ := List.mem_map.mp ho
    cases x with
    | error m => cases e
    | ok o => exact ⟨outs, o, rfl, hx, (Except.ok.inj e).symm⟩

/-! ## Configurations -/

/-- **The configuration invariant**: every thread's state is in `G` and
has no outstanding promise. -/
def GoodC (G : I.State → Prop) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → G t.st ∧ t.prom = []

omit hS in
theorem goodC_init {states : List I.State} (initMem : List (Loc × Val)) (h : ∀ s ∈ states, G s) :
    GoodC G (Config.init states initMem) := by
  intro i t ht
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨h s (List.mem_of_getElem? hs), rfl⟩

omit hS in
theorem mapC_init (states : List I.State) (initMem : List (Loc × Val)) :
    mapC f (Config.init states initMem) = Config.init (states.map f) initMem := by
  simp only [mapC, Config.init, List.map_toArray, List.map_map]
  rfl

/-- An instruction step keeps the invariant. -/
theorem goodC_step {A : Arch} {tid : Nat} {c c' : Config I} (hg : GoodC G c) (hi : InstrBy A tid c c') :
    GoodC G c' := by
  obtain ⟨t, outs, o, ht, hs, ho, rfl⟩ := hi
  obtain ⟨hG, hp⟩ := hg tid t ht
  intro i u hu
  rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at hu
  split at hu
  · cases hu
    exact ⟨stepOne_leaf A hs ho (hS.leaves _ hG), stepOne_prom_nil A hp hs ho⟩
  · exact hg i u hu

/-- `mapC f` is injective on `GoodC G`. -/
theorem mapC_inj {c c' : Config I} (hg : GoodC G c) (hg' : GoodC G c') (h : mapC f c = mapC f c') : c = c' := by
  obtain ⟨ths, mem⟩ := c
  obtain ⟨ths', mem'⟩ := c'
  simp only [mapC, Config.mk.injEq] at h
  obtain ⟨h1, rfl⟩ := h
  have hsz : ths.size = ths'.size := by simpa using congrArg Array.size h1
  refine Config.mk.injEq _ _ _ _ |>.mpr ⟨Array.ext hsz fun i hi hi' => ?_, rfl⟩
  have e := congrArg (fun a => a[i]?) h1
  simp only [Array.getElem?_map, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi',
    Option.map_some, Option.some.injEq] at e
  obtain ⟨hG, -⟩ := hg i _ (Array.getElem?_eq_getElem hi)
  obtain ⟨hG', -⟩ := hg' i _ (Array.getElem?_eq_getElem hi')
  have est : ths[i].st = ths'[i].st := hS.inj _ _ hG hG' (congrArg Thread.st e)
  have e' := e
  revert e' est
  generalize ths[i] = a
  generalize ths'[i] = b
  intro est e'
  cases a; cases b
  simp only [mapT, Thread.mk.injEq] at e' est ⊢
  exact ⟨est, e'.2⟩

theorem mapC_final {c : Config I} (hg : GoodC G c) (hf : c.final = true) : (mapC f c).final = true := by
  simp only [Config.final, Array.all_eq_true] at hf ⊢
  intro i hi
  have hi' : i < c.threads.size := by simpa [mapC] using hi
  have := hf i hi'
  obtain ⟨hG, -⟩ := hg i _ (Array.getElem?_eq_getElem hi')
  simp only [mapC, Array.getElem_map, mapT_prom]
  rw [halted_mapT hS hG]
  exact this

/-- An instruction step, mapped. -/
theorem instrBy_mapC {A : Arch} {tid : Nat} {c c' : Config I} (hg : GoodC G c) (hi : InstrBy A tid c c') :
    InstrBy A tid (mapC f c) (mapC f c') := by
  obtain ⟨t, outs, o, ht, hs, ho, rfl⟩ := hi
  obtain ⟨hG, -⟩ := hg tid t ht
  exact ⟨mapT f t, outs.map (Except.map (mapO f)), mapO f o, by simp [ht],
    by rw [mapC_mem, stepOne_mapT hS A hG, hs]; rfl, List.mem_map.mpr ⟨_, ho, rfl⟩, mapC_withThread f c tid _ _⟩

/-- An instruction step (with no promise left) is a successor, mapped. -/
theorem mem_succs_mapC {A : Arch} {fuel tid : Nat} {c c' : Config I} (hg : GoodC G c)
    (hi : InstrBy A tid c c') : mapC f c' ∈ (succs A (mapC f c) fuel).1 := by
  obtain ⟨t, outs, o, ht, hs, ho, rfl⟩ := hi
  obtain ⟨hG, hp⟩ := hg tid t ht
  rw [mapC_withThread]
  refine reach_mem_succs A fuel (outs := outs.map (Except.map (mapO f))) (o := mapO f o) ?_
    (List.mem_map.mpr ⟨_, ho, rfl⟩) (by simp [stepOne_prom_nil A hp hs ho])
  simp [stepThread, ht, stepOne_mapT hS A hG, hs]

omit hS in
/-- An instruction step of a promise-free thread is a successor. -/
theorem mem_succs_of_instrBy {A : Arch} {fuel tid : Nat} {c c' : Config I} (hg : GoodC G c)
    (hi : InstrBy A tid c c') : c' ∈ (succs A c fuel).1 := by
  obtain ⟨t, outs, o, ht, hs, ho, rfl⟩ := hi
  obtain ⟨-, hp⟩ := hg tid t ht
  exact reach_mem_succs A fuel (by simp [stepThread, ht, hs]) ho (by simp [stepOne_prom_nil A hp hs ho])

/-- **Enabledness reflects**: a thread enabled in the mapped configuration
is enabled (and instruction-enabled) in the configuration. -/
theorem enabled_of_mapC {A : Arch} {fuel tid : Nat} {c : Config I} (hg : GoodC G c)
    (he : Enabled A fuel tid (mapC f c)) : Enabled A fuel tid c := by
  -- an ok first step of the mapped thread
  have key : ∃ t' outs' o', (mapC f c).threads[tid]? = some t' ∧ stepOne A t' tid (mapC f c).mem = some outs' ∧
      .ok o' ∈ outs' := by
    obtain ⟨c', -, ⟨t, outs, o, ht, hs, ho, -⟩ | ⟨t, p, ht, ⟨t1, mem1, outs, o, hnp, hs, ho, -⟩, -⟩⟩ := he
    · exact ⟨t, outs, o, ht, hs, ho⟩
    · cases hnp with
      | refl => exact ⟨t, outs, o, ht, hs, ho⟩
      | step h₁ _ =>
        obtain ⟨outs', o', hs', ho', -⟩ := h₁
        exact ⟨t, outs', o', ht, hs', ho'⟩
  obtain ⟨t', outs', o', ht', hs', ho'⟩ := key
  simp only [mapC_get?, Option.map_eq_some_iff] at ht'
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨hG, hp⟩ := hg tid t ht
  obtain ⟨outs, o, hs, ho, -⟩ := ok_mem_mapT hS hG hs' ho'
  have hi : InstrBy A tid c (c.withThread tid o.thread o.mem) := ⟨t, outs, o, ht, hs, ho, rfl⟩
  exact ⟨_, mem_succs_of_instrBy hg hi, .inl hi⟩

end Sim

/-! ## Traces -/

section Trace

variable [I.LawfulState] {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)
  {A : Arch} {fuel : Nat} {tr : TraceS A fuel I} (hpf : PromiseFree A tr.cfg) (hg0 : GoodC G (tr.cfg 0))

include hS hpf hg0

/-- **Every configuration of a promise-free trace from a `GoodC` start is
`GoodC`.** -/
theorem trace_good (i : Nat) : GoodC G (tr.cfg i) := by
  induction i with
  | zero => exact hg0
  | succ i ih =>
    rcases SpinCommon.step_or hpf i with he | ⟨tid, hi, -⟩
    · rw [he]; exact ih
    · exact goodC_step hS ih hi

/-- **The mapped trace.** -/
def mapTrace : TraceS A fuel I where
  cfg i := mapC f (tr.cfg i)
  step i := by
    rcases tr.step i with hm | ⟨hf, he⟩
    · obtain ⟨tid, -, hi | hp⟩ := stepBy_of_mem_succs hm
      · exact .inl (mem_succs_mapC hS (trace_good hS hpf hg0 i) hi)
      · exact absurd hp (hpf i tid)
    · exact .inr ⟨mapC_final hS (trace_good hS hpf hg0 i) hf, by rw [he]⟩

@[simp] theorem mapTrace_cfg (i : Nat) : (mapTrace hS hpf hg0).cfg i = mapC f (tr.cfg i) := rfl

theorem mapTrace_promiseFree : PromiseFree A (mapTrace hS hpf hg0).cfg := by
  intro i tid hp
  obtain ⟨t', ht', hne⟩ := hp.prom_ne
  simp only [mapTrace_cfg, mapC_get?, Option.map_eq_some_iff] at ht'
  obtain ⟨t, ht, rfl⟩ := ht'
  exact hne (trace_good hS hpf hg0 (i + 1) tid t ht).2

theorem mapTrace_weakFair (hwf : WeakFair A fuel tr.cfg) : WeakFair A fuel (mapTrace hS hpf hg0).cfg := by
  intro tid ⟨n, hn⟩ m
  obtain ⟨i, hi, hs⟩ := hwf tid ⟨n, fun i hi => enabled_of_mapC hS (trace_good hS hpf hg0 i) (hn i hi)⟩ m
  refine ⟨i, hi, ?_⟩
  obtain ⟨hm, hi' | hp⟩ := hs
  · exact ⟨mem_succs_mapC hS (trace_good hS hpf hg0 i) hi', .inl (instrBy_mapC hS (trace_good hS hpf hg0 i) hi')⟩
  · exact absurd hp (hpf i tid)

theorem mapTrace_memFair (hmf : MemFair A tr.cfg) : MemFair A (mapTrace hS hpf hg0).cfg := by
  intro tid l hinf i ts w hw hl
  have hinf' : InfOften (fun i => ∃ ts, ReadsAt A tr.cfg tid l ts i) := by
    intro n
    obtain ⟨j, hj, ts', t', outs', o', ht', hs', ho', he', hr⟩ := hinf n
    refine ⟨j, hj, ts', ?_⟩
    simp only [mapTrace_cfg, mapC_get?, Option.map_eq_some_iff] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    have hg := trace_good hS hpf hg0 j
    obtain ⟨hG, -⟩ := hg tid t ht
    obtain ⟨outs, o, hs, ho, rfl⟩ := ok_mem_mapT hS hG hs' ho'
    have hi : InstrBy A tid (tr.cfg j) ((tr.cfg j).withThread tid o.thread o.mem) := ⟨t, outs, o, ht, hs, ho, rfl⟩
    have he : tr.cfg (j + 1) = (tr.cfg j).withThread tid o.thread o.mem :=
      mapC_inj hS (trace_good hS hpf hg0 (j + 1)) (goodC_step hS hg hi)
        (by rw [mapC_withThread]; exact he')
    exact ⟨t, outs, o, ht, hs, ho, he, hr⟩
  obtain ⟨j, hij, t, ht, hle⟩ := hmf tid l hinf' i ts w hw hl
  exact ⟨j, hij, mapT f t, by simp [ht], hle⟩

end Trace

/-! ## Transfer of liveness statements -/

section Transfer

variable [I.LawfulState] {f : I.State → I.State} {G : I.State → Prop} (hS : ExecSim f G)

/-- The promise-free fairness hypothesis of the existing liveness theorems. -/
abbrev FairPF (A : Arch) (fuel : Nat) (cfg : Nat → Config I) : Prop :=
  WeakFair A fuel cfg ∧ MemFair A cfg ∧ PromiseFree A cfg

include hS in
/-- **Transfer of `LiveFrom` (promise-free fragment).** If every thread of
`c0` is in `G` with no promise, and `Waiting`/`Done` read a configuration
only through `mapC f`, then liveness from `mapC f c0` gives liveness from
`c0`. -/
theorem liveFrom_transfer {A : Arch} {fuel : Nat} {c0 : Config I} (hg0 : GoodC G c0)
    {W D : Nat → Config I → Prop} (hW : ∀ tid c, W tid (mapC f c) ↔ W tid c)
    (hD : ∀ tid c, D tid (mapC f c) ↔ D tid c)
    (h : LiveFrom A fuel (mapC f c0) (FairPF A fuel) W D) : LiveFrom A fuel c0 (FairPF A fuel) W D := by
  intro tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  have hg0' : GoodC G (tr.cfg 0) := h0 ▸ hg0
  obtain ⟨j, hij, hd⟩ := h (mapTrace hS hpf hg0') (by simp [h0])
    ⟨mapTrace_weakFair hS hpf hg0' hwf, mapTrace_memFair hS hpf hg0' hmf, mapTrace_promiseFree hS hpf hg0'⟩
    tid i ((hW _ _).mpr hw)
  exact ⟨j, hij, (hD _ _).mp hd⟩

include hS in
/-- **Transfer of `Spin.ProgressFrom` (promise-free fragment).** -/
theorem progressFrom_transfer {A : Arch} {fuel : Nat} {c0 : Config I} (hg0 : GoodC G c0)
    {W D : Nat → Config I → Prop} (hW : ∀ tid c, W tid (mapC f c) ↔ W tid c)
    (hD : ∀ tid c, D tid (mapC f c) ↔ D tid c)
    (h : Spin.ProgressFrom A fuel (mapC f c0) (FairPF A fuel) W D) :
    Spin.ProgressFrom A fuel c0 (FairPF A fuel) W D := by
  intro tr h0 ⟨hwf, hmf, hpf⟩ tid i hw
  have hg0' : GoodC G (tr.cfg 0) := h0 ▸ hg0
  obtain ⟨j, hij, tid', hn, hd⟩ := h (mapTrace hS hpf hg0') (by simp [h0])
    ⟨mapTrace_weakFair hS hpf hg0' hwf, mapTrace_memFair hS hpf hg0' hmf, mapTrace_promiseFree hS hpf hg0'⟩
    tid i ((hW _ _).mpr hw)
  exact ⟨j, hij, tid', fun h' => hn ((hD _ _).mpr h'), (hD _ _).mp hd⟩

end Transfer

end Kraken.Promising.Live.RunnerSim

#print axioms Kraken.Promising.Live.RunnerSim.liveFrom_transfer
#print axioms Kraken.Promising.Live.RunnerSim.progressFrom_transfer
