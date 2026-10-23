/-
The bridge spike: progress of the target, so that `Correct` holds without
hypotheses (`correct`).

Progress (`Sim.progress`) is a fact about the target alone: every
configuration reachable from the loaded start configuration has no faulting
step and every live thread can step. It does not follow from `Rel`, for two
reasons:

* `Rel` says nothing about the writer's views before its store, and the
  store is enabled only if its timestamp can be above them (`writeOk`);
* `Rel` does not say that the writer has no promise after its store. That
  fact holds of every reachable configuration (the step into the post-store
  phase is certified, and a halted thread certifies only with no promise,
  `cert_halted`), but it is not preserved by every promise-free solo step:
  a store from a thread with two outstanding promises ends with one. The
  lockstep lemma needs its per-thread relation (`TRw`, built on `WPhase`)
  preserved by every such step, certified or not, so `WPhase` cannot carry
  it; it is a fact of `StepSemInf`-reachable configurations, whose steps
  carry `CertOk`.

So this file proves a target invariant of reachable configurations,
separately from `Rel`. It is generic in the reader (`TInvG`, `RSpec`): the
reader is described by a predicate `P` on its states and the facts of
`RSpec` (its solo steps keep `P`, its memory and its promises; it certifies
only with no promise; its trees have no fault; a non-halted reader can
step), so that the spinning reader of `Spike/Bridge/LoopCorrect.lean` reuses
it. For the straight-line reader (`rspec`):

* `WInv`: the writer before its store is its start thread with some promise
  set (`{ Thread.init st0 with prom := P }`; only promise steps happen there,
  and `promThread` changes nothing but the promises), the promise set empty
  or one promise of its own store's message; after its store it has no
  promise;
* `RInv`: the reader never promises, and is before or after its load;
* `MsgsOK`: every message is the writer's store.

From `TInv`:

* `noFault`: neither tree has a `fault` leaf, so no `stepOne` outcome is an
  error (`stepOne_no_error`), and a halted thread has no `stepOne`;
* `writer_can_step`: the writer's views and register views are `0`, so the
  store can promise now at `|M| + 1` or fulfil its promise `p > 0`, and the
  thread after it is halted with no promise, hence certified;
* `reader_can_step`: the reader can read the latest timestamp (no later
  write hides it, the reader has no promise), and is then halted with no
  promise.

`BaseProgress` collects the three target facts (no fault; final or some live
thread; every live thread steps) independently of `ExtMachine.Progress`, so
that both the present `Progress` (every live thread steps) and a variant
that also demands a live thread unless the configuration has terminated
follow from it (`progress_of_base`).
-/
import Spike.Bridge.Sim

namespace Spike.Bridge

open Kraken.Promising Kraken.Promising.Lower Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep
open Scc.Sem (ExtMachine)

/-! ## The target invariant -/

section Inv

variable {I : ISA}

/-- **The writer's target phase**: before its store, its start thread with
promise set empty or one promise of its own store's message; after it, no
promise. -/
def WInv (F : BitVec 64) (v1 : Val) (st0 sW : I.State) (t : Thread I) (mem : Memory) : Prop :=
  (t = { Thread.init st0 with prom := t.prom } ∧
      (t.prom = [] ∨ ∃ p, t.prom = [p] ∧ mem.get? p = some ⟨⟨F, 8⟩, v1, 0⟩)) ∨
    (t.st = sW ∧ t.prom = [])

/-- The straight-line reader's states: before or after its load. -/
def RSt (st1 : I.State) (fR : Val → I.State) (s : I.State) : Prop :=
  s = st1 ∨ ∃ v, s = fR v

/-- Every message is the writer's store of `v1` to the flag. -/
def MsgsOK (F : BitVec 64) (v1 : Val) (mem : Memory) : Prop :=
  ∀ j (h : j < mem.msgs.size), mem.msgs[j] = ⟨⟨F, 8⟩, v1, 0⟩

/-- **The target invariant** of reachable configurations, for a reader whose
states satisfy `P`: the writer's phase, no reader promise, every message the
writer's. -/
def TInvG (F : BitVec 64) (v1 : Val) (st0 sW : I.State) (P : I.State → Prop) (c : Config I) : Prop :=
  ∃ t0 t1, c.threads = #[t0, t1] ∧ MsgsOK F v1 c.mem ∧ WInv F v1 st0 sW t0 c.mem ∧ t1.prom = [] ∧ P t1.st

/-- The target invariant of the straight-line program. -/
abbrev TInv (F : BitVec 64) (v1 : Val) (st0 sW st1 : I.State) (fR : Val → I.State) : Config I → Prop :=
  TInvG F v1 st0 sW (RSt st1 fR)

/-- **What the invariant needs of the reader** (thread `1`), whose states
satisfy `P`: its solo steps keep its memory, its promises and `P`; it
certifies only with no promise; no outcome of its instructions is an error;
and, with no promise and not halted, it can step (from any configuration
whose messages are all the writer's). -/
structure RSpec (A : Arch) (F : BitVec 64) (v1 : Val) (P : I.State → Prop) : Prop where
  step : ∀ {t : Thread I} {mem : Memory} {q : Thread I × Memory}, P t.st → ThreadStep A 1 (t, mem) q →
    q.2 = mem ∧ q.1.prom = t.prom ∧ P q.1.st
  cert : ∀ {t : Thread I} {mem : Memory}, P t.st → CertOk A 1 t mem → t.prom = []
  ok : ∀ {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}, P t.st →
    stepOne A t 1 mem = some outs → ∀ m, (.error m : Except String (Outcome I)) ∉ outs
  can : ∀ {c : Config I} {t0 t1 : Thread I}, c.threads = #[t0, t1] → MsgsOK F v1 c.mem → t1.prom = [] →
    P t1.st → t1.halted = false → ∃ c', StepSemInf A 1 c c'

theorem MsgsOK.push {F : BitVec 64} {v1 : Val} {mem : Memory} (h : MsgsOK F v1 mem) :
    MsgsOK F v1 (mem.append ⟨⟨F, 8⟩, v1, 0⟩).1 := by
  intro j hj
  simp only [Memory.append, Array.size_push] at hj ⊢
  rw [Array.getElem_push]
  split
  · exact h j _
  · rfl

/-- Changing the promises of a start thread gives a start thread. -/
theorem init_with_prom {st : I.State} {t : Thread I} (h : t = { Thread.init st with prom := t.prom })
    (P : List Nat) : ({ t with prom := P } : Thread I) = { Thread.init st with prom := P } := by
  rw [h]

theorem tinvG_init {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {P : I.State → Prop} (h1 : P st1) :
    TInvG F v1 st0 sW P (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) :=
  ⟨Thread.init st0, Thread.init st1, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
    .inl ⟨rfl, .inl rfl⟩, rfl, h1⟩

variable (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW : I.State} {P : I.State → Prop}
  (hWS : WShape I F v1 st0 sW) (hR : RSpec A F v1 P)
include hWS hR

/-- **`TInvG` is preserved by every fuel-free step.** -/
theorem tinvG_step {c c' : Config I} {tid : Nat} (hI : TInvG F v1 st0 sW P c) (h : StepSemInf A tid c c') :
    TInvG F v1 st0 sW P c' := by
  obtain ⟨t0, t1, hc, hM, hW, hp1, hP1⟩ := hI
  rcases h with ⟨t, outs, o, ht, hst, ho, hcert, rfl⟩ | ⟨t, w, ht, hw, hcert, rfl⟩
  · rw [hc] at ht
    have hts : ThreadStep A tid (t, c.mem) (o.thread, o.mem) := ⟨outs, o, hst, ho, rfl⟩
    match tid, ht, hts, hcert with
    | 0, ht, hts, hcert =>
      change some t0 = some t at ht
      cases ht
      rcases hW with ⟨hst0, -⟩ | ⟨hsW, -⟩
      · have hst0' : t0.st = st0 := by rw [hst0]; rfl
        obtain ⟨hq, hq'⟩ := writer_out A hWS hst0' hts
        have hq1 : o.thread.st = sW := hq
        have hp := cert_halted A (hq1 ▸ hWS.wd) hcert
        refine ⟨o.thread, t1, ?_, ?_, .inr ⟨hq1, hp⟩, hp1, hP1⟩
        · show c.threads.set! 0 o.thread = _
          rw [hc]; rfl
        · show MsgsOK F v1 o.mem
          rcases hq' with ⟨p, -, -, -, hm⟩ | ⟨-, hm⟩
          · have hm' : o.mem = c.mem := hm
            rw [hm']; exact hM
          · have hm' : o.mem = (c.mem.append ⟨⟨F, 8⟩, v1, 0⟩).1 := hm
            rw [hm']; exact hM.push
      · exact absurd hts (no_threadStep A (hsW ▸ hWS.wd))
    | 1, ht, hts, hcert =>
      change some t1 = some t at ht
      cases ht
      obtain ⟨hm, hpr, hP'⟩ := hR.step hP1 hts
      have hm' : o.mem = c.mem := hm
      refine ⟨t0, o.thread, ?_, ?_, ?_, hpr.trans hp1, hP'⟩
      · show c.threads.set! 1 o.thread = _
        rw [hc]; rfl
      · show MsgsOK F v1 o.mem
        rw [hm']; exact hM
      · show WInv F v1 st0 sW t0 o.mem
        rw [hm']; exact hW
    | n + 2, ht, _, _ => simp at ht
  · rw [hc] at ht
    match tid, ht, hw, hcert with
    | 0, ht, hw, hcert =>
      change some t0 = some t at ht
      cases ht
      rcases hW with ⟨hst0, -⟩ | ⟨hsW, -⟩
      · have hst0' : t0.st = st0 := by rw [hst0]; rfl
        rcases certW_pre_shape A hWS (t := promThread t0 c.mem w) hst0' hcert with hnil | ⟨p, hp1, hg⟩
        · simp at hnil
        · have hP0 : t0.prom = [] := by
            have hl := congrArg List.length hp1
            simp only [List.length_append, List.length_singleton] at hl
            exact List.length_eq_zero_iff.mp (by omega)
          have hpe : (c.mem.append w).2 = p := by
            have := hp1
            simp only [hP0, List.nil_append, List.cons.injEq] at this
            exact this.1
          subst hpe
          have hgw : (c.mem.append w).1.get? (c.mem.append w).2 = some w := by
            simp [Memory.append, Memory.get?]
          obtain rfl : w = ⟨⟨F, 8⟩, v1, 0⟩ := Option.some.inj (hgw.symm.trans hg)
          refine ⟨promThread t0 c.mem ⟨⟨F, 8⟩, v1, 0⟩, t1, ?_, hM.push, .inl ⟨init_with_prom hst0 _, .inr ⟨_, hp1, hg⟩⟩,
            ‹t1.prom = []›, hP1⟩
          show c.threads.set! 0 _ = _
          rw [hc]; rfl
      · have := cert_halted A (hsW ▸ hWS.wd) hcert
        simp at this
    | 1, ht, hw, hcert =>
      change some t1 = some t at ht
      cases ht
      have := hR.cert (t := promThread t1 c.mem w) hP1 hcert
      simp at this
    | n + 2, ht, _, _ => simp at ht

/-- **`TInvG` holds of every reachable configuration.** -/
theorem tinvG_reach {c c' : Config I} (h : ReachableSemInf A c c') (hI : TInvG F v1 st0 sW P c) :
    TInvG F v1 st0 sW P c' := by
  induction h with
  | refl => exact hI
  | step tid hst _ ih => exact ih (tinvG_step A hWS hR hI hst)

end Inv

/-! ## No faulting step -/

section NoFault

variable {I : ISA} (A : Arch)

theorem runTree_store_ok {σ : Type} (tid : Nat) (iv : InstrViews) (c : Ctx) (k : Kraken.StoreKind) (l : Loc) (v : Val)
    (s : σ) : ∀ x ∈ runTree A tid iv c (.store k false l v fun _ => .done s), ∃ p, x = .ok p := by
  intro x hx
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap,
    List.mem_singleton] at hx
  obtain ⟨c1, -, rfl⟩ := hx
  exact ⟨_, rfl⟩

theorem runTree_load_ok {σ : Type} (tid : Nat) (iv : InstrViews) (c : Ctx) (k : Kraken.LoadKind) (l : Loc)
    (f : Val → σ) : ∀ x ∈ runTree A tid iv c (.load k false l fun v => .done (f v)), ∃ p, x = .ok p := by
  intro x hx
  simp only [runTree, List.mem_flatMap, List.mem_singleton] at hx
  obtain ⟨⟨ts, v, c1⟩, -, rfl⟩ := hx
  exact ⟨_, rfl⟩

/-- **An instruction whose tree runs to no error has no faulting outcome.** -/
theorem stepOne_no_error {t : Thread I} {tid : Nat} {mem : Memory} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree)
    (hok : ∀ x ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree, ∃ p, x = .ok p)
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) (m : String) :
    (.error m : Except String (Outcome I)) ∉ outs := by
  unfold stepOne at hs
  rw [hex] at hs
  have hs' : _ = outs := Option.some.inj hs
  subst hs'
  intro hm
  rw [List.mem_flatMap] at hm
  obtain ⟨r, hr, hm⟩ := hm
  obtain ⟨⟨st, c'⟩, rfl⟩ := hok r hr
  simp at hm

theorem runTree_done_ok {σ : Type} (tid : Nat) (iv : InstrViews) (c : Ctx) (s : σ) :
    ∀ x ∈ runTree A tid iv c (.done s), ∃ p, x = .ok p := by
  intro x hx
  simp only [runTree, List.mem_singleton] at hx
  exact ⟨_, hx⟩

variable {F : BitVec 64} {v1 : Val} {st0 sW : I.State} {P : I.State → Prop}
  (hWS : WShape I F v1 st0 sW) (hR : RSpec A F v1 P)
include hWS hR

/-- **No reachable configuration has a faulting step**: the writer's tree has
no `fault` leaf, a halted thread has no next instruction, and the reader's
instructions have no error outcome (`RSpec.ok`). -/
theorem noFaultG {c : Config I} (hI : TInvG F v1 st0 sW P c) (tid : Nat) (m : String) :
    ¬ c.FaultStep A tid m := by
  obtain ⟨t0, t1, hc, -, hW, -, hP1⟩ := hI
  rintro ⟨outs, hs, hm⟩
  cases ht : c.threads[tid]? with
  | none => simp [stepThread, ht] at hs
  | some t =>
    have hs' : stepOne A t tid c.mem = some outs := by simpa [stepThread, ht] using hs
    rw [hc] at ht
    match tid, ht, hs', hm with
    | 0, ht, hs', hm =>
      change some t0 = some t at ht
      cases ht
      rcases hW with ⟨hst0, -⟩ | ⟨hsW, -⟩
      · have hst0' : t0.st = st0 := by rw [hst0]; rfl
        obtain ⟨ks, hw⟩ := hWS.wr
        exact stepOne_no_error A (hst0' ▸ hw) (runTree_store_ok A _ _ _ _ _ _ _) hs' m hm
      · have hex : I.exec t0.st = none := hsW ▸ hWS.wd
        simp [stepOne, hex] at hs'
    | 1, ht, hs', hm =>
      change some t1 = some t at ht
      cases ht
      exact hR.ok hP1 hs' m hm
    | n + 2, ht, _, _ => simp at ht

end NoFault

/-! ## Every live thread can step -/

section Steps

variable {I : ISA} (A : Arch)

/-- `finishInstr` has an outcome. -/
theorem finishInstr_nonempty (t : Thread I) (d : Kraken.InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx) :
    ∃ th, th ∈ finishInstr t d iv st c := by
  unfold finishInstr
  simp only
  split <;> simp

/-- A thread with no promise certifies. -/
theorem certOk_nil {tid : Nat} {t : Thread I} {mem : Memory} (h : t.prom = []) : CertOk A tid t mem :=
  ⟨t, mem, .refl _, h⟩

/-- The register views of a thread whose register views are all `0` join
to `0`. -/
theorem joinViews_zero {T : Thread I} (hr : T.rview = Array.replicate I.numRegs 0)
    (hw : T.wview = Array.replicate I.numRegs 0) (rs : List I.RegId) : T.joinViews rs = (0, 0) := by
  unfold Thread.joinViews
  suffices h : ∀ acc : View × View, acc = (0, 0) →
      rs.foldl (fun (r, w) x => (max r (T.rviewOf x), max w (T.wviewOf x))) acc = (0, 0) from h _ rfl
  induction rs with
  | nil => intro acc h; exact h
  | cons x xs ih =>
    intro acc h
    subst h
    apply ih
    simp [Thread.rviewOf, Thread.wviewOf, hr, hw]

/-- **A thread with initial views stores at every positive timestamp.** -/
theorem writeOk_zero {tid tid' : Nat} {T : Thread I} (hr : T.rview = Array.replicate I.numRegs 0)
    (hw : T.wview = Array.replicate I.numRegs 0) (hv : T.views = {}) {d : Kraken.InstrDeps I.RegId}
    {mem : Memory} {k : Kraken.StoreKind} {l : Loc} {x : Nat} (hx : 0 < x) :
    writeOk tid ((instrViews T d).forStore 0) (ctx0 tid' T mem) k l none 0 x = true := by
  have hz : ∀ r w, (instrViews T d).dataPer[0]? = some (r, w) → r = 0 ∧ w = 0 := by
    intro r w h
    simp only [instrViews] at h
    rw [List.getElem?_map] at h
    cases h' : d.dataRegsPer[0]? with
    | none => simp [h'] at h
    | some rs => simp [h', joinViews_zero hr hw] at h; exact ⟨h.1.symm, h.2.symm⟩
  unfold InstrViews.forStore
  split
  · rename_i r w h
    obtain ⟨rfl, rfl⟩ := hz r w h
    simp [writeOk, Lower.writePre, instrViews, joinViews_zero hr hw, Views.getCoh, hv, hx]
  · simp [writeOk, Lower.writePre, instrViews, joinViews_zero hr hw, Views.getCoh, hv, hx]

/-- The latest timestamp is never hidden by a later write. -/
theorem writeIn_last (mem : Memory) (l : Loc) (hi : Nat) : mem.writeIn l mem.last hi = false := by
  unfold Memory.writeIn
  rw [List.any_eq_false]
  intro i _
  have : mem.get? (mem.last + i + 1) = none := by
    unfold Memory.get?
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    exact Array.getElem?_eq_none (by unfold Memory.last; omega)
  simp [this]

/-- The flag can be read at the latest timestamp. -/
theorem read_last {F : BitVec 64} {v1 : Val} {mem : Memory} (hM : MsgsOK F v1 mem) :
    ∃ v, mem.read? ⟨F, 8⟩ mem.last = some v := by
  by_cases h0 : mem.last = 0
  · exact ⟨mem.initVal ⟨F, 8⟩, by unfold Memory.read?; simp only [h0, ↓reduceIte]⟩
  · have hlt : mem.last - 1 < mem.msgs.size := by
      have h1 : mem.msgs.size ≠ 0 := h0
      show mem.msgs.size - 1 < mem.msgs.size
      omega
    have hg : mem.get? mem.last = some ⟨⟨F, 8⟩, v1, 0⟩ := by
      unfold Memory.get?
      simp only [h0, ↓reduceIte]
      rw [Array.getElem?_eq_getElem hlt, hM _ hlt]
    refine ⟨v1, ?_⟩
    unfold Memory.read?
    simp only [h0, ↓reduceIte, hg]
    simp

/-- **A thread at a load of the flag can step**, with no promise: read the
latest timestamp (no later write hides it, whatever its views); it then
still has no promise. -/
theorem load_can_step {F : BitVec 64} {v1 : Val} {c : Config I} {t0 t1 : Thread I} (hc : c.threads = #[t0, t1])
    (hM : MsgsOK F v1 c.mem) (hp : t1.prom = []) {kl : Kraken.LoadKind} {g : Val → I.State}
    (hex : I.exec t1.st = some (.load kl false ⟨F, 8⟩ fun v => .done (g v))) :
    ∃ c', StepSemInf A 1 c c' := by
  have ht : c.threads[1]? = some t1 := by rw [hc]; rfl
  obtain ⟨v, hv⟩ := read_last hM
  have hx := (mem_readSuccs A (iv := instrViews t1 (I.deps t1.st)) (c := ctx0 1 t1 c.mem) (k := kl) (xcl := false)
    (l := ⟨F, 8⟩) (noRet := false)).mpr ⟨c.mem.last, v, rfl, Nat.le_refl _, hv, writeIn_last _ _ _, by simp [hp]⟩
  have hp1 := readSuccs_prom A _ hx
  obtain ⟨th, hth⟩ := finishInstr_nonempty t1 (I.deps t1.st) (instrViews t1 (I.deps t1.st)) (g v)
    (readNext A (instrViews t1 (I.deps t1.st)) (ctx0 1 t1 c.mem) kl false ⟨F, 8⟩ false c.mem.last v)
  have hcert := certOk_nil A (tid := 1) (mem := (readNext A (instrViews t1 (I.deps t1.st)) (ctx0 1 t1 c.mem) kl false
    ⟨F, 8⟩ false c.mem.last v).mem) (((finishInstr_relKey hth).1).trans (hp1.trans hp))
  exact ⟨_, .inl ((instrSemInf_load_iff A 1 ht hex).mpr ⟨_, _, _, th, hx, hth, hcert, rfl⟩)⟩

/-- **A thread at a register-only instruction can step**, with no promise. -/
theorem done_can_step {c : Config I} {t0 t1 : Thread I} (hc : c.threads = #[t0, t1]) (hp : t1.prom = [])
    {s : I.State} (hex : I.exec t1.st = some (.done s)) : ∃ c', StepSemInf A 1 c c' := by
  have ht : c.threads[1]? = some t1 := by rw [hc]; rfl
  obtain ⟨th, hth⟩ := finishInstr_nonempty t1 (I.deps t1.st) (instrViews t1 (I.deps t1.st)) s (ctx0 1 t1 c.mem)
  have hcert := certOk_nil A (tid := 1) (mem := c.mem) (((finishInstr_relKey hth).1).trans hp)
  exact ⟨_, .inl ((instrSemInf_done_iff A 1 ht hex).mpr ⟨th, hth, hcert, rfl⟩)⟩

variable {F : BitVec 64} {v1 : Val} {st0 sW : I.State} (hWS : WShape I F v1 st0 sW)
include hWS

/-- **The writer before its store can step**: promise now (no promise) or
fulfil its promise; either way it is then halted with no promise. -/
theorem writer_can_step {c : Config I} {t0 t1 : Thread I} (hc : c.threads = #[t0, t1])
    (hst0 : t0 = { Thread.init st0 with prom := t0.prom })
    (hP : t0.prom = [] ∨ ∃ p, t0.prom = [p] ∧ c.mem.get? p = some ⟨⟨F, 8⟩, v1, 0⟩) :
    ∃ c', StepSemInf A 0 c c' := by
  have ht : c.threads[0]? = some t0 := by rw [hc]; rfl
  obtain ⟨ks, hw⟩ := hWS.wr
  have hst0' : t0.st = st0 := by rw [hst0]; rfl
  have hex := hst0' ▸ hw
  have hok : ∀ x, 0 < x → writeOk 0 ((instrViews t0 (I.deps t0.st)).forStore 0) (ctx0 0 t0 c.mem)
      (A.storeKind ks) ⟨F, 8⟩ none 0 x = true := by
    intro x hx
    exact writeOk_zero (by rw [hst0]; rfl) (by rw [hst0]; rfl) (by rw [hst0]; rfl) hx
  -- the context after the write has no promise
  suffices H : ∃ c1, c1 ∈ writeSuccs A 0 ((instrViews t0 (I.deps t0.st)).forStore 0) (ctx0 0 t0 c.mem) ks false
      ⟨F, 8⟩ v1 none ∧ c1.prom = [] by
    obtain ⟨c1, hc1, hp1⟩ := H
    obtain ⟨th, hth⟩ := finishInstr_nonempty t0 (I.deps t0.st) (instrViews t0 (I.deps t0.st)) sW c1
    have hcert : CertOk A 0 th c1.mem := certOk_nil A (((finishInstr_relKey hth).1).trans hp1)
    exact ⟨_, .inl ((instrSemInf_store_iff A 0 ht hex).mpr ⟨c1, th, hc1, hth, hcert, rfl⟩)⟩
  rcases hP with hP | ⟨p, hP, hg⟩
  · refine ⟨_, (mem_writeSuccs_iff A 0 _).mpr (.inr ⟨hok _ (Nat.succ_pos _), rfl⟩), ?_⟩
    simp [afterWrite, promiseNowCtx, hP]
  · have hp0 : 0 < p := by
      rcases Nat.eq_zero_or_pos p with rfl | h
      · simp [Memory.get?] at hg
      · exact h
    refine ⟨_, (mem_writeSuccs_iff A 0 _).mpr (.inl ⟨p, by simp [hP], hg, hok p hp0, rfl⟩), ?_⟩
    simp [afterWrite, hP]

end Steps

/-! ## Progress -/

section Progress

variable {I : ISA} (A : Arch)

/-- Thread `tid` exists and has not halted with no promise (the `live`
observation of `ExtMachine.ofBase`). -/
def BaseLive (c : Config I) (tid : Nat) : Prop :=
  ∃ t, c.threads[tid]? = some t ∧ ¬ (t.halted = true ∧ t.prom = [])

/-- **The target's progress facts**, stated on the existing machine and
independently of `ExtMachine.Progress`: no faulting step; the configuration
is final or some thread is live; every live thread can step. -/
def BaseProgress (c : Config I) : Prop :=
  (∀ tid m, ¬ c.FaultStep A tid m) ∧ (c.final = true ∨ ∃ tid, BaseLive c tid) ∧
    ∀ tid, BaseLive c tid → ∃ c', StepSemInf A tid c c'

/-- **`ExtMachine.Progress` of the base instance**, under any code marks,
from the target's progress facts: terminated (`Config.final`), or some
thread live and every live thread able to step. -/
theorem progress_of_base {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)}
    {μ : Scc.Sem.Marks} (hμ : ∀ k, μ.site k = none) {c : (ExtMachine.ofBase I A rv pl).Cfg} (h : BaseProgress A c.1) :
    (ExtMachine.ofBase I A rv pl).Progress μ c := by
  obtain ⟨hf, hfl, hs⟩ := h
  refine ⟨fun ⟨tid, m, h⟩ => hf tid m h, ?_⟩
  rcases hfl with hfin | hl
  · exact .inl (by simp [hfin])
  · refine .inr ⟨hl, fun tid hl => ?_⟩
    obtain ⟨c', h'⟩ := hs tid hl
    exact ⟨[], (c', ()), (ExtMachine.ofBase_step_iff hμ).mpr ⟨rfl, h'⟩⟩

variable {F : BitVec 64} {v1 : Val} {st0 sW : I.State} {P : I.State → Prop}
  (hWS : WShape I F v1 st0 sW) (hR : RSpec A F v1 P)
include hWS hR

/-- **The target's progress facts hold under `TInvG`.** -/
theorem baseProgressG {c : Config I} (hI : TInvG F v1 st0 sW P c) : BaseProgress A c := by
  refine ⟨noFaultG A hWS hR hI, ?_, ?_⟩
  · obtain ⟨t0, t1, hc, -, hW, hp1, -⟩ := hI
    rcases hW with ⟨hst0, -⟩ | ⟨hsW, hp0⟩
    · have hst0' : t0.st = st0 := by rw [hst0]; rfl
      refine .inr ⟨0, t0, by rw [hc]; rfl, fun ⟨hh, _⟩ => ?_⟩
      obtain ⟨ks, hw⟩ := hWS.wr
      simp [Thread.halted, hst0', hw] at hh
    · by_cases hh : t1.halted = true
      · left
        simp [Config.final, hc, Thread.halted, hsW, hWS.wd, hp0, hp1]
        simpa [Thread.halted] using hh
      · exact .inr ⟨1, t1, by rw [hc]; rfl, fun ⟨h, _⟩ => hh h⟩
  · obtain ⟨t0, t1, hc, hM, hW, hp1, hP1⟩ := hI
    rintro tid ⟨t, ht, hl⟩
    rw [hc] at ht
    match tid, ht with
    | 0, ht =>
      change some t0 = some t at ht
      cases ht
      rcases hW with ⟨hst0, hP⟩ | ⟨hsW, hp0⟩
      · exact writer_can_step A hWS hc hst0 hP
      · exact absurd ⟨by simp [Thread.halted, hsW, hWS.wd], hp0⟩ hl
    | 1, ht =>
      change some t1 = some t at ht
      cases ht
      exact hR.can hc hM hp1 hP1 (by simpa [hp1] using hl)
    | n + 2, ht => simp at ht

end Progress

/-! ## The straight-line reader -/

section Straight

variable {I : ISA} (A : Arch) {F : BitVec 64} {v1 : Val} {st0 sW st1 : I.State} {fR : Val → I.State}
  (hS : Shape I F v1 st0 sW st1 fR)
include hS

/-- **The straight-line reader meets `RSpec`.** -/
theorem rspec : RSpec A F v1 (RSt st1 fR) where
  step {t mem q} hP hts := by
    rcases hP with hst1 | ⟨v, hfv⟩
    · obtain ⟨hm, hpr, ts, v, hst', -⟩ := reader_out A hS hst1 hts
      exact ⟨hm, hpr, .inr ⟨v, hst'⟩⟩
    · exact absurd hts (no_threadStep A (hfv ▸ hS.rdd v))
  cert {t mem} hP hc := by
    rcases hP with hst1 | ⟨v, hst1⟩
    · exact certR_pre A hS hst1 hc
    · exact cert_halted A (hst1 ▸ hS.rdd v) hc
  ok {t mem outs} hP hs' m := by
    rcases hP with hst1 | ⟨v, hst1⟩
    · obtain ⟨kl, hr⟩ := hS.rd
      exact stepOne_no_error A (hst1 ▸ hr) (runTree_load_ok A _ _ _ _ _ _) hs' m
    · have hex : I.exec t.st = none := hst1 ▸ hS.rdd v
      simp [stepOne, hex] at hs'
  can {c t0 t1} hc hM hp hP hh := by
    rcases hP with hst1 | ⟨v, hst1⟩
    · obtain ⟨kl, hr⟩ := hS.rd
      exact load_can_step A hc hM hp (hst1 ▸ hr)
    · simp [Thread.halted, hst1, hS.rdd v] at hh

/-- **`TInv` holds of every configuration reachable from the start.** -/
theorem tinv_reach {c : Config I} (h : ReachableSemInf A (Config.init [st0, st1] [(⟨F, 8⟩, 0)]) c) :
    TInv F v1 st0 sW st1 fR c :=
  tinvG_reach A hS.toWShape (rspec A hS) h (tinvG_init (.inl rfl))

/-- **Progress, discharged**: every configuration reachable from the loaded
start configuration has progress. -/
theorem progressOf (rv : I.State → I.RegId → BitVec 64) (pl : I.State → BitVec 64 → Option (BitVec 64)) :
    ProgressOf A rv pl st0 st1 F := fun _ hre _ hμ =>
  progress_of_base A hμ (baseProgressG A hS.toWShape (rspec A hS) (tinv_reach A hS hre))

/-- **`Correct`**, with every clause of `Sim` discharged, progress included:
the existing machine as a target (`Target.ofBase`), the WeakCore program
from `srcInit`, any knobs and memory model on the source side, any budget. -/
theorem correct {rv : I.State → I.RegId → BitVec 64} {pl : I.State → BitVec 64 → Option (BitVec 64)}
    {rF rR : I.RegId} {k : Promises.Knobs} {arch : WeakMem.Arch}
    (hRg : Regs rv F st0 sW st1 fR rF rR) {Λ : Scc.Sem.Layout} (hΛ : FlagIn Λ F) (hwf : Λ.WF)
    (B : Scc.Sem.Budget) :
    Scc.Sem.Correct (Scc.Sem.Target.ofBase I A rv pl) (Scc.Sem.SrcSem.ofStep prog k arch (· = srcInit)) Λ B
      (asmOf st0 st1 F) :=
  correct_of_progress A hS hRg hΛ hwf B (progressOf A hS rv pl)

end Straight

end Spike.Bridge
