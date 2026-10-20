/-
Theorem 1′ for the SLR-adapted resource model: the instance of the design-(V)
laws, the step lemmas Theorem 1′'s
induction routes through, the temporary NT-free scope, and the statement for
variant (ii).

## Contents

- `EnvExt.refl`/`.trans`/`.withThread_other`/`.promise`,
  `NPStepBy.envExt_other`, `NPSafe.envExt`, `NPSafe.step`, `NPSafe.prepay`: the environment
  case (b) of Theorem 1′'s induction (other threads' steps and promises of
  any thread keep `NPSafe` applicable) and the step application of case (a).
- `PromSub.of_unfulfils`, `erase_pending`, `erase_fulfil`,
  `promisedRelease`: `ResModel.PromisedRelease` for `model` (`validate`),
  and the pending laws that were its fields until option (B), now
  instance lemmas used inside Theorem 1′'s proof (`erase_pending` from
  `Erase.unfulfil`, `erase_fulfil` from `Erase.fulfil`).
- `NPStepBy.unfulfils`, `Erase.npStep_fulfil`: an instruction step that
  appends nothing and fulfils only pending promises keeps erasure through
  `Erase.fulfil` (S2c finding (c)): how Theorem 1′ accounts the real
  fulfilling instruction `F` of a pending release.
- `Erase.npStep_top`, `hval_top`: with Theorem 1′'s validity-free erasure
  (`T = fun _ => True`, the `NPSafe`) the per-instruction lemma
  needs no `hval`: the RMW and store event lemmas' validity obligation is
  vacuous.
- `Erase.validate_all`: the erasure half of condition (3) (validity-free
  erasure plus `mayWrite` of non-pending promises is erasure at `⊥`).
- `Config.NTFree`, `Config.ntFree_armv8`: the temporary scope hypothesis of
  Theorem 1′ until the pending-NT erasure clause is proved (vacuous under `Arch.armv8`).
- `Theorem1II`: `NPSafeImpliesAdequateV` for `model`, `VirtualRel.ii`, scope
  `Config.NTFree`; `Theorem1II.scope_armv8`.
-/
import Kraken.Promising.SLR.Lift

namespace Kraken.Promising

variable {I : ISA}

/-! ## The temporary NT-free scope (until the pending-NT erasure clause) -/

/-- Every thread has made no non-temporal store and its next instruction
makes none (`Thread.NoNTStores` for every timestamp, `Thread.NextNoNT`): the
hypotheses of (S2)/(S1′) (`stutterStep_path`, `Config.advanceable_of_path`).

**Temporary** (until the pending-NT erasure clause is proved): Theorem 1′ for variant (ii) is
stated under this scope (`SLR.Theorem1II`); `Config.VirtualOfNT` (`VirtualRel.nt`) and the pending-NT
erasure clause are to replace it by `fun _ => True` with another
`VirtualRel`. Under `Arch.armv8` it holds at every reachable configuration
(`Config.ntFree_armv8`), so it restricts only x86 programs using `movnti`. -/
def Config.NTFree (A : Arch) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → (∀ ts, t.NoNTStores ts) ∧ t.NextNoNT A

/-- `Config.NTFree` under `Arch.armv8` along `ReachableK` (the `ReachableK` twin of
`Config.ntFree_armv8`). -/
theorem Config.ntFree_armv8K {states : List I.State}
    {initMem : List (Loc × Val)} {c : Config I}
    (hc : Live.Bridge.ReachableK Arch.armv8 (Config.init states initMem) c) : c.NTFree Arch.armv8 :=
  fun _ t ht => ⟨Thread.noNTStores_armv8 hc ht, Thread.nextNoNT_armv8 t⟩

theorem Config.ntFree_armv8 [I.LawfulState] {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {c : Config I}
    (hc : Reachable Arch.armv8 fuel (Config.init states initMem) c) : c.NTFree Arch.armv8 :=
  Config.ntFree_armv8K (.of_reachable hc)

/-- An instruction step of thread `tid` that leaves memory unchanged is an
un-fulfilment in reverse: the promises it fulfilled are exactly those of
`tid` it removed (`c.MachInv`: a promise belongs to its writer only). -/
theorem NPStepBy.unfulfils {A : Arch} {tid : Nat} {c c' : Config I} (hinv : c.MachInv)
    (hs : NPStepBy A tid c c') (hm : c'.mem = c.mem) :
    ∃ t t', c.threads[tid]? = some t ∧ c'.threads[tid]? = some t' ∧
      c'.Unfulfils c (SLR.fulfilledBy t t') := by
  obtain ⟨t, t', mem', ht, hst, rfl⟩ := hs
  have hn := lt_size_of_get? ht
  have hm' : mem' = c.mem := hm
  subst hm'
  have hget := fun i => Config.withThread_get? c (i := i) t' c.mem hn
  have hsub : ∀ p ∈ t'.prom, p ∈ t.prom := ThreadNP.prom_sub_of_silent (.step hst (.refl _))
  refine ⟨t, t', ht, by rw [hget, ite_eq_left rfl], rfl, Config.withThread_size _ _ _ _, ?_, ?_⟩
  · intro i ti hi
    rw [hget] at hi
    split at hi
    · next h => subst h; cases hi; exact ⟨t, ht, hsub⟩
    · exact ⟨ti, hi, fun _ h => h⟩
  · intro ts
    rw [SLR.mem_fulfilledBy]
    constructor
    · rintro ⟨hts, hts'⟩
      refine ⟨⟨tid, t, ht, hts⟩, ?_⟩
      rintro ⟨j, tj, hj, htsj⟩
      rw [hget] at hj
      split at hj
      · next h => subst h; cases hj; exact hts' htsj
      · next h =>
        obtain ⟨w, hw, hwt⟩ := hinv.promWf tid t ht ts hts
        obtain ⟨w', hw', hwt'⟩ := hinv.promWf j tj hj ts htsj
        rw [hw] at hw'; cases hw'
        exact h (hwt.symm.trans hwt')
    · rintro ⟨⟨i, ti, hi, htsi⟩, hno⟩
      by_cases h : tid = i
      · subst h
        rw [ht] at hi; cases hi
        exact ⟨htsi, fun h' => hno ⟨tid, t', by rw [hget, ite_eq_left rfl], h'⟩⟩
      · exact absurd ⟨i, ti, by rw [hget, ite_eq_right h]; exact hi, htsi⟩ hno

/-! ## Environment extension (case (b) of Theorem 1′'s induction) -/

theorem EnvExt.refl (tid : Nat) (c : Config I) : EnvExt tid c c :=
  ⟨rfl, List.prefix_refl _, fun t ht => ⟨[], by simpa using ht, fun _ h => absurd h List.not_mem_nil⟩⟩

theorem EnvExt.trans {tid : Nat} {c c₁ c₂ : Config I} (h₁ : EnvExt tid c c₁) (h₂ : EnvExt tid c₁ c₂) :
    EnvExt tid c c₂ := by
  obtain ⟨hi1, hp1, ht1⟩ := h₁
  obtain ⟨hi2, hp2, ht2⟩ := h₂
  refine ⟨hi2.trans hi1, hp1.trans hp2, fun t ht => ?_⟩
  obtain ⟨ps, ht1', hps⟩ := ht1 t ht
  obtain ⟨ps', ht2', hps'⟩ := ht2 _ ht1'
  have hle : c.mem.last ≤ c₁.mem.last := by
    simpa [Memory.last] using hp1.length_le
  refine ⟨ps ++ ps', by simpa [List.append_assoc] using ht2', fun p hp => ?_⟩
  rcases List.mem_append.mp hp with h | h
  · exact hps p h
  · exact Nat.lt_of_le_of_lt hle (hps' p h)

/-- A step of another thread `j` (it replaces `j`'s thread and extends the
memory) is an environment extension for `tid`. -/
theorem EnvExt.withThread_other {tid j : Nat} {c : Config I} {t' : Thread I} {mem' : Memory}
    (hne : j ≠ tid) (hj : j < c.threads.size) (hi : mem'.init = c.mem.init)
    (hp : c.mem.msgs.toList <+: mem'.msgs.toList) : EnvExt tid c (c.withThread j t' mem') :=
  ⟨hi, hp, fun t ht => ⟨[], by rw [Config.withThread_get? c t' mem' hj, ite_eq_right hne]; simpa using ht,
    fun _ h => absurd h List.not_mem_nil⟩⟩

/-- An instruction step of another thread is an environment extension. -/
theorem NPStepBy.envExt_other {A : Arch} {tid j : Nat} {c c' : Config I} (hne : j ≠ tid)
    (hs : NPStepBy A j c c') : EnvExt tid c c' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hst, ho, heq⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  obtain ⟨hi, hm⟩ := stepOne_ext A hst ho
  exact EnvExt.withThread_other hne (lt_size_of_get? ht) hi (by rw [hm]; exact List.prefix_append _ _)

/-- A promise step of thread `j` appends one message and one promise of `j`:
an environment extension for every thread, `j` included (`EnvExt` lets the
thread's own promise set grow by fresh timestamps). -/
theorem EnvExt.promise {tid j : Nat} {c : Config I} {t : Thread I} {w : Msg}
    (ht : c.threads[j]? = some t) :
    EnvExt tid c (c.withThread j { t with prom := t.prom ++ [(c.mem.append { w with tid := j }).2] }
      (c.mem.append { w with tid := j }).1) := by
  have hj := lt_size_of_get? ht
  refine ⟨rfl, by simp [Memory.append, Config.withThread], fun u hu => ?_⟩
  rw [Config.withThread_get? c _ _ hj]
  by_cases h : j = tid
  · subst h
    rw [ht] at hu; cases hu
    exact ⟨[(c.mem.append { w with tid := j }).2], by rw [ite_eq_left rfl],
      fun p hp => by simp only [List.mem_singleton] at hp; subst hp; simp [Memory.append, Memory.last]⟩
  · exact ⟨[], by rw [ite_eq_right h]; simpa using hu, fun _ h => absurd h List.not_mem_nil⟩

/-- **`NPSafe` is closed under environment extension and ghost growth**
(case (b) of Theorem 1′'s induction: another thread's step, or a promise of
`tid`, leaves `tid`'s `NPSafe` applicable), provided the ghost growth marks
none of `tid`'s promises pending that were not pending before (`hp`: in any
further extension `c₂`, a pending promise of `tid` at `g₁` was pending at
`g`; option (B): only `tid`'s own prepayments mark its promises pending). -/
theorem NPSafe.envExt {M : ResModel I} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid : Nat} : ∀ {n m : Nat} {cl : Prop} {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost},
    NPSafe M A B tid n m cl c r g → EnvExt tid c c₁ → M.ghostLe g g₁ →
    (∀ c₂ t₂, EnvExt tid c₁ c₂ → c₂.threads[tid]? = some t₂ → ∀ ts ∈ t₂.prom, M.pendingAt g₁ ts →
      M.pendingAt g ts) →
    NPSafe M A B tid n m cl c₁ r g₁
  | 0, _, _, _, _, _, _, _, _, _, _, _ => by simp [NPSafe]
  | n + 1, 0, _, _, _, _, _, _, h, he, hg, hp => by
    rw [NPSafe] at h ⊢
    exact fun m => NPSafe.envExt L (h m) he hg hp
  | n + 1, m + 1, _, _, _, _, _, _, h, he, hg, hp => by
    rw [NPSafe] at h ⊢
    intro c₂ g₂ he₂ hg₂
    obtain ⟨hd, hs, hpp⟩ := h c₂ g₂ (he.trans he₂) (L.ghostLe_trans _ _ _ hg hg₂)
    refine ⟨hd, fun rF c' E hst hinv hw hw' hpe => hs rF c' E hst hinv hw hw' fun t ht ts hts h2 =>
      hp c₂ t he₂ ht ts hts (hpe t ht ts hts h2), fun rF t₁ w ht E hinv hpe hrel =>
      hpp rF t₁ w ht E hinv (fun ts hts h2 => hp c₂ t₁ he₂ ht ts hts (hpe ts hts h2)) hrel⟩

/-- **`NPSafe`'s step at the configuration itself** (case (a) of Theorem 1′'s
induction, `c₁ = c`, `g₁ = g`): `EnvExt.refl` and `ghostLe_refl`; the
own-pending hypothesis is trivial at `g₁ = g`. -/
theorem NPSafe.step {M : ResModel I} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafe M A B tid (n + 1) (m + 1) cl c r g) :
    (cl → c.Done tid → B c r g) ∧
    ∀ (rF : Nat → M.R) (c' : Config I), M.erase (M.upd rF tid r) g (fun _ => True) c → NPStepBy A tid c c' →
      c.MachInv → c.WfProm tid → c'.WfProm tid →
      ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g g' ∧
        (∀ ts, M.pendingAt g ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
          M.pendingAt g' ts) ∧
        (∀ ts, M.pendingAt g' ts → M.pendingAt g ts) ∧
        NPSafe M A B tid (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g (fun _ => False) c) c' r' g' ∧
        M.acqLe r' g' r g ∧
        (∀ w, Written tid c c' w → M.owns r w.loc) ∧
        (∀ b, b ≤ c.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g x b) ∧
        (∀ b, b ≤ c.mem.last →
          (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
          ∀ x, M.reach r' g' x b → M.reach r g x b) := by
  rw [NPSafe] at h
  obtain ⟨hd, hs, -⟩ := h c g (EnvExt.refl _ _) (L.ghostLe_refl g)
  exact ⟨hd, fun rF c' E hs' hinv hw hw' => hs rF c' E hs' hinv hw hw' fun _ _ _ _ h => h⟩

/-- **`NPSafe`'s prepay conjunct at the configuration itself** (case (d1) of
Theorem 1′'s induction under option (B), `c₁ = c`, `g₁ = g`): the release
event of `tid`'s next instruction, which fulfils the new promise, is
accounted at promise time. -/
theorem NPSafe.prepay {M : ResModel I} (L : M.Laws) {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid n m : Nat} {cl : Prop} {c : Config I} {r : M.R} {g : M.Ghost}
    (h : NPSafe M A B tid (n + 1) (m + 1) cl c r g) (rF : Nat → M.R) (t₁ : Thread I) (w : Msg) (ht : c.threads[tid]? = some t₁)
    (E : M.erase (M.upd rF tid r) g (fun _ => True) c) (hinv : c.MachInv)
    (hrel : { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfilsLive A tid
        (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True)
        (c.withThread tid { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
          (c.mem.append { w with tid }).1) ∧
      M.ghostLe g g' ∧ M.pendingAt g' (c.mem.append { w with tid }).2 ∧
      (∀ ts, M.pendingAt g ts → M.pendingAt g' ts) ∧
      (∀ ts, M.pendingAt g' ts → M.pendingAt g ts ∨ ts = (c.mem.append { w with tid }).2) ∧
      NPSafe M A B tid (n + 1) m (cl ∧ M.erase (M.upd rF tid r) g (fun _ => False) c)
        (c.withThread tid { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }
          (c.mem.append { w with tid }).1) r' g' ∧
      M.acqLe r' g' r g ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g x b) ∧
      (∀ b, b ≤ c.mem.last →
        (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, M.reach r' g' x b → M.reach r g x b) := by
  rw [NPSafe] at h
  exact (h c g (EnvExt.refl _ _) (L.ghostLe_refl g)).2.2 rF t₁ w ht E hinv (fun _ _ h => h) hrel

/-- **The clean flag is antitone**: `NPSafe` with flag `cl` gives
`NPSafe` with any flag `cl'` that implies it. The resource conjuncts do not
mention the flag; the Done conjunct is asked under a stronger hypothesis, and
continuations' flags `cl' ∧ V` imply `cl ∧ V`. In particular a proof of
`NPSafe … True …` gives every flag, and a proof that never uses validity can
be stated for every `cl`. -/
theorem NPSafe.mono_flag {M : ResModel I} {A : Arch} {B : Config I → M.R → M.Ghost → Prop}
    {tid : Nat} : ∀ {n m : Nat} {cl cl' : Prop} {c : Config I} {r : M.R} {g : M.Ghost},
    (cl' → cl) → NPSafe M A B tid n m cl c r g → NPSafe M A B tid n m cl' c r g
  | 0, _, _, _, _, _, _, _, _ => by simp [NPSafe]
  | n + 1, 0, _, _, _, _, _, hc, h => by
    rw [NPSafe] at h ⊢
    exact fun m => NPSafe.mono_flag hc (h m)
  | n + 1, m + 1, _, _, _, _, _, hc, h => by
    rw [NPSafe] at h ⊢
    intro c₁ g₁ he hg
    obtain ⟨hd, hs, hpp⟩ := h c₁ g₁ he hg
    refine ⟨fun h' => hd (hc h'), fun rF c' E hst hinv hw hw' hpe => ?_,
      fun rF t₁ w ht E hinv hpe hrel => ?_⟩
    · obtain ⟨r', g', E', hg', hk, hk', hn, rest⟩ := hs rF c' E hst hinv hw hw' hpe
      exact ⟨r', g', E', hg', hk, hk', NPSafe.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩
    · obtain ⟨r', g', E', hg', hp', hk, hk', hn, rest⟩ := hpp rF t₁ w ht E hinv hpe hrel
      exact ⟨r', g', E', hg', hp', hk, hk', NPSafe.mono_flag (fun h' => ⟨hc h'.1, h'.2⟩) hn, rest⟩

end Kraken.Promising

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## The design-(V) laws for the SLR-adapted model -/

theorem PromSub.of_unfulfils {c' c : Config I} {P : List Time} (h : c'.Unfulfils c P) : PromSub c c' :=
  ⟨h.mem, h.size, h.sub⟩

/-- **Marking pending** (`PromisedRelease.pending`):
`Erase.unfulfil`. -/
theorem erase_pending {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c' c : Config I} {P : List Time}
    (E : Erase rF g T c') (hinv : c.MachInv) (hu : c'.Unfulfils c P)
    (hcl : ∀ k tw, (k, tw) ∈ g.claims → ¬ Outstanding c tw) :
    Erase rF { g with pend := P ++ g.pend } T c :=
  E.unfulfil (PromSub.of_unfulfils hu) hinv.promWf hcl fun ts => by
    rw [List.mem_append, hu.gone ts]
    unfold Outstanding
    exact Or.comm

/-- **Fulfilling pending promises** (`PromisedRelease.fulfil`):
`Erase.fulfil`, the pending list restricted to what is still outstanding. -/
theorem erase_fulfil {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I} {P : List Time}
    (E : Erase rF g T c) (hu : c'.Unfulfils c P) (hp : ∀ ts ∈ P, ts ∈ g.pend) :
    ∃ g' : Ghost, Erase rF g' T c' ∧ g.Le g' ∧ ∀ ts, ts ∈ g.pend → ts ∉ P → ts ∈ g'.pend := by
  classical
  refine ⟨{ g with pend := g.pend.filter fun ts => decide (Outstanding c' ts) }, ?_,
    ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, ?_⟩
  · refine E.fulfil (PromSub.of_unfulfils hu) (fun ts ho hno => hp ts ((hu.gone ts).mpr ⟨ho, hno⟩)) ?_
    intro ts
    simp only [List.mem_filter, decide_eq_true_eq]
  · intro ts hts hnp
    simp only [List.mem_filter, decide_eq_true_eq]
    refine ⟨hts, Classical.byContradiction fun hno => hnp ((hu.gone ts).mpr ⟨(E.pend ts hts).2, hno⟩)⟩

/-- **`ResModel.PromisedRelease` for the SLR-adapted model** (option (B): `validate` is its only field). -/
theorem promisedRelease : (model I).PromisedRelease (laws I) where
  validate := model_validate

/-! ## Steps Theorem 1′ routes through -/

/-- **A fulfilling instruction of pending promises keeps erasure** (S2c
finding (c)): an instruction step of `tid` that appends nothing (`F`'s
release store is its last memory event and every write of `F` fulfils a
promise) and fulfils only pending promises keeps erasure, with the pending
list shrunk to what is still outstanding and every other pending mark kept.
This is how Theorem 1′ accounts the real `F` of a pending release: its
resources were attached at promise time (`PromisedRelease.pending`), so
neither `NPSafe` nor `Erase.npStep` is involved. -/
theorem Erase.npStep_fulfil {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I}
    {tid : Nat} (hinv : c.MachInv) (E : Erase rF g T c) (hs : NPStepBy A tid c c') (hm : c'.mem = c.mem)
    (hp : ∀ t t', c.threads[tid]? = some t → c'.threads[tid]? = some t' → ∀ ts ∈ t.prom, ts ∉ t'.prom →
      ts ∈ g.pend) :
    ∃ g' : Ghost, Erase rF g' T c' ∧ g.Le g' ∧
      ∀ ts, ts ∈ g.pend → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
        ts ∈ g'.pend := by
  obtain ⟨t, t', ht, ht', hu⟩ := NPStepBy.unfulfils hinv hs hm
  obtain ⟨g', E', hle, hkeep⟩ := erase_fulfil E hu fun ts hts => by
    rw [mem_fulfilledBy] at hts
    exact hp t t' ht ht' ts hts.1 hts.2
  refine ⟨g', E', hle, fun ts hts ho => hkeep ts hts fun hP => ?_⟩
  exact ((hu.gone ts).mp hP).2 ho

/-- With Theorem 1′'s validity-free erasure the `hval` obligation of the
store and RMW event lemmas (`ErAt.store`, `ErAt.rmw`, `Erase.store`,
`Erase.rmw`) is vacuous: it only concerns threads outside `T`. -/
theorem hval_top {α : Type} (Q : Nat → α → Prop) :
    ∀ i (a : α), ¬ (fun _ : Nat => True) i → Q i a := fun _ _ h => absurd trivial h

/-- **The per-instruction lemma at validity-free erasure**: `Erase.npStep`
with `T = fun _ => True`, the form `NPSafe`'s step consumes. -/
theorem Erase.npStep_top {A : Arch} {rF : Nat → Res} {g : Ghost} {c c' : Config I} {tid : Nat}
    {r : Res} {Post : I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g (fun _ => True) c) (hs : NPStepBy A tid c c')
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWP A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t Post r g (ctx₀ t tid c.mem)) :
    ∃ st r' g' cx', Post st r' g' cx' ∧ Erase (setRes rF tid r') g' (fun _ => True) c' :=
  Erase.npStep hinv E hs hwp

/-- **Condition (3) of Theorem 1′, the erasure half**: validity-free erasure
(`T = fun _ => True`) together with `mayWrite` for every non-pending
outstanding promise is erasure at `T = ⊥` (the conclusion of
`NPSafeImpliesAdequateV`). Only `promValid` depends on `T`. -/
theorem Erase.validate_all {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (E : Erase rF g T c)
    (hv : ∀ i t, c.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend →
      ∀ w, c.mem.get? ts = some w → mayWrite (rF i) g w.loc) :
    Erase rF g (fun _ => False) c :=
  { E with promValid := fun i t ht _ => hv i t ht }

/-! ## The statement -/

/-- **Theorem 1′ for the SLR-adapted model, variant (ii)** (`Prop`, not
proved): `NPSafeImpliesAdequateV` with `model`, the
virtual relation `VirtualRel.ii` (`Config.VirtualOf`) and the temporary scope
`Config.NTFree`. Its law hypotheses are discharged by `laws` and
`promisedRelease`; the scope under `Arch.armv8` by
`Theorem1II.scope_armv8`. Option (B): every promised release is
prepaid (`NPSafe`'s prepay conjunct), so no escrow laws and no virtual
memory are needed. Generalisation: with the pending-NT erasure clause the scope becomes
`fun _ => True` and `VirtualRel.ii` becomes `VirtualRel.nt` (`Config.VirtualOfNT`). -/
abbrev Theorem1II (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  NPSafeImpliesAdequateV (model I) A fuel (VirtualRel.ii A) (Config.NTFree A)

/-- Under `Arch.armv8` the scope hypothesis of `Theorem1II` holds. -/
theorem Theorem1II.scope_armv8 (states : List I.State)
    (initMem : List (Loc × Val)) :
    ∀ c, Live.Bridge.ReachableK Arch.armv8 (Config.init states initMem) c → c.NTFree Arch.armv8 :=
  fun _ hc => Config.ntFree_armv8K hc

end Kraken.Promising.SLR
