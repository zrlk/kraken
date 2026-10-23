/-
**A word the thread owns reads as its last write** (`Scc/DESIGN.md` §7.3,
item 5: the memory side of the runtime counters; I1 of the stack-depth
plan): a runtime load of a word only the thread writes (its control block's
`depth`, the one-thread heap counter, `stackLimit`) returns the value of
the thread's last write to it, or the initial value, outstanding promises
or not.

Kraken's `read` rule never offers a timestamp the thread has promised and
not fulfilled, so under the cover (`CohCoversP`) a read returns the latest
write not promised (`TLatestP`, `readSuccs_tlatestP`), which is unique
(`TLatestP.unique`). `OwnVal tm prom a v` says that write's value is `v`:

- `OwnInv vs prom tm a v`: the cover, the promises distinct and at most
  `last`, and `OwnVal`; `Inv1.ownInv` gives the first three from the
  one-thread invariant (`Inv1.coh`, `MemRelP.tq_nodup`, `MemRelP.tq_le`);
- `readSuccs_own`, `stepOne_load_own`, `Inv1.rtLoad_own`: a read of the
  word returns `v`;
- `OwnStep a v c c'`: `OwnInv … v` kept across a context step. Every step
  but a write of the word keeps it (`readSuccs_ownStep`,
  `writeSuccs_ownStep` for a write elsewhere, fences, the RMW end), so a run
  of a tree with no write of the word does (`runTree_ownStep`,
  `stepOneWith_own`, `stepOne_own`);
- `writeSuccs_own`, `stepOne_store_own`: a store of `v` to the word, a
  fulfilment or an append, makes `OwnInv … v` (a fulfilment's timestamp is
  above the coherence view, so every later message of the word is
  promised);
- `stepOne_rmw_own`, `Inv1.rtRmw_own`: an RMW of the word (the runtime's
  `ldadd`/`swp`/`cas` of its counters and locks) reads `v` and leaves the
  word reading as `op v`, or `v` when it does not write;
- `own_promise`: a promise step keeps `OwnInv` (the message is promised).

No hypothesis on the promises is needed beyond what `Inv1` has: a promise
to the word (which a certification through the counter's own stores allows)
is never read before it is fulfilled (the example below).

Not covered (M2): other threads' writes of the word.
-/
import Scc.Sem.Coh
import Scc.Sem.Wide
import Scc.Sem.Rows1

namespace Scc.Sem

open Kraken Kraken.Promising

/-- **The word at `a` reads as `v`**: the latest write of it not promised
has the value `v`. -/
def OwnVal (tm : Memory) (prom : List Time) (a : Nat) (v : Val) : Prop :=
  ∃ k, TLatestP tm prom a k ∧ tm.read? (wordLoc a) k = some v

/-- **The latest write not promised is unique.** -/
theorem TLatestP.unique {tm : Memory} {prom : List Time} {a k₁ k₂ : Nat} (h₁ : TLatestP tm prom a k₁)
    (h₂ : TLatestP tm prom a k₂) : k₁ = k₂ := by
  rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exfalso
    rcases h₂.1 with h0 | ⟨w, hg, hl, hp⟩
    · omega
    · exact hp (h₁.2 k₂ w hlt hg hl)
  · exact heq
  · exfalso
    rcases h₁.1 with h0 | ⟨w, hg, hl, hp⟩
    · omega
    · exact hp (h₂.2 k₁ w hgt hg hl)

/-- At load (no message) the word reads as its initial value. -/
theorem ownVal_init {tm : Memory} (h : tm.msgs = #[]) (prom : List Time) (a : Nat) :
    OwnVal tm prom a (tm.initVal (wordLoc a)) := by
  refine ⟨0, ⟨.inl rfl, fun k w _ hg _ => ?_⟩, by simp [Memory.read?]⟩
  have := Memory.le_last_of_get? hg
  have hk : k ≠ 0 := by intro h0; subst h0; simp [Memory.get?] at hg
  simp only [Memory.last, h, Array.size_empty] at this
  omega

/-- A read of an appended memory at an old timestamp. -/
theorem read?_append_le {m : Memory} {w : Msg} {l : Loc} {k : Nat} (hk : k ≤ m.last) :
    (m.append w).1.read? l k = m.read? l k := by
  unfold Memory.read?
  split
  · rfl
  · rw [Memory.get?_append_le hk]

section Rules
variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A read of the word returns its value.** -/
theorem readSuccs_own {c : Ctx} {k : LoadKind} {xcl : Bool} {a : Nat} {noRet : Bool} {v : Val}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl (wordLoc a) noRet)
    (hc : CohCoversP c.views c.prom c.mem) (ho : OwnVal c.mem c.prom a v) : x.2.1 = v := by
  obtain ⟨hl, hv⟩ := readSuccs_tlatestP A iv hx hc
  obtain ⟨k', hk', hv'⟩ := ho
  rw [← hk'.unique hl, hv'] at hv
  exact (Option.some.inj hv).symm

/-- **The invariant**: the cover, the promises distinct and messages, and
the word at `a` reading as `v`. -/
def OwnInv (vs : Views) (prom : List Time) (mem : Memory) (a : Nat) (v : Val) : Prop :=
  CohCoversP vs prom mem ∧ prom.Nodup ∧ (∀ p ∈ prom, p ≤ mem.last) ∧ OwnVal mem prom a v

/-- At load (no message, no promise) the word reads as its initial value. -/
theorem ownInv_init {vs : Views} {tm : Memory} (h : tm.msgs = #[]) (a : Nat) :
    OwnInv vs [] tm a (tm.initVal (wordLoc a)) := by
  refine ⟨fun k w hk _ => ?_, List.nodup_nil, fun _ hp => absurd hp List.not_mem_nil, ownVal_init h [] a⟩
  have := Memory.le_last_of_get? hk
  have hk0 : k ≠ 0 := by intro h0; subst h0; simp [Memory.get?] at hk
  simp only [Memory.last, h, Array.size_empty] at this
  exact absurd (Nat.le_zero.mp this) hk0

/-- **The step invariant**: `OwnInv … v` kept from `c` to `c'`. -/
def OwnStep (a : Nat) (v : Val) (c c' : Ctx) : Prop :=
  OwnInv c.views c.prom c.mem a v → OwnInv c'.views c'.prom c'.mem a v

theorem OwnStep.refl {a : Nat} {v : Val} (c : Ctx) : OwnStep a v c c := fun h => h

theorem OwnStep.trans {a : Nat} {v : Val} {c₁ c₂ c₃ : Ctx} (h₁ : OwnStep a v c₁ c₂) (h₂ : OwnStep a v c₂ c₃) :
    OwnStep a v c₁ c₃ := fun h => h₂ (h₁ h)

/-- A step keeping memory and promises and raising coherence views. -/
theorem ownStep_of_eq {a : Nat} {v : Val} {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hle : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : OwnStep a v c c' := fun ⟨h₁, h₂, h₃, h₄⟩ => by
  refine ⟨cohStepP_of_eq hm hp hle h₁, ?_, ?_, ?_⟩
  · rw [hp]; exact h₂
  · rw [hp, hm]; exact h₃
  · rw [hm, hp]; exact h₄

/-- `finishInstr` keeps the invariant: it takes the context's promises and
coherence views. -/
theorem ownInv_finish {I : ISA} {a : Nat} {v : Val} {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews}
    {st : I.State} {c : Ctx} {th : Thread I} (hth : th ∈ finishInstr t d iv st c)
    (h : OwnInv c.views c.prom c.mem a v) : OwnInv th.views th.prom c.mem a v := by
  obtain ⟨e1, e2⟩ := finishInstr_relKey hth
  have e3 : th.views.coh = c.views.coh := by have := congrArg Views.coh e2; exact this
  have he : ∀ l, c.views.getCoh l ≤ th.views.getCoh l := fun l => by
    unfold Views.getCoh; rw [e3]; exact Nat.le_refl _
  rw [e1]
  exact ⟨h.1.mono he, h.2⟩

/-- Appending a timestamp not yet promised and erasing it leaves the
promises. -/
theorem erase_append_new {prom : List Time} {n : Time} (h : n ∉ prom) : (prom ++ [n]).erase n = prom := by
  rw [List.erase_append_right _ h]; simp

theorem readSuccs_ownStep {a : Nat} {v : Val} {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : OwnStep a v c x.2.2 := by
  obtain ⟨v', -, -, h⟩ := readSuccs_shape A iv hx
  refine ownStep_of_eq (by rw [h]) (readSuccs_prom A iv hx) ?_
  intro l'; rw [h]; exact getCoh_le_setCoh _ _ _ _

/-- **A write elsewhere keeps the word's value**: a fulfilment removes a
timestamp of another location from the promises, an append adds a message
of another location. -/
theorem writeSuccs_ownStep {a : Nat} {v₀ : Val} {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind}
    {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time} {extra : View}
    (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr) (hl : l ≠ wordLoc a) : OwnStep a v₀ c c' := by
  intro ⟨h₁, h₂, h₃, ⟨k', ⟨hk1, hk2⟩, hv⟩⟩
  have hc := writeSuccs_cohP A tid h h₁
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, -, rfl⟩ | ⟨-, rfl⟩
  · refine ⟨hc, ?_, ?_, k', ⟨?_, fun k'' w hlt hg' hla => ?_⟩, hv⟩
    · show (c.prom.erase t).Nodup
      exact h₂.erase t
    · show ∀ p ∈ c.prom.erase t, p ≤ c.mem.last
      exact fun p hp => h₃ p (List.mem_of_mem_erase hp)
    · rcases hk1 with h0 | ⟨w, hw, hwl, hp⟩
      · exact .inl h0
      · exact .inr ⟨w, hw, hwl, fun hm => hp (List.mem_of_mem_erase hm)⟩
    · have hg'' : c.mem.get? k'' = some w := hg'
      have hne : k'' ≠ t := by
        rintro rfl; rw [hg] at hg''; cases hg''; exact hl hla
      show k'' ∈ c.prom.erase t
      exact (List.mem_erase_of_ne hne).mpr (hk2 k'' w hlt hg'' hla)
  · have hn : c.mem.last + 1 ∉ c.prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
    have hk'le : k' ≤ c.mem.last := by
      rcases hk1 with h0 | ⟨w, hw, -, -⟩
      · rw [h0]; exact Nat.zero_le _
      · exact Memory.le_last_of_get? hw
    have ep : ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)) = c.prom := erase_append_new hn
    refine ⟨hc, ?_, ?_, k', ⟨?_, fun k'' w hlt hg' hla => ?_⟩, ?_⟩
    · show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      rw [ep]; exact h₂
    · show ∀ p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1),
        p ≤ (c.mem.append { loc := l, val := v, tid }).1.last
      rw [ep, Memory.last_append]; exact fun p hp => Nat.le_succ_of_le (h₃ p hp)
    · show k' = 0 ∨ ∃ w, (c.mem.append { loc := l, val := v, tid }).1.get? k' = some w ∧ w.loc = wordLoc a ∧
        k' ∉ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep, Memory.get?_append_le hk'le]; exact hk1
    · have hg'' : (c.mem.append { loc := l, val := v, tid }).1.get? k'' = some w := hg'
      show k'' ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep]
      by_cases he : k'' = c.mem.last + 1
      · subst he; rw [Memory.get?_append_new] at hg''; cases hg''; exact absurd hla hl
      · exact hk2 k'' w hlt (CohCoversP.get?_append_ne hg'' he) hla
    · show (c.mem.append { loc := l, val := v, tid }).1.read? (wordLoc a) k' = some v₀
      rw [read?_append_le hk'le]; exact hv

/-- **A write of `v` to the word makes it read as `v`**, whatever it read
as before (only the cover, the promises distinct and at most `last`): a
fulfilment's timestamp is above the coherence view of the word, so every
later message of it is promised; an append is the last message. -/
theorem writeSuccs_ownOf {a : Nat} {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind}
    {xcl : Bool} {v : Val} {tr : Option Time} {extra : View}
    (h : c' ∈ writeSuccs A tid iv' c k xcl (wordLoc a) v tr extra xr)
    (h₁ : CohCoversP c.views c.prom c.mem) (h₂ : c.prom.Nodup) (h₃ : ∀ p ∈ c.prom, p ≤ c.mem.last) :
    OwnInv c'.views c'.prom c'.mem a v := by
  have hc := writeSuccs_cohP A tid h h₁
  rcases (Lower.mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, hg, hok, rfl⟩ | ⟨-, rfl⟩
  · have hlt : c.views.getCoh (wordLoc a) < t := by
      unfold Lower.writeOk at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      exact Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1
    refine ⟨hc, ?_, ?_, t, ⟨?_, fun k'' w hlt' hg' hla => ?_⟩, ?_⟩
    · show (c.prom.erase t).Nodup
      exact h₂.erase t
    · show ∀ p ∈ c.prom.erase t, p ≤ c.mem.last
      exact fun p hp => h₃ p (List.mem_of_mem_erase hp)
    · exact .inr ⟨_, hg, rfl, h₂.not_mem_erase⟩
    · have hg'' : c.mem.get? k'' = some w := hg'
      show k'' ∈ c.prom.erase t
      refine (List.mem_erase_of_ne (Nat.ne_of_gt hlt')).mpr ?_
      refine Classical.byContradiction fun hp => ?_
      have := h₁ k'' w hg'' hp
      rw [hla] at this
      exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this (Nat.lt_trans hlt hlt'))
    · show c.mem.read? (wordLoc a) t = some v
      have ht0 : t ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)
      simp [Memory.read?, ht0, hg]
  · have hn : c.mem.last + 1 ∉ c.prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
    have ep : ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)) = c.prom := erase_append_new hn
    refine ⟨hc, ?_, ?_, c.mem.last + 1, ⟨?_, fun k'' w hlt hg' _ => ?_⟩, ?_⟩
    · show ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      rw [ep]; exact h₂
    · show ∀ p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1),
        p ≤ (c.mem.append { loc := wordLoc a, val := v, tid }).1.last
      rw [ep, Memory.last_append]; exact fun p hp => Nat.le_succ_of_le (h₃ p hp)
    · show c.mem.last + 1 = 0 ∨ ∃ w, (c.mem.append { loc := wordLoc a, val := v, tid }).1.get? (c.mem.last + 1) = some w ∧
        w.loc = wordLoc a ∧ c.mem.last + 1 ∉ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)
      rw [ep, Memory.get?_append_new]
      exact .inr ⟨_, rfl, rfl, hn⟩
    · have hg'' : (c.mem.append { loc := wordLoc a, val := v, tid }).1.get? k'' = some w := hg'
      have := Memory.le_last_of_get? hg''
      rw [Memory.last_append] at this
      exact absurd (Nat.lt_of_lt_of_le hlt this) (Nat.lt_irrefl _)
    · show (c.mem.append { loc := wordLoc a, val := v, tid }).1.read? (wordLoc a) (c.mem.last + 1) = some v
      simp [Memory.read?, Memory.get?_append_new]

/-- **A write of `v` to the word makes it read as `v`** (`writeSuccs_ownOf`). -/
theorem writeSuccs_own {a : Nat} {v₀ : Val} {xr : View} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind}
    {xcl : Bool} {v : Val} {tr : Option Time} {extra : View}
    (h : c' ∈ writeSuccs A tid iv' c k xcl (wordLoc a) v tr extra xr)
    (ho : OwnInv c.views c.prom c.mem a v₀) : OwnInv c'.views c'.prom c'.mem a v :=
  writeSuccs_ownOf A tid h ho.1 ho.2.1 ho.2.2.1

/-- A fence keeps the invariant. -/
theorem fenceStep_ownStep {a : Nat} {v : Val} (c : Ctx) (k : FenceKind) : OwnStep a v c (fenceStep c k) :=
  ownStep_of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fun l => by cases k <;> exact Nat.le_refl _)

theorem fenceOpt_ownStep {a : Nat} {v : Val} (c : Ctx) (b : Bool) :
    OwnStep a v c (if b then fenceStep c .sy else c) := by
  cases b
  · exact OwnStep.refl c
  · exact fenceStep_ownStep c .sy

/-- The end of an RMW keeps the invariant. -/
theorem rmwPost_ownStep {a : Nat} {v : Val} (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) :
    OwnStep a v c (rmwPost A k noRet l c) := by
  refine ownStep_of_eq ?_ ?_ ?_ <;> unfold rmwPost <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

/-- **A run of a tree with no write of the word keeps its value.** -/
theorem runTree_ownStep {a : Nat} {v₀ : Val} {σ : Type} (tree : EvTree σ)
    (hW : WriteTree (fun l _ => l ≠ wordLoc a) tree) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → OwnStep a v₀ c c' := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact OwnStep.refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i (hW i) c s c' h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_ownStep A iv hx).trans (ih x.2.1 (hW x.2.1) x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_ownStep A tid hc0 hl).trans (ih true (hW true) c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have := ih false (hW false) _ s c' h.2
      exact (ownStep_of_eq rfl rfl (fun _ => Nat.le_refl _)).trans this
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (fenceStep_ownStep c k).trans (ih () (hW ()) _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    obtain ⟨hl, hW⟩ := hW
    simp only [runTree] at h
    have h1 := fenceOpt_ownStep (a := a) (v := v₀) c A.rmwFence
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_ownStep A iv h2)
    simp only at h
    split at h
    · exact (h12.trans (fenceOpt_ownStep _ A.rmwFence)).trans (ih old (hW old) _ s c' h)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact (((h12.trans (writeSuccs_ownStep A tid hc3 (hl old new hnew))).trans
        (rmwPost_ownStep A c3 k noRet l)).trans (fenceOpt_ownStep _ A.rmwFence)).trans (ih old (hW old) _ s c' h)

end Rules

/-- **One instruction with no write of the word keeps its value**, under
any instruction semantics `cexec`. -/
theorem stepOneWith_own {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I}
    {tid : Nat} {mem : Memory} {a : Nat} {v : Val} {tree : EvTree I.State} (hex : cs.exec t.st = some tree)
    (hW : WriteTree (fun l _ => l ≠ wordLoc a) tree)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : cs.step A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInv t.views t.prom mem a v) :
    OwnInv o.thread.views o.thread.prom o.mem a v := by
  unfold CertSem.step stepOneWithD at hstep
  rw [hex] at hstep
  have hstep' : _ = outs := Option.some.inj hstep
  subst hstep'
  rw [List.mem_flatMap] at ho
  obtain ⟨r, hr, ho⟩ := ho
  cases r with
  | error m => simp at ho
  | ok q =>
    obtain ⟨st, c'⟩ := q
    simp only [List.mem_map, Except.ok.injEq] at ho
    obtain ⟨th, hth, rfl⟩ := ho
    exact ownInv_finish hth (runTree_ownStep A tid _ tree hW _ st c' hr hi)

/-- **One instruction with no write of the word keeps its value.** -/
theorem stepOne_own {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {a : Nat} {v : Val}
    {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hW : WriteTree (fun l _ => l ≠ wordLoc a) tree)
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInv t.views t.prom mem a v) :
    OwnInv o.thread.views o.thread.prom o.mem a v :=
  stepOneWith_own A (cs := CertSem.ofExec I.exec) hex hW hstep ho hi

/-- **A load of the word returns its value**, and keeps the invariant. -/
theorem stepOne_load_own {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInv t.views t.prom mem a v) :
    o.mem = mem ∧ o.thread.st = g v ∧ OwnInv o.thread.views o.thread.prom o.mem a v := by
  obtain ⟨hm, ts, v', hst, hl, hv⟩ := stepOne_load_tlatestP A hex hstep ho hi.1
  obtain ⟨k', hk', hv''⟩ := hi.2.2.2
  rw [← hk'.unique hl, hv''] at hv
  cases hv
  exact ⟨hm, hst, stepOne_own A hex (fun _ => trivial) hstep ho hi⟩

/-- **A store of `v` to the word makes it read as `v`.** -/
theorem stepOne_store_own {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : StoreKind} {a : Nat} {v₀ v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInv t.views t.prom mem a v₀) :
    o.thread.st = s ∧ OwnInv o.thread.views o.thread.prom o.mem a v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  refine ⟨finishInstr_st hth, ?_⟩
  rw [hm]
  exact ownInv_finish hth (writeSuccs_own A tid hw hi)

/-- **A store of `v` to the word makes it read as `v`**, whatever it read
as before: only the cover and the promises distinct and at most `last`
(`writeSuccs_ownOf`). -/
theorem stepOne_store_ownOf {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : StoreKind} {a : Nat} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false (wordLoc a) v fun _ => .done s))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hc : CohCoversP t.views t.prom mem)
    (hn : t.prom.Nodup) (hl : ∀ p ∈ t.prom, p ≤ mem.last) :
    o.thread.st = s ∧ OwnInv o.thread.views o.thread.prom o.mem a v := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_store_iff] at hr
  obtain ⟨rfl, hw⟩ := hr
  refine ⟨finishInstr_st hth, ?_⟩
  rw [hm]
  exact ownInv_finish hth (writeSuccs_ownOf A tid hw hc hn hl)

/-- The acquire-release bump after an RMW's write keeps the invariant. -/
theorem rmwBump_ownStep {a : Nat} {v : Val} (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    OwnStep a v c (Lower.rmwBump k noRet l c) := by
  refine ownStep_of_eq ?_ ?_ ?_ <;> unfold Lower.rmwBump <;> split <;> first | rfl | (intro; exact Nat.le_refl _)

/-- **An RMW of the word reads its value `v` and makes it read as
`op v`** (as `v` when `op v = none`, a failed compare): the read returns
`v` (`readSuccs_own`), and the paired write, if any, is a write of the word
(`writeSuccs_own`). -/
theorem stepOne_rmw_own {I : ISA} (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hi : OwnInv t.views t.prom mem a v) :
    o.thread.st = g v ∧ OwnInv o.thread.views o.thread.prom o.mem a ((op v).getD v) := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A tid hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  rw [Lower.run_rmw_iff] at hr
  obtain ⟨tr, old, c1, hx, rfl, hcase⟩ := hr
  have hf : ∀ {w : Val} (c : Ctx), OwnStep a w c (Lower.rmwFenceOpt A c) := fun c => fenceOpt_ownStep c A.rmwFence
  have h0 := hf (Live.TicketStep.ctx0 tid t mem) hi
  have hold : old = v := readSuccs_own A _ hx h0.1 h0.2.2.2
  subst hold
  have h1 := readSuccs_ownStep A _ hx h0
  refine ⟨finishInstr_st hth, ?_⟩
  rw [hm]
  refine ownInv_finish hth ?_
  rcases hcase with ⟨hop, rfl⟩ | ⟨new, c2, hop, hw, rfl⟩
  · rw [hop]
    exact hf c1 h1
  · rw [hop]
    have h2 : OwnInv c2.views c2.prom c2.mem a new := writeSuccs_own A tid hw h1
    exact hf _ (rmwBump_ownStep (A.rmwKind k) noRet (wordLoc a) { c2 with rmwWrote := true } h2)

/-- **A promise keeps the word's value**: the appended message is
promised. -/
theorem own_promise {vs : Views} {prom : List Time} {mem : Memory} {a : Nat} {v : Val}
    (h : OwnInv vs prom mem a v) (w : Msg) :
    OwnInv vs (prom ++ [(mem.append w).2]) (mem.append w).1 a v := by
  obtain ⟨h₁, h₂, h₃, k', ⟨hk1, hk2⟩, hv⟩ := h
  have e2 : (mem.append w).2 = mem.last + 1 := rfl
  have hn : mem.last + 1 ∉ prom := fun hm => Nat.not_succ_le_self _ (h₃ _ hm)
  have hk'le : k' ≤ mem.last := by
    rcases hk1 with h0 | ⟨w, hw, -, -⟩
    · rw [h0]; exact Nat.zero_le _
    · exact Memory.le_last_of_get? hw
  rw [e2]
  refine ⟨e2 ▸ h₁.promise w, ?_, ?_, k', ⟨?_, fun k'' w' hlt hg hla => ?_⟩, ?_⟩
  · exact List.nodup_append.mpr ⟨h₂, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun x hx y hy => by
      rw [List.mem_singleton] at hy; subst hy; rintro rfl; exact hn hx⟩
  · intro p hp
    rw [Memory.last_append]
    rcases List.mem_append.mp hp with hp | hp
    · exact Nat.le_succ_of_le (h₃ p hp)
    · rw [List.mem_singleton] at hp; rw [hp]; exact Nat.le_refl _
  · rcases hk1 with h0 | ⟨w', hw, hwl, hp⟩
    · exact .inl h0
    · refine .inr ⟨w', by rw [Memory.get?_append_le hk'le]; exact hw, hwl, fun hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hp hm
      · rw [List.mem_singleton] at hm; rw [hm] at hk'le; exact Nat.not_succ_le_self _ hk'le
  · by_cases he : k'' = mem.last + 1
    · exact List.mem_append_right _ (List.mem_singleton.mpr he)
    · exact List.mem_append_left _ (hk2 k'' w' hlt (CohCoversP.get?_append_ne hg he) hla)
  · rw [read?_append_le hk'le]; exact hv

/-- **A promise keeps a word's value** (`OwnVal` alone, `own_promise`
without the cover): the appended message is promised. -/
theorem ownVal_promise {prom : List Time} {mem : Memory} {a : Nat} {v : Val} (h : OwnVal mem prom a v)
    (w : Msg) : OwnVal (mem.append w).1 (prom ++ [(mem.append w).2]) a v := by
  obtain ⟨k', ⟨hk1, hk2⟩, hv⟩ := h
  have e2 : (mem.append w).2 = mem.last + 1 := rfl
  have hk'le : k' ≤ mem.last := by
    rcases hk1 with h0 | ⟨w, hw, -, -⟩
    · rw [h0]; exact Nat.zero_le _
    · exact Memory.le_last_of_get? hw
  rw [e2]
  refine ⟨k', ⟨?_, fun k'' w' hlt hg hla => ?_⟩, ?_⟩
  · rcases hk1 with h0 | ⟨w', hw, hwl, hp⟩
    · exact .inl h0
    · refine .inr ⟨w', by rw [Memory.get?_append_le hk'le]; exact hw, hwl, fun hm => ?_⟩
      rcases List.mem_append.mp hm with hm | hm
      · exact hp hm
      · rw [List.mem_singleton] at hm; rw [hm] at hk'le; exact Nat.not_succ_le_self _ hk'le
  · by_cases he : k'' = mem.last + 1
    · exact List.mem_append_right _ (List.mem_singleton.mpr he)
    · exact List.mem_append_left _ (hk2 k'' w' hlt (CohCoversP.get?_append_ne hg he) hla)
  · rw [read?_append_le hk'le]; exact hv

namespace Inv1

variable {I : ISA} {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {t : Thread I} {tm : Memory} {sm : WeakMem.Memory}

/-- **The one-thread invariant gives the cover, `Nodup` and the bound on
the promises**: with the word reading as `v`, `OwnInv`. -/
theorem ownInv (h : Inv1 Λ lbl lsize ts t tm sm) {a : Nat} {v : Val} (ho : OwnVal tm t.prom a v) :
    OwnInv t.views t.prom tm a v :=
  ⟨h.coh, h.mem.tq_nodup, fun p hp => (h.mem.tq_le p hp).2, ho⟩

/-- **A runtime load of a word the thread owns returns its last write**
(I1): under the one-thread invariant, a load of `wordLoc a` reading as `v`
returns `v`, leaves memory alone and keeps the word reading as `v`. No
hypothesis on the promises: a promise to the word is never read before it
is fulfilled. -/
theorem rtLoad_own (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {kl : LoadKind} {xcl : Bool} {a : Nat} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.load kl xcl (wordLoc a) fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hv : OwnVal tm t.prom a v) :
    o.mem = tm ∧ o.thread.st = g v ∧ OwnVal o.mem o.thread.prom a v :=
  let ⟨hm, hs, hi⟩ := stepOne_load_own A hex hstep ho (h.ownInv hv)
  ⟨hm, hs, hi.2.2.2⟩

/-- **A runtime RMW of a word the thread owns reads its last write**: under
the one-thread invariant, an RMW of `wordLoc a` reading as `v` continues
with `v` and leaves the word reading as `op v` (as `v` if it does not
write). -/
theorem rtRmw_own (h : Inv1 Λ lbl lsize ts t tm sm) (A : Arch) {tid : Nat}
    {k : RmwKind} {noRet : Bool} {a : Nat} {op : Val → Option Val} {v : Val} {g : Val → I.State}
    (hex : I.exec t.st = some (.rmw k noRet (wordLoc a) op fun v => .done (g v)))
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid tm = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hv : OwnVal tm t.prom a v) :
    o.thread.st = g v ∧ OwnVal o.mem o.thread.prom a ((op v).getD v) :=
  let ⟨hs, hi⟩ := stepOne_rmw_own A hex hstep ho (h.ownInv hv)
  ⟨hs, hi.2.2.2⟩

end Inv1

/-- A promised message of the word is not its value: with a promise of `5`
to word `8` outstanding, the word still reads as its initial `0`. -/
example : OwnVal ⟨[], #[{ loc := wordLoc 8, val := 5, tid := 0 }]⟩ [1] 8 0 := by
  refine ⟨0, ⟨.inl rfl, fun k w hlt hg _ => ?_⟩, by simp [Memory.read?, Memory.initVal]⟩
  have hle := Memory.le_last_of_get? hg
  have hk : k = 1 := by simp only [Memory.last, Array.size] at hle; simp at hle; omega
  subst hk; exact List.mem_singleton_self _

/-- Its fulfilment makes it the value: with no promise, the word reads as
`5`. -/
example : OwnVal ⟨[], #[{ loc := wordLoc 8, val := 5, tid := 0 }]⟩ [] 8 5 := by
  refine ⟨1, ⟨.inr ⟨_, rfl, rfl, List.not_mem_nil⟩, fun k w hlt hg _ => ?_⟩, by simp [Memory.read?, Memory.get?]⟩
  have hle := Memory.le_last_of_get? hg
  simp only [Memory.last, Array.size] at hle; simp at hle; omega

end Scc.Sem
