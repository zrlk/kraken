/-
**`certify` is sound at its fuel, writes
included** (`CertifySoundN'`, Q1 of `LiveBridge.lean`, proved). ISA-neutral,
architecture-neutral; executable machine (`certify`, `succs`) related to the
semantic notions `CertOkN`/`CertWriteN`.

`certify_go_soundN'` extends the invariant of the existing
`certify_go_soundN` (`LiveWfInstr.lean`) with the writes: an entry
`(t, mem, ws, done)` with budget `n` is reached by `k` instructions,
`k + n ≤ fuel`; a `done` entry has an empty promise set; every pending write
in `ws` is a `PathWrite` (performed as "promise now" on the path). At the
certification point a `PathWrite` is a `CertWriteN`; a write recorded after
`done` is one too, since a thread with no outstanding promise keeps none
(`RunnerSim.stepOne_prom_nil`).

**Fuel.** `certify.go`'s visited set and the certification cache ignore the
remaining fuel. That costs completeness only (`LiveBridgeTests.lean`), not
soundness at the exact fuel: every recording happens on an actual path of
the current search at its actual depth, and `go` does no cache lookup. A
cache entry computed at fuel `f` and looked up at a smaller fuel would be
unsound, but no existing function does that: `succs` starts from the empty
cache and queries one fuel throughout. The cache-threaded form
(`CacheSoundOnN'`, `certify_soundN2`) is what `succs` needs; it is keyed on
`KeyLawful` families as the existing `certify_soundN` is (hence
`[I.LawfulState]`; without it the cache can confuse two threads, see
`LiveBridgeTestsLawful.lean`).

Contents:
- `CertResult.SoundN'`, `PathWrite`, `GoEntryN'`;
- `certify_go_soundN'`, **`certifySoundN' : CertifySoundN' A I`** (no hypothesis);
- `CacheSoundOnN'`, `certify_soundN2` (cache-threaded);
- `promisedNow_tid`: a "promise now" write of thread `tid` carries `tid`.
-/
import Kraken.Promising.LiveBridge
import Kraken.Promising.LiveRunnerSim

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

/-- `certified` gives `CertOkN fuel`, and every recorded write is a `CertWriteN`. -/
def _root_.Kraken.Promising.CertResult.SoundN' (A : Arch) (tid : Nat) (t : Thread I) (mem : Memory) (fuel : Nat)
    (r : CertResult I) : Prop :=
  (r.certified = true → CertOkN A tid t mem fuel) ∧ ∀ p ∈ r.writes, CertWriteN A tid t mem fuel p

/-- `p` is performed as "promise now" at the `j + 1`-st instruction (`j < k`)
of a run of `k` instructions from `(t0, mem0)` to `q`. -/
def PathWrite (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) (k : Nat) (q : Thread I × Memory)
    (p : Msg × View) : Prop :=
  ∃ (j : Nat) (t1 : Thread I) (mem1 : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I),
    j < k ∧ ThreadNPn A tid j (t0, mem0) (t1, mem1) ∧ stepOne A t1 tid mem1 = some outs ∧ .ok o ∈ outs ∧
      p ∈ o.promisedNow ∧ ThreadNPn A tid (k - j - 1) (o.thread, o.mem) q

/-- An entry of `certify.go` with budget `n`: reached by `k` instructions
with `k + n ≤ fuel`; a `done` entry has an empty promise set; the pending
writes `ws` are writes of the path. -/
def GoEntryN' (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) (fuel n : Nat)
    (e : Thread I × Memory × List (Msg × View) × Bool) : Prop :=
  ∃ k, k + n ≤ fuel ∧ ThreadNPn A tid k (t0, mem0) (e.1, e.2.1) ∧
    (e.2.2.2 = true → e.1.prom = [] ∧ CertOkN A tid t0 mem0 fuel) ∧
    ∀ p ∈ e.2.2.1, PathWrite A tid t0 mem0 k (e.1, e.2.1) p

theorem PathWrite.tail {A : Arch} {tid : Nat} {t0 : Thread I} {mem0 : Memory} {k : Nat} {q r : Thread I × Memory}
    {p : Msg × View} (h : PathWrite A tid t0 mem0 k q p) (hs : ThreadStep A tid q r) :
    PathWrite A tid t0 mem0 (k + 1) r p := by
  obtain ⟨j, t1, mem1, outs, o, hj, h1, h2, h3, h4, h5⟩ := h
  refine ⟨j, t1, mem1, outs, o, by omega, h1, h2, h3, h4, ?_⟩
  rw [show k + 1 - j - 1 = (k - j - 1) + 1 by omega]
  exact h5.tail hs

theorem PathWrite.certWriteN {A : Arch} {tid : Nat} {t0 : Thread I} {mem0 : Memory} {k fuel : Nat}
    {q : Thread I × Memory} {p : Msg × View} (h : PathWrite A tid t0 mem0 k q p) (hk : k ≤ fuel)
    (hq : q.1.prom = []) : CertWriteN A tid t0 mem0 fuel p := by
  obtain ⟨j, t1, mem1, outs, o, hj, h1, h2, h3, h4, h5⟩ := h
  exact ⟨j, t1, mem1, outs, o, by omega, h1, h2, h3, h4, q.1, q.2, h5.mono (by omega), hq⟩

private theorem foldl_inv' {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_inv' P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

private theorem fold_then' {α β : Type} {P Q : β → Prop} (f : β → α → β) (l : List α) (b : β) (h0 : P b)
    (hs : ∀ b a, a ∈ l → P b → P (f b a)) (hQ : ∀ b, P b → Q b) : Q (l.foldl f b) :=
  hQ _ (foldl_inv' P f l b h0 hs)

/-- **`certify.go` is sound at the fuel, writes included.** -/
theorem certify_go_soundN' (A : Arch) (tid : Nat) (t0 : Thread I) (mem0 : Memory) (fuel : Nat) :
    ∀ (n : Nat) (s : Std.HashSet (Thread I × Memory) × CertResult I) (e : Thread I × Memory × List (Msg × View) × Bool),
      GoEntryN' A tid t0 mem0 fuel n e → s.2.SoundN' A tid t0 mem0 fuel →
        (certify.go A tid n s e).2.SoundN' A tid t0 mem0 fuel := by
  intro n
  induction n with
  | zero =>
    rintro ⟨visited, acc⟩ ⟨t, mem, ws, done⟩ he hs
    rw [certify.go]
    split
    · exact hs
    dsimp only
    split
    · exact hs
    obtain ⟨k, hk, hrun, -, hws⟩ := he
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_iff] at hc
      have hok : CertOkN A tid t0 mem0 fuel := ⟨t, mem, hrun.mono (by omega), hc.2⟩
      have hs' : CertResult.SoundN' A tid t0 mem0 fuel { acc with certified := true, writes := acc.writes ++ ws } :=
        ⟨fun _ => hok, fun p hp => by
          rcases List.mem_append.mp hp with hp | hp
          · exact hs.2 p hp
          · exact (hws p hp).certWriteN (by omega) hc.2⟩
      dsimp only
      split
      · exact hs'
      · exact ⟨fun _ => hok, hs'.2⟩
    · rw [ite_eq_right hc]
      dsimp only
      split
      · exact hs
      · exact ⟨hs.1, hs.2⟩
  | succ n ih =>
    rintro ⟨visited, acc⟩ ⟨t, mem, ws, done⟩ he hs
    rw [certify.go]
    split
    · exact hs
    dsimp only
    split
    · exact hs
    obtain ⟨k, hk, hrun, hdone, hws⟩ := he
    have key : ∀ (acc1 : CertResult I) (done1 : Bool), acc1.SoundN' A tid t0 mem0 fuel →
        (done1 = true → t.prom = [] ∧ CertOkN A tid t0 mem0 fuel) →
        (done1 = false → ∀ p ∈ ws, PathWrite A tid t0 mem0 k (t, mem) p) →
        CertResult.SoundN' A tid t0 mem0 fuel
          (if t.halted = true then (visited.insert (t, mem), acc1)
           else match stepOne A t tid mem with
            | none => (visited.insert (t, mem), acc1)
            | some outs =>
              let x := outs.foldl (init := ([], acc1)) fun (next, acc) o =>
                match o with
                | .error m => (next, { acc with faults := acc.faults ++ [m] })
                | .ok o =>
                  if done1 then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
                  else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
              x.1.foldl (certify.go A tid n) (visited.insert (t, mem), x.2)).2 := by
      intro acc1 done1 hs1 hd1 hw1
      split
      · exact hs1
      split
      · exact hs1
      rename_i outs hstep
      refine fold_then' (P := fun R : List (Thread I × Memory × List (Msg × View) × Bool) × CertResult I =>
          (∀ e ∈ R.1, GoEntryN' A tid t0 mem0 fuel n e) ∧ R.2.SoundN' A tid t0 mem0 fuel)
        (Q := fun R => CertResult.SoundN' A tid t0 mem0 fuel
          (List.foldl (certify.go A tid n) (visited.insert (t, mem), R.2) R.1).2)
        _ outs _ ⟨fun _ h => (by simp at h), hs1⟩ ?_ ?_
      · rintro ⟨next, acc⟩ o ho ⟨hn, ha⟩
        cases o with
        | error m => exact ⟨hn, ha.1, ha.2⟩
        | ok o =>
          have hst : ThreadStep A tid (t, mem) (o.thread, o.mem) := ⟨outs, o, hstep, ho, rfl⟩
          have hrun' : ThreadNPn A tid (k + 1) (t0, mem0) (o.thread, o.mem) := hrun.tail hst
          dsimp only
          split
          · rename_i hd
            obtain ⟨hp0, hok⟩ := hd1 hd
            have hp1 : o.thread.prom = [] := RunnerSim.stepOne_prom_nil A hp0 hstep ho
            refine ⟨fun e he' => ?_, ha.1, fun p hp => ?_⟩
            · rcases List.mem_cons.mp he' with rfl | he'
              · exact ⟨k + 1, by omega, hrun', fun _ => ⟨hp1, hok⟩, fun p hp => by cases hp⟩
              · exact hn e he'
            · rcases List.mem_append.mp hp with hp | hp
              · exact ha.2 p hp
              · exact ⟨k, t, mem, outs, o, by omega, hrun, hstep, ho, hp, o.thread, o.mem, .refl _ _, hp1⟩
          · rename_i hd
            have hw := hw1 (by simpa using hd)
            refine ⟨fun e he' => ?_, ha⟩
            rcases List.mem_cons.mp he' with rfl | he'
            · refine ⟨k + 1, by omega, hrun', fun h => (by cases h), fun p hp => ?_⟩
              rcases List.mem_append.mp hp with hp | hp
              · exact (hw p hp).tail hst
              · exact ⟨k, t, mem, outs, o, by omega, hrun, hstep, ho, hp, by
                  rw [show k + 1 - k - 1 = 0 by omega]; exact .refl _ _⟩
            · exact hn e he'
      · rintro ⟨next, acc⟩ ⟨hn, ha⟩
        exact foldl_inv' (fun s : Std.HashSet (Thread I × Memory) × CertResult I => s.2.SoundN' A tid t0 mem0 fuel)
          (certify.go A tid n) next _ ha (fun s e he' hs' => ih s e (hn e he') hs')
    by_cases hc : (!done && t.prom.isEmpty) = true
    · rw [ite_eq_left hc]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_iff] at hc
      have hok : CertOkN A tid t0 mem0 fuel := ⟨t, mem, hrun.mono (by omega), hc.2⟩
      refine key _ true ⟨fun _ => hok, fun p hp => ?_⟩ (fun _ => ⟨hc.2, hok⟩) (fun h => by cases h)
      rcases List.mem_append.mp hp with hp | hp
      · exact hs.2 p hp
      · exact (hws p hp).certWriteN (by omega) hc.2
    · rw [ite_eq_right hc]
      exact key acc done hs hdone (fun _ => hws)

/-- **`CertifySoundN'` (Q1), proved.** -/
theorem certifySoundN' (A : Arch) (I : ISA) : CertifySoundN' A I := by
  intro fuel tid t mem
  unfold certify
  have hnone : ({} : CertCache I)[(t, tid, mem)]? = none := by simp
  rw [hnone]
  have h := certify_go_soundN' A tid t mem fuel fuel ({}, {}) (t, mem, [], false)
    ⟨0, by omega, .refl _ _, fun h => (by cases h), fun p hp => by cases hp⟩
    ⟨fun h => (by cases h), fun p hp => by cases hp⟩
  exact ⟨h.1, h.2⟩

/-! ## The cache-threaded form -/

/-- The cache is `SoundN'` on the keys satisfying `K`. -/
def CacheSoundOnN' (A : Arch) (K : Thread I → Nat → Prop) (fuel : Nat) (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I),
    K t tid → cache[(t, tid, mem)]? = some r → r.SoundN' A tid t mem fuel

theorem cacheSoundOnN'_empty (A : Arch) (K : Thread I → Nat → Prop) (fuel : Nat) :
    CacheSoundOnN' A K fuel ({} : CertCache I) := fun _ _ _ _ _ h => by simp at h

private theorem prod_beq_iff2 {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show (a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true]

/-- **`certify` is sound at the fuel, cache-threaded**: on a key of a
`KeyLawful` family and a cache `SoundN'` on the family, the result is
`SoundN'` and the cache stays `SoundN'`. -/
theorem certify_soundN2 [I.LawfulState] {A : Arch} {K : Thread I → Nat → Prop} (hK : KeyLawful K) {fuel : Nat}
    {cache : CertCache I} (hc : CacheSoundOnN' A K fuel cache) {t : Thread I} {tid : Nat} (ht : K t tid)
    (mem : Memory) :
    (certify A cache t tid mem fuel).1.SoundN' A tid t mem fuel ∧
      CacheSoundOnN' A K fuel (certify A cache t tid mem fuel).2 := by
  unfold certify
  split
  · rename_i r h
    exact ⟨hc t tid mem r ht h, hc⟩
  · have hr := certify_go_soundN' A tid t mem fuel fuel ({}, {}) (t, mem, [], false)
      ⟨0, by omega, .refl _ _, fun h => (by cases h), fun p hp => (by cases hp)⟩
      ⟨fun h => (by cases h), fun p hp => (by cases hp)⟩
    refine ⟨hr, ?_⟩
    intro t' tid' mem' r' ht' h
    rw [Std.HashMap.getElem?_insert] at h
    split at h
    · rename_i heq
      obtain ⟨h1, h23⟩ := (prod_beq_iff2 _ _).mp heq
      obtain ⟨h2, h3⟩ := (prod_beq_iff2 _ _).mp h23
      simp only [beq_iff_eq] at h2 h3
      subst h2 h3
      cases h
      rw [← hK t t' tid ht ht' h1]
      exact hr
    · exact hc t' tid' mem' r' ht' h

/-! ## "Promise now" writes carry the thread id -/

section Tid

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- Every recorded "promise now" write of the context is of thread `tid`. -/
def TidOk (c : Ctx) : Prop := ∀ p ∈ c.promisedNow, p.1.tid = tid

theorem TidOk.of_eq {c c' : Ctx} (h : TidOk tid c) (hp : c'.promisedNow = c.promisedNow) : TidOk tid c' := by
  intro p hp'; rw [hp] at hp'; exact h p hp'

theorem writeSuccs_tidOk {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (hc : TidOk tid c) (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    TidOk tid c' := by
  rcases (mem_writeSuccs A tid).mp h with ⟨_, _, _, _, _, _, _, _, rfl⟩ | ⟨_, rfl⟩
  · exact hc.of_eq tid rfl
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hc p hp
    · rw [List.mem_singleton] at hp; subst hp; rfl

theorem fenceOpt_tidOk {c : Ctx} (hc : TidOk tid c) (b : Bool) (k : FenceKind) :
    TidOk tid (if b then fenceStep c k else c) := by
  cases b
  · exact hc
  · exact hc.of_eq tid (fenceStep_promisedNow c k)

theorem runTree_tidOk {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), TidOk tid c → .ok (s, c') ∈ runTree A tid iv c tree → TidOk tid c' := by
  induction tree with
  | done s0 =>
    intro c s c' hc h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc
  | fault msg =>
    intro c s c' _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hc hi
  | load k xcl l ret ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    exact ih v c0 s c' (hc.of_eq tid (readSuccs_mp A iv h0).2) h
  | store k xcl l v ret ih =>
    intro c s c' hc h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true c0 s c' (writeSuccs_tidOk A tid _ hc hc0) h
    · rw [List.mem_ite_nil_right] at h
      exact ih false { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
        s c' (fun p hp => hc p hp) h.2
  | fence k ret ih =>
    intro c s c' hc h
    simp only [runTree] at h
    exact ih () _ s c' (hc.of_eq tid (fenceStep_promisedNow c k)) h
  | rmw k noRet l op ret ih =>
    intro c s c' hc h
    simp only [runTree] at h
    have h1 := fenceOpt_tidOk tid hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : TidOk tid c2 := h1.of_eq tid (readSuccs_mp A iv h2).2
    simp only at h
    split at h
    · exact ih old _ s c' (fenceOpt_tidOk tid h12 _ _) h
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have h3 := writeSuccs_tidOk A tid _ h12 hc3
      refine ih old _ s c' (fenceOpt_tidOk tid ?_ _ _) h
      split
      · exact h3.of_eq tid rfl
      · exact h3.of_eq tid rfl

end Tid

/-- **A "promise now" write of thread `tid` is of thread `tid`.** -/
theorem promisedNow_tid (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : ∀ p ∈ o.promisedNow, p.1.tid = tid := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    simp only [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    rcases r with m | ⟨st, c'⟩
    · simp at ho
    · simp only [List.mem_map] at ho
      obtain ⟨th, -, he⟩ := ho
      cases he
      exact runTree_tidOk A tid _ tree _ st c' (fun p hp => by cases hp) hr

/-- A `CertWriteN` is a write of its thread. -/
theorem CertWriteN.tid {A : Arch} {tid : Nat} {t : Thread I} {mem : Memory} {fuel : Nat} {w : Msg} {ν : View}
    (h : CertWriteN A tid t mem fuel (w, ν)) : w.tid = tid := by
  obtain ⟨_, _, _, _, o, _, _, hs, ho, hp, _⟩ := h
  exact promisedNow_tid A hs ho _ hp

end Kraken.Promising.Live.Bridge
