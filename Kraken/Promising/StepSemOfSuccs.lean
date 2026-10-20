/-
**Executable ⊆ semantic, proved**
(`StepSemOfSuccs`, Q4 of `LiveBridge.lean`). ISA-neutral, given `I.LawfulState`.

Every `succs` successor of a bounded configuration is a semantic step
(`StepSem`): an instruction step kept by `succsL` either leaves no promise
(certified in zero instructions) or is `certified` by `certify`, hence
`CertOkN fuel` (`certify_soundN2`, Q1); a promise offered by
`certifiedPromises` is a write `(w, ν)` recorded by `certify` with
`ν ≤ |M|`, hence a `CertWriteN` (Q1), hence promisable within `fuel`
(`promReplay`, Q2). `succs` shares one certification cache across all
threads and steps, so the soundness used is the cache-threaded
`certify_soundN2` on the keys `succsL` asks about (`Config.SameProg`).

`I.LawfulState` cannot be dropped: the cache is a hash map keyed on threads,
and with an unlawful `BEq`/`Hashable` on states a cached result for one
thread answers for another (`LiveBridgeTestsLawful.lean`, `BadKey`: a
promise offered by `succs` at fuel 2 that the semantic machine allows only
at fuel 3).

Contents:
- `certifiedPromises_specSem`, `succsL_specSem`;
- `stepSemOfSuccs : StepSemOfSuccs A I`;
- `reachableSem_of_reachable'`: executable reachability is semantic
  reachability, with no open hypothesis. The binder-free AArch64 and x64
  instances are in `StepSemOfSuccsA64.lean` and `StepSemOfSuccsX64.lean`
  (the two ISAs cannot be imported together);
- `traceToSem : TraceToSem A I`: executable traces are semantic traces.
-/
import Kraken.Promising.PromReplay

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

private theorem foldl_invS {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => foldl_invS P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

/-- The promises `certifiedPromises` offers are semantic promise steps; the
cache stays `SoundN'` on the keys `succsL` asks about. -/
theorem certifiedPromises_specSem {A : Arch} [I.LawfulState] (cache : CertCache I) (c : Config I) (hb : c.Bnd)
    (fuel : Nat) (hc : CacheSoundOnN' A c.SameProg fuel cache) (tid : Nat) :
    CacheSoundOnN' A c.SameProg fuel (certifiedPromises A cache c tid fuel).2.2 ∧
      ∀ y ∈ (certifiedPromises A cache c tid fuel).1, StepSem A fuel tid c y.1 := by
  unfold certifiedPromises
  split
  · exact ⟨hc, fun _ h => by cases h⟩
  · rename_i t ht
    obtain ⟨⟨-, hw⟩, hc'⟩ := certify_soundN2 (Config.SameProg.keyLawful c) hc ⟨t, ht, rfl⟩ c.mem
    refine ⟨hc', ?_⟩
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨w, hw', rfl⟩ := hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_eraseDups.mp hw')
    obtain ⟨hp, hν⟩ := List.mem_filter.mp hp
    have hcw := hw p hp
    have hν' : p.2 ≤ c.mem.last := of_decide_eq_true hν
    have hwt : p.1.tid = tid := CertWriteN.tid hcw
    refine .inr ⟨t, p.1, ht, hwt, Proj.promReplay A I fuel tid t c.mem p.1 p.2 (hb tid t ht) hcw hν', ?_⟩
    simp only [msg_with_tid hwt]

/-- **Every successor `succsL` reports is a semantic step**, on a bounded
configuration and a cache `SoundN'` on `Config.SameProg`. -/
theorem succsL_specSem {A : Arch} [I.LawfulState] {fuel : Nat} {mp : Option Nat} (c : Config I) (hb : c.Bnd)
    (cache : CertCache I) (hc : CacheSoundOnN' A c.SameProg fuel cache) :
    ∀ x ∈ (succsL A cache c fuel mp).1, ∃ tid, StepSem A fuel tid c x.1 := by
  unfold succsL
  refine (foldl_invS (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
      CacheSoundOnN' A c.SameProg fuel acc.2.2.2 ∧ ∀ x ∈ acc.1, ∃ tid, StepSem A fuel tid c x.1) _ _ _
      ⟨hc, fun _ h => by cases h⟩ ?_).2
  rintro ⟨next, bound, faults, cache⟩ tid - ⟨hc, hn⟩
  have key : ∀ (F : List (Config I × List TraceEv) × Bool × List String × CertCache I)
      (ps : List (Config I × TraceEv)),
      (CacheSoundOnN' A c.SameProg fuel F.2.2.2 ∧ ∀ x ∈ F.1, ∃ tid, StepSem A fuel tid c x.1) →
      (∀ y ∈ ps, y ∈ (certifiedPromises A F.2.2.2 c tid fuel).1) →
      CacheSoundOnN' A c.SameProg fuel (certifiedPromises A F.2.2.2 c tid fuel).2.2 ∧
        ∀ x ∈ F.1.reverse ++ List.map (fun x => (x.1, [x.2])) ps, ∃ tid, StepSem A fuel tid c x.1 := by
    intro F ps ⟨hF, hF1⟩ hps
    obtain ⟨hc', hp'⟩ := certifiedPromises_specSem _ c hb fuel hF tid
    refine ⟨hc', fun x hx => ?_⟩
    rcases List.mem_append.mp hx with h | h
    · exact hF1 x (List.mem_reverse.mp h)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact ⟨tid, hp' y (hps y hy)⟩
  have hsub : ∀ (ps : List (Config I × TraceEv)) (y : Config I × TraceEv),
      y ∈ (match mp, c.threads[tid]? with
        | some k, some t => if t.prom.length < k then ps else []
        | _, _ => ps) → y ∈ ps := by
    intro ps y hy
    split at hy
    · split at hy
      · exact hy
      · cases hy
    · exact hy
  simp only
  split
  · exact key _ _ ⟨hc, hn⟩ (hsub _)
  · rename_i outs hstep
    obtain ⟨t, ht, hstep⟩ := stepThread_eq_some hstep
    refine key _ _ (foldl_invS (fun acc : List (Config I × List TraceEv) × Bool × List String × CertCache I =>
        CacheSoundOnN' A c.SameProg fuel acc.2.2.2 ∧ ∀ x ∈ acc.1, ∃ tid, StepSem A fuel tid c x.1) _ _ _
        ⟨hc, hn⟩ ?_) (hsub _)
    rintro ⟨next, bound, faults, cache⟩ o ho ⟨hc, hn⟩
    cases o with
    | error m => exact ⟨hc, hn⟩
    | ok o =>
      have hnew : CertOkN A tid o.thread o.mem fuel →
          ∃ tid', StepSem A fuel tid' c (c.withThread tid o.thread o.mem) :=
        fun hok => ⟨tid, .inl ⟨t, outs, o, ht, hstep, ho, hok, rfl⟩⟩
      obtain ⟨⟨hcert, -⟩, hc'⟩ :=
        certify_soundN2 (Config.SameProg.keyLawful c) hc ⟨t, ht, stepOne_static A hstep ho⟩ o.mem
      simp only
      split
      · rename_i he
        refine ⟨hc, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hnew ⟨o.thread, o.mem, .refl _ _, List.isEmpty_iff.mp he⟩
        · exact hn x hx
      · split
        · rename_i hcd
          refine ⟨hc', fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hnew (hcert hcd)
          · exact hn x hx
        · exact ⟨hc', hn⟩

/-- **Executable ⊆ semantic, proved** (Q4, one step): every `succs`
successor of a bounded configuration is a semantic step at the same fuel. -/
theorem stepSemOfSuccs [I.LawfulState] (A : Arch) : StepSemOfSuccs A I := by
  intro fuel c c' hb h
  unfold succs at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  exact succsL_specSem c hb {} (cacheSoundOnN'_empty A _ fuel) x hx

/-- **Executable reachability is semantic reachability**, from a bounded
configuration (e.g. `Config.init`, `Config.init_bnd`), with no open
hypothesis: `reachableSem_of_reachable` at `stepSemOfSuccs`. -/
theorem reachableSem_of_reachable' [I.LawfulState] {A : Arch} {fuel : Nat} {c c' : Config I} (hb : c.Bnd)
    (h : Reachable A fuel c c') : ReachableSem A fuel c c' :=
  reachableSem_of_reachable (stepSemOfSuccs A) hb h

/-- **Every executable trace from a bounded start is a semantic trace**
(`TraceToSem`, proved): the same configurations, each step a `StepSem`
step by `stepSemOfSuccs`, with `Config.Bnd.succ` carrying the bound. -/
theorem traceToSem [I.LawfulState] (A : Arch) : TraceToSem A I := by
  intro fuel tr hb
  have hbi : ∀ i, (tr.cfg i).Bnd := by
    intro i
    induction i with
    | zero => exact hb
    | succ i ih =>
      rcases tr.step i with h | ⟨-, h⟩
      · exact ih.succ h
      · rw [h]; exact ih
  exact ⟨⟨tr.cfg, fun i => (tr.step i).imp (fun h => stepSemOfSuccs A fuel _ _ (hbi i) h) id⟩, rfl⟩

end Kraken.Promising.Live.Bridge
