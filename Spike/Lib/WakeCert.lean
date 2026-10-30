/-
**wake.w after the spawn keeps the certification invariant** (`WakeObligations.cert_step`, AArch64): a step from `Post`
keeps `CertAll`.

- `sysStep_frame`: a kernel system-call step keeps the memory, every other
  thread and every other slot.
- `spawnStep_dormant`: a `clone` step needs a dormant slot below the thread
  count.
- `certAll_step_of`: `cert_step`. **The thread that steps** is certified
  after its step by the semantics (`Spike.Lib.WakeW1.step1_cases`): an
  instruction or a promise step carries `CertOkC` at the kernel state (kept)
  and the outcome memory; a kernel step carries `CertAfter`; at the
  post-state's `Post` the named hypothesis `hconv` (`CertConv`) makes it
  append-free (`CertReplay.CertOkCNA`, `CertAll`). A `clone` from
  `Post` is impossible (`KR`: no dormant slot), and so is a range transfer
  (both threads at no transfer site: `WCompat.noSite`, `WCompat0.noSite0`;
  main in `Mi` while the process runs, `KR`'s `MainLive`). **The thread
  that does not step** keeps its state; its certification is transported
  across the other thread's step by the named hypothesis `henv` (`CertReplay` transports of `CertOkCNA`: the memory-extension replay with
  kernel-state independence, for main and for the worker).
-/
import Spike.Lib.WakeProgress

namespace Spike.Lib.WakeCert

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1

/-! ## Frames of the kernel steps -/

section Frame

variable {I : ISA} {K : Abi I}

theorem withThread_ne {c : Config I} {tid i : Nat} {u : Thread I} {mem : Memory} (h : i ≠ tid) :
    (c.withThread tid u mem).threads[i]? = c.threads[i]? := by
  rw [withThread_get]
  simp [Ne.symm h]

theorem set_ne {x : KState} {tid i : Nat} {s : Slot} (h : i ≠ tid) : (x.set tid s).slots[i]? = x.slots[i]? := by
  simp only [KState.set, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [Ne.symm h]

/-- The frame of a step: memory kept, every other thread and slot kept. -/
def Frame (tid : Nat) (c c' : Config I × KState) : Prop :=
  c'.1.mem = c.1.mem ∧ (∀ i, i ≠ tid → c'.1.threads[i]? = c.1.threads[i]?) ∧
    ∀ i, i ≠ tid → c'.2.slots[i]? = c.2.slots[i]?

theorem frame_with {tid : Nat} {c : Config I × KState} {u : Thread I} {x : KState}
    (hx : ∀ i, i ≠ tid → x.slots[i]? = c.2.slots[i]?) : Frame tid c (c.1.withThread tid u c.1.mem, x) :=
  ⟨rfl, fun _ h => withThread_ne h, hx⟩

/-- **A kernel system-call step keeps the memory, the other threads and
the other slots.** -/
theorem sysStep_frame {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : Frame tid c c' := by
  have hkeep : ∀ i, i ≠ tid → c.2.slots[i]? = c.2.slots[i]? := fun _ _ => rfl
  have hset : ∀ s, ∀ i, i ≠ tid → (c.2.set tid s).slots[i]? = c.2.slots[i]? := fun _ _ h => set_ne h
  have hback : ∀ (u : Thread I) r x es', (∀ i, i ≠ tid → x.slots[i]? = c.2.slots[i]?) →
      back K tid c u r x es' = some (es, c') → Frame tid c c' := by
    intro u r x es' hx hb
    simp only [back, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨-, rfl⟩ := hb
    exact frame_with hx
  unfold sysStep at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | exact hback _ _ _ _ hkeep h
    | exact hback _ _ _ _ (hset _) h
    | (simp only at h
       repeat' split at h
       all_goals first
         | (simp at h; done)
         | exact hback _ _ _ _ hkeep h
         | exact hback _ _ _ _ (hset _) h
         | (obtain ⟨⟨b, t'⟩, -, he⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at he
            obtain ⟨-, rfl⟩ := he
            exact frame_with (hset _)))
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       exact ⟨rfl, fun _ _ => rfl, hset _⟩)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       exact ⟨rfl, fun _ _ => rfl, hkeep⟩)

/-- **A `clone` step needs a dormant slot** below the thread count. -/
theorem spawnStep_dormant {tid j : Nat} {c c' : Config I × KState} {r : BitVec 64}
    (h : spawnStep K tid c j r = some c') : c.2.slots[j]? = some .dormant ∧ j < c.1.threads.size := by
  unfold spawnStep at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · by_cases hd : c.2.slots[j]? = some .dormant ∧ j < c.1.threads.size
    · exact hd
    · rw [ite_eq_right (fun h' => hd ⟨h'.1, h'.2.1⟩)] at h
      cases h
  · cases h

end Frame

/-! ## `cert_step` -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {μ : Marks}
  {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}

/-- **The step of a running thread from `Post` is neither a `clone` nor a
range transfer**, and the thread is in its side's invariant (at no
transfer site). -/
theorem no_site_of_post (hC : WCompat Q D μ Λ arch) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1) {t : Cfg} {s : TermRun.Cfg}
    (hP : Q.Post Λ t s) (hx : t.2.exited = none) {tid : Nat} {th : Thread isaLSE2}
    (ht : t.1.threads[tid]? = some th) : siteAt abi μ th.st = none := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hT, hS, -, h0, h1, -⟩, hK⟩ := hP
  rw [hKR] at hK
  simp only [WakeRel.PTw] at h0 h1
  rw [hPT0] at h0
  rw [hC.pt1] at h1
  rcases tid with _ | _ | n
  · have e : some t0 = some th := by rw [← ht, hT]; rfl
    cases e
    exact hC0.noSite0 w _ _ (h0.2.1.resolve_right (hK.2.2.2.2.1 hx s0 (by rw [hS]; rfl)))
  · have e : some t1 = some th := by rw [← ht, hT]; rfl
    cases e
    exact hC.noSite w _ _ h1.1
  · rw [hT] at ht; simp at ht

/-- **`cert_step`**: a step from `Post` to `Post` keeps `CertAll`. The
stepping thread by the semantics (`CertOkC`), made append-free at the
post-state by `hconv`; the other by `henv` (the transports of
`CertOkCNA`). -/
theorem certAll_step_of (hC : WCompat Q D μ Λ arch) (hC0 : WakeM0.WCompat0 Q M μ Λ)
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (henv : ∀ tid t es t' s i th, Q.Post Λ t s → i ≠ tid → (machine (kernel 2)).Step μ tid t es t' →
      t.2.exited = none → t'.2.exited = none →
      t.1.threads[i]? = some th → t'.1.threads[i]? = some th → t.2.runs i = true → th.prom ≠ [] →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t.2 i) i th t.1.mem →
      CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th t'.1.mem)
    (hconv : ∀ t s, Q.Post Λ t s → CertConv μ t) :
    ∀ tid t es t' s s', Q.Post Λ t s → CertAll μ t → (machine (kernel 2)).Step μ tid t es t' →
      Q.Post Λ t' s' → CertAll μ t' := by
  intro tid t es t' s s' hP hca hs hP' hx'
  obtain ⟨⟨th, ht⟩, hx, -⟩ := hs.runs
  have hx : t.2.exited = none := hx
  have hlt : tid < t.1.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  -- the other thread: kept, transported by `henv`
  have hother : ∀ i th', i ≠ tid → t'.1.threads[i]? = t.1.threads[i]? →
      (t'.2.runs i = true → t.2.runs i = true) → t'.1.threads[i]? = some th' → t'.2.runs i = true →
      th'.prom ≠ [] → CertReplay.CertOkCNA Arch.armv8 (certSem abi Arch.armv8 μ t'.2 i) i th' t'.1.mem := by
    intro i th' hne he hr ht' hr' hp
    have ht0 : t.1.threads[i]? = some th' := he ▸ ht'
    exact henv tid t es t' s i th' hP hne hs hx hx' ht0 ht' (hr hr') hp (hca hx i th' ht0 (hr hr') hp)
  rcases step1_cases ht hs with ⟨-, -, outs, o, -, -, rfl, hco⟩ | ⟨-, w, -, rfl, hco⟩ | ⟨p, hsy, hca'⟩ |
      ⟨-, j, r, hsp⟩ | ⟨-, k, hk, -⟩
  · intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      have e : (t.1.withThread i o.thread o.mem).threads[i]? = some o.thread := by
        rw [withThread_get, ite_eq_left ⟨rfl, hlt⟩]
      cases (show some o.thread = some th' from e.symm.trans ht')
      exact hconv _ _ hP' hx' _ _ ht' hr' hp hco
    · exact hother i th' hi (withThread_ne hi) id ht' hr' hp
  · intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      have e : (t.1.withThread i (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1).threads[i]? =
          some (Live.Sem.promThread th t.1.mem w) := by
        rw [withThread_get, ite_eq_left ⟨rfl, hlt⟩]
      cases (show some (Live.Sem.promThread th t.1.mem w) = some th' from e.symm.trans ht')
      exact hconv _ _ hP' hx' _ _ ht' hr' hp hco
    · exact hother i th' hi (withThread_ne hi) id ht' hr' hp
  · obtain ⟨-, hth, hsl⟩ := sysStep_frame hsy
    intro i th' ht' hr' hp
    by_cases hi : i = tid
    · subst hi
      exact hconv _ _ hP' hx' _ th' ht' hr' hp (hca' th' ht')
    · refine hother i th' hi (hth i hi) (fun h => ?_) ht' hr' hp
      simp only [KState.runs] at h ⊢
      rw [← hsl i hi]
      exact h
  · exfalso
    obtain ⟨hd, hj⟩ := spawnStep_dormant hsp
    obtain ⟨w, ⟨t0, t1, -, -, -, -, -, hT, -⟩, hK⟩ := hP
    rw [hKR] at hK
    obtain ⟨-, ⟨j0, h0⟩, h1, -⟩ := hK
    rw [hT] at hj
    rcases j with _ | _ | j
    · rw [h0] at hd; cases hd
    · exact h1 hd
    · simp at hj; omega
  · exfalso
    obtain ⟨a, ha, t2, ht2, hpc⟩ := hk
    cases (show some t2 = some th from ht2.symm.trans ht)
    have hn := siteAt_eq_none_iff.mp (no_site_of_post hC hC0 hPT0 hKR hP hx ht)
    subst hpc
    cases k
    · exact hn.1 ha
    · exact hn.2 ha

/-- info: 'Spike.Lib.WakeCert.certAll_step_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms certAll_step_of

end Spike.Lib.WakeCert
