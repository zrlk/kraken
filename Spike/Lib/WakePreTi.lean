/-
**wake.w on AArch64, the pre-spawn trace invariant**:
`WakeObligations`' parameter `Ti` (`Spike/Lib/WakeA64.lean`) before the
spawn, and its `ti_load`, `ti_step` (on `Pre`) and `pre_abort` from
one-slot statements (`Pre1T`).

Before the spawn the trace invariant is `TIC Ab Ac` on the one-slot
configuration `d` of `up d u` (`TiPre`: for every such decomposition with
`u` inert and the slot count matching); `up` is injective (`up_inj`), so
it is a statement about one `d`. A `clone` into the extra slot leaves a
configuration whose last slot runs (`afterClone_ne_up`), so `TiPre` holds
of it vacuously; after the spawn `TiPre` holds vacuously as long as the last
slot never becomes dormant again (`TiPre.of_not_up`, the `Post` side's
obligation, `hpost` of `ti_stepPre`).

`Pre1T` is `Spike.Lib.WakePre.Pre1` with the abort obligation taking
`TIC Ab Ac tr d` (the `writeErr`/`threads` cases need the trace:
`Spike.Lib.A64ConsumerA.r_abortACH`), plus `TIC` at the one-slot load
(`ti0`, from `ti0_of`) and along one-slot steps (`tiStep`,
`ti_stepACH` when `R1` is `RSAH`). In a `WakeObligations` instance whose
`Ti` is (or includes) `TiPre Ab Ac`: `ti_load` from `O.ti_load`,
`ti_step`'s `Pre` case from `O.ti_stepPre`, `pre_abort := O.pre_abort`.
-/
import Spike.Lib.WakePre
import Spike.Lib.A64ConsumerACorrect
import Scc.Sem.OwnDom

namespace Spike.Lib.WakePreTi

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.A64ConsumerA (TIC)
open Spike.Lib.Handover (afterClone step_up_cases)

/-- **`up` is injective.** -/
theorem up_inj {d d' : Cfg} {u u' : Thread isaLSE2} (h : up d u = up d' u') : d = d' ∧ u = u' := by
  obtain ⟨⟨th, m⟩, x⟩ := d
  obtain ⟨⟨th', m'⟩, x'⟩ := d'
  cases x; cases x'
  simp only [up, upC, upX, Prod.mk.injEq, Config.mk.injEq, KState.mk.injEq] at h
  obtain ⟨⟨h1, rfl⟩, h2, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨rfl, rfl⟩ := Array.push_eq_push.mp h1
  obtain ⟨-, rfl⟩ := Array.push_eq_push.mp h2
  exact ⟨rfl, rfl⟩

/-- **After a `clone` the last slot runs**, so the configuration is no
lift (whose last slot is dormant). -/
theorem afterClone_ne_up {d : Cfg} {tid : Nat} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    (d' : Cfg) (u' : Thread isaLSE2) : afterClone abi d tid th stack tls r ≠ up d' u' := by
  intro h
  have h2 := congrArg (fun c : Cfg => c.2.slots) h
  simp only [afterClone, up, upX] at h2
  exact absurd (Array.push_eq_push.mp h2).1 (by simp)

/-- **The trace invariant before the spawn**: `TIC Ab Ac` of the one-slot
configuration of every lift with an inert extra thread. -/
def TiPre (Ab Ac : State → Prop) (t : Cfg) (tr : List Ev) : Prop :=
  ∀ d u, t = up d u → Inert u → d.1.threads.size = d.2.slots.size → TIC Ab Ac tr d

/-- `TiPre` of a lift is `TIC` of its one-slot configuration. -/
theorem TiPre.up_iff {Ab Ac : State → Prop} {d : Cfg} {u : Thread isaLSE2} {tr : List Ev} (hu : Inert u)
    (hn : d.1.threads.size = d.2.slots.size) : TiPre Ab Ac (up d u) tr ↔ TIC Ab Ac tr d := by
  refine ⟨fun h => h d u rfl hu hn, fun h d' u' he _ _ => ?_⟩
  obtain ⟨rfl, -⟩ := up_inj he
  exact h

/-- `TiPre` holds vacuously off the lifts. -/
theorem TiPre.of_not_up {Ab Ac : State → Prop} {t : Cfg} {tr : List Ev} (h : ∀ d u, t ≠ up d u) :
    TiPre Ab Ac t tr :=
  fun d u he _ _ => (h d u he).elim

/-- **`TIC` at the one-slot load** from the loaded thread off both abort
phases (`Spike.Lib.A64Consumer.ti_load`). -/
theorem ti0_of {E : Entry} {asm : String} {Λ : Scc.Sem.Layout} {prog : Program} {secs : DataSecs}
    {Ab Ac : State → Prop} (hpa : textProgram asm = .ok prog) (hd : dataSections asm = some secs)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hac0 : ¬ Ac (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d := by
  intro d h
  have hl := (load_of_parsed (kernel 1) E Λ hpa hd).symm.trans h
  exact ⟨fun th h hab => absurd hab (Spike.Lib.A64Consumer.ti_load hab0 hl th h),
    fun th h hac => absurd hac (Spike.Lib.A64Consumer.ti_load hac0 hl th h)⟩

/-- **The pre-spawn obligations at one slot, with the trace invariant**
`TIC Ab Ac`: `Pre1` with `abort` given `TIC` of the trace, plus `TIC` at
the load (`ti0`) and along one-slot steps from `R1` (`tiStep`). -/
structure Pre1T (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : String) (E : Entry)
    (R1 : Cfg → TermRun.Cfg → Prop) (Ab Ac : State → Prop) : Prop where
  /-- The one-slot load is related to a source start. -/
  init : ∀ d, (target (kernel 1) E).load asm Λ = some d → ∃ s0, (wakeS arch).init s0 ∧ R1 d s0
  /-- A one-slot step keeps `R1` and the slot count, with a matching source run. -/
  step : ∀ tid d es d' s, R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' →
    ∃ s', (wakeS arch).Run s (obs es) s' ∧ R1 d' s' ∧ d'.1.threads.size = d'.2.slots.size
  /-- Progress and layout at one slot, off a `clone`. -/
  progress : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ¬ AtClone d →
    (machine (kernel 1)).Progress ((target (kernel 2) E).marks asm Λ) d ∧ InLayout (M := machine (kernel 1)) Λ d
  /-- Progress and layout at a `clone`, of the lifted configuration. -/
  progressClone : ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) →
    d.1.threads.size = d.2.slots.size → AtClone d →
    (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
      InLayout (M := machine (kernel 2)) Λ (up d u)
  /-- A one-slot abort step after a trace with `TIC` is justified, with
  one-slot components (`r_abortACH`). -/
  abort : ∀ tr d s tid es d' k, (wakeS arch).Reach (obs tr) s → R1 d s → d.1.threads.size = d.2.slots.size →
    TIC Ab Ac tr d →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
    ∃ w i, Components (machine (kernel 1)) Λ w d s ∧ w.thr i = some tid ∧ AbortJustified B (wakeS arch) tr s i k
  /-- The explicit witness at one slot. -/
  wit : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ∃ w, Components (machine (kernel 1)) Λ w d s
  /-- No stack range is held for the extra slot's index. -/
  held : ∀ d s, R1 d s → d.1.threads.size = d.2.slots.size → ∀ h ∈ d.2.held, h.1 ≠ d.1.threads.size
  /-- `TIC` at the one-slot load (`ti0_of`). -/
  ti0 : ∀ d : Cfg, (target (kernel 1) E).load asm Λ = some d → TIC Ab Ac [] d
  /-- A one-slot step from `R1` extends `TIC` by its events (`ti_stepACH`). -/
  tiStep : ∀ tid d es d' s pre, R1 d s → d.1.threads.size = d.2.slots.size →
    (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → TIC Ab Ac pre d →
    TIC Ab Ac (pre ++ es) d'

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- `WakeObligations.pre_progress`. -/
theorem pre_progress (O : Pre1T arch Λ B asm E R1 Ab Ac) :
    ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
      (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) (up d u) ∧
        InLayout (M := machine (kernel 2)) Λ (up d u) := by
  intro d u s hR hu hpl hn
  by_cases hc : AtClone d
  · exact O.progressClone d u s hR hu hpl hn hc
  · obtain ⟨hp, hl⟩ := O.progress d s hR hn hc
    exact ⟨progress_up hn hu hp, hl⟩

/-- `WakeObligations.pre_abort`, for any `Ti` that implies `TiPre Ab Ac`. -/
theorem pre_abort (O : Pre1T arch Λ B asm E R1 Ab Ac) {Ti : Cfg → List Ev → Prop}
    (hTi : ∀ t tr, Ti t tr → TiPre Ab Ac t tr) :
    ∀ tr d u s tid es d' k, (wakeS arch).Reach (obs tr) s → R1 d s → Inert u →
      (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size → Ti (up d u) tr →
      (machine (kernel 1)).Step ((target (kernel 2) E).marks asm Λ) tid d es d' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w (up d u) s ∧ w.thr i = some tid ∧
        AbortJustified B (wakeS arch) tr s i k := by
  intro tr d u s tid es d' k hr hR hu hpl hn hT hs hk
  obtain ⟨w, i, hc, hw, hj⟩ := O.abort tr d s tid es d' k hr hR hn ((TiPre.up_iff hu hn).mp (hTi _ _ hT)) hs hk
  exact ⟨w, i, components_up hn hpl (O.held d s hR hn) hc, hw, hj⟩

/-- `WakeObligations.pre_wit`. -/
theorem pre_wit (O : Pre1T arch Λ B asm E R1 Ab Ac) :
    ∀ d u s, R1 d s → Inert u → (∀ a, privLoad u.st a = none) → d.1.threads.size = d.2.slots.size →
      ∃ w, Components (machine (kernel 2)) Λ w (up d u) s := by
  intro d u s hR _ hpl hn
  obtain ⟨w, hc⟩ := O.wit d s hR hn
  exact ⟨w, components_up hn hpl (O.held d s hR hn) hc⟩

/-- **`WakeObligations.ti_load` for `TiPre`**: the two-slot load is the
lifted one-slot load (`load_two`). -/
theorem ti_load (O : Pre1T arch Λ B asm E R1 Ab Ac) :
    ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → TiPre Ab Ac t0 [] := by
  intro t0 h0
  obtain ⟨d, u, hd, rfl, hu, -, hn⟩ := load_two h0
  exact (TiPre.up_iff hu hn).mpr (O.ti0 d hd)

/-- **`WakeObligations.ti_step` for `TiPre`, on `Pre`**: a lifted step is
a one-slot step (`tiStep`); after a `clone` `TiPre` is vacuous
(`afterClone_ne_up`). -/
theorem ti_stepPre (O : Pre1T arch Λ B asm E R1 Ab Ac) {Q : WakeRel} (hQ : Q.R1 = R1) :
    ∀ tid t es t' s pre, Q.Pre t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → TiPre Ab Ac t pre →
      TiPre Ab Ac t' (pre ++ es) := by
  rintro tid t es t' s pre ⟨d, u, ht, hu, -, hn, hR⟩ hs hT
  subst ht hQ
  have hT := (TiPre.up_iff hu hn).mp hT
  obtain ⟨-, ⟨d', hd', rfl⟩ | ⟨-, th, stack, tls, r, -, -, -, -, -, -, -, rfl, -⟩⟩ := step_up_cases hn hs
  · intro d'' u'' he _ _
    obtain ⟨rfl, -⟩ := up_inj he
    exact O.tiStep tid d es d' s pre hR hn hd' hT
  · exact TiPre.of_not_up afterClone_ne_up

/-- **`WakeObligations.ti_step` for `TiPre`**: on `Pre` by `ti_stepPre`;
on `Post` given that a step from `Post` never reaches a lift (`hpost`: the
last slot, once running, never becomes dormant again). -/
theorem ti_step (O : Pre1T arch Λ B asm E R1 Ab Ac) {Q : WakeRel} (hQ : Q.R1 = R1)
    (hpost : ∀ tid t es t' s, Q.Post Λ t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → ∀ d u, t' ≠ up d u) :
    ∀ tid t es t' s pre, Q.Rw Λ t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → TiPre Ab Ac t pre →
      TiPre Ab Ac t' (pre ++ es) := by
  intro tid t es t' s pre hR hs hT
  rcases hR with hP | hP
  · exact O.ti_stepPre hQ tid t es t' s pre hP hs hT
  · exact TiPre.of_not_up (hpost tid t es t' s hP hs)

end Pre1T

/-! ## Off the lifts after the spawn

`Pre1T.ti_step`'s `hpost` without `Post`'s content: no kernel step makes a
slot dormant (`step_dormant`) or changes the slot count (`step_slots_size`),
and a lift's last slot is dormant (`ne_up_of_last`); so `hpost_of` needs only
that `Post` configurations have a last slot that is not dormant (after the
spawn it runs or has exited). -/
section
variable {I : ISA} {K : Abi I}

/-- **No slot made dormant**: every dormant slot of `c'` was dormant in `c`. -/
def NoNewDormant (c c' : Config I × KState) : Prop :=
  ∀ k : Nat, c'.2.slots[k]? = some Slot.dormant → c.2.slots[k]? = some Slot.dormant

variable (K) in
theorem sysStep_dormant {A : Arch} {tid : Nat} {c c' : Config I × KState} {p : Pick} {es : List Ev}
    (h : sysStep K A tid c p = some (es, c')) : NoNewDormant c c' := by
  unfold sysStep at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i t _ _
  rcases hcall : callOf K t with _ | call
  · simp [hcall] at h
  cases call <;> cases p <;> simp only [hcall] at h <;> (repeat' split at h) <;>
    simp only [back, Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals first
    | obtain ⟨-, rfl⟩ := h
    | obtain ⟨_, _, -, rfl⟩ := h
  all_goals intro k hk
  all_goals first
    | exact hk
    | (refine Scc.Sem.Kernel.set_dormant ?_ hk; simp)

variable (K) in
theorem spawnStep_dormant {tid j : Nat} {c c' : Config I × KState} {r : BitVec 64}
    (h : spawnStep K tid c j r = some c') : NoNewDormant c c' := by
  unfold spawnStep at h
  repeat' split at h
  all_goals try cases h
  all_goals intro k hk; exact OwnDom.set_dormant_run hk

variable (K) in
theorem xferStep_dormant {k : XferKind} {tid : Nat} {c c' : Config I × KState}
    (h : xferStep K k tid c = some c') : NoNewDormant c c' := by
  cases k <;> simp only [xferStep, takeStep, releaseStep] at h <;> split at h <;> try cases h
  all_goals
    split at h
    · cases h; exact fun _ h => h
    · cases h
end

/-- **No kernel step makes a slot dormant** (a `clone` activates one, `exit`
ends one; none goes back). -/
theorem step_dormant {n : Nat} {μ : Marks} {tid : Nat} {c c' : (machine (kernel n)).Cfg} {es : List Ev}
    (h : (machine (kernel n)).Step μ tid c es c') : NoNewDormant c c' := by
  cases h with
  | instr => exact fun _ h => h
  | spawn _ hs => obtain ⟨j, r, hs, -⟩ := hs; exact spawnStep_dormant abi hs
  | sys _ hs => obtain ⟨p, hs, -⟩ := hs; exact sysStep_dormant abi hs
  | xfer k _ _ hx => exact xferStep_dormant abi hx

/-- A configuration whose last slot is not dormant is no lift. -/
theorem ne_up_of_last {t : Cfg} (h : t.2.slots.back? ≠ some Slot.dormant) : ∀ d u, t ≠ up d u := by
  rintro d u rfl
  exact h (by simp [up, upX])

/-- A kernel step keeps the number of slots. -/
theorem step_slots_size {n : Nat} {μ : Marks} {tid : Nat} {c c' : (machine (kernel n)).Cfg} {es : List Ev}
    (h : (machine (kernel n)).Step μ tid c es c') : c'.2.slots.size = c.2.slots.size := by
  cases h with
  | instr => rfl
  | spawn _ hs => obtain ⟨j, r, hs, -⟩ := hs; exact (spawnStep_facts abi hs).2.2
  | sys _ hs => obtain ⟨p, hs, -⟩ := hs; exact sysStep_slots abi hs
  | xfer k _ _ hx => exact xferStep_slots abi hx

/-- If the last slot is dormant after a step, it was before. -/
theorem step_last_dormant {n : Nat} {μ : Marks} {tid : Nat} {c c' : (machine (kernel n)).Cfg} {es : List Ev}
    (h : (machine (kernel n)).Step μ tid c es c') (h' : c'.2.slots.back? = some Slot.dormant) :
    c.2.slots.back? = some Slot.dormant := by
  rw [Array.back?_eq_getElem?] at h' ⊢
  rw [step_slots_size h] at h'
  exact step_dormant h _ h'

/-- **`Pre1T.ti_step`'s `hpost` from the slots alone**: if `Post` configurations
have a last slot that is not dormant, no step from `Post` reaches a lift. -/
theorem hpost_of {Λ : Scc.Sem.Layout} {μ : Marks} {Q : WakeRel}
    (h : ∀ t s, Q.Post Λ t s → t.2.slots.back? ≠ some Slot.dormant) :
    ∀ tid t es t' s, Q.Post Λ t s → (machine (kernel 2)).Step μ tid t es t' → ∀ d u, t' ≠ up d u :=
  fun _ t _ _ s hP hs => ne_up_of_last fun h' => h t s hP (step_last_dormant hs h')

/-- info: 'Spike.Lib.WakePreTi.Pre1T.pre_abort' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1T.pre_abort

/-- info: 'Spike.Lib.WakePreTi.Pre1T.ti_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1T.ti_step

/-- info: 'Spike.Lib.WakePreTi.Pre1T.ti_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1T.ti_load

/-- info: 'Spike.Lib.WakePreTi.ti0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ti0_of

/-- info: 'Spike.Lib.WakePreTi.hpost_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hpost_of

end Spike.Lib.WakePreTi
