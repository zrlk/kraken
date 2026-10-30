/-
**wake.w on AArch64, no source event before the spawn**:
the pre-spawn relation strengthened by "while the process runs, the source
has observed nothing" (`NoObs`), so that at main's `clone` the source's
observed list is empty (`SrcSem.traceOf s = []`, the trace conjunct of
`Spike.Lib.WakeKR.KR` / `WakeSpawn.SpawnPre`).

- `sysStep_evs`: a kernel step emits `out` only at a `write(1, …)` of a
  thread at its system call, and `exit` only into an exited process;
- `step_obs_nil`: a one-slot step whose thread is at no `write(1, …)`,
  into a process that has not exited, has no observable event;
- `NoObs d s`: `d.2.exited = none → srcObs SrcSem.traceOf s = []`; kept
  along source runs of `obs es = []` (`run_trace_wc`), true at wake.w's
  start (`noObs_start`), and it gives `SrcSem.traceOf s = []` and
  `mainExit s = []` (`NoObs.traceOf_nil`), also after a run with the empty
  trace (`NoObs.run_nil`);
- `Pre1T.noObs`: any `Pre1T … R1` whose `R1` sees no `write(1, …)` while
  the process runs (`hw`) is a `Pre1T` at `fun d s => R1 d s ∧ NoObs d s`.
  At `RSAH` `hw` is `rsah_hw`, from `pre1T_of`'s `hnw`.
-/
import Spike.Lib.WakePreAsm
import Scc.Sem.SrcOutProto

namespace Spike.Lib.WakeNoObs

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WakeT1 Spike.Lib.WakeA64 Spike.Lib.WakePre
open Spike.Lib.WakePreTi

/-! ## The events of a step -/

/-- **The observable events of a kernel step**: `out` only at a
`write(1, …)` of thread `tid`, which is at its system call; `exit` only
into an exited process. -/
theorem sysStep_evs {tid : Nat} {c c' : Cfg} {p : Pick} {es : List Ev}
    (h : sysStep abi Arch.armv8 tid c p = some (es, c')) :
    (∀ b, Ev.out b ∈ es → ∃ t buf n, c.1.threads[tid]? = some t ∧ abi.atSys t.st = true ∧
      callOf abi t = some (.write 1 buf n)) ∧
    (∀ e, Ev.exit e ∈ es → c'.2.exited = some (.exit e)) := by
  unfold sysStep at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h
    · rename_i hrd
      have hsys : abi.atSys t.st = true := by
        have h' : ready abi tid c t = true := by simpa using hrd
        simp only [ready, Bool.and_eq_true] at h'
        exact h'.1.1
      split at h
      all_goals try simp only [back, Option.ite_none_right_eq_some, Option.map_eq_some_iff,
        Option.some.injEq, Prod.mk.injEq] at h
      case h_1 fd buf n _ hc =>
        obtain ⟨-, a, -, rfl, rfl⟩ := h
        by_cases h1 : fd = 1
        · subst h1; exact ⟨fun _ _ => ⟨t, buf, n, ht, hsys, hc⟩, by simp⟩
        · simp [h1]
      case h_2 =>
        repeat' split at h
        all_goals (simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h)
        all_goals (obtain ⟨rfl, rfl⟩ := h; simp)
      all_goals first
        | (obtain ⟨-, rfl, rfl⟩ := h; simp)
        | cases h

/-- **A one-slot step has no observable event** when no running thread at
its system call is at a `write(1, …)` (`hw`) and the process has not exited
after it. -/
theorem step_obs_nil {μ : Marks} {tid : Nat} {d d' : (machine (kernel 1)).Cfg} {es : List Ev}
    (hw : ∀ t, d.1.threads[tid]? = some t → abi.atSys t.st = true → ∀ buf n, callOf abi t ≠ some (.write 1 buf n))
    (hx : d'.2.exited = none) (hs : (machine (kernel 1)).Step μ tid d es d') : obs es = [] := by
  cases hs with
  | instr => rfl
  | spawn => rfl
  | xfer => rfl
  | sys _ h hl _ _ =>
    obtain ⟨p, hp, -⟩ := h
    obtain ⟨ho, he⟩ := sysStep_evs hp
    match es, hl with
    | [], _ => rfl
    | [e], _ =>
      cases e with
      | out b =>
        obtain ⟨t, buf, n, ht, hsy, hc⟩ := ho b List.mem_cons_self
        exact (hw t ht hsy buf n hc).elim
      | exit k => rw [he k List.mem_cons_self] at hx; cases hx
      | writeErr => rfl
      | cloneErr => rfl
      | abort k => rfl

/-! ## The invariant -/

/-- **Nothing observed while the process runs**: the source's observable
trace (`srcObs` of the observed list `SrcSem.traceOf`) is empty as long as
`d` has not exited. -/
def NoObs (d : Cfg) (s : TermRun.Cfg) : Prop :=
  d.2.exited = none → SrcSem.srcObs SrcSem.traceOf s = []

/-- `cutAtExit` is empty only on the empty list. -/
theorem cutAtExit_eq_nil {l : List Ev} (h : SrcSem.cutAtExit l = []) : l = [] := by
  match l, h with
  | [], _ => rfl
  | .exit _ :: _, h => cases h
  | .out _ :: _, h => cases h
  | .writeErr :: _, h => cases h
  | .cloneErr :: _, h => cases h
  | .abort _ :: _, h => cases h

/-- **`NoObs` gives the empty observed list** (`KR`'s trace conjunct) and
`main` not returned. -/
theorem NoObs.traceOf_nil {d : Cfg} {s : TermRun.Cfg} (h : NoObs d s) (hx : d.2.exited = none) :
    SrcSem.traceOf s = [] ∧ SrcSem.mainExit s = [] :=
  List.append_eq_nil_iff.mp (cutAtExit_eq_nil (h hx))

/-- **`NoObs` along a source run with no observable event** (`run_trace_wc`
at wake.w's parameters). -/
theorem NoObs.run {arch : WeakMem.Arch} {d d' : Cfg} {s s' : TermRun.Cfg} {tr : List Ev} (h : NoObs d s)
    (hr : (wakeS arch).Run s tr s') (htr : tr = []) (hx : d'.2.exited = none → d.2.exited = none) :
    NoObs d' s' := by
  intro hx'
  have : SrcSem.srcObs SrcSem.traceOf s' = SrcSem.srcObs SrcSem.traceOf s ++ tr :=
    Scc.Sem.SrcOutProto.run_trace_wc (P := srcPo 2 arch wakeSrc) (p := wakeSrc) rfl hr
  rw [this, h (hx hx'), htr]
  rfl

/-- **The empty observed list after a run with the empty trace**: the
trace conjunct of `WakeSpawn.SpawnPre` at the spawned source. -/
theorem NoObs.run_nil {arch : WeakMem.Arch} {d : Cfg} {s s' : TermRun.Cfg} (h : NoObs d s)
    (hr : (wakeS arch).Run s [] s') (hx : d.2.exited = none) : SrcSem.traceOf s' = [] :=
  (NoObs.traceOf_nil (d := d) (h.run hr rfl id) hx).1

/-- **`NoObs` at wake.w's start**: no event, `main` not returned. -/
theorem noObs_start {arch : WeakMem.Arch} {d : Cfg} {s0 : TermRun.Cfg} (h : (wakeS arch).init s0) : NoObs d s0 := by
  intro _
  have h0 : s0 = tidStartT 2 := by
    have h' : progInitT wakeSrc 2 s0 := h
    rw [wake_start] at h'
    exact h'
  subst h0
  rfl

/-! ## The pre-spawn obligations with `NoObs` -/

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- **`Pre1T` with `NoObs`**: from `R1`'s obligations and no `write(1, …)`
of a thread at its system call while the process runs (`hw`), the
obligations at `R1 ∧ NoObs`. A step keeps `NoObs`: into an exited process
vacuously, otherwise it has no observable event (`step_obs_nil`; a step
leaves no process un-exited: `exited_no_step`). -/
theorem noObs (O : Pre1T arch Λ B asm E R1 Ab Ac)
    (hw : ∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isaLSE2), R1 d s → d.2.exited = none →
      d.1.threads[tid]? = some t → abi.atSys t.st = true → ∀ buf n, callOf abi t ≠ some (.write 1 buf n)) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ NoObs d s) Ab Ac where
  init d hd := by
    obtain ⟨s0, hi, hR⟩ := O.init d hd
    exact ⟨s0, hi, hR, noObs_start hi⟩
  step tid d es d' s h hn hs := by
    obtain ⟨hR, hN⟩ := h
    obtain ⟨s', hr, hR', hn'⟩ := O.step tid d es d' s hR hn hs
    refine ⟨s', hr, ⟨hR', ?_⟩, hn'⟩
    have hx : d'.2.exited = none → d.2.exited = none := fun _ => by
      cases hd : d.2.exited with
      | none => rfl
      | some o => exact (Kernel.exited_no_step abi (o := o) hd hs).elim
    intro hx'
    exact NoObs.run hN hr (step_obs_nil (fun t ht hsy => hw d s tid t hR (hx hx') ht hsy) hx' hs) hx hx'
  progress d s h hn hc := O.progress d s h.1 hn hc
  progressClone d u s h hu hpl hn hc := O.progressClone d u s h.1 hu hpl hn hc
  abort tr d s tid es d' k hr h hn hti hs hk := O.abort tr d s tid es d' k hr h.1 hn hti hs hk
  wit d s h hn := O.wit d s h.1 hn
  held d s h hn := O.held d s h.1 hn
  ti0 := O.ti0
  tiStep tid d es d' s pre h hn hs hti := O.tiStep tid d es d' s pre h.1 hn hs hti

end Pre1T

open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA in
/-- **`Pre1T.noObs`'s `hw` at `RSAH`**: from `Spike.Lib.WakePreAsm.pre1T_of`'s
`hnw` (no `write(1, …)` at a system call of the fragment); after the exit
vacuously. -/
theorem rsah_hw {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {H : State → List (Nat × Range) → Prop}
    (hnw : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true →
      ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)) :
    ∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isaLSE2), RSAH Λ P p G own I H μ ar d s →
      d.2.exited = none → d.1.threads[tid]? = some t → abi.atSys t.st = true →
      ∀ buf n, callOf abi t ≠ some (.write 1 buf n) := by
  intro d s tid t h hx ht hsys buf n
  rcases h with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · obtain ⟨th', _, _, lbl, lsize, _, _, _, _, hth', _, _, _, _, _, _, _, _, hI, _⟩ := h
    obtain ⟨-, rfl⟩ := get_one hth' ht
    exact hnw _ _ _ _ _ hI hsys buf n
  · rw [hk] at hx; cases hx

/-- info: 'Spike.Lib.WakeNoObs.sysStep_evs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sysStep_evs

/-- info: 'Spike.Lib.WakeNoObs.NoObs.run_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoObs.run_nil

/-- info: 'Spike.Lib.WakeNoObs.Pre1T.noObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1T.noObs

/-- info: 'Spike.Lib.WakeNoObs.rsah_hw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rsah_hw

end Spike.Lib.WakeNoObs
