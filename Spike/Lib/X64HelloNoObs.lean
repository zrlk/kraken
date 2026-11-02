/-
**hello.w on x86-64, no source event before the spawn**: hello's
instances of `Spike.Lib.X64WakeNoObs`, at `p := helloSrc` (hello's source
starts before its setup block, `X64HelloSrc.hello_start`).

- `NoObs.runH` / `NoObs.run_nilH`: `NoObs` along a `helloS` run with no
  observable event, and the empty observed list after a run with the empty
  trace;
- `noObs_startH`: `NoObs` at hello.w's start (`setupStartT 2`);
- `Pre1T.noObsH`: any `Pre1T … R1 … helloSrc` whose `R1` sees no
  `write(1, …)` while the process runs (`hw`) is a `Pre1T` at
  `fun d s => R1 d s ∧ NoObs d s`. At `RSAH` `hw` is
  `X64WakeNoObs.rsah_hw`.

x86-64 twin of `Spike/Lib/HelloNoObs.lean` (same names, namespaces with the `X64` prefix).

**Where this differs from AArch64**: nothing beyond the ISA: the observable event is a `syscall` `write(1, …)`
(A64's `svc`), as `X64WakeNoObs` states it; the statements are the A64 file's.
-/
import Spike.Lib.X64WakeNoObs
import Spike.Lib.X64HelloSrc

namespace Spike.Lib.X64HelloNoObs

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.TwoSlot Spike.Lib.X64TwoSlot Spike.Lib.X64WakeT1 Spike.Lib.X64WakeA64 Spike.Lib.X64WakePre
open Spike.Lib.X64WakePreTi Spike.Lib.X64WakeNoObs Spike.Lib.X64HelloSrc

/-- **`NoObs` along a hello source run with no observable event**
(`run_trace_wc` at hello.w's parameters). -/
theorem NoObs.runH {arch : WeakMem.Arch} {d d' : Cfg} {s s' : TermRun.Cfg} {tr : List Ev} (h : NoObs d s)
    (hr : (helloS arch).Run s tr s') (htr : tr = []) (hx : d'.2.exited = none → d.2.exited = none) :
    NoObs d' s' := by
  intro hx'
  have : SrcSem.srcObs SrcSem.traceOf s' = SrcSem.srcObs SrcSem.traceOf s ++ tr :=
    Scc.Sem.SrcOutProto.run_trace_wc (P := srcPo 2 arch helloSrc) (p := helloSrc) rfl hr
  rw [this, h (hx hx'), htr]
  rfl

/-- **The empty observed list after a hello run with the empty trace**:
the trace conjunct at the spawned source. -/
theorem NoObs.run_nilH {arch : WeakMem.Arch} {d : Cfg} {s s' : TermRun.Cfg} (h : NoObs d s)
    (hr : (helloS arch).Run s [] s') (hx : d.2.exited = none) : SrcSem.traceOf s' = [] :=
  (NoObs.traceOf_nil (d := d) (NoObs.runH h hr rfl id) hx).1

/-- **`NoObs` at hello.w's start**: no event, `main` not returned. -/
theorem noObs_startH {arch : WeakMem.Arch} {d : Cfg} {s0 : TermRun.Cfg} (h : (helloS arch).init s0) :
    NoObs d s0 := by
  intro _
  have h0 : s0 = setupStartT 2 := by
    have h' : progInitT helloSrc 2 s0 := h
    rw [hello_start] at h'
    exact h'
  subst h0
  rfl

namespace Pre1T

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {E : Entry}
  {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop}

/-- **`Pre1T` with `NoObs` at hello.w**: as `X64WakeNoObs.Pre1T.noObs`, at
`p := helloSrc`. -/
theorem noObsH (O : Pre1T arch Λ B asm E R1 Ab Ac (p := helloSrc))
    (hw : ∀ (d : Cfg) (s : TermRun.Cfg) (tid : Nat) (t : Thread isa), R1 d s → d.2.exited = none →
      d.1.threads[tid]? = some t → abi.atSys t.st = true → ∀ buf n, callOf abi t ≠ some (.write 1 buf n)) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ NoObs d s) Ab Ac (p := helloSrc) where
  init d hd := by
    obtain ⟨s0, hi, hR⟩ := O.init d hd
    exact ⟨s0, hi, hR, noObs_startH hi⟩
  step tid d es d' s h hn hs := by
    obtain ⟨hR, hN⟩ := h
    obtain ⟨s', hr, hR', hn'⟩ := O.step tid d es d' s hR hn hs
    refine ⟨s', hr, ⟨hR', ?_⟩, hn'⟩
    have hx : d'.2.exited = none → d.2.exited = none := fun _ => by
      cases hd : d.2.exited with
      | none => rfl
      | some o => exact (Kernel.exited_no_step abi (o := o) hd hs).elim
    intro hx'
    exact NoObs.runH hN hr (step_obs_nil (fun t ht hsy => hw d s tid t hR (hx hx') ht hsy) hx' hs) hx hx'
  progress d s h hn hc := O.progress d s h.1 hn hc
  progressClone d u s h hu hpl hn hc := O.progressClone d u s h.1 hu hpl hn hc
  abort tr d s tid es d' k hr h hn hti hs hk := O.abort tr d s tid es d' k hr h.1 hn hti hs hk
  wit d s h hn := O.wit d s h.1 hn
  held d s h hn := O.held d s h.1 hn
  ti0 := O.ti0
  tiStep tid d es d' s pre h hn hs hti := O.tiStep tid d es d' s pre h.1 hn hs hti

end Pre1T

/-- info: 'Spike.Lib.X64HelloNoObs.NoObs.run_nilH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NoObs.run_nilH

/-- info: 'Spike.Lib.X64HelloNoObs.noObs_startH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noObs_startH

/-- info: 'Spike.Lib.X64HelloNoObs.Pre1T.noObsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pre1T.noObsH

end Spike.Lib.X64HelloNoObs
