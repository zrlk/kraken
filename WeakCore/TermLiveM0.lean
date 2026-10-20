import WeakCore.TermLiveGrow
import WeakCore.TermStep

/-! # TermLiveM0 (M0 pre-rebase): capacity `Cfg.cap`

Under M0 the configuration carries its thread capacity `Cfg.cap`, which no machine step
changes (`TermStep.step_cap`).  So the unchanged `Step` machine is a growing sound system
whose capacity is read off the configuration: `capOf := Cfg.cap`, with `capInv` from
`step_cap` and no re-proof. -/

namespace TermLiveGrow
open CoreLang CoreTerm TermRun TermLiveProps TermLiveMach
open WeakMem (Arch)

/-- (M0) A labelled machine step keeps `Cfg.cap`. -/
theorem machine_cap {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {l : Nat × Bool}
    (h : (machine p k arch).S c l c') : c'.cap = c.cap :=
  TermStep.step_cap (mstep_iff_Step.1 ⟨l, h⟩)

/-- (M0) The `Step` machine is a growing sound system with capacity `Cfg.cap`. -/
theorem machine_soundX (p : Prog) (k : Promises.Knobs) (arch : Arch) :
    SoundX (machine p k arch) p k arch (fun _ _ _ => False) Cfg.cap :=
  let s := soundX_of_sound (machine_sound p k arch) 0
  { mem := s.mem, coh := s.coh, mono := s.mono, thr := s.thr, grow := s.grow, actor_thr := s.actor_thr
    cap := fun c l c' h hlt => absurd ((machine_sound p k arch).size c l c' h) (Nat.ne_of_gt hlt)
    capInv := fun _ _ _ h => machine_cap h }

end TermLiveGrow

/-! Axiom reports (auditor, every theorem). -/
#print axioms TermLiveGrow.machine_cap
#print axioms TermLiveGrow.machine_soundX
