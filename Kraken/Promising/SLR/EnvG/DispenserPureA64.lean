/-
**The purity-and-phase environment of a single-RMW dispenser program**
(AArch64 specification). Moved verbatim from `EnvG/TicketLockPure.lean`, so that
other single-RMW dispenser programs can reuse it;
the names stay in `TicketLock` (unchanged fully-qualified names).

- `dispPure A Q x N`: state `Bool` (`true`: after the hand-out). `ok` is
  `relPureQ`'s condition, no store to `x`, and an RMW on `x` only before the
  hand-out, writing `old + 1` below `N`; an RMW on `x` that writes moves to
  `true`, every other step keeps the phase. `Skips`.
- `TreeJ.disp`: the tree judgment `RelWrites ∧ All (∃ b, Post · b) ∧ (BefX`
  at `false`) `∧ (AftX` at `true)`.
  `dispPure` moved (with its `Skips` instance and simp lemmas) and
  `TreeJ.disp` to the ISA-neutral `EnvG/DispenserPure.lean` (same names).
- `DispSpec`, `dispSpec_step`, `DispSpec.ofProgram`,
  `DispSpec.holds_of_partialTripleEnv` (AArch64): `RelPureSpec`/
  `relPureSpec_step` with the phase as the environment state.
- With strict sized declarations (moved here from
  `EnvG/A64TicketRunner.lean`): `DispSpec.HoldsD` (`decls = ds`),
  `DispSpec.holdsD_of_noDecls`, `dispSpec_stepD` (through
  `exec_treeJ_of_reresolve`).

The ticket lock's instance (`tkWorker_dispPure`, `tkDispSpec`) stays in
`EnvG/TicketLockPure.lean`.
-/
import Kraken.Promising.SLR.EnvG.DispenserPure
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.DispenserRun
import Kraken.AArch64.EnvCfg
import Kraken.Promising.SLR.EnvG.A64DeclsBridge

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.TicketLock

variable {A : Arch} {Q : Loc → Val → Prop} {x : Loc} {N : Nat}

/-! ## The AArch64 specification -/

/-- **A thread's purity-and-phase specification** (`RelPureSpec` with the
phase as the environment state). -/
structure DispSpec (A : Arch) (Q : Loc → Val → Prop) (x : Loc) (N : Nat) where
  e : Kraken.Executable Directive
  valid : Kraken.Executable.ValidLayout e
  endPc : Int64
  post : MachineState × Bool → Prop
  post_end : ∀ y, post y → y.1.2 = endPc

/-- The specification holds at a thread state in phase `b`. -/
def DispSpec.Holds (sp : DispSpec A Q x N) (b : Bool) (st : AArch64.State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧
    Safely (sp.e.instrStepEnv (dispPure A Q x N)) sp.post (st.st, b)

/-- **One instruction** (`relPureSpec_step` for `dispPure`). -/
theorem dispSpec_step (sp : DispSpec A Q x N) {b : Bool} {st : AArch64.State} (h : sp.Holds b st) (tree : EvTree AArch64.State)
    (hex : isa.exec st = some tree) : (TreeJ.disp A Q x N (fun s b => sp.Holds b s)).W tree b := by
  obtain ⟨he, hend, hds, hs⟩ := h
  have hv := sp.valid
  rcases hs.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = sp.endPc := sp.post_end _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · exact EnvSpike.exec_treeJ_of_instrStepEnv (TreeJ.disp A Q x N (fun s b => sp.Holds b s)) he hds hT
      (fun m g' hm => ⟨he, hend, hds, hR _ hm⟩) tree hex

/-- The specification of a laid-out program `p`: the end of its text. -/
def DispSpec.ofProgram [layout : _root_.Layout] (p : Program) [hv : Kraken.Executable.ValidLayout (layout p)]
    (Q' : MachineData → Bool → Prop) : DispSpec A Q x N where
  e := layout p
  valid := hv
  endPc := (layout p).addrOf p.length
  post y := (y.1.2 = (layout p).addrOf p.length ∧ Q' y.1.1 y.2) ∨ False
  post_end _ h := h.elim And.left False.elim

/-- **The spec from a partial triple** (`RelPureSpec.holds_of_partialTripleEnv`). -/
theorem DispSpec.holds_of_partialTripleEnv [CodeEnv] [layout : _root_.Layout] {p : Program}
    [Kraken.Executable.ValidLayout (layout p)] {P Q' : MachineData → Bool → Prop}
    {E : Int64 → MachineData → Bool → Prop}
    (ht : MachineWP.PartialTripleEnv (dispPure A Q x N) P p Q' E)
    (henv : cenv = layout p) {st : AArch64.State} (he : st.exe = layout p) (hds : st.decls = {})
    (hend : st.endPc = (layout p).addrOf p.length) (hpc : st.st.2 = (layout p).addrOf 0) {b : Bool}
    (hP : P st.st.1 b) (hE : ∀ a s g, ¬ E a s g := by simp) :
    (DispSpec.ofProgram (A := A) (Q := Q) (x := x) (N := N) p Q').Holds b st := by
  refine ⟨he, hend, hds, ?_⟩
  have hst : st.st = (st.st.1, Kraken.Layout.start Directive) := by
    refine Prod.ext rfl ?_; rw [hpc, Executable.addrOf_zero, Layout.apply_fst]
  rw [hst]
  exact (Program.instrStepEnv_of_partialTripleEnv ht hP henv).mono fun _ h => h.imp id (hE _ _ _)

/-! ## With declarations (moved from `EnvG/A64TicketRunner.lean`) -/

/-- **The purity-and-phase specification holds at a thread state with
declarations `ds`** in phase `b` (`DispSpec.Holds` with `decls = ds`). -/
def DispSpec.HoldsD (sp : DispSpec A Q x N) (ds : Decls) (b : Bool) (st : AArch64.State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = ds ∧
    Safely (sp.e.instrStepEnv (dispPure A Q x N)) sp.post (st.st, b)

/-- **`HoldsD` from `Holds` at the thread with its declarations dropped.** -/
theorem DispSpec.holdsD_of_noDecls {sp : DispSpec A Q x N} {ds : Decls} {b : Bool} {s : AArch64.State}
    (hd : s.decls = ds) (h : sp.Holds b s.noDecls) : sp.HoldsD ds b s :=
  ⟨h.1, h.2.1, hd, h.2.2.2⟩

/-- **One instruction with strict sized declarations** (`dispSpec_step`
through `exec_treeJ_of_reresolve`). -/
theorem dispSpec_stepD (sp : DispSpec A Q x N) {ds : Decls} (hsz : ds.StrictSized)
    (hnp : Kraken.Executable.noPairs sp.e = true) {b : Bool} {st : AArch64.State} (h : sp.HoldsD ds b st)
    (tree : EvTree AArch64.State) (hex : isa.exec st = some tree) :
    (TreeJ.disp A Q x N (fun s b => sp.HoldsD ds b s)).W tree b :=
  exec_treeJ_of_safelyD (TreeJ.disp A Q x N (fun s b => sp.HoldsD ds b s)) hsz (hv := sp.valid) hnp sp.post_end
    (fun _ _ a b c d => ⟨a, b, c, d⟩) h.1 h.2.1 h.2.2.1 h.2.2.2 tree hex

end Kraken.Promising.SLR.EnvG.TicketLock
