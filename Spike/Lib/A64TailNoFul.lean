/-
**`WriteNoProm` from a closed tail** on the canonical AArch64 target: the
consumers' programs reach a `write` only in the abort stub, after which only
private stores and `exit_group` follow; no certifying run from there can
fulfil a promise, so a certified thread at the `write` has none.

* `TailNoFul I Λ rS Tk μ Dt`: a predicate `Dt` of thread states holds at
  every fragment pair at a `write` (`entry`, given `rS` owned in the phase
  `Tk`), and every certification step from `Dt` lands in `Dt` keeping the
  promise set (`step`);
* `writeNoProm_of_tail`: `WriteNoProm` from `TailNoFul`, by
  `prom_nil_of_closed` (`Spike/Lib/CertClosed.lean`) on `Pre`'s
  certification;
* `tailNoFul_of_wrIn`: from `WrIn` (`inst_of_segW`'s export) and the
  closure of `Dt`;
* `tailNoFul_of_noWrite`: `NoWrite` (`Spike/Lib/A64SegInst.lean`) is the
  case `Dt` false.
-/
import Spike.Lib.A64SegInst
import Spike.Lib.CertClosed

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1

/-- **The tail after a `write` is closed** (fragment `I`, layout `Λ`,
stack range `rS`, phase `Tk`, marks `μ`, tail states `Dt`): `entry`, a pair
at a `write` system call is in `Dt` (given `rS` owned in the phase); `step`,
a certification step of thread 0 from `Dt`, for any kernel state, lands in
`Dt` and keeps the promise set. -/
structure TailNoFul (I : Inv) (Λ : Scc.Sem.Layout) (rS : Range) (Tk : State → Prop) (μ : Marks)
    (Dt : State → Prop) : Prop where
  entry : ∀ lbl lsize s c, I lbl lsize s c → (Tk s → Owned Λ rS s) → abi.atSys s = true → ∀ fd buf n,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s
  step : ∀ x (p q : Thread isaLSE2 × Memory), Dt p.1.st →
    ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 p q → Dt q.1.st ∧ q.1.prom = p.1.prom

/-- **`WriteNoProm` from a closed tail**: in `Pre` thread 0 is certified
(`CertOkC`); at a `write` its state is in `Dt` (`TailNoFul.entry`, `rS`
owned in the phase by `HeldOk`), which the certifying run never leaves
keeping the promise set (`TailNoFul.step`), so the set is empty
(`prom_nil_of_closed`). -/
theorem writeNoProm_of_tail {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : Own} {I : Inv} {rS : Range} {Tk : State → Prop} {μ : Marks} {Dt : State → Prop}
    (h : TailNoFul I Λ rS Tk μ Dt) : WriteNoProm Λ P p G own I rS Tk μ := by
  rintro t s th ⟨th', _, _, lbl, lsize, _, _, _, _, hth, -, -, hh, -, hc, -, -, -, -, hI, -⟩ hth1 hat ⟨fd, buf, n, hw⟩
  rw [hth] at hth1
  cases Option.some.inj (show some th' = some th from congrArg (·[0]?) hth1)
  have ho : Tk th.st → Owned Λ rS th.st := fun htk => by
    rcases hh with ⟨-, hn⟩ | ⟨-, -, ho⟩
    · exact (hn htk).elim
    · exact ho
  exact prom_nil_of_closed (Q := fun x => Dt x.1.st) (t := th) (mem := t.1.mem)
    (fun x y hx hs => h.step _ x y hx hs) (h.entry _ _ th.st _ hI ho hat fd buf n hw) hc

/-- **`NoWrite` is the tail `Dt` false**: no pair is at a `write`. -/
theorem tailNoFul_of_noWrite {Λ : Scc.Sem.Layout} {I : Inv} {rS : Range} {Tk : State → Prop} {μ : Marks}
    (h : NoWrite I) : TailNoFul I Λ rS Tk μ (fun _ => False) :=
  ⟨fun lbl lsize s c hI _ hat fd buf n hw => h lbl lsize s c hI hat fd buf n hw, fun _ _ _ h _ => h.elim⟩

/-- **A closed tail from `WrIn`**: the fragment's states at a `write` in `Dt`
(`WrIn`, which `inst_of_segW` exports from `SFacts.wrTail`) and `Dt` closed
under the certification steps keeping the promise set (`hs`). -/
theorem tailNoFul_of_wrIn {Λ : Scc.Sem.Layout} {I : Inv} {rS : Range} {Tk : State → Prop} {μ : Marks}
    {Dt : State → Prop} (h : WrIn I Dt)
    (hs : ∀ x (p q : Thread isaLSE2 × Memory), Dt p.1.st →
      ThreadStepC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 p q → Dt q.1.st ∧ q.1.prom = p.1.prom) :
    TailNoFul I Λ rS Tk μ Dt :=
  ⟨fun lbl lsize s c hI _ => h lbl lsize s c hI, hs⟩

end Spike.Lib.A64Consumer
