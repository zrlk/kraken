/-
**The start facts of `Obl2X` at the loaded thread** (x86-64): `hst`,
`htk0` and `hab0` at the layout `lay2 Λ p`, the record `ofPlaceOK h
(imms2Me Λ p)` and the loaded thread `threadAt E …` of `Rest2X`; the twin
of `Spike/Lib/LowerA64/Start2Facts.lean`.

- `hst2X_of`: the loaded thread in the multi-level fragment `IN ar (fun _ =>
  none) (fun _ => 0) inv` at the layout's (empty) placement, given the
  family `inv` contains the start's fragment `At … (entryN0 lab c0)` at no
  frame (`nodes2_of_starts`' first conjunct, `h0_ofPlaceOK`'s start).
- `htk0X_2`: the loaded thread is off the take's phase `PhRec.Tk`
  (`_start`'s phase is `13`).
- `hab0X_2`: the loaded thread is off the write abort `WriteAb.Ab`.
-/
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.LowerX64.Entry2
import Spike.Lib.LowerX64.AbStart
import Spike.Lib.AllocReach

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.AllocReach (IN Reach)
open Spike.Lib.X64.Rt (RuntimeLayout rtF entryR)

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog} {o : Scc.Cert.PlaceOK.X64.Out}
    (h : placeOKAt pcfg (lay2 Λ p) o = true)
include h

set_option hygiene false in
/-- The record of `ofPlaceOK` at `lay2`'s immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

/-- **`hst`**: at an admissible entry state `E`, the loaded thread with the
control `c0` at no frame is in `IN ar (fun _ => none) (fun _ => 0) inv` at
the layout's placement (no static label) and no size, for any family `inv`
containing the start's fragment at `_start`'s node `entryN0 lab c0`, the
entry stack `entryR E` and any frame condition `FE` the runtime's unloaded
words (`rtF`) imply. -/
theorem hst2X_of {E : Entry} (hE : E.Ok (lay2 Λ p)) {ar : Arena} {inv : InvS}
    {FE : MachineData → Prop} (hF : ∀ m, rtF (Ly) m → FE m) {c0 : Ctl}
    (hS0 : ∀ s c fs, (Spike.Lib.X64.At (Ly).exe (Ly).endPc (entryR E) FE
      (Spike.Lib.X64.Rt.entryN0 (Ly).lab c0)).at [] s c fs → inv (fun _ => none) (fun _ => 0) s c fs) :
    IN ar (fun _ => none) (fun _ => 0) inv (lay2 Λ p).static (fun _ => 0)
      (threadAt E (lay2 Λ p).code.lo o.prog (loadSyms (lay2 Λ p) o.secs.rodata)) c0 [] := by
  refine ⟨Reach.base, hS0 _ _ _ ⟨?_, rfl⟩⟩
  obtain ⟨h1, h2, h3, h4, σ, hA, hR, hJ⟩ :=
    entry_atXEC h _ c0 hE (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h _ E)
  exact ⟨h1, h2, h3, h4, σ, hA, hF _ hR, hJ⟩

/-- **`htk0`**: at any entry state `E`, the loaded thread is off the
take's phase. -/
theorem htk0X_2 (E : Entry) :
    ¬ Spike.Lib.X64.PhRec.Tk (Ly) (threadAt E (lay2 Λ p).code.lo o.prog (loadSyms (lay2 Λ p) o.secs.rodata)) :=
  Spike.Lib.X64.PhRec.htk0_ofPlaceOK h _
    (Spike.Lib.X64.PhRec.hph0_of h _ (Spike.Lib.X64.PhRec.hpc_ofPlaceOKE h _ E)
      (Spike.Lib.X64.PhRec.hph0_ofPlaceOK h _))

/-- **`hab0`**: at any entry state `E`, the loaded thread is off the write
abort. -/
theorem hab0X_2 (E : Entry) :
    ¬ Spike.Lib.X64.WriteAb.Ab (Ly).lab
      (threadAt E (lay2 Λ p).code.lo o.prog (loadSyms (lay2 Λ p) o.secs.rodata)) :=
  hab0_ofPlaceOKE h _ E

end Start

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hst2X_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hst2X_of

/-- info: 'Spike.Lib.LowerX64.htk0X_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms htk0X_2

/-- info: 'Spike.Lib.LowerX64.hab0X_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hab0X_2

end Spike.Lib.LowerX64
