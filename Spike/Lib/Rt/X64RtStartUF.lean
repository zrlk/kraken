/-
**`scc_rt_start`'s states inside `W`, for any placed output, with an extra
frame `Fw` after the switch** (x86-64): `startAllUW_gen`
(`Spike/Lib/Rt/X64RtStartU.lean`) at `StartAllUWF`
(`Spike/Lib/Rt/X64SegsF.lean`).

- `startAllUWF_gen`: `startAllUW_gen`'s statement, the switch's obligations
  `hs3` at `SwUWF`; the parts before the switch by `st0W_gen` and
  `x0W_of_bare`.
-/
import Spike.Lib.Rt.X64RtPhRec
import Spike.Lib.Rt.X64EntryOfPlaceOK
import Spike.Lib.Rt.X64StartArith
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.Rt.X64SegsF

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (TN TK TI TcbG TiG TakeG TcbW TiW TakeW StackM pinA pnA lockA freeNA nextA stacksA
  St0W X0W x0L x1L startCall startCall2 startFs startSw startCall_ok startCall2_ok startFs_ok startSw_ok
  startCallIn startCall2In startTailIn stackM_stable)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

section Start

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option quotPrecheck false

/-- The runtime's layout of the output. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h i

/-- **`startAllUW_gen` with the extra frame `Fw` after the switch**: the
same obligations up to the switch (`st0W_gen`, `x0W_of_bare`), the switch's
and `scc_rt_main`'s as given at `Fw ∧ swFSL …` (`hs3`). -/
theorem startAllUWF_gen
    {p : Prog} {lbl : Lbl} {ms : MemSide isa} {rS : Range} {Dt : State → Prop} {c0 : Ctl} {R : Region}
    {F : MachineData → Prop} {Fw : _root_.Mem 64 → Prop} {n0 k0 : BitVec 64} {L : Int} {mc : MainCode}
    {D : Int} {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} (hs : o.place.tail = .bare)
    (hC0 : CFacts (Ly).Λ lbl c0) (hR : R.OK) (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi)
    (hFr : ∀ m, F m → rtF (Ly) m) (hn0 : n0 = 0#64)
    (hrS : rS = ⟨(stacksA (Ly).lab + k0).toNat, 16384⟩) (hsub : rS.Sub (Ly).pool)
    (hout : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hs3 : SwUWF (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R (fun m => F m ∧ StackM rS m) Fw ms rS
      (pinA (Ly).lab + n0 + 8#64) (stacksA (Ly).lab + k0 + 16384#64) c0 L mc D ZU Post) :
    StartAllUWF (fun s c => SFacts (Ly).Λ (PhRec.μ (Ly)) (PhRec.own (Ly)) rS (PhRec.Tk (Ly)) lbl s c Dt)
      (PhRec.K (Ly) rS) p lbl (Ly).exe (Ly).endPc R F Fw ms rS n0 k0 c0 L mc D ZU Post := by
  subst hn0
  exact ⟨st0W_gen h i hC0 hR hlo hhi hFr, x0W_of_bare h i hs hC0 hR hlo hhi hFr hrS hsub hout, hs3⟩

end Start

end Spike.Lib.X64.Rt
