/-
**`scc_rt_start`'s obligations at `ret0.x`'s placed record**
(`Spike/Lib/Rt/X64RtStartU.lean`): the generic lemma applies at the record of
`ret0_placeOK`, in `_start`'s call's callee region at the first stack
(`ec_facts`'s region premises); a wrong phase row of `scc_rt_start` fails the
table, and a pc after the take is not before it. The twin of
`Spike/Test/A64RtStartU.lean`.
-/
import Spike.Lib.Rt.X64RtStartU
import Spike.Lib.LowerX64.StartSeg
import Spike.Test.X64Ret0PlaceOK

namespace Spike.Lib.X64.Rt.StartUTest

open Scc.Cert.PlaceOK.X64 (atTables)

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (rtPhOk)
open Spike.Lib.X64 Spike.Lib.X64.Rt
open Scc.Cert.PlaceOK.X64.Test (ret0_placeOK)
open SccCode (ret0Imms ret0Λ ret0Cells)

/-- `scc_rt_start`'s obligations at `ret0.x`'s placed record. -/
example := @startAllUW_gen _ _ _ (atTables ret0_placeOK) ret0Imms

/-- At the first stack (`k0 = 0`) in the callee region of `_start`'s call at
the Linux entry: only the source's facts, the frame condition and the
switch's obligations are left. -/
example {p : CoreTerm.Prog} {lbl : Spike.Lib.X64Consumer.Lbl} {ms : MemSide isa} {Dt : State → Prop}
    {c0 : Spike.Lib.Ctl} {F : MachineData → Prop} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Spike.Lib.Ctl → BitVec 64 → Prop}
    (hC0 : Spike.Lib.X64Consumer.CFacts (Spike.Lib.X64.Rt.ret0P).Λ lbl c0)
    (hFr : ∀ m, F m → rtF (Spike.Lib.X64.Rt.ret0P) m)
    (hs3 : SwUW (fun s c => Spike.Lib.X64Consumer.SFacts (Spike.Lib.X64.Rt.ret0P).Λ
        (PhRec.μ (Spike.Lib.X64.Rt.ret0P)) (PhRec.own (Spike.Lib.X64.Rt.ret0P))
        (rS0 (Spike.Lib.X64.Rt.ret0P)) (PhRec.Tk (Spike.Lib.X64.Rt.ret0P))
        lbl s c Dt)
      (PhRec.K (Spike.Lib.X64.Rt.ret0P) (rS0 (Spike.Lib.X64.Rt.ret0P))) p lbl
      (Spike.Lib.X64.Rt.ret0P).exe (Spike.Lib.X64.Rt.ret0P).endPc
      ((entryR Scc.Sem.Entry.linux).callee (-8) (-296) 8)
      (fun m => F m ∧ Spike.Lib.X64.Flow.Ret0.StackM (rS0 (Spike.Lib.X64.Rt.ret0P)) m) ms
      (rS0 (Spike.Lib.X64.Rt.ret0P))
      (Spike.Lib.X64.Flow.Ret0.pinA (Spike.Lib.X64.Rt.ret0P).lab + 0#64 + 8#64)
      (Spike.Lib.X64.Flow.Ret0.stacksA (Spike.Lib.X64.Rt.ret0P).lab + 0#64 + 16384#64)
      c0 L mc D ZU Post) :=
  have hE := RuntimeLayout.linux_ok_ofPlaceOK (atTables ret0_placeOK) ret0Imms
  have hsub := rS0_sub (Spike.Lib.X64.Rt.ret0P)
  have hEC := Spike.Lib.LowerX64.ec_facts _ hE hsub
  startAllUW_gen (atTables ret0_placeOK) ret0Imms hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFr rfl
    (by rw [rS0, ← (Spike.Lib.X64.Rt.ret0P).lab_stacks]) hsub hEC.2.2.2.2 hs3

/-- The rows themselves pass. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ startPhTab = true := by
  decide +kernel

/-- `.x0` is in phase `12`, not `13`: the wrong row fails. -/
example : rtPhOk ret0Λ.code.lo ret0Cells ret0Λ (startPhTab ++ [.ph Code.Start.x0L 0 13]) = false := by
  decide +kernel

/-- Phases `13` and `12` are before the take (`noTk_of_ph`'s side
condition); a phase with bit 3 clear, e.g. `4`, is not. -/
example : (13 / 8 % 2 = 1) ∧ (12 / 8 % 2 = 1) ∧ ¬ (4 / 8 % 2 = 1) := by decide

end Spike.Lib.X64.Rt.StartUTest
