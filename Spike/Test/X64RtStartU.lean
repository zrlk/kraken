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
  startAllUW_gen (atTables ret0_placeOK) ret0Imms rfl hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFr rfl
    (by rw [rS0, ← (Spike.Lib.X64.Rt.ret0P).lab_stacks]) hsub hEC.2.2.2.2 hs3

/-- The `scc_rt_thread_init` step at any tail applies at `ret0.x`'s placed
record (no bare-tail premise). -/
example := @startTiAtW_gen _ _ _ (atTables ret0_placeOK) ret0Imms

/-- At `ret0.x`'s bare tail it is `X0W.ti`'s `TiW` (`tiWAt_x7`), at the
first stack in the callee region of `_start`'s call. -/
example {lbl : Spike.Lib.X64Consumer.Lbl} {Dt : State → Prop} {c0 : Spike.Lib.Ctl} {F : MachineData → Prop}
    (hC0 : Spike.Lib.X64Consumer.CFacts (Spike.Lib.X64.Rt.ret0P).Λ lbl c0)
    (hFr : ∀ m, F m → rtF (Spike.Lib.X64.Rt.ret0P) m) :
    ∀ g, g.ra = ((Spike.Lib.X64.Rt.ret0P).lab Spike.Lib.X64.Flow.Ret0.x1L).toBitVec → ∀ j,
      Spike.Lib.X64.Flow.Ret0.TiW (fun s c => Spike.Lib.X64Consumer.SFacts (Spike.Lib.X64.Rt.ret0P).Λ
          (PhRec.μ (Spike.Lib.X64.Rt.ret0P)) (PhRec.own (Spike.Lib.X64.Rt.ret0P))
          (rS0 (Spike.Lib.X64.Rt.ret0P)) (PhRec.Tk (Spike.Lib.X64.Rt.ret0P)) lbl s c Dt)
        (PhRec.K (Spike.Lib.X64.Rt.ret0P) (rS0 (Spike.Lib.X64.Rt.ret0P)))
        (Spike.Lib.X64.Rt.ret0P).exe (Spike.Lib.X64.Rt.ret0P).endPc
        (((entryR Scc.Sem.Entry.linux).callee (-8) (-296) 8).callee (-48 - 0) (-248) 8) F
        (Spike.Lib.X64.Flow.Ret0.StackM (rS0 (Spike.Lib.X64.Rt.ret0P)))
        ⟨g, Spike.Lib.X64.Flow.Ret0.pinA (Spike.Lib.X64.Rt.ret0P).lab + 0#64 + 8#64, 0#64, c0⟩ j :=
  have hE := RuntimeLayout.linux_ok_ofPlaceOK (atTables ret0_placeOK) ret0Imms
  have hsub := rS0_sub (Spike.Lib.X64.Rt.ret0P)
  have hEC := Spike.Lib.LowerX64.ec_facts _ hE hsub
  fun g hg j => tiWAt_x7 j ▸ startTiAtW_gen (atTables ret0_placeOK) ret0Imms hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFr
    (by rw [rS0, ← (Spike.Lib.X64.Rt.ret0P).lab_stacks]) hsub hEC.2.2.2.2 g hg j

/-- `.x0` to the switch at any tail (`X0WAt`) applies at `ret0.x`'s placed
record. -/
example := @x0WAt_gen _ _ _ (atTables ret0_placeOK) ret0Imms

/-- At `ret0.x`'s bare tail it is `X0W`, at the first stack in the callee
region of `_start`'s call. -/
example {lbl : Spike.Lib.X64Consumer.Lbl} {Dt : State → Prop} {c0 : Spike.Lib.Ctl} {F : MachineData → Prop}
    (hC0 : Spike.Lib.X64Consumer.CFacts (Spike.Lib.X64.Rt.ret0P).Λ lbl c0)
    (hFr : ∀ m, F m → rtF (Spike.Lib.X64.Rt.ret0P) m) :
    Spike.Lib.X64.Flow.Ret0.X0W (fun s c => Spike.Lib.X64Consumer.SFacts (Spike.Lib.X64.Rt.ret0P).Λ
        (PhRec.μ (Spike.Lib.X64.Rt.ret0P)) (PhRec.own (Spike.Lib.X64.Rt.ret0P))
        (rS0 (Spike.Lib.X64.Rt.ret0P)) (PhRec.Tk (Spike.Lib.X64.Rt.ret0P)) lbl s c Dt)
      (PhRec.K (Spike.Lib.X64.Rt.ret0P) (rS0 (Spike.Lib.X64.Rt.ret0P)))
      (Spike.Lib.X64.Rt.ret0P).exe (Spike.Lib.X64.Rt.ret0P).endPc
      ((entryR Scc.Sem.Entry.linux).callee (-8) (-296) 8) F (rS0 (Spike.Lib.X64.Rt.ret0P)) 0#64 0#64 c0 :=
  have hE := RuntimeLayout.linux_ok_ofPlaceOK (atTables ret0_placeOK) ret0Imms
  have hsub := rS0_sub (Spike.Lib.X64.Rt.ret0P)
  have hEC := Spike.Lib.LowerX64.ec_facts _ hE hsub
  x0W_of_bare (atTables ret0_placeOK) ret0Imms rfl hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFr
    (by rw [rS0, ← (Spike.Lib.X64.Rt.ret0P).lab_stacks]) hsub hEC.2.2.2.2

/-- `scc_rt_start` whole at any tail (`StartAllUWAt`) applies at `ret0.x`'s
placed record. -/
example := @startAllUWAt_gen _ _ _ (atTables ret0_placeOK) ret0Imms

/-- At `ret0.x`'s bare tail, `startAllUW_of_bare` gives `startAllUW_gen`'s
conclusion at the same premises. -/
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
  startAllUW_of_bare (atTables ret0_placeOK) ret0Imms rfl hC0 hEC.1 hEC.2.1 hEC.2.2.1 hFr rfl
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
