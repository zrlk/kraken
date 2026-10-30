/-
**`hello1`'s output call segments at a current placement** (AArch64; the
twin of `Spike/Test/X64Hello1PrintL.lean`): `MainPreUAL`'s `PrintCallC` and
`PrintCallCH` conjuncts (`Spike/Test/A64Hello1HUL.lean`) at `hello1o`'s
`main`: `hello1_printCallCA`, `hello1_printCallCHA`
(`Spike/Test/A64Hello1Print.lean`) with the world `W2AtL`/`MSAtL`
(`Spike/Lib/LowerA64/RtMainXRL.lean`) at a placement `L0`, `ls` in place of
the start's (no label placed). `printCallC_instAI`, `printCallCH_instAI`
take any placement; the frames under `main`'s are none at any labels
(`FramesPlacedInI.nil`).

Left as premises, beyond `hello1_printCallCA`'s: the placed labels inside
the heap (`hrg`; `lblRange_reach` at a reachable placement).

- `hello1_printCallCAL`, `hello1_printCallCHAL`: the conjuncts at `L0`, `ls`.
-/
import Spike.Test.A64Hello1Print
import Spike.Lib.LowerA64.RtMainXRL

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (InvS)
open Spike.Lib.A64.Rt (RuntimeLayout setupMC rS0 swFSL)
open Spike.Lib.A64.WriteAb (Ab)

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- `hello1o`'s `main`. -/
local notation "MD" => Spike.Test.Hello1MainSrc.mainD

open Spike.Test.Hello1MainSrc (hello1_main_compiled2 hello1_main_tails)

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A)
  (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me LeA P1A)

set_option hygiene false in
/-- The runtime's layout of the output at the lowering's immediates (`fnCode2OfP`'s). -/
local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1A)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A))

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance, at the current placement `L0`, `ls`. -/
local notation "W2S" J:max => W2AtL h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0) L0 ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`), at the current placement `L0`, `ls`. -/
local notation "MSS" J:max => MSAtL h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum J (ab2 P1A (Ly).lab)
  (fun _ => 0) L0 ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 P1A)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h LeA 1 MD hello1_main_compiled2

set_option hygiene false in
/-- `main`'s callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(SC).Z.toInt) (-D) 0

set_option hygiene false in
/-- `main`'s code predicate at the return address of `g`. -/
local notation "CD" g:max => CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec (WcG.ra g))

/-- **`MainPreUAL`'s `PrintCallC` conjunct at `hello1o`, at a current
placement `L0`, `ls`** (`printCallC_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λx P1`, `main`'s code
`fnCode2OfPMe`, the region `RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`; the placed labels inside the heap
(`hrg`). -/
theorem hello1_printCallCAL {L0 : Lbl} {ls : Lsize} {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64)
    (F' : MachineData → Prop) (hok : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hst : FStable (RC) F')
    (hD : ((FC).cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0) (hrg : LblRange (Ly).Λ L0 ls)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ab' : FragS isaLSE2}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1A 1 (.let_ x (.call "print" is a []) e) →
      At (LY).exe (LY).endPc (RC) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx L0 (imms2Me LeA P1A) x e c1)
        s c → Ab' s c [printFrame x e c1]) :
    PrintCallC P1A L0 ls (FC).lcx (FC).cx (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
      (RC) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] G0 (imms2Me LeA P1A) (TailAt2 P1A 1) Ab' := by
  have hsp := fnCode2OfPMe_spec hello1o_accepted2 h LeA 1 MD hello1_main_compiled2
  have hBl0 : ∀ pc g' k, (FC).Bl g.ra pc g' k →
      BlC2L OP (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (FC).cx
        (Int64.ofBitVec g.ra) pc g' k := by
    intro pc g' k hb
    rw [hsp.2.1] at hb
    rw [hello1_okPcA]
    exact hb
  have e1 : (RC).lo = -D := rfl
  have e2 : (RC).hi = 0 := rfl
  have hab : ab2 P1A (Ly).lab = some (Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1A = true from by decide, ↓reduceIte]
  simp only [MSAtL, hab]
  exact printCallC_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me LeA P1A) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.PrintG.printPhOkF_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (FC).hf (FC).h1 (FC).h16 hok hal (by rw [e1]; omega) (by rw [e2]; exact Int.le_refl _)
    (by rw [e1]; omega) (by rw [e2]; rfl)
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    hFO (progNoS_zbad_of_accepted2 hello1o_accepted2) hst
    (fun _ _ hc => by rw [hello1_okPcA]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    rfl rfl (by rw [hsp.1]) hrg
    (below32_of_placeOKAt h)
    (by simp) (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F
    (fun x g' is a ts e xe ht _ => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      exact ⟨rfl, rfl⟩)
    g.fp g.ra TP0
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      trivial)
    hDtP hAb (fun _ _ _ _ h => h)
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      rfl)

/-- **`MainPreUAL`'s `PrintCallCH` conjunct at `hello1o`, at a current
placement `L0`, `ls`** (`printCallCH_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λx P1`, `main`'s code
`fnCode2OfPMe`, the region `RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`; the placed labels inside the heap
(`hrg`). -/
theorem hello1_printCallCHAL {L0 : Lbl} {ls : Lsize} {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64)
    (F' : MachineData → Prop) (hok : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hst : FStable (RC) F')
    (hD : ((FC).cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0) (hrg : LblRange (Ly).Λ L0 ls)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ab' : FragS isaLSE2}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1A 1 (.let_ x (.call "print" is a []) e) →
      At (LY).exe (LY).endPc (RC) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx L0 (imms2Me LeA P1A) x e c1)
        s c → Ab' s c [printFrame x e c1]) :
    PrintCallCH P1A L0 ls (FC).lcx (FC).cx (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
      (RC) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] G0 (imms2Me LeA P1A) (TailAt2 P1A 1) Ab' := by
  have hsp := fnCode2OfPMe_spec hello1o_accepted2 h LeA 1 MD hello1_main_compiled2
  have hBl0 : ∀ pc g' k, (FC).Bl g.ra pc g' k →
      BlC2L OP (Spike.Lib.A64.PhRec.okPc (Ly)) (Spike.Lib.A64.PhRec.ph (Ly)) (Ly).lab (FC).cx
        (Int64.ofBitVec g.ra) pc g' k := by
    intro pc g' k hb
    rw [hsp.2.1] at hb
    rw [hello1_okPcA]
    exact hb
  have e1 : (RC).lo = -D := rfl
  have e2 : (RC).hi = 0 := rfl
  have hab : ab2 P1A (Ly).lab = some (Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1A = true from by decide, ↓reduceIte]
  simp only [MSAtL, hab]
  exact printCallCH_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me LeA P1A) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.PrintG.printPhOkF_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (FC).hf (FC).h1 (FC).h16 hok hal (by rw [e1]; omega) (by rw [e2]; exact Int.le_refl _)
    (by rw [e1]; omega) (by rw [e2]; rfl)
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    hFO (progNoS_zbad_of_accepted2 hello1o_accepted2) hst
    (fun _ _ hc => by rw [hello1_okPcA]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    rfl rfl (by rw [hsp.1]) hrg
    (below32_of_placeOKAt h)
    (by simp) (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F
    (fun x g' is a ts e xe ht _ => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      exact ⟨rfl, rfl⟩)
    g.fp g.ra TP0
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      trivial)
    hDtP hAb (fun _ _ _ _ h => h)
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      rfl)

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_printCallCAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_printCallCAL

/-- info: 'Spike.Lib.LowerA64.hello1_printCallCHAL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_printCallCHAL
