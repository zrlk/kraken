/-
**`hello1`'s output call segments at a current placement** (x86-64):
`MainPreUL`'s `PrintCallC` and `PrintCallCH` conjuncts
(`Spike/Test/X64Hello1HUL.lean`) at `hello1o`'s `main`: `hello1_printCallC`,
`hello1_printCallCH` (`Spike/Test/X64Hello1Print.lean`) with the world
`W2AtL`/`MSAtL` (`Spike/Lib/LowerX64/RtMainXRL.lean`) at a placement `L0`,
`ls` in place of the start's (no label placed). `printCallC_instAI`,
`printCallCH_instAI` take any placement; the frames under `main`'s are none
at any labels (`FramesPlacedInI.nil`).

Left as premises, beyond `hello1_printCallC`'s: the placed labels inside the
heap (`hrg`; `lblRange_reach` at a reachable placement).

- `hello1_printCallCL`, `hello1_printCallCHL`: the conjuncts at `L0`, `ls`.
-/
import Spike.Test.X64Hello1Print
import Spike.Lib.LowerX64.RtMainXRL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout setupMC rS0 swFSL)
open Spike.Lib.X64.WriteAb (Ab)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- `hello1o`'s `main`. -/
local notation "MD" => Spike.Test.Hello1MainSrc.mainD

open Spike.Test.Hello1MainSrc (hello1_main_compiled2 hello1_main_tails)

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1)
  (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes
    SccCertificate.labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Le P1)

set_option hygiene false in
/-- The runtime's layout of the output at the lowering's immediates (`fnCode2OfP`'s). -/
local notation "LY" => RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of P1)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes
  SccCertificate.labelOffs)

set_option hygiene false in
/-- `W2AtL` at `Closed2At`'s instance, at the current placement `L0`, `ls`. -/
local notation "W2S" J:max => W2AtL h (imms2Me Le P1) P1 Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)
  L0 ls

set_option hygiene false in
/-- `MSAtL` at `Closed2At`'s instance (the nodes' abort `ab2`), at the current placement `L0`, `ls`. -/
local notation "MSS" J:max => MSAtL h (imms2Me Le P1) P1 Spike.Lib.LowerNode.IsNum J (ab2 P1 (Ly).lab) (fun _ => 0)
  L0 ls

set_option hygiene false in
/-- The stack take at the first stack's range. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 P1)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h Le 1 MD hello1_main_compiled2

set_option hygiene false in
/-- `main`'s callee region. -/
local notation "RC" => (RS v).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8

set_option hygiene false in
/-- `main`'s code predicate at the return address of `g`. -/
local notation "CD" g:max => CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
  (Int64.ofBitVec (WcG.ra g))

/-- **`MainPreUL`'s `PrintCallC` conjunct at `hello1o`, at a current placement `L0`,
`ls`** (`printCallC_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λe P1`, `main`'s code
`fnCode2OfP`, the region `rbR RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`; the placed labels
inside the heap (`hrg`). -/
theorem hello1_printCallCL {L0 : Lbl} {ls : Lsize} {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64)
    (F' : MachineData → Prop)
    (hok : (RC).OK) (hst : FStable (RC) F') (hD : ((FC).fr.size : Int) + 64 ≤ D) (hD8 : D % 8 = 0)
    (hal : (rbR (RC)).base.toNat % 16 = 0) (hrg : LblRange (Ly).Λ L0 ls)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (LY).exe (LY).endPc R' F''
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ab' : FragS isa}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1 1 (.let_ x (.call "print" is a []) e) →
      Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RC)) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).fr L0 (imms2Me Le P1) x e c1) s c →
      Ab' s c [printFrame x e c1]) :
    PrintCallC P1 L0 ls (FC).lcx (FC).fr (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
      (rbR (RC)) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] G0 (imms2Me Le P1) (TailAt2 P1 1) Ab' := by
  have hsp := fnCode2OfPMe_spec hello1o_accepted2 h Le 1 MD hello1_main_compiled2
  have hBl0 : ∀ pc z g' k, (FC).Bl g.ra pc z g' k →
      BlC2L OP (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (FC).fr
        (Int64.ofBitVec g.ra) pc z g' k := by
    intro pc z g' k hb
    rw [hsp.2.1] at hb
    rw [hello1_okPc]
    exact hb
  have hlo0 : -(D : Int) ≤ -8 := by omega
  have e1 : (RC).lo = -D := rfl
  have e2 : (RC).hi = 8 := rfl
  have hab : ab2 P1 (Ly).lab = some (Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1 = true from by decide, ↓reduceIte]
  simp only [MSAtL, hab]
  exact printCallC_instAI (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Le P1) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (Spike.Lib.X64.PrintG.printPhOk_of_placeOKAt h _)
    (FC).hf (FC).h1 (FC).h16 (rbR_ok hok (by omega) (by omega)) hal
    (by simp only [rbR, Region.callee] at e1 ⊢; omega) (by simp only [rbR, Region.callee] at e2 ⊢; omega)
    (by simp only [rbR, Region.callee] at e1 ⊢; omega) (by simp only [rbR, Region.callee] at e2 ⊢; omega)
    (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub (Ly)))
    (fun m hm => stackOff_rbR hok (by omega) (by omega) (hFO m hm))
    (progNoS_zbad_of_accepted2 hello1o_accepted2) (rbR_fstable hok (by omega) (by omega) hst)
    (fun _ _ hc => by rw [hello1_okPc]; exact CdCLE.toCdCL hc)
    (fun _ _ _ _ hb => ⟨(hBl0 _ _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ _ hb)⟩)
    rfl rfl (by rw [hsp.1]) hrg
    (by show ∀ r ∈ (Le).rodata :: (Le).regions, r.lo + r.size ≤ 2 ^ 32; decide +kernel)
    (by simp) (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F (fun _ _ _ _ h => h)
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      rfl)
    (fun x g' is a ts e xe ht _ => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      exact ⟨rfl, rfl⟩)
    g.fp g.ra TP0
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      trivial)
    (fun _ _ _ hb => (hBl0 _ _ _ _ hb).1) hDtP hAb

/-- **`MainPreUL`'s `PrintCallCH` conjunct at `hello1o`, at a current placement `L0`,
`ls`** (`printCallCH_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λe P1`, `main`'s code
`fnCode2OfP`, the region `rbR RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`; the placed labels
inside the heap (`hrg`). -/
theorem hello1_printCallCHL {L0 : Lbl} {ls : Lsize} {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64)
    (F' : MachineData → Prop)
    (hok : (RC).OK) (hst : FStable (RC) F') (hD : ((FC).fr.size : Int) + 64 ≤ D) (hD8 : D % 8 = 0)
    (hal : (rbR (RC)).base.toNat % 16 = 0) (hrg : LblRange (Ly).Λ L0 ls)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (LY).exe (LY).endPc R' F''
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ab' : FragS isa}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1 1 (.let_ x (.call "print" is a []) e) →
      Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RC)) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).fr L0 (imms2Me Le P1) x e c1) s c →
      Ab' s c [printFrame x e c1]) :
    PrintCallCH P1 L0 ls (FC).lcx (FC).fr (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
      (rbR (RC)) F' (W2S J) (KT) (MSS J) g.fp g.ra TP0 [] G0 (imms2Me Le P1) (TailAt2 P1 1) Ab' := by
  have hsp := fnCode2OfPMe_spec hello1o_accepted2 h Le 1 MD hello1_main_compiled2
  have hBl0 : ∀ pc z g' k, (FC).Bl g.ra pc z g' k →
      BlC2L OP (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (FC).fr
        (Int64.ofBitVec g.ra) pc z g' k := by
    intro pc z g' k hb
    rw [hsp.2.1] at hb
    rw [hello1_okPc]
    exact hb
  have hlo0 : -(D : Int) ≤ -8 := by omega
  have e1 : (RC).lo = -D := rfl
  have e2 : (RC).hi = 8 := rfl
  have hab : ab2 P1 (Ly).lab = some (Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1 = true from by decide, ↓reduceIte]
  simp only [MSAtL, hab]
  exact printCallCH_instAI (Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (imms2Me Le P1) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (Spike.Lib.X64.PrintG.printPhOk_of_placeOKAt h _)
    (FC).hf (FC).h1 (FC).h16 (rbR_ok hok (by omega) (by omega)) hal
    (by simp only [rbR, Region.callee] at e1 ⊢; omega) (by simp only [rbR, Region.callee] at e2 ⊢; omega)
    (by simp only [rbR, Region.callee] at e1 ⊢; omega) (by simp only [rbR, Region.callee] at e2 ⊢; omega)
    (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub (Ly)))
    (fun m hm => stackOff_rbR hok (by omega) (by omega) (hFO m hm))
    (progNoS_zbad_of_accepted2 hello1o_accepted2) (rbR_fstable hok (by omega) (by omega) hst)
    (fun _ _ hc => by rw [hello1_okPc]; exact CdCLE.toCdCL hc)
    (fun _ _ _ _ hb => ⟨(hBl0 _ _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ _ hb)⟩)
    rfl rfl (by rw [hsp.1]) hrg
    (by show ∀ r ∈ (Le).rodata :: (Le).regions, r.lo + r.size ≤ 2 ^ 32; decide +kernel)
    (by simp) (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) hG0F (fun _ _ _ _ h => h)
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      rfl)
    (fun x g' is a ts e xe ht _ => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      exact ⟨rfl, rfl⟩)
    g.fp g.ra TP0
    (fun x is a e ht => by
      rcases hello1_main_tails (ht _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
      trivial)
    (fun _ _ _ hb => (hBl0 _ _ _ _ hb).1) hDtP hAb

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_printCallCL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_printCallCL

/-- info: 'Spike.Lib.LowerX64.hello1_printCallCHL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_printCallCHL
