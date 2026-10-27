/-
**`hello1`'s output call segments** (AArch64; the twin of
`Spike/Test/X64Hello1Print.lean`): `MainPreUA`'s `PrintCallC` and
`PrintCallCH` conjuncts (`Spike/Test/A64Hello1HU.lean`) at `hello1o`'s `main`
(compiled block `1`), from `printCallC_instAI`, `printCallCH_instAI`
(`Spike/Lib/LowerA64/PrintCallInstAI.lean`) at the record of the placement
check: the world `W2At`/`MSAt` and the code facts `fnCode2OfPMe` both at the
theorem's immediates `imms2Me Λx P1`.

Discharged at `hello1o`: the continuation of `main`'s one `print` call is
`ret 0`, free of `ZBad` (`hNoS`); the tables agree (one table); `main`'s
calls are at `BlC2L` (`fnCode2OfPMe_spec`) and `main` is not one of the runtime's functions
(`ProOK`), so their return addresses are in `done`'s phase and off the write
abort; the instance from `instOk_ofPlaceOK`, `print`'s and the abort's code
and `print`'s phase check from the placement check; `main`'s frame facts from
`fnCode2OfPMe`; the stack `rS0` in the pool; no label placed (`LblRange`), the
linked layout's regions below `2 ^ 32`; no frame under `main`'s; the nodes'
abort `ab2` is the write abort (`hasPrint`).

Left as premises (the caller's, per context): the callee region's room
(`hD`, `hD8`), its words of `rS0` off it (`hFO`), its frame condition stable
(`hst`), `FrOk2` along `G0` (`hG0F`), the write tail `hDtP` and the abort
`hAb` at `printNAS`.

- `hello1_okPcA`: the record's sites at either immediates' table;
- `hello1_imms_leA`, `hello1_imms_retA`: the lowering's table `imms2Of` against `imms2Me` at `hello1o`;
- `hello1_printCallCA`, `hello1_printCallCHA`: the conjuncts.
-/
import Spike.Test.A64Hello1HU
import Spike.Lib.LowerA64.PrintCallInstAI
import Spike.Lib.Rt.A64PrintNoSite

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

/-- **Each entry of `imms2Of hello1o` is `imms2Me`'s**: the lowering's table
has no entry at the setup start's terms (`imms2Me_of_ne` elsewhere). -/
theorem hello1_imms_leA : ∀ t x k v, Scc.Lower.imms2Of P1A t x k = some v → imms2Me LeA P1A t x k = some v := by
  intro t x k v hv
  by_cases hs : (t = Scc.Sem.SrcSem.setupTerm ∨ t = setupK) ∧ x = "me" ∧ k = 0
  · obtain ⟨ht | ht, rfl, rfl⟩ := hs <;> subst ht
    · have h0 : Scc.Lower.imms2Of P1A Scc.Sem.SrcSem.setupTerm "me" 0 = none := by decide
      rw [h0] at hv; cases hv
    · have h0 : Scc.Lower.imms2Of P1A setupK "me" 0 = none := by decide
      rw [h0] at hv; cases hv
  · rw [imms2Me_of_ne fun _ ht hx hk => hs ⟨ht, hx, hk⟩]
    exact hv

/-- **The two tables agree at `ret 0`**, `main`'s `print` call's
continuation. -/
theorem hello1_imms_retA : imms2Me LeA P1A (.ret (.lit 0)) = Scc.Lower.imms2Of P1A (.ret (.lit 0)) := by
  funext x k
  refine imms2Me_of_ne fun _ ht _ _ => ?_
  rcases ht with ht | ht <;> simp [Scc.Sem.SrcSem.setupTerm, setupK] at ht

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
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum J (ab2 P1A (Ly).lab) (fun _ => 0)

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

/-- **The record's sites at either immediates' table**: `okPcOf` reads the
layout only through its abort labels. -/
theorem hello1_okPcA : Spike.Lib.A64.PhRec.okPc (Ly) = Spike.Lib.A64.PhRec.okPc (LY) := by
  have e1 : (Ly).Λ.code.lo = (LY).Λ.code.lo := rfl
  have e2 : (Ly).prog = (LY).prog := rfl
  have e3 : (Ly).Λ.abortLbl = (LY).Λ.abortLbl := rfl
  unfold Spike.Lib.A64.PhRec.okPc
  rw [e1, e2]
  funext pc
  unfold Scc.Cert.Rt.A64.okPcOf Scc.Cert.Rt.A64.sitesOf Scc.Cert.Rt.A64.sitesBy Scc.Cert.Rt.A64.siteLabels
  rw [e3]

/-- **`MainPreUA`'s `PrintCallC` conjunct at `hello1o`** (`printCallC_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λx P1`, `main`'s code
`fnCode2OfPMe`, the region `RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`. -/
theorem hello1_printCallCA {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64) (F' : MachineData → Prop)
    (hok : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hst : FStable (RC) F')
    (hD : ((FC).cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ab' : FragS isaLSE2}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1A 1 (.let_ x (.call "print" is a []) e) →
      At (LY).exe (LY).endPc (RC) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx (fun _ => none) (imms2Me LeA P1A) x e c1)
        s c → Ab' s c [printFrame x e c1]) :
    PrintCallC P1A (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
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
  simp only [MSAt, hab]
  exact printCallC_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me LeA P1A) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.StubW.printPhOk_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (FC).hf (FC).h1 (FC).h16 hok hal (by rw [e1]; omega) (by rw [e2]; exact Int.le_refl _)
    (by rw [e1]; omega) (by rw [e2]; rfl)
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    hFO (progNoS_zbad_of_accepted2 hello1o_accepted2) hst
    (fun _ _ hc => by rw [hello1_okPcA]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    rfl rfl (by rw [hsp.1]) (fun _ _ hb => by cases hb)
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

/-- **`MainPreUA`'s `PrintCallCH` conjunct at `hello1o`** (`printCallCH_instAI`
at the record's instance `instOk_ofPlaceOK` at `imms2Me Λx P1`, `main`'s code
`fnCode2OfPMe`, the region `RC`): at every callee frame of `main`'s call,
every return address and `G0` along which the controls are `FrOk2`. -/
theorem hello1_printCallCHA {Dt : State → Prop} (J : InvS) (L D : Int) (v : BitVec 64) (F' : MachineData → Prop)
    (hok : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hst : FStable (RC) F')
    (hD : ((FC).cx.frame : Int) + 48 ≤ D) (hD8 : D % 8 = 0)
    (hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m) (g : WcG)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 [])
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ab' : FragS isaLSE2}
    (hAb : ∀ c0 x is a e c1 s c, G0 c0 → TailAt2 P1A 1 (.let_ x (.call "print" is a []) e) →
      At (LY).exe (LY).endPc (RC) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx (fun _ => none) (imms2Me LeA P1A) x e c1)
        s c → Ab' s c [printFrame x e c1]) :
    PrintCallCH P1A (fun _ => none) (fun _ => 0) (FC).lcx (FC).cx (CD g) ((FC).Bl g.ra) (LY).exe (LY).endPc
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
  simp only [MSAt, hab]
  exact printCallCH_instAI (Spike.Lib.A64.PhRec.instOk_ofPlaceOK h (imms2Me LeA P1A) (rS := rS0 (Ly)))
    (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h)
    (Spike.Lib.A64.StubW.printPhOk_of_tailPhOk (Spike.Lib.A64.Rt.tailPhOk_ofPlaceOK h _))
    (FC).hf (FC).h1 (FC).h16 hok hal (by rw [e1]; omega) (by rw [e2]; exact Int.le_refl _)
    (by rw [e1]; omega) (by rw [e2]; rfl)
    (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly)))
    hFO (progNoS_zbad_of_accepted2 hello1o_accepted2) hst
    (fun _ _ hc => by rw [hello1_okPcA]; exact CdCLE.toCdCL hc)
    (fun _ _ _ hb => ⟨(hBl0 _ _ _ hb).1.1, BlC2L.posOff (hBl0 _ _ _ hb)⟩)
    hsp.2.2.1 (fun _ _ hb => (hBl0 _ _ _ hb).1)
    rfl rfl (by rw [hsp.1]) (fun _ _ hb => by cases hb)
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

/-- info: 'Spike.Lib.LowerA64.hello1_okPcA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_okPcA

/-- info: 'Spike.Lib.LowerA64.hello1_imms_leA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_imms_leA

/-- info: 'Spike.Lib.LowerA64.hello1_imms_retA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_imms_retA

/-- info: 'Spike.Lib.LowerA64.hello1_printCallCA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_printCallCA

/-- info: 'Spike.Lib.LowerA64.hello1_printCallCHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_printCallCHA
