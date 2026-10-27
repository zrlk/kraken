/-
**`hello1`'s `main` call at the start's frame condition `WordsNone`**
(x86-64): `HUBVF` (`Spike/Test/X64Hello1ClosedBVBF.lean`), `main`'s call
at the switch region's frame condition with `WordsNone`, closed at every
entry state, placement, landings' states and the write tail `fun _ => True`.

- `MainCallWSF.mono_F`: `MainCallWSF` at a stronger frame condition, the
  limit word unloaded under the weaker one (`uNM`'s `LimOk` reads the frame
  condition only for that word);
- `hello1_hUBVF`: `HUBVF` at `hello1o` from `mainCallWSF_ofVacHMV` at
  `hello1_mainPreUT` (`main`'s targets' check `hello1_mainTg`), moved to the
  `WordsNone` frame condition by `MainCallWSF.mono_F` (the switch region's
  `swF` has the limit word unloaded).
-/
import Spike.Test.X64Hello1ClosedBVBF
import Spike.Test.X64Hello1Reduce

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Ret0 (WcG LimOk limA CallerCells)
open Spike.Lib.X64.Rt (MainCallWSF uNM NxF)

/-- **`MainCallWSF` at a stronger frame condition** `F₁` (inside `F₂`), the
limit word `limA tp` unloaded under `F₂`: the callee's frame conditions
inside `F₁` are inside `F₂`, and the entry's `LimOk` at `F₁` is one at `F₂`
(its only read of the frame condition is that word). -/
theorem MainCallWSF.mono_F {W : FragS isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F₁ F₂ : MachineData → Prop}
    {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Pre : Ctl → Reg64s → Prop}
    {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop} {ra : BitVec 64} {tp : UInt64}
    (hF : ∀ m, F₁ m → F₂ m) (hU : ∀ m, F₂ m → Mem.loadInt m.dmem (limA tp) 8 = none)
    (h : MainCallWSF W K p lbl ms exe endPc R F₂ fn Z D ZU Pre Post ra tp) :
    MainCallWSF W K p lbl ms exe endPc R F₁ fn Z D ZU Pre Post ra tp := by
  intro F' hR hS hFF g hra htp
  refine (h F' hR hS (fun m hm => ⟨hF _ (hFF m hm).1, (hFF m hm).2⟩) g hra htp).mono_pre ?_
  rintro s c fs ⟨⟨he, hn, hdc, hpc, σ, hA, hF', hpre, hlim⟩, hfs⟩
  subst htp
  exact ⟨⟨he, hn, hdc, hpc, σ, hA, hF', hpre, ⟨hlim.rt, hlim.mp, hU, hlim.room⟩⟩, hfs⟩

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`hello1`'s `main` call at `WordsNone`** (`HUBVF`) at every placement,
entry state and landings' states, at the write tail `fun _ => True`:
`mainCallWSF_ofVacHMV` at `hello1_mainPreUT` (as `hello1_hUBV`), moved to the
frame condition with `WordsNone` (`MainCallWSF.mono_F`, the limit word
unloaded by the switch region's `swF`). -/
theorem hello1_hUBVF (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) :
    HUBVF h hello1_hty.choose E El (fun _ => True) := by
  intro L D1 D2 lS lM fS nS fM nM hB J _ v
  obtain ⟨-, -, -, -, -, -, -, -, -, hfD, -, hrowM, hL0, hLm, hL8, -, -, hD0, hD8, -, -, hL2, -⟩ := id hB
  have hcx : (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).lcx.externs = Scc.Frontend.externs P1 := by
    rw [(fnCode2OfPMe_spec Spike.Lib.LowerNode.hello1o_accepted2 h Le 1 Spike.Test.Hello1MainSrc.mainD
      Spike.Test.Hello1MainSrc.hello1_main_compiled2).1]
  have H := mainCallWSF_ofVacHMV h Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec
    Spike.Test.Hello1MainSrc.hello1_main_compiled2 Spike.Test.Hello1MainSrc.hello1_main_find
    rfl (by decide) (by rw [hello1_hty_eq]; rfl) (by rw [hello1_hty_eq]; decide) (by decide)
    (Spike.Test.Hello1MainSrc.hello1_main_noCallee hcx) Spike.Test.Hello1MainSrc.hello1_main_noXchg
    Spike.Test.Hello1MainSrc.hello1_main_noNewBuf hrowM J hfD hL0 hLm hL8 hD0 hD8 hL2 v
    (hello1_mainPreUT h hB J (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (hello1_mainTg h))
  exact MainCallWSF.mono_F (fun m hm => ⟨hm.1.2, hm.2⟩) (fun m hm => hm.1.1.2) H

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.MainCallWSF.mono_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.MainCallWSF.mono_F

/-- info: 'Spike.Lib.LowerX64.hello1_hUBVF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hUBVF
