/-
**`hello1`'s `main`: `MainPreUA` assembled** (AArch64): `MainPreUA`
(`Spike/Test/A64Hello1HU.lean`) at `hello1o` at the first stack's top, at
every choice of the bounds (`Bounds2A`), from `print`'s call segments
(`hello1_printCallCA`, `hello1_printCallCHA`,
`Spike/Test/A64Hello1Print.lean`) and one premise still open: `main`'s
blocks inside `W2` (`MainBlkA`, `CxBlk2`).

Discharged here: `main`'s frame below the bounds' depth (`hD`, from the
bounds' `main` row and `fnCode2OfPMe_spec2`), the region's alignment
(`hD8`), the words of the first stack off the callee region (`hFO`, by
`stackOff_callee` from the switch region's frame condition and the caller
cells), the ghosts' `FrOk2` (`FrOk2.runM` from the entry control's). The
aborts' fragment is closed: no state is at `main`'s overflow label (its
body has no addition), and an abort of `print` landing with `main`'s slots
(`printNAS`) never ends (`printAb_segP`).

`main`'s blocks follow from `cxBlk2_mainA` given the check of its blocks'
branch targets (`MainTgA`).

- `MainBlkA`: `main`'s blocks inside `W2`, at every callee frame of `main`'s call;
- `hello1_mainPreUA`: `MainPreUA` from it, at a choice of the bounds;
- `MainTgA`, `hello1_mainBlkA`, `hello1_mainPreUAT`: `MainBlkA` and `MainPreUA` from the targets' check.
-/
import Spike.Test.A64Hello1Print
import Spike.Lib.LowerA64.PrintAbP

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
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me LeA P1A) P1A Spike.Lib.LowerNode.IsNum J (ab2 P1A (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The setup code's record. -/
local notation "SC" => setupMC (setupWords2 P1A)

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hello1o_accepted2 h LeA 1 MD hello1_main_compiled2

set_option hygiene false in
/-- `main`'s callee region at the first stack's top. -/
local notation "RC" => (swR (TOP) (-L) 0).callee (-(SC).Z.toInt) (-D) 0

set_option hygiene false in
/-- The ghosts: the controls a frame run reaches from `cP`. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM P1A (cP, []) (c, [])

/-- **`main`'s blocks inside `W2` at its callee frames** (open; `CxBlk2`). -/
def MainBlkA (Dt : State → Prop) (J : InvS) (L D : Int) : Prop :=
  ∀ F' : MachineData → Prop, (RC).OK → (RC).base.toNat % 16 = 0 → FStable (RC) F' →
    (∀ m, F' m → (FS (TOP)) m ∧ CallerCells (swR (TOP) (-L) 0) (-(SC).Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ((Ly).lab (SC).sp1).toBitVec → g.tp = TP0 → ∀ cP : Ctl, FrOk2 cP [] →
      CxBlk2 (W2S J) (KT) P1A (fun _ => none) (fun _ => 0) (FC) (RC) F' [] g.fp g.ra (GM cP)

/-- **`MainPreUA` at `hello1o`** at the first stack's top, at a choice of
the bounds (`hB`): `main`'s blocks given (`HB`), the write tails at
`print`'s and the write abort's system calls (`hDtP`, `hDtW`, trivial at
`Dt := fun _ => True`); `print`'s segments by `hello1_printCallCA`,
`hello1_printCallCHA`; the aborts' fragment: the overflow label's states
(none: `main`'s walk has no addition) and `print`'s aborts landing at
`printNAS` (`printAb_segP`, `main`'s continuation `ret 0`). -/
theorem hello1_mainPreUA {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A SccCertificate.config P1A (Ly) L D1 D lS lM fS nS fM nM) (J : InvS)
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (HB : MainBlkA h Dt J L D) :
    MainPreUA h hello1o_accepted2 hello1_main_compiled2 Dt J L D (TOP) := by
  obtain ⟨-, -, -, -, -, -, hnD, hnD2, -, hrowM, hL0, hLm, hL8, -, -, -, hD8, -, hL2, -⟩ := id hB
  obtain ⟨-, -, -, -, hrM, hfn, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id hB
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hello1o_accepted2 h LeA 1 MD hello1_main_compiled2
  have hframe : (FC).cx.frame = fM := by
    rw [hcx]; exact hrowM _ _ hmem rfl rfl
  have hD : ((FC).cx.frame : Int) + 48 ≤ D := by rw [hframe]; omega
  have hs : (Scc.Lower.setupOf P1A).isSome = true := by rw [hello1_htyA.choose_spec]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hello1o_accepted2 hs)
    (rtCodeOkS_setupWords2A h hello1o_accepted2 hs)).1
  have hZ := setupMC_Z _ hsw
  intro F' hok hal hst hFF g hra htp cP hcP
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m := by
    intro m hm
    obtain ⟨⟨-, hoff⟩, hcc⟩ := hFF m hm
    have hok' : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok' h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hG0F : ∀ c0, (GM cP) c0 → FrOk2 c0 [] := fun _ hc =>
    FrOk2.runM (progNoS_zbad_of_accepted2 hello1o_accepted2) hc hcP
  have hab2 : ab2 P1A (Ly).lab = some (Spike.Lib.A64.WriteAb.Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1A = true from by decide, ↓reduceIte]
  -- the aborts: the overflow label's states, `print`'s aborts landing with `main`'s slots
  refine ⟨fun s c fs => (∃ c0, (GM cP) c0 ∧ (At (LY).exe (LY).endPc (RC) F'
      (abortN2 (imms2Me LeA P1A) (TailAt2 P1A 1) P1A (fun _ => none) (FC).cx
        (_root_.Executable.labels (LY).exe).label g.fp g.ra c0)).at [] s c fs) ∨
    ∃ x is a e c1, TailAt2 P1A 1 (.let_ x (.call "print" is a []) e) ∧
      (At (LY).exe (LY).endPc (RC) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx (fun _ => none) (imms2Me LeA P1A) x e
          c1)).at [printFrame x e c1] s c fs,
    fun c0 hc s c' h => .inl ⟨c0, hc, h, rfl⟩, HB F' hok hal hst hFF g hra htp cP hcP,
    hello1_printCallCA h J L D (TOP) F' hok hal hst hD hD8 hFO g hG0F hDtP
      fun _ x is a e c1 s c _ hT h => .inr ⟨x, is, a, e, c1, hT, h, rfl⟩,
    hello1_printCallCHA h J L D (TOP) F' hok hal hst hD hD8 hFO g hG0F hDtP
      fun _ x is a e c1 s c _ hT h => .inr ⟨x, is, a, e, c1, hT, h, rfl⟩, ?_⟩
  simp only [MSAt, hab2]
  refine SegWS.or_pre ?_ ?_
  · -- no state at the overflow label: `main`'s walk has no addition
    refine SegWS.empty ?_
    rintro s c fs ⟨c0, -, ⟨-, -, -, -, σ, -, -, ⟨⟨⟨sv, lits, hAb, -, -, -, hTc⟩, -⟩, -⟩⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    rw [he] at hTc
    rcases hello1_main_tails (hTc _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
  · refine (SegWS.exists_pre (P := fun q : String × List String × CoreTerm.At × Expr × Ctl => fun s c fs =>
      TailAt2 P1A 1 (.let_ q.1 (.call "print" q.2.1 q.2.2.1 []) q.2.2.2.1) ∧
        (At (LY).exe (LY).endPc (RC) F'
          (printNAS (_root_.Executable.labels (LY).exe).label (FC).cx (fun _ => none) (imms2Me LeA P1A)
            q.1 q.2.2.2.1 q.2.2.2.2)).at [printFrame q.1 q.2.2.2.1 q.2.2.2.2] s c fs)
      fun ⟨x, is, a, e, c1⟩ => ?_).mono_pre
      fun s c fs ⟨x, is, a, e, c1, hT, hA⟩ => ⟨⟨x, is, a, e, c1⟩, hT, hA⟩
    by_cases hT : TailAt2 P1A 1 (.let_ x (.call "print" is a []) e)
    case neg => exact SegWS.empty fun _ _ _ h => hT h.1
    have he : e = .ret (.lit 0) := by
      rcases hello1_main_tails (hT _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h' <;> rfl
    subst he
    refine (printAb_segP h (imms2Me LeA P1A) (it := imms2Me LeA P1A) (e := .ret (.lit 0)) (FC).hf
      (FC).h16 hok hal (by show -D ≤ _; omega) (by show (0 : Int) ≤ 0; decide)
      (by show (-D) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; decide) hst
      (Spike.Lib.A64.Rt.rS0_sub (Ly)) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub (Ly))) hFO
      (progNoS_zbad_of_accepted2 hello1o_accepted2) rfl trivial (by simp)
      (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) (fun _ h => h) rfl hDtW _).mono_pre
      fun _ _ _ h => h.2

/-- **Every label a `Kind2` block of `main`'s code at the setup call's
return point branches or calls to is off the write abort** (`cxBlk2_ofFn`'s
`hTg` at `main`; open: a check over the output's user runs). -/
def MainTgA : Prop :=
  ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY) (Spike.Lib.A64.PhRec.ph LY) (LY).lab
      (Int64.ofBitVec ((Ly).lab (SC).sp1).toBitVec)) pc blk →
    Kind2 (FC).cx blk → ∀ k (hk : k < blk.length) L,
      (classify blk[k] = some (.b L) ∨ classify blk[k] = some (.bl L) ∨
        (∃ cc, classify blk[k] = some (.bcond cc L)) ∨ (∃ t, classify blk[k] = some (.cbz t L)) ∨
        ∃ t, classify blk[k] = some (.cbnz t L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **`MainBlkA` at `hello1o`** at a choice of the bounds (`hB`) and the
targets' check (`hTg`): `cxBlk2_mainA` in the callee region (the words of
the first stack off it as `hello1_mainPreUA`'s), the ghosts' `FrOk2`
(`FrOk2.runM`), the return point `scc_rt_main`'s off the write abort
(`posOff_mainRetS`). -/
theorem hello1_mainBlkA {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A SccCertificate.config P1A (Ly) L D1 D lS lM fS nS fM nM) (J : InvS) (hTg : MainTgA h) :
    MainBlkA h Dt J L D := by
  obtain ⟨-, -, -, -, -, -, hnD, hnD2, -, hrowM, hL0, hLm, hL8, -, -, -, hD8, -, hL2, -⟩ := id hB
  obtain ⟨-, -, -, -, hrM, hfn, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := id hB
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hello1o_accepted2 h LeA 1 MD hello1_main_compiled2
  have hframe : (FC).cx.frame = fM := by
    rw [hcx]; exact hrowM _ _ hmem rfl rfl
  have hD : ((FC).cx.frame : Int) + 48 ≤ D := by rw [hframe]; omega
  have hs : (Scc.Lower.setupOf P1A).isSome = true := by rw [hello1_htyA.choose_spec]; rfl
  have hc := rtCodeOkS_setupWords2A h hello1o_accepted2 hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hello1o_accepted2 hs) hc).1
  have hZ := setupMC_Z _ hsw
  have hpN := progNoS_zbad_of_accepted2 hello1o_accepted2
  intro F' hok hal hst hFF g hra htp cP hcP
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m := by
    intro m hm
    obtain ⟨⟨-, hoff⟩, hcc⟩ := hFF m hm
    have hok' : (swR (TOP) (-L) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok' h8 (by show (-L) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  exact cxBlk2_mainA h hello1o_accepted2 hello1_main_compiled2 J hst hok hal (by show -D ≤ _; omega)
    (by show (0 : Int) ≤ 0; decide) (by show (-D) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; decide) hFO
    (fun _ hc' => FrOk2.runM hpN hc' hcP)
    (by rw [hra, Int64.ofBitVec_toBitVec]; exact posOff_mainRetS (Spike.Lib.A64.Rt.mainSIn_of_okS hc))
    (by rw [hra]; exact hTg)

/-- **`MainPreUA` at `hello1o` from the targets' check** (`hello1_mainPreUA`
at `hello1_mainBlkA`). -/
theorem hello1_mainPreUAT {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2A SccCertificate.config P1A (Ly) L D1 D lS lM fS nS fM nM) (J : InvS)
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At (LY).exe (LY).endPc R' F''
        (Spike.Lib.A64.Flow.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc σC .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hTg : MainTgA h) :
    MainPreUA h hello1o_accepted2 hello1_main_compiled2 Dt J L D (TOP) :=
  hello1_mainPreUA h hB J hDtP hDtW (hello1_mainBlkA h hB J hTg)

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_mainPreUA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainPreUA

/-- info: 'Spike.Lib.LowerA64.hello1_mainBlkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainBlkA

/-- info: 'Spike.Lib.LowerA64.hello1_mainPreUAT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_mainPreUAT
