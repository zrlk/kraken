/-
**`hello1`'s `main` callee entry** (x86-64; the twin of
`Spike/Test/A64Hello1Main.lean`): `MainPreU` at `hello1o`'s `main`
(compiled block `1`) at the first stack's top, from `print`'s call segments
`hello1_printCallC`, `hello1_printCallCH` (`Spike/Test/X64Hello1Print.lean`)
at the callee region's facts: its room (`hD`, from the bounds' `main` row and
`fnCode2OfPMe_spec2`), alignment (`hD8`; `hal` from the first stack's top and
the setup record's `Z`, both multiples of `16`), the words of the first
stack off it (`hFO`, `stackOff_callee` twice from the switch region's frame
condition and the caller cells), the ghosts' `FrOk2` (`FrOk2.runM` from the
entry control's) and the write tails (`hDtP`, `hDtW`). The aborts' fragment
is closed: no state is at `main`'s overflow label (its body has no
addition), and an abort of `print` landing with `main`'s slots
(`printNAS`) never ends (`printAb_segP`).

- `MainBlk`: the open premise, at every callee frame of `main`'s call;
- `hello1_mainPreU`: `MainPreU` from them, at a choice of the bounds;
- `MainTg`, `hello1_mainBlk`: `MainBlk` by `cxBlk2_ofFn` at `main`'s code in
  the rebased callee region, from the targets' check `MainTg`;
- `hello1_mainPreUT`: `MainPreU` with `MainTg` its only open premise.
-/
import Spike.Test.X64Hello1Print
import Spike.Lib.LowerX64.PrintAbP

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
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Le P1) P1 Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Le P1) P1 Spike.Lib.LowerNode.IsNum J (ab2 P1 (Ly).lab) (fun _ => 0)

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

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM P1 (cP, []) (c, [])

/-- **`main`'s blocks inside `W2` at its callee frames** (open; `CxBlk2`). -/
def MainBlk (Dt : State → Prop) (J : InvS) (L D : Int) (v : BitVec 64) : Prop :=
  ∀ F' : MachineData → Prop, (RC).OK → FStable (RC) F' →
    (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (SC).Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ((Ly).lab (SC).sp1).toBitVec → g.tp = TP0 → (RC).base = g.sp →
    ∀ cP : Ctl, FrOk2 cP [] →
      CxBlk2 (W2S J) (KT) P1 (fun _ => none) (fun _ => 0) (FC) (rbR (RC)) F' [] g.fp g.ra (GM cP)

set_option hygiene false in
/-- `main`'s callee region at the first stack's top. -/
local notation "RT" => (RS (TOP)).callee (-8 - (SC).Z.toInt - 8 - 0) (-D) 8

/-- **`MainPreU` at `hello1o`** at the first stack's top, at a choice of
the bounds (`hB`): `main`'s blocks given (`HB`), the write tails at
`print`'s and the write abort's system calls (`hDtP`, `hDtW`, trivial at
`Dt := fun _ => True`); `print`'s segments by `hello1_printCallC`,
`hello1_printCallCH`; the aborts' fragment: the overflow label's states
(none: `main`'s walk has no addition) and `print`'s aborts landing at
`printNAS` (`printAb_segP`, `main`'s continuation `ret 0`). -/
theorem hello1_mainPreU {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs (Ly) L D1 D lS lM
      fS nS fM nM) (J : InvS)
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (LY).exe (LY).endPc R' F''
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc ko σC .sys) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Abort.N (Ly).lab Abort.write c .sys) s c' → Dt s)
    (HB : MainBlk h Dt J L D (TOP)) :
    MainPreU h hello1o_accepted2 hello1_main_compiled2 Dt J L D (TOP) := by
  obtain ⟨-, -, -, -, -, -, hnM, -, hnD, -, -, hrowM, hL0, hLm, hL8, -, -, hD0, hD8, -, -, hL2, -⟩ := id hB
  obtain ⟨w, -, -, hmem, hfr⟩ := fnCode2OfPMe_spec2 hello1o_accepted2 h Le 1 MD hello1_main_compiled2
  have hframe : (FC).fr.size = fM := by
    rw [hfr]; exact hrowM _ hmem rfl rfl
  have hD : ((FC).fr.size : Int) + 64 ≤ D := by rw [hframe]; omega
  have hs : (Scc.Lower.setupOf P1).isSome = true := by rw [hello1_hty.choose_spec]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hello1o_accepted2 hs)
    (rtCodeOkS_setupWords2 h hello1o_accepted2 hs)).1
  have hZ := setupMC_Z _ hsw
  intro F' hok' hst hFF g hra htp hb cP hcP
  -- the regions: the switch region, its callee `RS TOP`, `main`'s `RC`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have h16 : (TOP).toNat % 16 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_h16 (Ly)
  have htop8 : (TOP).toNat % 8 = 0 := by omega
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (SC).Z.toInt - 8 - 0)
    (lo' := -D) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hbr := Region.callee_base (hi' := (RT).hi + 8) (kc := -8) (lo' := (RT).lo + 8) hok'
    (by omega) (by show -D + 8 ≤ (0 : Int); omega) (by show (-8 : Int) < 8; decide)
  have hal : (rbR (RT)).base.toNat % 16 = 0 := by
    show ((RT).callee (-8) ((RT).lo + 8) ((RT).hi + 8)).base.toNat % 16 = 0
    omega
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RT) m := fun m hm =>
    Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
      (hFF m hm).2
  have hG0F : ∀ c0, (GM cP) c0 → FrOk2 c0 [] := fun _ hc =>
    FrOk2.runM (progNoS_zbad_of_accepted2 hello1o_accepted2) hc hcP
  have hab2 : ab2 P1 (Ly).lab = some (Spike.Lib.X64.WriteAb.Ab (Ly).lab) := by
    simp only [ab2, show Scc.Lower.hasPrint P1 = true from by decide, ↓reduceIte]
  have hrr : (rbR (RT)).OK := rbR_ok hok' (by show -D ≤ -8; omega) (by show (0 : Int) ≤ 8; decide)
  have hFOr : ∀ m, F' m → StackOff (rS0 (Ly)) (rbR (RT)) m := fun m hm =>
    stackOff_rbR hok' (by show -D ≤ -8; omega) (by show (0 : Int) ≤ 8; decide) (hFO m hm)
  -- the aborts: the overflow label's states, `print`'s aborts landing with `main`'s slots
  refine ⟨fun s c fs => (∃ c0, (GM cP) c0 ∧ (Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RT)) F'
      (abortN2 (imms2Me Le P1) (TailAt2 P1 1) P1 (fun _ => none) (FC).fr
        (_root_.Executable.labels (LY).exe).label g.fp g.ra c0)).at [] s c fs) ∨
    ∃ x is a e c1, TailAt2 P1 1 (.let_ x (.call "print" is a []) e) ∧
      (Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RT)) F'
        (printNAS (_root_.Executable.labels (LY).exe).label (FC).fr (fun _ => none) (imms2Me Le P1) x e
          c1)).at [printFrame x e c1] s c fs,
    fun c0 hc s c' h => .inl ⟨c0, hc, h, rfl⟩, HB F' hok' hst hFF g hra htp hb cP hcP,
    hello1_printCallC h J L D (TOP) F' hok' hst hD hD8 hal hFO g hG0F hDtP
      fun _ x is a e c1 s c _ hT h => .inr ⟨x, is, a, e, c1, hT, h, rfl⟩,
    hello1_printCallCH h J L D (TOP) F' hok' hst hD hD8 hal hFO g hG0F hDtP
      fun _ x is a e c1 s c _ hT h => .inr ⟨x, is, a, e, c1, hT, h, rfl⟩, ?_⟩
  simp only [MSAt, hab2]
  refine SegWS.or_pre ?_ ?_
  · -- no state at the overflow label: `main`'s walk has no addition
    refine SegWS.empty ?_
    rintro s c fs ⟨c0, -, ⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hTc⟩, -⟩, -⟩, -⟩
    obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
    rw [he] at hTc
    rcases hello1_main_tails (hTc _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h'
  · refine (SegWS.exists_pre (P := fun q : String × List String × CoreTerm.At × Expr × Ctl => fun s c fs =>
      TailAt2 P1 1 (.let_ q.1 (.call "print" q.2.1 q.2.2.1 []) q.2.2.2.1) ∧
        (Spike.Lib.X64.At (LY).exe (LY).endPc (rbR (RT)) F'
          (printNAS (_root_.Executable.labels (LY).exe).label (FC).fr (fun _ => none) (imms2Me Le P1)
            q.1 q.2.2.2.1 q.2.2.2.2)).at [printFrame q.1 q.2.2.2.1 q.2.2.2.2] s c fs)
      fun ⟨x, is, a, e, c1⟩ => ?_).mono_pre
      fun s c fs ⟨x, is, a, e, c1, hT, hA⟩ => ⟨⟨x, is, a, e, c1⟩, hT, hA⟩
    by_cases hT : TailAt2 P1 1 (.let_ x (.call "print" is a []) e)
    case neg => exact SegWS.empty fun _ _ _ h => hT h.1
    have he : e = .ret (.lit 0) := by
      rcases hello1_main_tails (hT _ hello1_main_compiled2) with h' | h' | h' | h' <;> cases h' <;> rfl
    subst he
    refine (printAb_segP h (imms2Me Le P1) (it := imms2Me Le P1) (e := .ret (.lit 0)) (FC).hf hrr
      (by omega) (by show -D + 8 ≤ _; omega)
      (by show (0 : Int) ≤ 16; decide) (by show (-D + 8) % 8 = 0; omega) (by show (16 : Int) % 8 = 0; decide)
      (rbR_fstable hok' (by show -D ≤ -8; omega) (by show (0 : Int) ≤ 8; decide) hst)
      (Spike.Lib.X64.Rt.rS0_sub (Ly)) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub (Ly))) hFOr
      (progNoS_zbad_of_accepted2 hello1o_accepted2) rfl trivial (by simp)
      (fun _ _ => ⟨fun _ => False, FramesPlacedInI.nil _⟩) (fun _ h => h) rfl hDtW _).mono_pre
      fun _ _ _ h => h.2

/-- **Every label a `Kind2` block of `main`'s code at the setup call's
return point jumps or calls to is off the write abort** (`cxBlk2_ofFn`'s
`hTg` at `main`; open: a check over the output's user runs). -/
def MainTg : Prop :=
  ∀ pc blk, SubCd (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY) (Spike.Lib.X64.PhRec.ph LY) (LY).lab
      (Int64.ofBitVec ((Ly).lab (SC).sp1).toBitVec)) pc blk →
    Kind2 (FC).fr blk → ∀ k (hk : k < blk.length) L,
      (Spike.Lib.X64.classify blk[k].1 = some (.jmp L) ∨ Spike.Lib.X64.classify blk[k].1 = some (.call L) ∨
        ∃ cc, Spike.Lib.X64.classify blk[k].1 = some (.jcc cc L)) → PosOff OP (Ly).lab ((Ly).lab L)

/-- **`MainBlk` at `hello1o`** at the first stack's top, at a choice of the
bounds (`hB`) and the targets' check (`hTg`): `cxBlk2_ofFn` at `main`'s
code (`fnCode2OfPMe`) in the rebased callee region (`cxBlk2_main`; `rbR_facts`,
`rbR_base`, `stackOff_rbR`, the region facts as `hello1_mainPreU`'s), no
frames below (`FramesPlacedInI.nil`), the ghosts' `FrOk2` (`FrOk2.runM`),
the return point `scc_rt_main`'s off the write abort (`posOff_mainRetS`). -/
theorem hello1_mainBlk {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs (Ly) L D1 D lS lM
      fS nS fM nM) (J : InvS) (hTg : MainTg h) :
    MainBlk h Dt J L D (TOP) := by
  obtain ⟨-, -, -, -, -, -, hnM, -, hnD, -, -, hrowM, hL0, hLm, hL8, -, -, hD0, hD8, -, -, hL2, -⟩ := id hB
  obtain ⟨w, -, -, hmem, hfr⟩ := fnCode2OfPMe_spec2 hello1o_accepted2 h Le 1 MD hello1_main_compiled2
  have hframe : (FC).fr.size = fM := by
    rw [hfr]; exact hrowM _ hmem rfl rfl
  have hD : ((FC).fr.size : Int) + 64 ≤ D := by rw [hframe]; omega
  have hs : (Scc.Lower.setupOf P1).isSome = true := by rw [hello1_hty.choose_spec]; rfl
  have hc := rtCodeOkS_setupWords2 h hello1o_accepted2 hs
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hello1o_accepted2 hs) hc).1
  have hZ := setupMC_Z _ hsw
  have hpN := progNoS_zbad_of_accepted2 hello1o_accepted2
  intro F' hok' hst hFF g hra htp hb cP hcP
  -- the regions: the switch region, its callee `RS TOP`, `main`'s `RT`
  have hok : (swR (TOP) (-L) 0).OK := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
  have htop8 : (TOP).toNat % 8 = 0 := by
    rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
  have hR1 : (RS (TOP)).OK :=
    Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      (by show _ ≤ (0 : Int); omega)
  have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
    Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
  have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (SC).Z.toInt - 8 - 0)
    (lo' := -D) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo0 : (RT).lo ≤ -8 - ((FC).fr.size : Int) := by show -D ≤ _; omega
  have hhi0 : (8 : Int) ≤ (RT).hi := by show (8 : Int) ≤ 8; exact Int.le_refl _
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RT) m := fun m hm =>
    Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
      (hFF m hm).2
  -- the body's blocks inside `W2` in the rebased region (`cxBlk2_ofFn`)
  obtain ⟨hF2, hR2, hlo2, hhi2⟩ := rbR_facts hst hok' hlo0 hhi0
  have hb2 := rbR_base hok' (by omega) (by omega)
  exact cxBlk2_main h hello1o_accepted2 hello1_main_compiled2 J hF2 hR2 (by omega) hlo2 hhi2
    (by show (-D + 8) % 8 = 0; omega) (by show ((8 : Int) + 8) % 8 = 0; decide)
    (fun m hm => stackOff_rbR hok' (by omega) (by omega) (hFO m hm)) (fun _ hc' => FrOk2.runM hpN hc' hcP)
    (by rw [hra, Int64.ofBitVec_toBitVec]; exact posOff_mainRetS (Spike.Lib.X64.Rt.mainSIn_of_okS hc))
    (by rw [hra]; exact hTg)

/-- **`MainPreU` at `hello1o` from the targets' check** (`hello1_mainPreU`
at `hello1_mainBlk`): at a choice of the bounds, the write tails and
`MainTg`. -/
theorem hello1_mainPreUT {Dt : State → Prop} {L D1 D : Int} {lS lM : String} {fS nS fM nM : Nat}
    (hB : Bounds2 SccCertificate.config P1 SccCertificate.sizes SccCertificate.labelOffs (Ly) L D1 D lS lM
      fS nS fM nM) (J : InvS)
    (hDtP : ∀ (R' : Region) (F'' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      Spike.Lib.X64.At (LY).exe (LY).endPc R' F''
        (Spike.Lib.X64.PrintCall.pN (_root_.Executable.labels (LY).exe).label Pc Qc ko σC .sys) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Abort.N (Ly).lab Abort.write c .sys) s c' → Dt s)
    (hTg : MainTg h) :
    MainPreU h hello1o_accepted2 hello1_main_compiled2 Dt J L D (TOP) :=
  hello1_mainPreU h hB J hDtP hDtW (hello1_mainBlk h hB J hTg)

end Hello1

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_mainPreU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_mainPreU

/-- info: 'Spike.Lib.LowerX64.hello1_mainBlk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_mainBlk

/-- info: 'Spike.Lib.LowerX64.hello1_mainPreUT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_mainPreUT
