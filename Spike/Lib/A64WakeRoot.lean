/-
**wake.w's AArch64 root** (`CorrectE 2`): `WakeFinalCAW.wake_finalCA_genW` at
the root's choices, with `h1` assembled.

- `inv1R`: `h1`'s invariant per entry, `WakeH1Inv.inv1W` at the dummy heap
  word `WakeHG.cTW` and the write tail `DtW`.
- `msBot`, `inv0R`, `StartP`: `h0`'s memory side with `I2`'s `inv0`
  disjunct `⊥`, `h0`'s invariant the greatest closed invariant inside `W0W`
  there (`A64GfpS.GfpS`), and the start pair.
- `RootOpen`: the open premises given `h1`'s statement (`H1Stmt` at
  `inv1R`, from `WakeH1Root.wake_h1`): the start's segment `hst0` (with no
  exit), `OpenW`'s `hctr0`, `hnew0` at `inv0R`. `OpenW.h0` comes from
  `GfpS` lifted to `I2 inv0R` (`A64GfpS.segInvS_mono_xa`), `hst` from
  `gfpS_of_segWS hst0`.
  `hpost`/`hCl` are derived: `OPrem` from the other fields
  (`WakeOPremI.oPrem_WI`), then `WakeHClW.hpost_W`/`hCl_W` (the clone's
  states of `inv1W` in `CloneInv`, `h0`'s never at the clone).
- `wake_root`: `CorrectE 2` from the loader's facts, `wake_h1`'s premises
  per entry (`hG`, `hobl`; `hokb` by `hokb_R` at `ms0 := msBot E (fs0 E)`),
  and `RootOpen` per entry.
  `OpenW.h1`/`h1t`/`h1o` come from `WakeH1Inv.h1_of`/`h1Take_of`/
  `h1TakeOwn_of`. `hsub1` comes from `StartPlaceLy.hsub1_W`, and
  `hcT`/`hr0`/`hr1` are `rfl`.
- `wake_rootP`: the same at the certificate's output, `hpa`/`hwp`/`hd`
  from the single loader check `hP`, `hc` by `WakeFinalCAO.ctrZ_cert`; `hB`
  stays a premise (non-vacuous: the `example` after it).
-/
import Spike.Lib.WakeFinalCAW
import Spike.Lib.A64WakeH1Root
import Spike.Lib.A64WakeHClW

namespace Spike.Lib.WakeRoot

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeSpawnR
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.WakeOPremW (W0W W1W)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeFinalCAW (DW OpenW)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2)
  (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- **`h1`'s invariant at entry `E`**: `inv1W` at the dummy heap word and `DtW`. -/
abbrev inv1R (E : Entry) : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2 :=
  WakeH1Inv.inv1W hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)

/-- **`h1`'s statement at entry `E`** (`wake_h1`'s conclusion) at the box
landing at `h0`'s memory side `ms0` and frame condition `F0`. -/
abbrev H1R (ms0 : MemSide isaLSE2) (F0 : MachineData → Prop) (E : Entry) : Prop :=
  Spike.Lib.A64.Flow.WakeWc.H1Stmt (W1W hp i E DtW (Ctx E) (ls0 E)) (WakeH1Inv.K1W hp i E) (WakeOD.arW hp i)
    (L0T (Ly).Λ) (WakeH1Inv.ms1W hp i E (WakeHG.cTW hp i) (ls0 E)) (Ly) (WakeSpawnR.endR hp i)
    (Spike.Lib.A64.Flow.WakeWc.Box (Ly) ms0 F0)
    (inv1R hp i ls0 Ctx E)

/-- **`h0`'s memory side at entry `E` with no pre-allocation fragment**:
`msOfA` at `wakeD`'s `rd`, `G`, `own`, `ar`, the start's placement, with
`I2`'s `inv0` disjunct `⊥` (an allocation only reaches `inv1R`). -/
abbrev msBot (E : Entry) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  msOfA (Ly).Λ ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
    (WakeOG.gW hp i (WakeHG.cTW hp i))
    (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (WakeOD.arW hp i)
    (I2 (WakeOD.arW hp i) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) (fun _ _ _ => False)
      (inv1R hp i ls0 Ctx E)) (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) fs

/-- **`h0`'s invariant at entry `E`**: the greatest closed invariant inside
`W0W` under the take move at `msBot` (`A64GfpS.GfpS`). -/
abbrev inv0R (E : Entry) : FragS isaLSE2 :=
  A64GfpS.GfpS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (TakeCKS (WakeOSide.aW hp i E) (WakeOD.ClW hp i)) wakeSrc
    (L0T (Ly).Λ) (msBot hp i ls0 Ctx E)

/-- **The start pair**: the loaded thread with `wakeTh0`'s control. -/
def StartP (E : Entry) : FragS isaLSE2 := fun s c fs =>
  s = threadAt E (Ly).Λ.code.lo o.prog (loadSyms (Ly).Λ o.secs.rodata) ∧
    c = ⟨Spike.Lib.WakePreAsm.wakeTh0.term, Spike.Lib.WakePreAsm.wakeTh0.env, none⟩ ∧
    fs = Spike.Lib.WakePreAsm.wakeTh0.stack

set_option hygiene false in
/-- `DW` at the root's choices. -/
local notation "DE" => DW hp i (fun _ => WakeHG.cTW hp i) ls0 Ctx frM (inv0R hp i ls0 Ctx frM) (inv1R hp i ls0 Ctx) E

set_option hygiene false in
/-- The entry's marks. -/
local notation "μE" => (target (kernel 2) E).marks SccCertificate.asm (Ly).Λ

set_option hygiene false in
/-- The pre-spawn relation at `DW`. -/
local notation "R1W" => fun E d s =>
  WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ)
    (DW hp i (fun _ => WakeHG.cTW hp i) ls0 Ctx frM (inv0R hp i ls0 Ctx frM) (inv1R hp i ls0 Ctx) E) d s
  ∧ VPriv (Ly).Λ E d

set_option hygiene false in
/-- `I2` at `DE`. -/
local notation "I2E" => I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1

set_option hygiene false in
/-- `h0`'s memory side at `DE`. -/
local notation "ms0E" => msOfA (Ly).Λ μE (DE).rd (DE).G (DE).own (DE).ar I2E (DE).L0 (DE).ls0

/-- **The root's open premises at entry `E`**: `OpenW`'s fields except
`h1`, `h1t`, `h1o`, each at `OpenW`'s type with `inv1 := inv1R`. -/
structure RootOpen (E : Entry) : Prop where
  /-- `hst0`: the start's segment, from the start pair, inside `W0W` under
  the take move at `msBot`, with no exit (its allocation lands in `inv1R`). -/
  hst0 : SegWS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (TakeCKS (WakeOSide.aW hp i E) (WakeOD.ClW hp i))
    wakeSrc (L0T (Ly).Λ) (msBot hp i ls0 Ctx E) (StartP hp i E) (fun _ _ _ => False)
  /-- `hctr0`: the counter row at `Ctx`'s states. -/
  hctr0 : ∀ s c fs, inv0R hp i ls0 Ctx frM E s c fs → Ctx E s c fs → WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    CtrRow (ms0E fs') (fun s' c'' => PendA wakeSrc I2E (DE).L0 (DE).ls0 s' c'' fs') s c'
  /-- `hnew0`: the box's initialising store. -/
  hnew0 : ∀ s c fs, inv0R hp i ls0 Ctx frM E s c fs → Ctx E s c fs → ¬ WrAt s (DE).ar.ctrLoc →
    ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → abi.atSys s = false →
    ∀ L, WrAt s L → ¬ ArenaW (DE).ar (DE).L0 (DE).ls0 c' L → NewStM wakeSrc (DE).L0 (ms0E fs') s c'

/-- **`wake_h1`'s `hokb` at an `h0` memory side of `msOfA` shape**: the box
call's premises carry from `msOfA` at `wakeD`'s `rd`, `G`, `own`, `ar`, at
the start's placement `L0T`/`ls0T` (any fragment `I`, any frames `fs`) to
`ms1W` (`WakeBoxW.okb_ms1`; `arW.OK` by `WakeOD.hok_W` from `CtrZ`).
`h0`'s own memory side (`OpenW.h0`'s, at `I2`) is of this shape. -/
theorem hokb_R (hc : Spike.Lib.A64.Rt.CtrZ o) (E : Entry) (I : InvS) (fs : List TermRun.Frame) :
    ∀ l b n, L0T (Ly).Λ l = none → AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.A64.Alloc.Call,
        q.OKB (msOfA (Ly).Λ ((target (kernel 2) E).marks SccCertificate.asm (Ly).Λ) (fun _ => True)
          (WakeOG.gW hp i (WakeHG.cTW hp i))
          (fun s _ => Spike.Lib.A64.WakePh.ownG (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s)
          (WakeOD.arW hp i) I (L0T (Ly).Λ) (Spike.Lib.WakeLoadT.ls0T (ls0 E)) fs) (Ly).lab →
        q.OKB (WakeH1Inv.ms1W hp i E (WakeHG.cTW hp i) (ls0 E) l b n []) (Ly).lab :=
  fun _ _ _ hl hb _ h => WakeBoxW.okb_ms1
    (WakeOD.hok_W hp i E (WakeHG.cTW hp i) DtW (ls0 E) (fun _ _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc)
    (WakeOD.arW_newOk hp i) hl hb h

/-- **wake.w's AArch64 root**: `CorrectE 2` from the loader's facts, at
each admissible entry `wake_h1`'s premises and the remaining `RootOpen`
(given `h1`'s statement), at `h0`'s memory side `msBot E (fs0 E)` and frame
condition `F0`. -/
theorem wake_root {arch : WeakMem.Arch} {B : Budget}
    (fs0 : Entry → List TermRun.Frame) (F0 : Entry → MachineData → Prop)
    /- the loader's parses of the certificate -/
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hd : dataSections SccCertificate.asm = some o.secs)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe) (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hnz : WakeOInit.NtZ Λ0 o = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- `wake_h1`'s premises per entry -/
    (hG : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, WakeHMid.BoxPure (Ly) (F0 E) n R F J0 t →
        WakeH1Root.H1G hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n R F J0 t)
    (hobl : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n)
    /- the rest of `OpenW`, given `h1`'s statement -/
    (hRO : ∀ E : Entry, E.Ok (Ly).Λ → H1R hp i ls0 Ctx (msBot hp i ls0 Ctx E (fs0 E)) (F0 E) E →
      RootOpen hp i ls0 Ctx frM E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm :=
  WakeFinalCAW.wake_finalCA_genW hp i (fun _ => WakeHG.cTW hp i) ls0 Ctx frM (inv0R hp i ls0 Ctx frM)
    (inv1R hp i ls0 Ctx)
    (r0 := fun _ => WakeOSide.r0W hp i) (r1 := fun _ => WakeOSide.r1W hp i)
    hpa hwp hd hlo hstat hpin2 hinit2 hwide (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13) hc hnz hB
    (fun E hE =>
      have h1 : H1R hp i ls0 Ctx (msBot hp i ls0 Ctx E (fs0 E)) (F0 E) E :=
        WakeH1Root.wake_h1 hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) hpa hwp hlo hA13 hpin2 hc
          (hokb_R hp i ls0 hc E _ (fs0 E)) ⟨rfl, rfl, rfl, rfl⟩ (hG E hE) (hobl E hE)
      have hR := hRO E hE h1
      have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13
      have h0 : SegInvS (W0W hp i E DtW (Ctx E) (ls0 E) (frM E))
          (TakeCKS (WakeOSide.aW hp i E) (WakeOD.ClW hp i)) wakeSrc (L0T (Ly).Λ) ms0E (inv0R hp i ls0 Ctx frM E) :=
        A64GfpS.segInvS_mono_xa A64GfpS.segInvS_gfpS (fun fs => A64GfpS.msOfA_with_xa fs) fun fs _ _ _ _ _ h =>
          A64GfpS.msOfA_xa_mono (fun _ _ _ _ _ hI => hI.elim (fun hF => hF.2.2.elim) .inr) fs h
      have hst := A64GfpS.gfpS_of_segWS hR.hst0 _ _ _ ⟨rfl, rfl, rfl⟩
      have hO := WakeOPremI.oPrem_WI hp i arch E (WakeHG.cTW hp i) (ls0 E) (Ctx E) (frM E) (inv0R hp i ls0 Ctx frM E)
        (inv1R hp i ls0 Ctx E) hpa hwp hd hlo hstat hpin2 hsub1 hc hnz hE.1 hB
        (WakeH1Inv.h1_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
          (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0R hp i ls0 Ctx frM E))
        h0 (WakeH1Inv.h1Take_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E))
        (WakeH1Inv.h1TakeOwn_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)) hst hR.hctr0 hR.hnew0
      { h1 := WakeH1Inv.h1_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
          (W0W hp i E DtW (Ctx E) (ls0 E) (frM E)) (inv0R hp i ls0 Ctx frM E)
        h0 := h0
        h1t := WakeH1Inv.h1Take_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
        h1o := WakeH1Inv.h1TakeOwn_of hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)
        hst := hst
        hctr0 := hR.hctr0
        hnew0 := hR.hnew0
        hpost := WakeHClW.hpost_W hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) (frM E) (inv0R hp i ls0 Ctx frM E)
          (fun _ _ h => h.1) hO
        hCl := WakeHClW.hCl_W hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) (frM E) (inv0R hp i ls0 Ctx frM E)
          (fun _ _ h => h.1) hO hsub1 })
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- **`wake_root` at the certificate's output** `o := outLit`, its three
parses from the single loader check `hP` (`WakeSpawnRP.parsed_outLit`, as
`WakeFinalCAW.wake_finalCA_genWP`). -/
theorem wake_rootP (hp : PlaceW pcfg Λ0 SccCertificate.outLit) {arch : WeakMem.Arch} {B : Budget}
    (fs0 : Entry → List TermRun.Frame) (F0 : Entry → MachineData → Prop)
    /- the loader's check of the certificate (the trust boundary) -/
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    /- instance facts -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hnz : WakeOInit.NtZ Λ0 SccCertificate.outLit = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- `wake_h1`'s premises per entry -/
    (hG : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ R F J0 t, WakeHMid.BoxPure (Ly) (F0 E) n R F J0 t →
        WakeH1Root.H1G hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n R F J0 t)
    (hobl : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      WakeRefSeg.RefObl hp i E (WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) l b n)
    /- the rest of `OpenW`, given `h1`'s statement -/
    (hRO : ∀ E : Entry, E.Ok (Ly).Λ → H1R hp i ls0 Ctx (msBot hp i ls0 Ctx E (fs0 E)) (F0 E) E →
      RootOpen hp i ls0 Ctx frM E) :
    CorrectE 2 (wakeS arch) (Ly).Λ B SccCertificate.asm :=
  wake_root hp i ls0 Ctx frM fs0 F0 (WakeSpawnRP.parsed_outLit hP).1 (WakeSpawnRP.parsed_outLit hP).2.1
    (WakeSpawnRP.parsed_outLit hP).2.2 hlo hstat hA13 hpin2 hinit2 hwide WakeFinalCAO.ctrZ_cert hnz hB hG hobl hRO

/-- **`hB` is satisfiable**: a budget with `allocCells` cells meets it. -/
example (B : Budget) : ({ B with cells := Scc.Cert.PlaceOK.allocCells } : Budget).cells =
    Scc.Cert.PlaceOK.allocCells := rfl


end Spike.Lib.WakeRoot

/-- info: 'Spike.Lib.WakeRoot.wake_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRoot.wake_root

/-- info: 'Spike.Lib.WakeRoot.wake_rootP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRoot.wake_rootP

/-- info: 'Spike.Lib.WakeRoot.hokb_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeRoot.hokb_R
