/-
**wake.w's AArch64 root with `hst0` from `StartH0U.hst0_ofU`**:
`WakeRoot.wake_rootP` at the root's immediate table `IW`, `fs0 := []`,
`RootOpen.hst0` by `hst0_ofU`, its `h1` the `H1R` `wake_root` hands to `hRO`
(from `WakeH1Root.wake_h1`), its `hF0` from `F0 E ⊇ wF`.

- `wFU`: the union of `wc_main`'s frame conditions; `F0 := wFU` meets `hF0`.
- `wake_rootU`: the statement; `RootOpen`'s `hctr0`/`hnew0` and
  `hst0_ofU`'s `hctrD`, `hWp`/`hWs` (at `msU`) stay premises.
-/
import Spike.Lib.A64WakeStartH0U

namespace Spike.Lib.A64.WakePh.RootU

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib.Consumer1 Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W)
open Spike.Lib.A64.KeepTP (tpXa)
open Spike.Lib (FragS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib.HeapLand (AllocLand)

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 SccCertificate.outLit)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "MU" => Spike.Lib.A64.WakePh.StartH0U.msU hp ls0 Ctx E []

set_option hygiene false in
local notation "WSE" => Spike.Lib.A64.WakePh.StartWf.WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab)
  (Spike.Lib.WakeOD.arW hp IW) wakeSrc Spike.Lib.A64.WakeWf.DtW (Spike.Lib.WakeOD.ClW hp IW) (Ctx E) (L0T (Ly).Λ)
  (ls0T (ls0 E)) (frM E) (Spike.Lib.A64.WakeWf.X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
/-- The start's fragment needed only at main's thread pointer (`WakeWc.tpG`). -/
local notation "TGE" => Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSE)

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "DE" => WakeFinalCAW.DW hp IW (fun _ => WakeHG.cTW hp IW) ls0 Ctx frM (WakeRoot.inv0R hp IW ls0 Ctx frM)
  (WakeRoot.inv1R hp IW ls0 Ctx) E

set_option hygiene false in
local notation "I2E" => Spike.Lib.A64ConsumerA.I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1

set_option hygiene false in
local notation "ms0E" => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks SccCertificate.asm (Ly).Λ) (DE).rd (DE).G (DE).own (DE).ar
  I2E (DE).L0 (DE).ls0

/-- **`wc_main`'s frame conditions, joined**: `F0 := wFU` gives `hF0`. -/
def wFU : MachineData → Prop := fun m => ∃ v m0 σC, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m

set_option linter.unusedVariables false in
/-- **wake.w's root, `hst0` by `hst0_ofU`**: `wake_rootP` at `IW`, `fs0 := []`;
`hF0` from `hF0` (`F0 := wFU hp` meets it by `⟨v, m0, σC, h⟩`). -/
theorem wake_rootU {arch : WeakMem.Arch} {B : Budget} (F0 : Entry → MachineData → Prop)
    (hF0 : ∀ E v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m → F0 E m)
    (hP : Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ SccCertificate.outLit.prog SccCertificate.outLit.secs).initVal
      ⟨Spike.Lib.WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hwide : Scc.Cert.WideA64.ExeWide (Ly).exe)
    (hnz : WakeOInit.NtZ Λ0 SccCertificate.outLit = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hG : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp IW).heap (WakeOD.arW hp IW).cells b n →
      ∀ R F J0 t, WakeHMid.BoxPure (Ly) (F0 E) n R F J0 t →
        WakeH1Root.H1G hp IW E (WakeHG.cTW hp IW) Spike.Lib.A64.WakeWf.DtW (Ctx E) (ls0 E) l b n R F J0 t)
    (hobl : ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp IW).heap (WakeOD.arW hp IW).cells b n →
      WakeRefSeg.RefObl hp IW E (WakeHG.cTW hp IW) Spike.Lib.A64.WakeWf.DtW (Ctx E) (ls0 E) l b n)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hWp : ∀ E v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC) ((JW) σC))
    (hWs : ∀ E v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (TGE) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MU (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC))
    (hctr0 : ∀ E : Entry, E.Ok (Ly).Λ →
      Spike.Lib.WakeRoot.H1R hp IW ls0 Ctx (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (F0 E) E →
      ∀ s c fs, WakeRoot.inv0R hp IW ls0 Ctx frM E s c fs → Ctx E s c fs →
      WrAt s (DE).ar.ctrLoc → ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → Scc.Sem.A64.abi.atSys s = false →
      Spike.Lib.A64ConsumerA.CtrRow (ms0E fs')
        (fun s' c'' => Spike.Lib.A64ConsumerA.PendA wakeSrc I2E (DE).L0 (DE).ls0 s' c'' fs') s c')
    (hnew0 : ∀ E : Entry, E.Ok (Ly).Λ →
      Spike.Lib.WakeRoot.H1R hp IW ls0 Ctx (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []) (F0 E) E →
      ∀ s c fs, WakeRoot.inv0R hp IW ls0 Ctx frM E s c fs → Ctx E s c fs →
      ¬ WrAt s (DE).ar.ctrLoc → ∀ c' fs', FrameRun wakeSrc (c, fs) (c', fs') → Scc.Sem.A64.abi.atSys s = false →
      ∀ L, WrAt s L → ¬ Spike.Lib.A64ConsumerA.ArenaW (DE).ar (DE).L0 (DE).ls0 c' L →
        NewStM wakeSrc (DE).L0 (ms0E fs') s c') :
    CorrectE 2 (Spike.Lib.WakeA64.wakeS arch) (Ly).Λ B SccCertificate.asm :=
  WakeRoot.wake_rootP IW ls0 Ctx frM hp (fun _ => []) F0 hP hlo hstat hA13 hpin2 hinit2 hwide hnz hB hG hobl
    fun E hE h1 => ⟨Spike.Lib.A64.WakePh.StartH0U.hst0_ofU hp ls0 Ctx frM E hE
      (WakeSpawnRP.parsed_outLit hP).1 (WakeSpawnRP.parsed_outLit hP).2.1 hlo hstat hA13 hpin2 hctrD
      WakeFinalCAO.ctrZ_cert h1 (hF0 E) (hWp E) (hWs E), hctr0 E hE h1, hnew0 E hE h1⟩

/-- `F0 := wFU` meets `wake_rootU`'s `hF0`. -/
example : ∀ (E : Entry) v m0 σC m, wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC m →
    (fun (_ : Entry) => wFU hp) E m := fun _ v m0 σC _ h => ⟨v, m0, σC, h⟩

end Spike.Lib.A64.WakePh.RootU

/-- info: 'Spike.Lib.A64.WakePh.RootU.wake_rootU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.RootU.wake_rootU
