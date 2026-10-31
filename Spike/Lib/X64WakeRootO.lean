/-
**`X64WakeFinal.OpenX` from `h0`, `hctr0`, `hnew0` and the start in
`inv0`** (wake.w, x86-64): at the root's dummy heap word `cT := cTW` and any
`Ctx`, `inv0`, the remaining fields of `OpenX` are discharged:

- `hinit` by `X64WakeOHinit.hinit_W` (carrying the start in `inv0`, `hst`);
- `hG` by `X64WakeHG.memInv_gW` (`hG_W`);
- `hCl` by `X64WakeHClC.hCl_W` at the `OPrem` that
  `X64.WakeOPremW.oPrem_W` builds from `h0`, `hctr0`, `hnew0` and `hinit`.

- `hG_W`: `OpenX.hG` at `cT := cTW`.
- `openX_of`: `OpenX` at `cT := cTW` from `h0`, `hctr0`, `hnew0`, `hst`.
- `wake_finalX_LUO`: `RootUL.wake_finalX_LU` with `hO` by `openX_of`: open
  per entry are only the counter add's tail `hland`, the box store's landing
  `hland1` and the start in `inv0G` at `CtxRU` (`hst`), besides the instance
  facts.

x86-64 twin of the `hinit`/`hG`/`hCl` wiring of
`Spike/Lib/WakeFinalCAW.lean`. **Unlike AArch64**:
- `OpenX` (`X64WakeFinal`) keeps `hinit`, `hG`, `hCl` as fields, closed here
  in a separate module (A64 `OpenW` discharges them inside
  `wake_finalCA_genW`);
- the instance facts `hstat` (no static labels) and `hnz`
  (`X64WakeOInit.NtZ`: `scc_rt_nthreads` starts at `0`) are premises (A64
  decides `NtZ` at the certificate, `WakeFinalCAO.hnt_cert`).
-/
import Spike.Lib.X64WakeRootUL
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64WakeOHinit

namespace Spike.Lib.X64WakeRootO

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (I2)
open Spike.Lib.X64WakeParse (certAsm parsed_outLit)
open Spike.Lib.X64.WakeH1Inv (inv1W)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64WakeFinal (DX H0X HCtrX HNewX OpenX inv0G)
open Spike.Lib.X64.WakePh.RootUL (CtxRU HLandU HLand1U)
open SccCertificate (outLit)

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isa) (frM : Entry → TermRun.Frame) (inv0 : Entry → FragS isa)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The root's `cT`: the dummy heap word. -/
local notation "cTR" => fun _ : Entry => Spike.Lib.X64WakeHG.cTW hp i

set_option hygiene false in
/-- `DX` at the root's `cT` and the entry `E`. -/
local notation "DE" => DX hp i cTR ls0 Ctx frM inv0 E

/-- **`OpenX.hG` at the root's `cT`** (`X64WakeHG.memInv_gW`): `DX`'s
guarantee is `gW` at `cTW`. -/
theorem hG_W (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (E : Entry)
    {R : Cfg → TermRun.Cfg → Prop} :
    ∀ d s (th : Thread isa) (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) ts hd l T S pT cw,
      R d s → d.1.threads = #[th] → s.ths = #[th0] →
      I2 (DE).ar (DE).L0 (DE).ls0 (DE).inv0 (DE).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
      Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∀ X, X64WakePreA.ClonePre (Ly).Λ (DE).r0 (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) X lbl d s →
      MemInv (DE).G d.1.mem →
      MemInv (X64WakeInst.wakeG' hp i (X64WakeOkW.recW T S lbl lsize l pT cw)) d.1.mem :=
  fun _ _ _ _ lbl lsize _ _ l T S pT cw _ _ _ _ _ _ _ _ hm =>
    Spike.Lib.X64WakeHG.memInv_gW hp i hpin2 (X64WakeOkW.recW T S lbl lsize l pT cw) hm

/-- **`OpenX` at the root's `cT`** from `h0`, `hctr0`, `hnew0` and the start
in `inv0` (`hst`): `hinit` by `hinit_W`, `hG` by `hG_W`, `hCl` by `hCl_W` at
`oPrem_W`'s `OPrem`. -/
theorem openX_of {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hnz : X64WakeOInit.NtZ Λ0 outLit = true)
    (E : Entry) (hE : E.Ok (Ly).Λ)
    (h0 : H0X hp i cTR ls0 Ctx frM inv0 E) (hctr0 : HCtrX hp i cTR ls0 Ctx frM inv0 E)
    (hnew0 : HNewX hp i cTR ls0 Ctx frM inv0 E)
    (hst : inv0 E (threadAt E (Ly).Λ.code.lo outLit.prog (loadSyms (Ly).Λ outLit.secs.rodata))
      ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
      Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    OpenX hp i cTR ls0 Ctx frM inv0 arch hP E := by
  have hpa := parsed_outLit hP
  have hinit := X64WakeOHinit.hinit_W hp i hpa.1 hpa.2.1 hpa.2.2.1 hpa.2.2.2 hlo hstat hsub1 hc hnz hpin2 arch
    hE.1 (Spike.Lib.X64WakeHG.cTW hp i) DtW (ls0 E) (X64.WakeOPremW.W0W certAsm hp i E DtW (Ctx E) (ls0 E) (frM E))
    (inv0 E) (X64.WakeOPremW.W1W certAsm hp i E DtW (Ctx E) (ls0 E))
    (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)) hst
  have hOP := X64.WakeOPremW.oPrem_W certAsm hp i arch E (Spike.Lib.X64WakeHG.cTW hp i) DtW (ls0 E) (Ctx E)
    (frM E) (inv0 E) (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (Ctx E) (ls0 E)) hpa.1 hpa.2.1
    hpa.2.2.1 hlo hpin2 hsub1 hc hB
    (fun l b n h1 h2 => X64.WakeH1Inv.h1_of certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (Ctx E) (ls0 E) _
      (inv0 E) l b n h1 h2)
    h0 (Spike.Lib.X64.WakeWf.h0Take_of h0) (Spike.Lib.X64.WakeWf.h0TakeOwn_of h0)
    (X64.WakeH1Inv.h1Take_of certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (Ctx E) (ls0 E))
    (X64.WakeH1Inv.h1TakeOwn_of certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (Ctx E) (ls0 E))
    hctr0 hnew0 X64.WakeWf.hdtW hinit (B := B)
  exact ⟨h0, hctr0, hnew0, hinit, hG_W hp i ls0 Ctx frM inv0 hpin2 E,
    X64WakeHClC.hCl_W hp i (Spike.Lib.X64WakeHG.cTW hp i) DtW (ls0 E) (Ctx E) (frM E) (inv0 E)
      (fun _ _ h => h.1) hOP⟩

/-- **wake.w's x86-64 statement at the root's context with the child's
stack unmapped, `OpenX` closed** (`RootUL.wake_finalX_LU` with `hO` by
`openX_of` at `Ctx := CtxRU`, `inv0 := inv0G`): open per entry are the
counter add's tail `hland` (`HLandU`), the box store's landing `hland1`
(`HLand1U`) and the start in `inv0G` (`hst`), besides the instance facts. -/
theorem wake_finalX_LUO {arch : WeakMem.Arch} {B : Budget} (c0 : Ctl)
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hnz : X64WakeOInit.NtZ Λ0 outLit = true)
    /- OPEN: the counter add's tail, the box store's landing and the start, per entry -/
    (hland : ∀ E : Entry, E.Ok (Ly).Λ →
      HLandU hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E) E)
    (hland1 : ∀ E : Entry, E.Ok (Ly).Λ →
      HLand1U hp i c0 ls0 (inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E)
        (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (CtxRU hp i c0 ls0 E) (ls0 E)) E)
    (hst : ∀ E : Entry, E.Ok (Ly).Λ →
      inv0G hp i cTR ls0 (CtxRU hp i c0 ls0) frM E
        (threadAt E (Ly).Λ.code.lo outLit.prog (loadSyms (Ly).Λ outLit.secs.rodata))
        ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
        Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm :=
  X64.WakePh.RootUL.wake_finalX_LU hp i c0 ls0 frM hP hB hlo hA13 hpin2 hinit2 hsub1 hc hland hland1
    fun E hE h0 hctr0 hnew0 => openX_of hp i ls0 (CtxRU hp i c0 ls0) frM _ hP hB hlo hstat hpin2 hsub1 hc hnz E hE
      h0 hctr0 hnew0 (hst E hE)

end Spike.Lib.X64WakeRootO

/-- info: 'Spike.Lib.X64WakeRootO.hG_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeRootO.hG_W

/-- info: 'Spike.Lib.X64WakeRootO.openX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeRootO.openX_of

/-- info: 'Spike.Lib.X64WakeRootO.wake_finalX_LUO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeRootO.wake_finalX_LUO
