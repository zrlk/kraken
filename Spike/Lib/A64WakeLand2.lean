/-
**`RootOpen` at the root's context `CtxR`** (wake.w, AArch64): the
three open fields of `WakeRoot.RootOpen` at `i := IW`, `Ctx := CtxR`:

- `hst0` by `StartH0R.hst0_ofW` (its `hxa` by `Hxa.hxa_R` at `msBot E []`,
  `hUn1` moved from `refW` by `at_bX_xa`);
- `hctr0` by `Land.hctr0_R`, given the counter add's tail `HLand` (OPEN);
- `hnew0` by `WakeCtr.hnew0_of`, its landing by `Land.hland1_R`.

- `rootOpen_R`: the structure.
-/
import Spike.Lib.A64WakeLand
import Spike.Lib.A64WakeStartH0R

namespace Spike.Lib.A64.WakePh.Land

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize Pz)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakeWf (DtW X0W)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "LyW" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RSW" => Spike.Lib.A64.Rt.rS0 (LyW)

set_option hygiene false in
local notation "MSW" => Spike.Lib.WakeRoot.msBot hp IW ls0 (CtxR hp IW ls0) E []

set_option hygiene false in
local notation "WSW" => WS (LyW) (Spike.Lib.A64.Rt.Reserve.ntA (LyW).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc DtW
  (Spike.Lib.WakeOD.ClW hp IW) (CtxR hp IW ls0 E) (L0T (LyW).Λ) (ls0T (ls0 E)) (frM E)
  (X0W (LyW) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
local notation "JWW" => fun σC => wJ0 (wNC (LyW).lab (JS (LyW) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPWW" => TP (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64))

/-- **`RootOpen` at `CtxR`** (at `IW`): `hst0` by `hst0_ofW` (its `hxa` by
`hxa_R`), `hctr0` by `hctr0_R` (given `hland`), `hnew0` by `hnew0_of` with
`hland1_R`. Open: `hWp`/`hWs` (at `CtxR`), `h1`/`hF0`, `hUn1` (at
`refW`), `hland`. -/
theorem rootOpen_R (E : Entry) (hE : E.Ok (LyW).Λ)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (LyW).Λ o.prog o.secs = true)
    (hpin2 : (LyW).pinA.toNat + 168 ≤ (LyW).Λ.pinned.lo + (LyW).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(LyW).pnA, (LyW).lockA, (LyW).freeNA, (LyW).nextA], (LyW).Λ.data.contains a.toNat)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64)) (WSW))
      (Spike.Lib.A64.PhRec.K (LyW) RSW))
      (Spike.Lib.A64.PhRec.K (LyW) RSW) (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
      (tpXa MSW (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64))) ((JWW) σC) ((JWW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64)) (WSW))
      (Spike.Lib.A64.PhRec.K (LyW) RSW))
      (Spike.Lib.A64.PhRec.K (LyW) RSW) (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
      (tpXa MSW (UInt64.ofBitVec (pinA (LyW).lab + 0#64 + 8#64))) ((JWW) σC))
    {F0 : MachineData → Prop}
    (h1 : Spike.Lib.WakeRoot.H1R hp IW ls0 (CtxR hp IW ls0) MSW F0 E)
    (hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC m → F0 m)
    (hUn1 : ∀ v m0 σC l A s c, L0T (LyW).Λ l = none →
      At (LyW).exe (LyW).endPc (wR (swR v (-384) 0) 336) (wF (swR v (-384) 0) 336 (FS (LyW) RSW 384 0#64 v) m0 σC)
        (bX (refW hp IW ls0 E) (LyW).lab ((JWW) σC) l A) s c → TPWW s →
      Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (LyW).lab) s)
    (hland : HLand hp IW ls0 frM E) :
    Spike.Lib.WakeRoot.RootOpen hp IW ls0 (CtxR hp IW ls0) frM E where
  hst0 := Spike.Lib.A64.WakePh.StartH0R.hst0_ofW hp ls0 (CtxR hp IW ls0) frM E hE hpa hwp hlo0 hstat hA13
    hpin2 hctrD hc hWp hWs
    (Hxa.hxa_R hp ls0 (CtxR hp IW ls0) E hA13 h1 hF0
      (fun v m0 σC l A s c hl hA htp => hUn1 v m0 σC l A s c hl (at_bX_xa rfl hA) htp))
  hctr0 := hctr0_R hp IW ls0 frM hpa hwp hc E hland
  hnew0 := fun s c fs h0 hC => Spike.Lib.A64.WakeCtr.hnew0_of (hcode_R hp IW hpa hwp)
    (hland1_R (hp := hp) (ls0 := ls0) (frM := frM) E hA13 h1 hF0 hUn1) s c fs h0 hC.ctxW

end Spike.Lib.A64.WakePh.Land

/-- info: 'Spike.Lib.A64.WakePh.Land.rootOpen_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Land.rootOpen_R
