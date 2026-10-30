/-
**`RootOpen.hst0` at the root's immediate table** (wake.w, AArch64): the
start segment `StartH0B.hst0_of` at `i := immsW2 Λ0 wakeImms`
(`WakeFinalCAW.iW`), its start segment `hG` from
`StartH0G.wake_start_wc_h0W` at the root's choices (`L0T`/`ls0T (ls0 E)`,
`DtW`, `Ctx E`, `frM E`, `wakeSrc`, `msBot E []`'s marks, `rd`, `I2`), the
placements discharged:

- `hplS` by `WakeImmsC0.placedSE_start2W` (`wakeTh0`'s control);
- `hpl0` by `WakeImmsC0.placedSE_c0WW` (`c0W`);
- the heap abort's segment `hC` by `StartH0C.wake_hab_closed` (its `hpl0`
  as above);
- the consumer facts `hC0` at `c0W` by `WakeC0CF.cfacts_c0WW`;
- `hst0_of`'s `Pe`, the site frame `Pz rS0`, at the loaded thread
  (`pz_rS0_load`: the pool is off the entry stack's memory,
  `WakeOHinit.unowned_stack`).

Left as premises: the loader's facts (`hpa`, `hwp`, `hlo0`, `hstat`, `hA13`,
`hpin2`, `hctrD`, `hc`), and `wc_main`'s `hWp`/`hWs`/`hxa` at the root's
choices.

- `pz_rS0_load`: `Pz rS0` at the loaded thread.

- `hst0_ofW`: the statement.
-/
import Spike.Lib.A64WakeStartH0B
import Spike.Lib.WakeImmsC0
import Spike.Lib.A64WakeStartH0C
import Spike.Lib.A64WakeC0CF
import Spike.Lib.WakeOHinit

namespace Spike.Lib.A64.WakePh.StartH0R

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.WakeWf (DtW X0W)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib (FragS SegWS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeT1 (wakeSrc)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib.WakeOPremW (W0W)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o)
  (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The root's immediate table (`WakeFinalCAW.iW`). -/
local notation "IW" => Spike.Lib.WakeImmsC0.immsW2 Λ0 SccCode.wakeImms

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp IW

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
/-- `msBot E []`, the start's memory side at the root's choices. -/
local notation "MS" => Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E []

set_option hygiene false in
/-- The start's fragment at the root's choices (`StartH0G`'s `WSW`). -/
local notation "WSE" => WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp IW) wakeSrc DtW
  (Spike.Lib.WakeOD.ClW hp IW) (Ctx E) (L0T (Ly).Λ) (ls0T (ls0 E)) (frM E)
  (X0W (Ly) (Spike.Lib.WakeOSide.aW hp IW E))

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0W)).J σC

set_option hygiene false in
local notation "TPW" => TP (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))

/-- **`Pz rS0` at the loaded thread**: main's stack, in the pool, is off
the entry stack's memory (`WakeOHinit.unowned_stack`). -/
theorem pz_rS0_load (E : Entry) (hE : E.Ok (Ly).Λ) :
    Spike.Lib.A64Consumer.Pz (Spike.Lib.A64.Rt.rS0 (Ly))
      (Scc.Sem.A64.threadAt E (Ly).Λ.code.lo o.prog (Scc.Sem.loadSyms (Ly).Λ o.secs.rodata)).st.1 := by
  have hst := (Ly).stacks_sub
  have hpf := (Ly).pool_fit
  simp only [Scc.Sem.Range.Sub] at hst
  refine Spike.Lib.A64Consumer.pz_of_unowned (by exact (by decide : (0 : Nat) < 16384))
    (Spike.Lib.WakeOHinit.unowned_stack hp IW hE.1 (Spike.Lib.A64.Rt.rS0_sub (Ly)) ?_ _ rfl)
  show ((Ly).stacksA + 0#64).toNat + 16384 ≤ 2 ^ 64
  rw [BitVec.add_zero]; omega

/-- **`RootOpen.hst0` at `iW`**: `StartH0B.hst0_of` with `hplS` by
`placedSE_start2W`, `Pe` the site frame `Pz rS0` (`pz_rS0_load`), and `hG` by `StartH0G.wake_start_wc_h0W` at the root's
choices, its `hpl0` by `placedSE_c0WW` and `hC0` by `cfacts_c0WW`, and `hC` by
`wake_hab_closed`. -/
theorem hst0_ofW (E : Entry) (hE : E.Ok (Ly).Λ)
    (hpa : textProgram SccCertificate.asm = .ok o.prog) (hwp : textProgram SccCertificate.asm = .ok wakeProg)
    (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    (hWp : ∀ v m0 σC, WcPreW (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSE)) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC) ((JW) σC))
    (hWs : ∀ v m0 σC, WcSp0W (Spike.Lib.A64.Flow.NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)) (WSE)) (Spike.Lib.A64.PhRec.K (Ly) RS))
      (Spike.Lib.A64.PhRec.K (Ly) RS) (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
      (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC)
      (tpXa MS (UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64))) ((JW) σC))
    (hxa : ∀ v m0 σC l A s c, L0T (Ly).Λ l = none →
      Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc (wR (swR v (-384) 0) 336)
        (wF (swR v (-384) 0) 336 (FS (Ly) RS 384 0#64 v) m0 σC) (bX MS (Ly).lab ((JW) σC) l A) s c →
      TPW s → (MS).xa l A 1 s c) :
    SegWS (W0W hp IW E DtW (Ctx E) (ls0 E) (frM E))
      (TakeCKS (Spike.Lib.WakeOSide.aW hp IW E) (Spike.Lib.WakeOD.ClW hp IW))
      wakeSrc (L0T (Ly).Λ) (Spike.Lib.WakeRoot.msBot hp IW ls0 Ctx E)
      (Spike.Lib.WakeRoot.StartP hp IW E) (fun _ _ _ => False) :=
  Spike.Lib.A64.WakePh.StartH0B.hst0_of hp IW ls0 Ctx frM E hE hpa hwp hlo0
    (Spike.Lib.WakeImmsC0.placedSE_start2W hp) (Pe := fun s => Spike.Lib.A64Consumer.Pz (RS) s.st.1)
    (pz_rS0_load hp E hE)
    (Spike.Lib.A64.WakePh.StartH0G.wake_start_wc_h0W hp IW hE hpa hwp hlo0 hstat hA13
      hpin2 hctrD hc (Spike.Lib.WakeImmsC0.placedSE_c0WW hp) (Spike.Lib.A64.WakeC0CF.cfacts_c0WW hp) hWp hWs hxa)
    (Spike.Lib.A64.WakePh.StartH0C.wake_hab_closed hp IW hpa hwp hlo0 (Spike.Lib.WakeImmsC0.placedSE_c0WW hp))

end Spike.Lib.A64.WakePh.StartH0R

/-- info: 'Spike.Lib.A64.WakePh.StartH0R.hst0_ofW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0R.hst0_ofW

/-- info: 'Spike.Lib.A64.WakePh.StartH0R.pz_rS0_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.StartH0R.pz_rS0_load
