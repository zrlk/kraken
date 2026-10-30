/-
**`H1GA.ti` from `WakeTi2Hat.hti_W`** (AArch64): `tiA_of` applies
`hti_W` with every landed premise discharged:

- `hpg`, `hlo`, `haW`, `hs`, `hro`, `hsub`: `WakeSrcCtl.oprog_W`,
  `StartPlaceLy.hlo_W`, `WakeOSide.aW_site`, `StartPlaceLy.wsep_W`,
  `WakeOSide.hro_W`, `StartPlaceLy.hsub1_W`.
- `hSctl`: `WakeSrcCtl.spawnSrc_ctl`; `hpl`: `PlacedCal.hti_placed`.
- `hmF`, `hnoF`, `hoffT`, `hoffL`, `hoffX`, `hfld`: `Ti2Fld.hmF2_W`,
  `hnoF2_W`, `hoffT2_W`, `hoffL_W`, `hoffX_W`, `hfld2_W`.
- `htk`: `Ti2Tk.htk2_W` (its `hctr2` by `StartPlaceLy.hctr2_of_data`).
- `hbase`, `hRs`, `hR8`, `hF0`: `BoxPure`.

Left as premises: `hFr`, `hunF` (the runtime's and the second TCB's words
unmapped under `F`: at the root from `F ⊆ wFU`) and the counters in `.data`
(`hctrD`). The SegW pre carries `Pz r1W` (supplied by `WakeHatA.hmid_boxA` from `Box`).
No absolute address appears in this file.
-/
import Spike.Lib.A64WakeH1A
import Spike.Lib.A64WakeTi2Hat
import Spike.Lib.A64WakeWfTi2Tk

namespace Spike.Lib.WakeTiA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.WakeWc (t2)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.WakeHMid (BoxPure)
open Spike.Lib.HeapLand (AllocLand)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Spike.Lib.A64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceW hp i

/-- **`H1GA.ti` at one ghost of `Box`**: `hti_W` at the loader's facts,
`BoxPure`, `l`'s freshness and `b`'s landing; the open premises named. -/
theorem tiA_of (hpa : textProgram SccCertificate.asm = .ok o.prog)
    (hwp : textProgram SccCertificate.asm = .ok wakeProg) (hlo0 : Λ0.code.lo = Spike.Lib.A64.WakePh.lo)
    (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.A64.Rt.CtrZ o)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat)
    {l : WeakMem.AllocLabel} {b n : Nat} {F0 : MachineData → Prop} {R : Region} {F : MachineData → Prop}
    {J0 : AS → Ctl → Prop} {t : UInt64} (hB : BoxPure (Ly) F0 n R F J0 t) (hl : L0T (Ly).Λ l = none)
    (hland : AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n)
    (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF (Ly) m)
    (hunF : ∀ a ∈ Spike.Lib.A64.Rt.Ti.tiAddrs (t2 (Ly).lab), ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    WakeH1A.TiA hp i E cT Dt Ctx ls0 l b n R F t := by
  have hpg := WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.A64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  have hprog := WakeSrcCtl.prog_W hp i hpa hwp
  have hwpL : textProgram SccCertificate.asm = .ok (Ly).prog := by rw [hprog]; exact hwp
  have haW := WakeOSide.aW_site hp i hpa hwp hwpL (Spike.Lib.PlaceW.site_ofPlaceW hp i) E
  obtain ⟨⟨-, -, -, hRlo, hhi, -, -⟩, -, -, ⟨-, -, hbase⟩, -, -, -, -, -, hF0, hR8⟩ := hB
  exact Spike.Lib.WakeTi2Hat.hti_W hp i E cT Dt Ctx ls0 l b n hpg hlo hpa haW
    (Spike.Lib.A64.WakePh.StartPlaceLy.wsep_W hp i hA13) (Spike.Lib.WakeOSide.hro_W hp i)
    (fun _ _ _ h => WakeSrcCtl.spawnSrc_ctl h.2.2) (Spike.Lib.A64.WakePh.PlacedCal.hti_placed hl) hFr
    (Spike.Lib.A64.WakePh.Ti2Fld.hmF2_W hp i hpin2) hunF (Spike.Lib.A64.WakePh.Ti2Fld.hnoF2_W hp i hA13)
    (Spike.Lib.A64.WakePh.Ti2Fld.hoffT2_W hp i hpin2 hcz) (Spike.Lib.A64.WakePh.Ti2Fld.hoffL_W hp i)
    (Spike.Lib.A64.WakePh.Ti2Fld.hoffX_W hp i) hbase ⟨hRlo, hhi⟩ hR8
    (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp i hA13) hF0
    (Spike.Lib.A64.WakePh.Ti2Fld.hfld2_W hp i E cT ls0 l b n hpin2 hstat hland hunF)
    (Spike.Lib.A64.WakePh.Ti2Tk.htk2_W hp i E cT ls0 l b n hpg hlo hbase hFr
      (Spike.Lib.A64.WakePh.StartPlaceLy.hctr2_of_data hp i hpin2 hctrD) hstat hland)

end Spike.Lib.WakeTiA

/-- info: 'Spike.Lib.WakeTiA.tiA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeTiA.tiA_of
