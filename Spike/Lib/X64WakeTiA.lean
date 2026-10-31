/-
**`H1G.ti` from `X64.WakeTi2Hat.hti_W`** (x86-64, the twin of
`Spike/Lib/A64WakeTiA.lean`): `tiA_of` applies `hti_W` at the shape of
`WakeHB1.hB1_W`'s `hti` (per entry, box ghost and `BoxPure` at
`F0 := RootU.wFU`), every landed premise discharged:

- `hpg`, `hlo`: `WakeSrcCtl.oprog_W`, `StartPlaceLy.hlo_W`.
- `hSctl`: `WakeBoxCtl.box_ctl`; `hpl`: `Ti2Fld.hti_placedX`.
- `hFr`, `hunF`: `WakeTiF.hFr_U`, `hunF_U` (the frame inside `wFU`, from
  `BoxPure`).
- `hmF`, `hnoF`, `hoffT`, `hoffL`, `hoffX`, `hfld`: `Ti2Fld.hmF2_W`,
  `hnoF2_W`, `hoffT2_W`, `hoffL_W`, `hoffX_W`, `hfld2_W`.
- `htk`: `Ti2Tk.htk2_W` (its `hctr2` by `StartPlaceLy.hctr2_of_data`, from
  the counters in `.data`, `hctrD`).
- `hbase`, `hRs`, `hR8`, `hF0`: `BoxPure`.

No premise is left beyond the loader's facts (`hpa`, `hwp`, `hlo0`,
`hstat`, `hA13`, `hpin2`, `hcz`, `hctrD`) and `hB1_W`'s binders.

**Unlike AArch64**: `hFr`, `hunF` are discharged (A64 leaves them premises);
`hti_W` takes `hA13` for the word separation, the rodata, the second stack's
range and the take site; the assembly is a parameter `asm`; the result is
quantified over the entry, the ghost and `BoxPure` (`hB1_W`'s `hti`). No
absolute address appears in this file.
-/
import Spike.Lib.X64WakeTi2Hat
import Spike.Lib.X64WakeWfTi2Fld
import Spike.Lib.X64WakeWfTi2Tk
import Spike.Lib.X64WakeTiF
import Spike.Lib.X64WakeBoxCtl
import Spike.Lib.X64WakeH1GOf

namespace Spike.Lib.X64.WakeTiA

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.WakeWc (t2)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (cT : Loc) (Dt : State → Prop) (Ctx : Entry → FragS isa) (ls0 : Entry → Spike.Lib.X64Consumer.Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i

/-- **`hB1_W`'s `hti`**: `hti_W` at the loader's facts, `BoxPure` at
`wFU`, `l`'s freshness and `b`'s landing. -/
theorem tiA_of (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hcz : Spike.Lib.X64.Rt.CtrZ o)
    (hctrD : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], (Ly).Λ.data.contains a.toNat) :
    ∀ E : Entry, E.Ok (Ly).Λ → ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (WakeOD.arW hp i).heap (WakeOD.arW hp i).cells b n →
      ∀ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
        BoxPure (Ly) (Spike.Lib.X64.WakePh.RootU.wFU hp i) n R F J0 t →
        Spike.Lib.X64.WakeH1GOf.TiG asm hp i E cT Dt (Ctx E) (ls0 E) l b n R F t := by
  intro E _ l b n hl hland R F J0 t hB
  have hpg := Spike.Lib.X64.WakeSrcCtl.oprog_W hpa hwp
  have hlo := Spike.Lib.X64.WakePh.StartPlaceLy.hlo_W hp i hlo0
  obtain ⟨⟨-, -, -, hRlo, hhi⟩, -, hF, ⟨-, -, hbase, -⟩, -, -, ⟨-, -, -, hF0, hR8a, hR8b⟩⟩ := hB
  have hFr := Spike.Lib.X64.WakeTiF.hFr_U hp i hF
  have hunF := Spike.Lib.X64.WakeTiF.hunF_U hp i hF hA13
  exact Spike.Lib.X64.WakeTi2Hat.hti_W asm hp i E cT Dt (Ctx E) (ls0 E) l b n hpg hlo hpa hA13
    (fun _ _ _ h => Spike.Lib.X64.WakeBoxCtl.box_ctl h.2.2.1)
    (Spike.Lib.X64.WakePh.Ti2Fld.hti_placedX hl) hFr
    (Spike.Lib.X64.WakePh.Ti2Fld.hmF2_W hp i hpin2) hunF
    (Spike.Lib.X64.WakePh.Ti2Fld.hnoF2_W hp i hA13)
    (Spike.Lib.X64.WakePh.Ti2Fld.hoffT2_W hp i hpin2 hcz) (Spike.Lib.X64.WakePh.Ti2Fld.hoffL_W hp i)
    (Spike.Lib.X64.WakePh.Ti2Fld.hoffX_W hp i) hbase ⟨hRlo, by omega⟩ ⟨hR8a, hR8b⟩ hF0
    (Spike.Lib.X64.WakePh.Ti2Fld.hfld2_W asm hp i E cT (ls0 E) l b n hpin2 hstat hland hunF)
    (Spike.Lib.X64.WakePh.Ti2Tk.htk2_W asm hp i E cT (ls0 E) l b n hpg hlo hbase hFr
      (Spike.Lib.X64.WakePh.StartPlaceLy.hctr2_of_data hp i hpin2 hctrD) hstat hland)

end Spike.Lib.X64.WakeTiA

/-- info: 'Spike.Lib.X64.WakeTiA.tiA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeTiA.tiA_of
