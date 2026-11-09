/-
**`Box ⊆ inv1W` at the start's memory side** (wake.w, x86-64): `h1`'s
`Box` clause (`(H1Stmt …).2.1`, from `X64WakeH1A.wake_h1A`) at the memory
side `msS` of the start (`msOfA` at `I2 arW L0T ls0T inv0 inv1W`, `inv0`
generic) and the frame `F0 := RootU.wFU`, in the shape the start's
`hxa` (`Hxa.hxa_R`'s `hB1`) consumes.

- `msS`: the start's memory side at `inv0`.
- `hokb_S`, `hg_S`: `wake_h1A`'s `hokb`/`hg` at `msS` (`WakeBoxW.okb_ms1`;
  the arena's fields by `rfl`).
- `hB1_W`: `Box (Ly) msS wFU ⊆ inv1W`, with `wake_h1A`'s `hG` by
  `RootU.h1GA_U`; carried: the loader facts, the callee `ti` per box ghost,
  and `RefObl` (`hobl`).

**Unlike AArch64**: A64 consumes `h1`'s whole statement (`WakeRoot.H1R` at
`msBot`) inside `Hxa.hxa_R`; x86-64's `hxa_R` takes only the `Box ⊆ inv1`
clause at a generic `msOfA … I2 … inv0 inv1` side, so this file states it
on its own; `H1G` is `H1GA` (`wake_h1A`), whose unmapped words come from
`F0 := wFU` (`RootU.hunB_U`).
-/
import Spike.Lib.X64WakeRootU

namespace Spike.Lib.X64.WakeHB1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (PlaceWX FragS MemSide Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64ConsumerA (msOfA I2)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.HeapLand (AllocLand)
open SccCode (wakeCells)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
  (inv0 : FragS isa)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The start's memory side** at `inv0`: `msOfA` at the root's guarantee
and owned words, the arena `arW`, `I2`'s `inv1` disjunct `inv1W`. -/
abbrev msS : MemSide isa :=
  msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True) (Spike.Lib.X64WakeOG.gW hp i cT)
    (fun s _ => Spike.Lib.X64.WakePh.ownGXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s)
    (Spike.Lib.X64.WakeOD.arW hp i)
    (I2 (Spike.Lib.X64.WakeOD.arW hp i) (L0T (Ly).Λ) (ls0T ls0) inv0
      (Spike.Lib.X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0))
    (L0T (Ly).Λ) (ls0T ls0) []

/-- **`wake_h1A`'s `hokb` at `msS`** (`WakeBoxW.okb_ms1`; the arena's facts
from the counter's zeroed item). -/
theorem hokb_S (hc : Spike.Lib.X64.Rt.CtrZ o) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      ∀ q : Spike.Lib.X64.Alloc.Call, q.OKB (msS asm hp i E cT Dt Ctx ls0 inv0) (Ly).lab →
        q.OKB (Spike.Lib.X64.WakeH1Inv.ms1W asm hp i E cT ls0 l b n []) (Ly).lab :=
  fun _ _ _ hl hb _ h => Spike.Lib.X64.WakeBoxW.okb_ms1
    (Spike.Lib.X64.WakeOD.hok_W hp i E cT (fun _ => False) ls0 (fun _ _ _ => False) (fun _ _ _ => False)
      (fun _ _ _ _ _ _ => False) (fun _ _ _ _ _ _ => False) hc)
    (Spike.Lib.X64.WakeOD.arW_newOk hp i) hl hb h

/-- **`wake_h1A`'s `hg` at `msS`**: its arena fields are `arW`'s. -/
theorem hg_S : (msS asm hp i E cT Dt Ctx ls0 inv0).heap = (Spike.Lib.X64.WakeOD.arW hp i).heap ∧
    (msS asm hp i E cT Dt Ctx ls0 inv0).cells = (Spike.Lib.X64.WakeOD.arW hp i).cells ∧
    (msS asm hp i E cT Dt Ctx ls0 inv0).off = (Spike.Lib.X64.WakeOD.arW hp i).off ∧
    (msS asm hp i E cT Dt Ctx ls0 inv0).units = (Spike.Lib.X64.WakeOD.arW hp i).units :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **`Box ⊆ inv1W` at `msS` and `F0 := wFU`** (`hxa_R`'s `hB1`): `h1`'s
`Box` clause from `wake_h1A`, its `hG` by `RootU.h1GA_U`. Carried: the
loader facts, the callee `ti` at each box ghost, `RefObl`. -/
theorem hB1_W (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) (hwp : Scc.Sem.X64.cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hti : ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      ∀ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
        BoxPure (Ly) (Spike.Lib.X64.WakePh.RootU.wFU hp i) n R F J0 t →
        Spike.Lib.X64.WakeH1GOf.TiG asm hp i E cT Dt Ctx ls0 l b n R F t)
    (hobl : ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      Spike.Lib.X64.WakeRefSeg.RefObl asm hp i E cT Dt Ctx ls0 l b n) :
    ∀ l b n, L0T (Ly).Λ l = none →
      AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
      ∀ s c, Spike.Lib.X64.Flow.WakeWc.Box (Ly) (msS asm hp i E cT Dt Ctx ls0 inv0)
          (Spike.Lib.X64.WakePh.RootU.wFU hp i) l b n s c →
        Spike.Lib.X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0 l b n s c [] :=
  fun l b n hl hb =>
    (Spike.Lib.X64.WakeH1A.wake_h1A asm hp i E cT Dt Ctx ls0 hpa hwp hlo0 hA13 hpin2 hc
      (hokb_S asm hp i E cT Dt Ctx ls0 inv0 hc) (hg_S asm hp i E cT Dt Ctx ls0 inv0)
      (fun l b n hl hb R F J0 t hB => Spike.Lib.X64.WakePh.RootU.h1GA_U hp i asm E cT Dt Ctx ls0 hpa hwp hlo0
        hstat hA13 hb hB (hti l b n hl hb R F J0 t hB))
      hobl l b n hl hb).2.1

end Spike.Lib.X64.WakeHB1

/-- info: 'Spike.Lib.X64.WakeHB1.hokb_S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHB1.hokb_S

/-- info: 'Spike.Lib.X64.WakeHB1.hB1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeHB1.hB1_W
