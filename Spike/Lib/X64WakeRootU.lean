/-
**`wc_main`'s frame conditions joined, and `H1G`'s unmapped words from
them** (wake.w, x86-64; the twin of `Spike/Lib/A64WakeRootU.lean`'s `wFU`):
at the start's switch depth `wcLsw` and `wc_main`'s frame depth `wcD`,
the union `wFU` of `wc_main`'s frame conditions is the root's `F0`; a box
ghost's frame `F` inside it (`BoxPure`) gives `Hun.HunB F`, hence `H1GA`.

- `wFU`: `∃ v m0 σC, wF (RS wcLsw v) wcD (FS …) m0 σC`.
- `hF0_U`: each frame condition is inside `wFU` (`Hxa.box_landing`'s and
  `hxa_R`'s `hF0` at `F0 := wFU`).
- `hunB_U`: `HunB F` from `BoxPure (Ly) wFU n R F J0 t`.
- `h1GA_U`: `Hun.h1GA_of` at `F0 := wFU`.

**Unlike AArch64**: `wc_main`'s region is `MainGlue.RS wcLsw v` (the
callee region of `call scc_rt_main` below the switch, `wcLsw = 384`,
`wcD = 328`) where A64 has `swR v (-384) 0` at `336`; `Hun.WF` is stated at
`swR v (-Lsw) 0`, so `hunB_U` reads `FS`'s `WordsNoneP` directly rather than
through `Hun.hunB_of`; A64 consumes `wFU` in `WakeRoot.wake_rootP`'s `hG`
at `BoxPure (F0 E)`, x86-64 in `h1GA_of`'s `HunB`.
-/
import Spike.Lib.X64WakeHun
import Spike.Lib.X64WakeStartFacts

namespace Spike.Lib.X64.WakePh.RootU

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (cellsOf)
open SccCode (wakeCells)
open Spike.Lib (PlaceWX Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64.Flow.WakeM (wF)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.WakeHMid (BoxPure)
open Spike.Lib.HeapLand (AllocLand)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **`wc_main`'s frame conditions, joined**: at every base `v`, entry memory
`m0` and caller state `σC`; the root's `F0`. -/
def wFU : MachineData → Prop := fun m =>
  ∃ v m0 σC, wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m

/-- **Each of `wc_main`'s frame conditions is inside `wFU`**: the `hF0` of
`Hxa.box_landing`/`hxa_R` at `F0 := wFU`. -/
theorem hF0_U : ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m →
    wFU hp i m :=
  fun v m0 σC _ h => ⟨v, m0, σC, h⟩

/-- **A word of `.data` or `pinned`, byte by byte, loads none under `wFU`**
(`FS`'s `WordsNoneP`). -/
theorem hunB_wFU : Hun.HunB hp i (wFU hp i) := fun _ hb _ ⟨_, _, _, h⟩ =>
  h.1.1.1 _ fun j hj => (hb j hj).elim (.inr ∘ .inl) (.inr ∘ .inr)

/-- **`HunB` at a box ghost's frame inside `wFU`** (`BoxPure`'s `F ⊆ F0`). -/
theorem hunB_U {n : Nat} {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64}
    (hB : BoxPure (Ly) (wFU hp i) n R F J0 t) : Hun.HunB hp i F :=
  fun a hb m hm => hunB_wFU hp i a hb m (hB.2.2.1 m hm)

/-- **`H1GA` at `F0 := wFU`**: `Hun.h1GA_of` with `HunB` by `hunB_U`. -/
theorem h1GA_U (asm : Scc.Sem.X64.Asm) (E : Scc.Sem.Entry) (cT : Loc) (Dt : State → Prop)
    (Ctx : Spike.Lib.FragS isa) (ls0 : Spike.Lib.X64Consumer.Lsize)
    (hpa : cellsOf asm = some o.prog) (hwp : cellsOf asm = some wakeCells)
    (hlo0 : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {l : WeakMem.AllocLabel} {b n : Nat}
    (hland : AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n)
    {R : Region} {F : MachineData → Prop} {J0 : AS → Ctl → Prop} {t : UInt64}
    (hB : BoxPure (Ly) (wFU hp i) n R F J0 t)
    (ti : Spike.Lib.X64.WakeH1GOf.TiG asm hp i E cT Dt Ctx ls0 l b n R F t) :
    Spike.Lib.X64.WakeH1A.H1GA asm hp i E cT Dt Ctx ls0 l b n R F t :=
  Hun.h1GA_of hp i asm E cT Dt Ctx ls0 hpa hwp hlo0 hstat hA13 hland hB (hunB_U hp i hB) ti

end Spike.Lib.X64.WakePh.RootU

/-- info: 'Spike.Lib.X64.WakePh.RootU.hunB_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootU.hunB_U

/-- info: 'Spike.Lib.X64.WakePh.RootU.h1GA_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.RootU.h1GA_U
