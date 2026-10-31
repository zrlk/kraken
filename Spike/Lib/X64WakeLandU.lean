/-
**The counter add's tail and the box store's landing at `CtxRU`, at the
start control `c0W`** (wake.w, x86-64): `RootUL.HLandU` and
`RootUL.HLand1U` at `inv0G … CtxRU` (and `inv1W … CtxRU`), so that
`X64WakeRootO.wake_finalX_LUO` at `c0 := c0W` owes only the start (`hst`)
besides the carried premises.

- `box_xa`: `WakeWc.Box` reads no `xa` (`Land.at_bX_xa`).
- `hland_RU`: `HLandU` at `inv0G … CtxRU`: `Land.hland_segU` at `inv0 := ⊥`,
  `inv1 := inv1W … CtxR` (that is, `msBotX`), its exit dropped to
  `Land5.QabX`, `Land5.inv0_of_habW` to `inv0G … CtxR`, lifted by
  `RootUL.inv0_up` with the `c2` state's `U r1Of`.
- `hland1_RU`: `HLand1U` at `inv0G … CtxRU`, `inv1W … CtxRU`:
  `Land.hland1_U`; `inv1W` reads no `Ctx` (`W1` drops it).
- `wake_finalX_land`: `wake_finalX_LUO` at `c0W` with `hland`/`hland1` by
  the two above.

Carried, stated as in `StartH0B.hst0_W` (one producer closes both):
`c0W`'s placement `hpl0`, the heap abort's lift `hlft` (`StartH0C.HabLft`),
`h1`'s `Box ⊆ inv1W` clause `hB1` at `msBotX … CtxR … E []` (from
`WakeHB1.hB1_W`, which carries `hti`/`hobl`) with the frame `F0`, and
`hF0` (`RootU.hF0_U` at `F0 := wFU`); in `wake_finalX_land` also the start
`hst` and `wake_finalX_LUO`'s instance facts.

x86-64 twin of `Spike/Lib/A64WakeLandU.lean`'s `hland_RU`.

**Where x86-64 differs from AArch64**:
- the segment and its `keepUn` move are `Land.hland_segU` (A64 inlines
  them in `hland_RU`); `hWp`/`hWs` are not premises (proved in
  `Land.hland_seg`);
- `h1` enters as its `Box ⊆ inv1W` clause `hB1` at `msBotX` (A64 the whole
  `WakeRoot.H1R` at `msBot`), moved to `Land4`'s memory sides by `box_xa`;
- `HLandU` lands in `inv0G … CtxR` and is lifted to `CtxRU` by
  `RootUL.inv0_up` (A64's `HLandU` is at `CtxR`'s `inv0` directly);
- `HLand1U` (`hland1_RU`) is new here: A64 closes the landing inside
  `hnew0` by `Hxa.box_landing`;
- `inv0_of_habW` takes `c0W`'s box shape, facts, placement and `HabLft`
  (A64 none: its start control is fixed inside).
-/
import Spike.Lib.X64WakeLand4
import Spike.Lib.X64WakeLand5
import Spike.Lib.X64WakeRootO

namespace Spike.Lib.X64.WakePh.LandU

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64.Flow.WakeM (wF)
open Spike.Lib.X64.Flow.WakeWc (Box)
open Spike.Lib.X64.WakePh.MainGlue (FS RS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib (FragS MemSide PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T)
open Spike.Lib.X64WakeParse (certAsm)
open Spike.Lib.X64.WakeH1Inv (inv1W)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64WakeFinal (msBotX inv0G)
open Spike.Lib.X64.WakePh.RootUL (CtxRU HLandU HLand1U)
open Spike.Lib.X64.WakeC0 (c0W)
open SccCertificate (outLit)

/-- **`Box` reads no `xa`**: a box landing at `ms` is one at `ms'`, `ms'`
being `ms` but for `xa` (`Land.at_bX_xa`). -/
theorem box_xa {L : RuntimeLayout} {ms ms' : MemSide isa} {F0 : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl} (he : ms' = { ms with xa := ms'.xa })
    (h : Box L ms F0 l b n s c) : Box L ms' F0 l b n s c := by
  obtain ⟨R, F, J0, t, h1, h2, h3, h4, ⟨hA, h5⟩, h6⟩ := h
  exact ⟨R, F, J0, t, h1, h2, h3, h4, ⟨Spike.Lib.X64.WakePh.Land.at_bX_xa he hA, h5⟩, h6⟩

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 outLit) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
/-- The root's `cT`: the dummy heap word. -/
local notation "cTR" => fun _ : Entry => Spike.Lib.X64WakeHG.cTW hp i

set_option hygiene false in
/-- The root's context at `c0W`. -/
local notation "CtxL" => fun E : Entry =>
  Spike.Lib.X64.WakePh.Land.CtxR (Ly) c0W (Spike.Lib.X64.WakePh.Land.refW certAsm hp i ls0 E)

set_option hygiene false in
/-- `h1`'s `Box ⊆ inv1W` clause at `msBotX` (as `StartH0B.hst0_W`'s `hB1`). -/
local notation "HB1" => ∀ l b n, L0T (Ly).Λ l = none →
  Spike.Lib.HeapLand.AllocLand (Spike.Lib.X64.WakeOD.arW hp i).heap (Spike.Lib.X64.WakeOD.arW hp i).cells b n →
  ∀ s c, Box (Ly) (msBotX hp i (cTR) ls0 (CtxL) frM E []) F0 l b n s c →
    inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW ((CtxL) E) (ls0 E) l b n s c []

set_option hygiene false in
/-- `wc_main`'s frame inside `F0`. -/
local notation "HF0" => ∀ v m0 σC m, wF (RS wcLsw v) wcD (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) wcLsw 0#64 v) m0 σC m →
  F0 m

set_option maxHeartbeats 1600000 in
/-- **The counter add's tail at `CtxRU`**: `Land.hland_segU` at `msBotX`
(`inv0 := ⊥`, `inv1 := inv1W … CtxR`) from the `c2` state (moved from
`ms0`: the add's node reads no `xa`), its exit `QabX`, in `inv0G … CtxR` by
`Land5.inv0_of_habW`, lifted to `CtxRU` by `RootUL.inv0_up`. -/
theorem hland_RU (E : Entry) (hpa : cellsOf certAsm = some outLit.prog)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly)) {F0 : MachineData → Prop}
    (hB1 : HB1) (hF0 : HF0) :
    HLandU hp i c0W ls0 (inv0G hp i (cTR) ls0 (CtxRU hp i c0W ls0) frM E) E := by
  have hax : (Spike.Lib.X64WakeOSide.aW hp i E).toBitVec.toNat =
      ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
    rw [Spike.Lib.X64WakeOSide.aW_site hp i hpa E]
  intro ms0 R F q hms hG hok s c hAt htp hu
  obtain ⟨X, rfl⟩ : ∃ X, ms0 = { Spike.Lib.X64.WakePh.Land.refW certAsm hp i ls0 E with xa := X } :=
    ⟨_, hms⟩
  obtain ⟨v, m0, σC, rfl, rfl, hra⟩ := hG
  have hS := Spike.Lib.X64.WakePh.Land.hland_segU certAsm hp i ls0 (E := E) (Dt := DtW) (frM := frM E)
    (ax := Spike.Lib.X64WakeOSide.aW hp i E) (inv0 := fun _ _ _ => False)
    (inv1 := inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW ((CtxL) E) (ls0 E)) (F0 := F0)
    Spike.Lib.X64WakeParse.outLit_prog hlo hc hA13 hax hpl0
    (fun l b n hl hb s c h => hB1 l b n hl hb s c (box_xa rfl h)) hF0
    v m0 σC q { hok.okb with toS := { hok.okb.toS with } } hra
  refine Spike.Lib.X64.WakePh.RootUL.inv0_up hp i c0W ls0 frM (cTR) E s c [] ?_ hu
  exact Spike.Lib.X64.WakePh.Land5.inv0_of_habW hp i (cTR) ls0 (CtxL) frM E hpa hlo
    Spike.Lib.X64.WakeC0.c0W_box Spike.Lib.X64.WakeC0.c0W_ctl hpl0 hlft
    (hS.mono_post fun _ _ h => h.1) s c ⟨⟨hAt, htp⟩, hu⟩

/-- **The box store's landing at `CtxRU`**: `Land.hland1_U` at
`inv0G … CtxRU` and `inv1W … CtxRU`, `hB1` moved from `msBotX` by `box_xa`
(`inv1W` reads no `Ctx`: `W1` drops it). -/
theorem hland1_RU (E : Entry) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    {F0 : MachineData → Prop} (hB1 : HB1) (hF0 : HF0) :
    HLand1U hp i c0W ls0 (inv0G hp i (cTR) ls0 (CtxRU hp i c0W ls0) frM E)
      (inv1W certAsm hp i E (Spike.Lib.X64WakeHG.cTW hp i) DtW (CtxRU hp i c0W ls0 E) (ls0 E)) E :=
  Spike.Lib.X64.WakePh.Land.hland1_U certAsm hp i ls0 (E := E) (F0 := F0) hA13
    (fun l b n hl hb s c h => hB1 l b n hl hb s c (box_xa rfl h)) hF0

/-- **wake.w's x86-64 root at `c0W` with the tails closed**:
`X64WakeRootO.wake_finalX_LUO` at `c0 := c0W`, `hland` by `hland_RU`,
`hland1` by `hland1_RU`. Open: the start `hst`, `c0W`'s placement `hpl0`,
`HabLft`, `hB1`/`hF0`, and the instance facts. -/
theorem wake_finalX_land {arch : WeakMem.Arch} {B : Budget}
    (hP : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ outLit.prog outLit.secs = true)
    (hpin2 : (Ly).pinA.toNat + 168 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ outLit.prog outLit.secs).initVal
      ⟨Spike.Lib.X64WakeGOf2.lim2A (Ly), 8⟩ = 0)
    (hsub1 : (Spike.Lib.X64WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) (hc : Spike.Lib.X64.Rt.CtrZ outLit)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 outLit = true)
    (hpl0 : ∀ s, PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0W [])
    (hlft : Spike.Lib.X64.WakePh.StartH0C.HabLft (Ly)) {F0 : MachineData → Prop}
    (hB1 : ∀ E : Entry, E.Ok (Ly).Λ → HB1) (hF0 : HF0)
    (hst : ∀ E : Entry, E.Ok (Ly).Λ →
      inv0G hp i (cTR) ls0 (CtxRU hp i c0W ls0) frM E
        (threadAt E (Ly).Λ.code.lo outLit.prog (loadSyms (Ly).Λ outLit.secs.rodata))
        ⟨Spike.Lib.X64WakePreAsm.wakeTh0.term, Spike.Lib.X64WakePreAsm.wakeTh0.env, none⟩
        Spike.Lib.X64WakePreAsm.wakeTh0.stack) :
    CorrectE 2 (wakeS arch) (Ly).Λ B certAsm :=
  have hpa := (Spike.Lib.X64WakeParse.parsed_outLit hP).1
  Spike.Lib.X64WakeRootO.wake_finalX_LUO (hp := hp) (i := i) (ls0 := ls0) (frM := frM) c0W hP hB hlo hstat
    hA13 hpin2 hinit2 hsub1 hc hnz
    (fun E hE => hland_RU hp i ls0 frM E hpa hlo hc hA13 hpl0 hlft (hB1 E hE) hF0)
    (fun E hE => hland1_RU hp i ls0 frM E hA13 (hB1 E hE) hF0) hst

end Spike.Lib.X64.WakePh.LandU

/-- info: 'Spike.Lib.X64.WakePh.LandU.box_xa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.LandU.box_xa

/-- info: 'Spike.Lib.X64.WakePh.LandU.hland_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.LandU.hland_RU

/-- info: 'Spike.Lib.X64.WakePh.LandU.hland1_RU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.LandU.hland1_RU

/-- info: 'Spike.Lib.X64.WakePh.LandU.wake_finalX_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.LandU.wake_finalX_land
