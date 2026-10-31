/-
**`hWs`'s top case at the root, inside `WSX`** (wake.w, x86-64):
`StartPlace.wake_start_wc_placeX`'s `hWs` at the first stack's top, at the
root's memory side `tpXa (Land.refW …) t` and context `Land.CtxR`, the
level `OwnImp.WSX`, inside `NoSetFsW`, guarded by main's thread pointer;
then at every base by `hWs_W`.

- `hTopS_R`: `wcSp0W_WSOg` at the top; the nodes' `SFactsSt2` by
  `OwnWc.wcSp0W_wcGX` (the box's cell mapped, unloaded and unowned by
  `hcellB_of_wordsNone`, `StartH0.mp_cellW`, `not_ownW`; off `tcbM` by
  `hboxM_of`), the store's obligation by `Land.hwr_R`, the placement by
  `WcPl.hplS_W`.
- `hWs_R`: every base.

x86-64 twin of `Spike/Lib/A64WakeWcWfR.lean`'s `tau_c0W`, `hTopS_Rpl`,
`hTopS_R` (namespace `Spike.Lib.X64.WakePh.WcWfR`). **Where this differs
from AArch64**: as `X64WakeWcTopR`'s `hTopP_R` (level `WSX` at `ownGXW`,
`NoSetFsW`, `c0` generic); the box's type from `Land.box_c0` at
`hbx : C0Box c0` (A64 `tau_c0W` at `c0W`); `ownGXW`'s box store also needs
the cell off `tcbM` (`hboxM`, discharged by `hboxM_of`).
-/
import Spike.Lib.X64WakeWcTopR

namespace Spike.Lib.X64.WakePh.WcWfR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS topS tcbS)
open Spike.Lib.X64.WakePh.StartFacts (wcD wcLsw)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.X64.Flow.WakeWc (WcPreW WcSp0W AGB)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.Rt.Reserve (ntA)
open Spike.Lib.X64.WakePh.StartH0 (C0Box)
open Spike.Lib (PlaceWX)
open Scc.Sem (Entry)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeT1 (wakeSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (asm : Scc.Sem.X64.Asm) (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (c0 : Ctl) (ls0 : Entry → Lsize)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
/-- The take (`PhRec.K`). -/
local notation "KW" => Spike.Lib.X64.PhRec.K (Ly) (RS0)

set_option hygiene false in
/-- Main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The top of the first stack. -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_main`'s entry invariant from the caller's state. -/
local notation "JW" => fun σC => wJ0 (wNC (Ly).lab (JS (Ly) 0#64 c0)).J σC

set_option hygiene false in
/-- The root's memory side at entry `E`. -/
local notation "MR" => tpXa (Spike.Lib.X64.WakePh.Land.refW asm hp i ls0 E) (TV)

set_option hygiene false in
/-- The start's level at `ownGXW` at the root's context. -/
local notation "WSR" => Spike.Lib.X64.WakePh.WSX (Ly) (ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp i) wakeSrc Dt Cl
  (Spike.Lib.X64.WakePh.Land.CtxR (Ly) c0 (Spike.Lib.X64.WakePh.Land.refW asm hp i ls0 E)) (L0T (Ly).Λ)
  (ls0T (ls0 E)) frM (Spike.Lib.X64.WakeWf.X0W (Ly) ax)

set_option maxHeartbeats 1600000 in
/-- **`hWs`'s top case at the root, inside `WSX`**: `wcSp0W_WSOg` at the
first stack's top inside `NoSetFsW`; the nodes' `SFactsSt2` at `ownGXW` by
`OwnWc.wcSp0W_wcGX`, the store's obligation by `Land.hwr_R`, the placement
by `WcPl.hplS_W`. -/
theorem hTopS_R (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hbx : C0Box c0)
    {Dt Cl : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf wakeSrc c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0 [])
    (E : Entry) (m0 : MachineData) (σC : Spike.Lib.X64.AS) :
    WcSp0W (Spike.Lib.X64.NoSetFsW (tpG (TV) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc (wR (RS wcLsw (TOP)) wcD)
      (wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (MR) ((JW) σC) := by
  -- the layout's facts
  haveI := (Ly).valid
  have hprog : (Ly).prog = wakeCells := hpo
  have hpS : Scc.Cert.Rt.X64.Lays (Ly).exe wakeCells (Ly).pfx := hprog ▸ (Ly).lays
  have hendS : (Ly).endPc = Scc.Cert.Rt.X64.endOf (Ly).exe wakeCells (Ly).pfx := by
    show Scc.Cert.Rt.X64.endOf (Ly).exe (Ly).prog (Ly).pfx = _; rw [hprog]
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX i hp
  have hwf' : (Ly).Λ.WF := hwf
  have hlab : ∀ l x, codeLabel lo wakeCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hp i l x (by rw [hlo, hpo]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link i hp)
  have hsite := Spike.Lib.PlaceWX.site_ofPlaceWX hp i
  have hX0 := Spike.Lib.X64.WakePh.StartGlue.x0W_of_freeN hlab hax
  have hsep := Spike.Lib.X64.WakePh.tcbSep_W hp i
  have ha := Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp i hA13
  have hW := Spike.Lib.X64.WakePh.tcb2_notG_W hp i hA13
  -- the region
  obtain ⟨hR, -⟩ := top_ok (Ly) hwf' m0 σC
  have hbW : Spike.Lib.X64.WakePh.BandOnP (Ly) (wR (RS wcLsw (TOP)) wcD) (-80) 8 :=
    Spike.Lib.X64.WakePh.OwnMid.bandOnP_mono (top_band (Ly)) (by decide) (by decide)
  -- the heap
  have hL := Spike.Lib.PlaceWX.link i hp
  have hsz : 16 * Scc.Cert.PlaceOK.allocCells ≤ (Ly).Λ.heap.size :=
    Spike.Lib.X64.Rt.ArenaW.PlaceWX.heapSize_of_placeWX hL
  have hhb : (Ly).Λ.heap.lo + (Ly).Λ.heap.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.heap_below_of_placeW hL
  have hh : (MR).heap = (Ly).Λ.heap.lo := rfl
  have hcl' : (MR).cells = 4194304 := rfl
  have hA : Scc.Cert.PlaceOK.allocCells = 4194304 := rfl
  have hu2 : (MR).units 1 .int = 2 := rfl
  have hf1 : (MR).off 1 .int = 8 := rfl
  have hc0q : ∀ q : AGB (MR) (Ly).lab, (∃ σ, (JW) σC σ q.1.c0) → q.1.c0 = c0 :=
    fun _ ⟨_, hJ⟩ => Spike.Lib.X64.WakePh.WcPl.c0_wJ0 hJ
  have hoB : ∀ q : AGB (MR) (Ly).lab, q.1.c0 = c0 → (MR).off 1 q.1.τ + 16 ≤ 16 * (MR).units 1 q.1.τ :=
    fun q hq => by
      obtain ⟨_, hτ, -⟩ := Spike.Lib.X64.WakePh.Land.box_c0 hbx q hq
      rw [hτ, hf1, hu2]; omega
  have hcell := Spike.Lib.X64.WakePh.StartGlue.hcellB_of_wordsNone
    (F := wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (P := fun q => q.c0 = c0)
    (ms := MR) (lab := (Ly).lab)
    (fun _ h => h.1.1.1.wn) (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl']; omega)
    (by rw [hh, hcl']; omega) hoB
    (fun q _ o h1 h2 => Spike.Lib.X64.WakePh.StartH0.mp_cellW hp i
      (⟨q.1, { q.2 with toS := { q.2.toS with } }⟩ : AGB (Spike.Lib.X64.WakePh.Land.refW asm hp i ls0 E) (Ly).lab)
      o h1 h2)
  have hbox : ∀ (q : AGB (MR) (Ly).lab) (o' : Nat), (∃ σ, (JW) σC σ q.1.c0) → (MR).lo o' →
      o' + (MR).units 1 q.1.τ ≤ (MR).cells →
      Spike.Lib.X64.WakePh.WcW.BoxOk (Ly).Λ (Ly) (ntA (Ly).lab)
        (wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC)
        (BitVec.ofNat 64 ((MR).heap + 16 * o' + (MR).off 1 q.1.τ)) := by
    intro q o' hJ hlo' hle
    have hq := hc0q q hJ
    obtain ⟨hmp, hun⟩ := hcell q hq o' hlo' hle
    obtain ⟨_, hτ, -⟩ := Spike.Lib.X64.WakePh.Land.box_c0 hbx q hq
    refine ⟨hmp.1, hun, not_ownW (heap := (MR).heap) (cells := (MR).cells) (ctr := (MR).ctr)
      (fun w' hw' => offW_own hp i hA13 w' hw') (.inr ?_)⟩
    rw [hτ, hu2, hcl'] at hle
    rw [hτ, hf1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [hh]; omega), hh, hcl']
    omega
  have hboxM := Spike.Lib.X64.WakePh.hboxM_of (L := Ly) hwf' (ms := MR) (lab := (Ly).lab)
    (by rw [hh]; exact Nat.le_refl _) (by rw [hh, hcl']; omega) (by rw [hh, hcl']; omega)
    (P := fun q => ∃ σ, (JW) σC σ q.1.c0) (fun q hJ => hoB q (hc0q q hJ))
  have hS : WcSp0W (fun s _ => Spike.Lib.X64ConsumerA.SFactsSt2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly))
      (Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) s) (KW) (Ly).exe (Ly).endPc (wR (RS wcLsw (TOP)) wcD)
      (wF (RS wcLsw (TOP)) wcD (FS (Ly) (RS0) wcLsw 0#64 (TOP)) m0 σC) (MR) ((JW) σC) :=
    Spike.Lib.X64.WakePh.OwnWc.wcSp0W_wcGX (Λ := (Ly).Λ) hprog hlo hΛ hlab hsite hsep ha hW hbW hR
      (by show -wcD ≤ -72; decide) (by show (8 : Int) ≤ 8; decide) hbox
      (fun q o' hJ h1 h2 => hboxM q o' hJ h1 h2)
  exact Spike.Lib.X64.Flow.WakeWc.WcSp0W.noSetFs hpS hendS
    (wcSp0W_WSOg (own := Spike.Lib.X64.WakePh.ownGXW (Ly) (ntA (Ly).lab)) hprog hlo hΛ hlab hsite hcl hX0
      hR (by show -wcD ≤ -72; decide) (by show (8 : Int) ≤ 8; decide)
      (fun q o' hJ h1 h2 => (hbox q o' hJ h1 h2).2.1)
      (fun _ _ h => by rw [Spike.Lib.X64.WakePh.WcPl.c0_wJ0 h]; exact hc0) hS
      (Spike.Lib.X64.WakePh.WcPl.hplS_W hpl0 σC)
      (Spike.Lib.X64.WakePh.Land.hwr_R asm hp i c0 ls0 hprog hc hbx E rfl (TOP) m0 σC))

/-- **`hWs` at the root, inside `WSX`, at every base** (`hWs_W` from
`hTopS_R`). -/
theorem hWs_R (hpo : o.prog = wakeCells) (hlo : (Ly).Λ.code.lo = lo) (hc : Spike.Lib.X64.Rt.CtrZ o)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (hbx : C0Box c0)
    {Dt Cl : State → Prop} {frM : TermRun.Frame} {ax : Int64}
    (hcl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hax : ax.toBitVec.toNat = ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
    (hc0 : (∀ a, c0.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf wakeSrc c0 [])
    (hpl0 : ∀ s, Spike.Lib.X64ConsumerS.PlacedSE (Ly).Λ (L0T (Ly).Λ) s c0 []) (E : Entry) :
    ∀ v m0 σC, WcSp0W (Spike.Lib.X64.NoSetFsW (tpG (TV) (WSR)) (KW)) (KW) (Ly).exe (Ly).endPc
      (wR (RS wcLsw v) wcD) (wF (RS wcLsw v) wcD (FS (Ly) (RS0) wcLsw 0#64 v) m0 σC) (MR) ((JW) σC) :=
  hWs_W (J := JW) (hTopS_R asm hp i c0 ls0 hpo hlo hc hA13 hbx hcl hax hc0 hpl0 E)

end Spike.Lib.X64.WakePh.WcWfR

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hTopS_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hTopS_R

/-- info: 'Spike.Lib.X64.WakePh.WcWfR.hWs_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcWfR.hWs_R
