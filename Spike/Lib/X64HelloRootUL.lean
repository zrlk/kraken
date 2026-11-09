/-
**hello's root context with the child's stack unmapped** (x86-64; the twin of `Spike/Lib/A64HelloRootUL.lean`'s
live part, at hello's level-0 invariant `RootH0.inv0Hg`): `CtxU Ctx := Ctx ∧ U r1Of`, so the counter add's tail
(`RootL0X.HLandRdUg`, `U r1Of` at `c2`) gets the child's stack unmapped from the context itself. The root's level 0
is at `ownGHXW`, so the lifts of `inv0` and the start segment to `CtxU Ctx` (AArch64 `takeU_H`, `inv0_upH`,
`hst0_UH`) are `RootL0X`'s `takeU_Hg`, `inv0_upHg`, `hst0_UHg` at an own map.

- `CtxU`: the context with `r1Of` unmapped.
- `ctrRow_ofFTU`: the counter add's row at a frame-indexed counter add with `TP t` and `U r` kept into the landing
  (the `hctr0` lift's row).

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` at `X64.HelloImms.immsH` (AArch64 `ofPlaceW` at `C0S.immsH`).
- `ctrRow_ofFTU` takes the allocator's code from the layout (`hp : Lays exe cells kp`, `hend`, `hin`, under
  `Executable.ValidLayout exe`; AArch64 `hcode : ∀ ms0 q, Alloc.Code ms0 q exe endPc`), its row is
  `WakeCtr.ctrRow_allocS_c2`'s, landing at `c2` (AArch64 `ctrRow_allocS_n4` at `n4`), and the thread pointer is
  kept by `KeepTP.exec_tp` with no code premise (AArch64 through `NoMsrAt`, no `msr`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `inv0_downH`.
-/
import Spike.Lib.X64HelloLandR
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloRdHAb
import Spike.Lib.X64HelloHAbW
import Spike.Lib.X64HelloHabCtlRd
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloRodata
import Spike.Lib.X64HelloC0S
import Spike.Lib.X64WakeAbOffW
import Spike.Lib.X64HelloClH
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloMainPreT
import Spike.Lib.X64HelloLand3
import Spike.Lib.X64Hello1RodataTP
import Spike.Lib.X64AllocNR
import Spike.Lib.X64CallResume
import Spike.Lib.X64KeepUn
import Spike.Lib.X64WakeStartH0X
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64WakeTP
import Spike.Lib.X64GfpS
import Spike.Lib.X64WakeLand5
import Spike.Lib.LowerX64.LandHu
import Spike.Lib.X64HelloCtrF
import Spike.Lib.X64WakeRootUL

namespace Spike.Lib.X64.HelloPh.RootUL

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib (FragS PlaceWX)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- **The root's context with the child's stack unmapped** (wake's `RootUL.CtxRU`). -/
def CtxU (Ctx : FragS isa) : FragS isa := fun s c fs => Ctx s c fs ∧ U (R1) s

/-! ## The counter add's row with the thread pointer and `r` unmapped kept -/

section Row

variable {p : Prog} {exe : _root_.Executable} {endPc : Int64} {cells : List (Directive × Nat)} {kp : Nat}
  {ref : List TermRun.Frame → Spike.Lib.MemSide isa}
  {Gc : List TermRun.Frame → Spike.Lib.MemSide isa → Spike.Lib.Region → (MachineData → Prop) →
    Spike.Lib.X64.Alloc.Call → Prop}
  {M : List TermRun.Frame → Spike.Lib.MemSide isa} {J : Spike.Lib.X64ConsumerS.InvS} {L0 : Lbl} {ls0 : Lsize}

/-- **The counter add's row with `r` unmapped** (`RootUL.rootOpen_U`'s `hctr0` at a frame-indexed counter add):
the add keeps `TP t` (`KeepTP.exec_tp`) and `U r` (`KeepUn.exec_un`) into the landing at `c2`, so `hland` may
assume both. -/
theorem ctrRow_ofFTU [Executable.ValidLayout exe] {t : UInt64} {r : Scc.Sem.Range} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : Spike.Lib.X64.Alloc.allocIn cells = true)
    (hM : ∀ fs, M fs = { ref fs with xa := (M fs).xa })
    (hland : ∀ fs (ms0 : Spike.Lib.MemSide isa) R F q, ms0 = { ref fs with xa := ms0.xa } → Gc fs ms0 R F q →
      Spike.Lib.X64.HelloPh.Land.CtrOkS ms0 (_root_.Executable.labels exe).label R F q →
      ∀ s c, Spike.Lib.X64.At exe endPc R F
        (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms0 q .c2) s c →
        Spike.Lib.X64.KeepTP.TP t s → U r s → J L0 ls0 s c fs)
    {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (hC : Spike.Lib.X64.HelloPh.Land.CtrAtF ref exe endPc Gc s c fs) (htp : Spike.Lib.X64.KeepTP.TP t s)
    (hu : U r s) {c' : Spike.Lib.Ctl} {fs' : List TermRun.Frame} (hr : Spike.Lib.FrameRun p (c, fs) (c', fs')) :
    Spike.Lib.X64ConsumerA.CtrRow (M fs') (fun s' c'' => Spike.Lib.X64ConsumerA.PendA p J L0 ls0 s' c'' fs') s c' := by
  obtain ⟨ms0, R, F, q, hms, hGc, hok, hAt⟩ := hC
  obtain rfl : c = q.c0 := Spike.Lib.X64.WakeCtr.ctrAt_c0 hAt
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Spike.Lib.X64.HelloPh.CtrF.FrameRun.eq_of_site hr hok.oks.site)
  have hrow := Spike.Lib.X64.WakeCtr.ctrRow_allocS_c2 hp hend hin hok.fst hok.oks hok.mem hAt
  refine Spike.Lib.X64.WakeCtr.ctrRow_xa ?_ (show M fs' = { ms0 with xa := (M fs').xa } by rw [hM fs', hms])
  obtain ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, h7⟩ := hrow
  have hT := Spike.Lib.X64.KeepTP.exec_tp htp h1
  have hU := Spike.Lib.X64.KeepUn.exec_un hu h1
  refine ⟨k, op, g, x, τ, e, n, h1, h2, h3, h4, h5, h6, fun old hG hown hle hlo => ?_⟩
  obtain ⟨hG', hL⟩ := h7 old hG hown hle hlo
  refine ⟨hG', fun _ a h => Spike.Lib.X64.HelloPh.CtrF.site_not_ret hok.oks.site a h, _, _, .refl _, ?_⟩
  rcases hL with ⟨_, hj⟩ | ⟨y, _⟩
  · exact hland fs' ms0 R F q hms hGc hok _ _ hj (hT old) (hU old)
  · exact y.elim

end Row

end Spike.Lib.X64.HelloPh.RootUL

/-- info: 'Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU
