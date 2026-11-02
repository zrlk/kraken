/-
**hello's root context with the child's stack unmapped** (x86-64; the twin of `Spike/Lib/A64HelloRootUL.lean`'s
live part, at hello's level-0 invariant `RootH0.inv0H`): `CtxU Ctx := Ctx ∧ U r1Of`, so the counter add's tail
(`LandRd.HLandRdU`, `U r1Of` at `c2`) gets the child's stack unmapped from the context itself. `inv0H` at `Ctx`
with `r1Of` unmapped is at `CtxU Ctx` (`inv0_upH`: `W0` monotone in its context, `WakePh.RootUL.w0_mono`; `GfpS`
carries `U r1Of`, `WakePh.RootUL.SegInvS.keepUn`, under the take of `rS0`, disjoint from `r1Of`), and the start
segment at `Ctx` is one at `CtxU Ctx` (`hst0_UH`, `U r1Of` true at the loaded thread). All generic in the context
`Ctx` (and in `inv1`, `inv2`: `msBotH` does not read the context).

- `CtxU`: the context with `r1Of` unmapped.
- `takeU_H`: `W0H`'s outside moves keep `r1Of` unmapped.
- `inv0_upH`: `inv0H` at `Ctx` with `r1Of` unmapped is at `CtxU Ctx`.
- `hst0_UH`: `hst0` at `CtxU Ctx` from `hst0` at `Ctx`.
- `ctrRow_ofFTU`: the counter add's row at a frame-indexed counter add with `TP t` and `U r` kept into the landing
  (the `hctr0` lift's row).

## Differences from the AArch64 version

- The layout is `RuntimeLayout.ofPlaceWX` at `X64.HelloImms.immsH` (AArch64 `ofPlaceW` at `C0S.immsH`).
- The stacks' bound is `X64WakeHClC.hbd_W` (from `stacks_lt`), so `takeU_H` and `inv0_upH` take no `a13data`
  premise (AArch64 through `StartPlaceLy.hsub1_W`); `hst0_UH`'s loaded thread is `WakePh.StartH0X.entry_U`'s
  (AArch64 `wideSt_threadAt` and `WakeOHinit.unowned_stack` inline).
- `ctrRow_ofFTU` takes the allocator's code from the layout (`hp : Lays exe cells kp`, `hend`, `hin`, under
  `Executable.ValidLayout exe`; AArch64 `hcode : ∀ ms0 q, Alloc.Code ms0 q exe endPc`), its row is
  `WakeCtr.ctrRow_allocS_c2`'s, landing at `c2` (AArch64 `ctrRow_allocS_n4` at `n4`), and the thread pointer is
  kept by `KeepTP.exec_tp` with no code premise (AArch64 through `NoMsrAt`, no `msr`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `inv0_downH`.
-/
import Spike.Lib.X64HelloLandRd
import Spike.Lib.X64HelloCtrF
import Spike.Lib.X64WakeRootUL

namespace Spike.Lib.X64.HelloPh.RootUL

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (SegInvS TakeCKS)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.X64.HelloPh.RootH0 (msBotH inv0H)
open Spike.Lib (FragS SegWS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeH1Inv (segInvS_weakW)
open Spike.Lib.X64.WakePh.RootUL (w0_mono)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The root's context with the child's stack unmapped** (wake's `RootUL.CtxRU`). -/
def CtxU (Ctx : FragS isa) : FragS isa := fun s c fs => Ctx s c fs ∧ U (R1) s

/-- **`W0H`'s outside moves keep `r1Of` unmapped** (wake's `RootUL.takeU`): at `X0WH`'s states the take at the site
label is `PhRec.K`, the take of `rS0` (`StartH0B.takeCKS_iffH`), disjoint from `r1Of` (`KeepUn.take_un`). -/
theorem takeU_H (E : Entry) (Dt : State → Prop) (Cx : FragS isa) (lsize : Lsize) (frM : TermRun.Frame) :
    ∀ s c fs, W0H (asm := asm) hpw IH E Dt Cx lsize frM s c fs → ∀ s',
      TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly)) s s' → U (R1) s → U (R1) s' := by
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  obtain ⟨h1l, h1s⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  rw [(Ly).lab_stacks] at h1l hbd'
  have hSl : (RS).lo = (Ly).stacksA.toNat := by
    show ((Ly).stacksA + 0#64).toNat = _; rw [BitVec.add_zero]
  have hSs : (RS).size = 16384 := rfl
  have hw1 : (R1).lo + (R1).size ≤ 2 ^ 64 := by omega
  have hwS : (RS).lo + (RS).size ≤ 2 ^ 64 := by omega
  have hd : (R1).Disjoint (RS) := by unfold Scc.Sem.Range.Disjoint; omega
  intro s c fs hW s' hk hu
  obtain ⟨-, pm, rfl⟩ := (Spike.Lib.X64.HelloPh.StartH0B.takeCKS_iffH hpw IH hW.2.1).1 hk
  exact Spike.Lib.X64.KeepUn.take_un pm hd hw1 hwS hu

variable (E : Entry) (rd : TermRun.Word → Prop) (Ctx : FragS isa) (ls : Lsize) (frM : TermRun.Frame)
  (inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa)
  (inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa)

set_option hygiene false in
local notation "I0" => fun Cx => inv0H (asm := asm) hpw IH E rd Cx ls ls frM inv1 inv2

/-- **`inv0H` at `Ctx` with `r1Of` unmapped is at `CtxU Ctx`** (wake's `RootUL.inv0_up`; `keepUn` on `GfpS`,
`takeU_H`). -/
theorem inv0_upH : ∀ s c fs, (I0) Ctx s c fs → U (R1) s → (I0) (CtxU hpw i0 Ctx) s c fs :=
  fun s c fs hi hu => Spike.Lib.X64GfpS.le_gfpS (segInvS_weakW
    (Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn (fun _ => rfl) Spike.Lib.X64GfpS.segInvS_gfpS
      (takeU_H hpw i0 E _ _ _ _)) fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩) s c fs ⟨hi, hu⟩

/-- **`hst0` at `CtxU Ctx`** from `hst0` at `Ctx` (wake's `RootUL.hst0_U`): its witness with `U r1Of` (`keepUn`),
true at the loaded thread (`WakePh.StartH0X.entry_U`). -/
theorem hst0_UH (hE : E.Ok (Ly).Λ) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hst0 : SegWS (W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (L0T (Ly).Λ)
      (msBotH (asm := asm) hpw IH E rd ls inv1 inv2) (StartPH hpw IH E) (fun _ _ _ => False)) :
    SegWS (W0H (asm := asm) hpw IH E DtW (CtxU hpw i0 Ctx) (ls0T ls) frM)
      (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) helloSrc (L0T (Ly).Λ)
      (msBotH (asm := asm) hpw IH E rd ls inv1 inv2) (StartPH hpw IH E) (fun _ _ _ => False) := by
  obtain ⟨inv, hP, hS⟩ := Spike.Lib.X64ConsumerA.SegInvS.ofSegWS hst0
  have hS' := segInvS_weakW (Spike.Lib.X64.WakePh.RootUL.SegInvS.keepUn (fun _ => rfl) hS
      (takeU_H hpw i0 E _ _ _ _))
    (W := W0H (asm := asm) hpw IH E DtW (CtxU hpw i0 Ctx) (ls0T ls) frM) fun _ _ _ h => w0_mono h.1 fun hc => ⟨hc, h.2⟩
  refine ⟨fun s c fs => inv s c fs ∧ U (R1) s, fun s c fs hp => ⟨hP s c fs hp, ?_⟩,
    fun s c fs hi => (hS' s c fs hi).1,
    fun s c fs hi => ⟨fun hk => ((hS' s c fs hi).2.1 hk).mono fun _ _ _ h => h.mono fun _ _ _ => .inl,
      (hS' s c fs hi).2.2.mono fun _ _ _ => .inl⟩⟩
  obtain ⟨rfl, -, -⟩ := hp
  exact Spike.Lib.X64.WakePh.StartH0X.entry_U (hpw := hpw) (i := IH) hE.1 hA13 _ _

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

/-- info: 'Spike.Lib.X64.HelloPh.RootUL.takeU_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootUL.takeU_H

/-- info: 'Spike.Lib.X64.HelloPh.RootUL.inv0_upH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootUL.inv0_upH

/-- info: 'Spike.Lib.X64.HelloPh.RootUL.hst0_UH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootUL.hst0_UH

/-- info: 'Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootUL.ctrRow_ofFTU
