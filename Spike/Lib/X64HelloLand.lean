/-
**hello's root context: the counter add at any site and frame list** (x86-64; the twin of
`Spike/Lib/A64HelloLand.lean`'s live part): the counter add's call facts at any allocation site and its states at a
frame-indexed reference side, the root's reference side, and the start's frame condition `FS` at the first stack's
top.

hello's start adds to the counter at two calls, at different frame lists: `wc_rodata`'s buffer call under main's
frame and `wc_main`'s box call at no frames. Wake's `WakeCtr.CtrAt` is at no frames and at a box call
(`CtrOk.okb`), so hello's is
- frame-indexed (`CtrAtF`): its reference memory side per frame list;
- site-generic (`CtrOkS`): the call's site premises `Call.OKS` (a buffer or a box allocation).

- `CtrOkS`, `CtrAtF`: the counter add's call facts at any site; the counter add's states at a frame-indexed
  reference side and call family. `CtrOk.toS`: wake's call facts are an instance.
- `refH`: the reference side (`msUH` with no allocation fragment).
- `GcRdH`: `wc_rodata`'s buffer call under main's frame (the root's `wc_rodata` counter add's call family).
- `ctr_none_FS`: the counter word is unloaded under the start's `FS` at the root's reference side.
- `fstable_FS`: the start's `FS` at the first stack's top is stable in the new stack's callee region.

## Differences from the AArch64 version

- `FS` (`X64.WakePh.MainGlue.FS`) carries `call scc_rt_main`'s `CallerCells` (AArch64: `WordsNoneP ∧ swFSL` only),
  so it is stable in the callee region `MainGlue.RS helloLsw top` (`Rt.mainEF_ok`), not in `swR top (-helloLsw) 0`;
  `fstable_FS` gives `swR`'s and `RS`'s `OK` and no alignment (x86-64's `Hello1.mR_ok` asks none).
- No import of `HelloHrdArena`: this part uses none of its constants (AArch64 imports it for the chain only).
- `GcRdH`'s caller invariant `StartWcS.rdJH` takes `scc_rt_main`'s region (x86-64's `mNC` pins `%rbp` in it), so
  it is `rdJH lab (RS helloLsw v) …` at the call's base `v`; the call returns to `.Lwc_rodata.x15` (AArch64
  `.L19_wc_rodata.sp0`) and its `CallerCells` reach `8` (AArch64 `0`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `GcMH`, `GsH`, `CtxRH`,
  `ctrAtF_of_ctrAt`, `hctx_rdH`, `hctx_mainH`, `hctx_stH`, `hctx_rdU`, `hctx_mainU`.
-/
import Spike.Lib.X64HelloLand3
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64HelloFrameD
import Spike.Lib.Rt.X64StartEF
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloC0S

namespace Spike.Lib.X64.HelloPh.Land

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (Region MemSide FragS PlaceWX)
open Spike.Lib.X64 (swR At FStable)
open Spike.Lib.X64.Flow.Ret0 (CallerCells tpOf)
open Spike.Lib.X64.Flow.Hello1 (mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (RdCtx)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.WakeCtr (CtrOk)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUH)

/-! ## The counter add at any site and frame list -/

/-- **The counter add's call facts at any allocation site** (wake's `WakeCtr.CtrOk` with the site premises
`Call.OKS` for `Call.OKB`): the site premises, the frame stable, the counter word unloaded. -/
structure CtrOkS (ms : MemSide isa) (lab : Label → Int64) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop where
  oks : q.OKS ms lab
  fst : FStable R F
  mem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none

/-- **The counter add's states at a frame-indexed reference side** (wake's `WakeCtr.CtrAt` at any frames):
`scc_rt_alloc`'s `rmw` node for a call `Gc fs` admits at the frames `fs`, with `CtrOkS`, at a memory side `ms0`
that is `ref fs` but for `xa`. -/
def CtrAtF (ref : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64)
    (Gc : List TermRun.Frame → MemSide isa → Region → (MachineData → Prop) → Call → Prop) : FragS isa :=
  fun s c fs => ∃ (ms0 : MemSide isa) (R : Region) (F : MachineData → Prop) (q : Call),
    ms0 = { ref fs with xa := ms0.xa } ∧ Gc fs ms0 R F q ∧ CtrOkS ms0 (_root_.Executable.labels exe).label R F q ∧
    At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c

/-- Wake's call facts are ones at the call's site. -/
theorem _root_.Spike.Lib.X64.WakeCtr.CtrOk.toS {ms : MemSide isa} {lab : Label → Int64} {R : Region}
    {F : MachineData → Prop} {q : Call} (h : CtrOk ms lab R F q) : CtrOkS ms lab R F q :=
  ⟨h.okb.toS, h.fst, h.mem⟩

/-! ## The root's reference side and the start's frame condition -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

/-- **The reference memory side at the frames `fs`**: the root's memory side `msUH` with no allocation fragment
(wake's `refW`; `msUH`'s fragment enters only `xa`). -/
noncomputable abbrev refH (fs : List TermRun.Frame) : MemSide isa :=
  msUH (asm := asm) hpw i0 E rd (fun _ _ _ _ _ => False) ls fs

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root, at `scc_rt_main`'s region `RS helloLsw v` (x86-64's `mNC`
reads it). -/
local notation "J'" => fun v : BitVec 64 =>
  Spike.Lib.X64.HelloPh.StartWcS.rdJH (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 Spike.Lib.X64.HelloPh.C0S.c0S)

set_option hygiene false in
/-- main's frame at the root. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH Spike.Lib.X64.HelloPh.C0S.c0S.env

/-- **`wc_rodata`'s buffer call**: under main's frame, a buffer allocation (`Call.OK`) returning to
`.Lwc_rodata.x15`, in the region `aR (mR (RS helloLsw v))` with `wc_rodata`'s frame condition at the start's `FS`
and the caller's entry invariant `J' v`. -/
def GcRdH (fs : List TermRun.Frame) (ms0 : MemSide isa) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop :=
  fs = [FR] ∧ q.OK ms0 (Ly).lab ∧ ∃ v m0 σC, R = aR (mR (RS helloLsw v)) ∧
    F = (fun m => mF (RS helloLsw v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m ∧
      CallerCells (mR (RS helloLsw v)) (-48) (-160) 8 m ∧
      RdCtx ms0 (Ly).lab (mR (RS helloLsw v)) (mRdJ0 ((J') v) σC) (mRdJ0 ((J') v) σC) q m) ∧
    q.ra = ((Ly).lab ".Lwc_rodata.x15").toBitVec

/-- **The counter word is unloaded under the start's `FS`** at the root's reference side (`WordsNoneP`, the
counter inside `.data`). -/
theorem ctr_none_FS (hc : Spike.Lib.X64.Rt.CtrZ o) {fs : List TermRun.Frame} {X} {k0 v : BitVec 64} :
    ∀ m, FS (Ly) (RS0) helloLsw k0 v m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 ({ refH (asm := asm) hpw i0 E rd ls fs with xa := X } : MemSide
          isa).ctr) 8 =
        none := by
  intro m hm
  have hL := Spike.Lib.PlaceWX.link IH hpw
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.X64.Rt.ArenaW.ctr_item_of_placeW hL hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 := Spike.Lib.X64.Rt.ArenaW.data_below_of_placeW hL
  show Mem.loadInt m.dmem (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) 8 = none
  refine hm.1.1.wn _ (.inr ?_)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega

/-- **The start's `FS` at the first stack's top is stable** in the new stack's callee region `RS helloLsw top`
(`wordsNoneP_swFSL_fstable` in `swR top (-helloLsw) 0`, then `Rt.mainEF_ok` for `call scc_rt_main`'s cells). -/
theorem fstable_FS :
    (swR (topS (Ly) 0#64) (-helloLsw) 0).OK ∧ (RS helloLsw (topS (Ly) 0#64)).OK ∧
      FStable (RS helloLsw (topS (Ly) 0#64)) (FS (Ly) (RS0) helloLsw 0#64 (topS (Ly) 0#64)) := by
  have hwf := Spike.Lib.PlaceWX.wf_link_of_placeWX IH hpw
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  have hok : (swR (topS (Ly) 0#64) (-helloLsw) 0).OK := by
    (try simp only [topS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
    exact Spike.Lib.X64.Rt.rt_hokD _ (by decide) (by decide)
  have hFwS := Spike.Lib.X64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.X64.Flow.Ret0.limA (tpOf (tcbS (Ly)))) (v := topS (Ly) 0#64) hwf hsub hok (by decide)
    (by decide)
    (by (try simp only [topS]); rw [Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rS0_subRD _ (by decide) (by decide))
    (by (try simp only [tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0]; exact Spike.Lib.X64.Rt.rt_hfit _)
    (by (try simp only [topS, tcbS]); rw [Spike.Lib.X64.Rt.pinA_lab0, Spike.Lib.X64.Rt.stacksA_lab0]
        exact Spike.Lib.X64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.X64.Rt.fitS_of_sub _ hsub)
  have hR2 := Spike.Lib.X64.Rt.mainEF_ok (tcb := tcbS (Ly)) (by decide) (by decide) hok hFwS
  exact ⟨hok, hR2.1, hR2.2⟩

end Spike.Lib.X64.HelloPh.Land

/-- info: 'Spike.Lib.X64.WakeCtr.CtrOk.toS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeCtr.CtrOk.toS

/-- info: 'Spike.Lib.X64.HelloPh.Land.ctr_none_FS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.ctr_none_FS

/-- info: 'Spike.Lib.X64.HelloPh.Land.fstable_FS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.fstable_FS
