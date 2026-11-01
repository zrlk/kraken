/-
**hello.w's root context** (AArch64; the twin of `Spike/Lib/A64WakeLand.lean`'s `CtxR` and
`Spike/Lib/A64WakeLand3.lean`'s `hctx_R` at helloProg): the context `Ctx` the root's `W0H` asks at every write of
the counter word (`HelloRootO.helloDR`'s `Ctx`), and the start's obligations into it.

hello's start adds to the counter at two calls, at different frame lists: `wc_rodata`'s buffer call (returning to
`.L19_wc_rodata.sp0`, frame 48) under main's frame `frH c0S.env`, and `wc_main`'s box call (returning to
`.L22_wc_main.sp0`, frame 144) at no frames, under main's thread pointer. Wake's `WakeCtr.CtxT` is at no frames
(`CtrAt`'s `fs = []`) and at a box call (`CtrOk.okb`), so hello's context is
- frame-indexed (`CtrAtF`): its reference memory side per frame list, `msOfA`'s `pl` reading the frames;
- site-generic (`CtrOkS`): the call's site premises `Call.OKS` (a buffer or a box allocation), the site's own
  premises (`Call.OK`, `Call.OKB`) in the call family `Gc`.

- `CtrOkS`, `CtrAtF`: the counter add's call facts at any site; the counter add's states at a frame-indexed
  reference side and call family. `CtrOk.toS`, `ctrAtF_of_ctrAt`: wake's are instances.
- `refH`, `GcRdH`, `GcMH`, `GsH`, `CtxRH`: the reference side (`msUH` with no allocation fragment), the two calls,
  the box store's landings, the context: `wc_rodata`'s counter add, or `wc_main`'s under main's thread pointer, or
  the box's store (`StAt`, as wake's). The `wc_rodata` add is also under main's thread pointer (the root's `hrd` at
  `WakeWc.tpG`, L0-tpG), for its landing's `StartH0H1.RdLandH`.
- `hctx_rdH`: `HrdS.hrd_WSHF`'s `hctx` at `CtxRH` (its `CtrAtF` disjunct at `GcRdH`; `CtrOkS` by `fstable_aRH` at
  the first stack's top and `WordsNone` at the counter).
- `hctx_mainH`: `WcWfR.wcPreW_WSgH`'s `hctx` at `CtxRH` (at `GcMH` under the thread pointer; `fstable_wARH`).
- `hctx_stH`: `Land3.hwr_stH`'s `hCtx` at `CtxRH`.
- `hctx_rdU`, `hctx_mainU` (non-vacuity): `hctx_rdH`/`hctx_mainH` at the root's memory sides themselves (`msUH` at
  any fragment `I`; `tpXa` of it for the box call), no premise left but the counter add's state: every counter add
  the root's start reaches is in `CtxRH`.

The consumer side (`W0`'s counter row at `CtxRH`, wake's `hctr0_R`/`hnew0_R`) is not here.
-/
import Spike.Lib.A64HelloHrdArena
import Spike.Lib.A64HelloLand3

namespace Spike.Lib.A64.HelloPh.Land

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib (Region MemSide FragS Frag)
open Spike.Lib.A64.Flow (swR At FStable)
open Spike.Lib.A64.Flow.Ret0 (CallerCells pinA)
open Spike.Lib.A64.Flow.Hello1 (mR mF mRdJ0 mWC aR)
open Spike.Lib.A64.Flow.HelloRd (RdCtx)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wARH WcCtxH bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.WakeCtr (CtrAt CtrOk StAt)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.WakeLoadT (L0T)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-! ## The counter add at any site and frame list -/

/-- **The counter add's call facts at any allocation site** (wake's `WakeCtr.CtrOk` with the site premises
`Call.OKS` for `Call.OKB`): the site premises, the frame stable, the counter word unloaded. -/
structure CtrOkS (ms : MemSide isaLSE2) (lab : Label → Int64) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop where
  oks : q.OKS ms lab
  fst : FStable R F
  mem : ∀ m, F m → Mem.loadInt m.dmem (BitVec.ofNat 64 ms.ctr) 8 = none

/-- **The counter add's states at a frame-indexed reference side** (wake's `WakeCtr.CtrAt` at any frames):
`scc_rt_alloc`'s `rmw` node for a call `Gc fs` admits at the frames `fs`, with `CtrOkS`, at a memory side `ms0`
that is `ref fs` but for `xa`. -/
def CtrAtF (ref : List TermRun.Frame → MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64)
    (Gc : List TermRun.Frame → MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop) : FragS isaLSE2 :=
  fun s c fs => ∃ (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call),
    ms0 = { ref fs with xa := ms0.xa } ∧ Gc fs ms0 R F q ∧ CtrOkS ms0 (_root_.Executable.labels exe).label R F q ∧
    At exe endPc R F (N (_root_.Executable.labels exe).label ms0 q .rmw) s c

/-- Wake's call facts are ones at the call's site. -/
theorem _root_.Spike.Lib.A64.WakeCtr.CtrOk.toS {ms : MemSide isaLSE2} {lab : Label → Int64} {R : Region}
    {F : MachineData → Prop} {q : Call} (h : CtrOk ms lab R F q) : CtrOkS ms lab R F q :=
  ⟨h.okb.toS, h.fst, h.mem⟩

/-- **Wake's counter add is one at a frame-indexed reference side**: `CtrAt ref Gc` is `CtrAtF` at the constant
reference side and the call family `Gc` at no frames. -/
theorem ctrAtF_of_ctrAt {ref : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {Gc : MemSide isaLSE2 → Region → (MachineData → Prop) → Call → Prop} {s : State} {c : Spike.Lib.Ctl}
    {fs : List TermRun.Frame} (h : CtrAt ref exe endPc Gc s c fs) :
    CtrAtF (fun _ => ref) exe endPc (fun fs ms R F q => fs = [] ∧ Gc ms R F q) s c fs := by
  obtain ⟨rfl, ms0, R, F, q, hms, hGc, hok, hAt⟩ := h
  exact ⟨ms0, R, F, q, hms, ⟨rfl, hGc⟩, hok.toS, hAt⟩

/-! ## The root's context -/

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (as `StartH0U`). -/
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- `wc_rodata`'s caller's entry invariant at the root (`StartH0U`'s `J'`). -/
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
/-- main's frame at the root (`StartH0U`'s `FR`). -/
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

/-- **The reference memory side at the frames `fs`**: the root's memory side `msUH` with no allocation fragment
(wake's `refW`; `msUH`'s fragment enters only `xa`). -/
noncomputable abbrev refH (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  msUH (asm := asm) hpw i0 E rd (fun _ _ _ _ _ => False) ls fs

/-- **`wc_rodata`'s buffer call** (`hrd_WSHF`'s): under main's frame, a buffer allocation (`Call.OK`) returning
to `.L19_wc_rodata.sp0`, in the region `aR (mR (swR v (-helloLsw) 0))` with `wc_rodata`'s frame condition at
the start's `FS` and the caller's entry invariant `J'`. -/
def GcRdH (fs : List TermRun.Frame) (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop :=
  fs = [FR] ∧ q.OK ms0 (Ly).lab ∧ ∃ v m0 σC, R = aR (mR (swR v (-helloLsw) 0)) ∧
    F = (fun m => mF (swR v (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m ∧
      CallerCells (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 m ∧
      RdCtx ms0 (Ly).lab (mR (swR v (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0 (J') σC) q m) ∧
    q.ra = ((Ly).lab ".L19_wc_rodata.sp0").toBitVec

/-- **`wc_main`'s box call** (`MainWcPS.hWp`'s): at no frames, a box allocation (`Call.OKB`) returning to
`.L22_wc_main.sp0`, in the region `wARH (wcR (swR v (-helloLsw) 0) helloD)` with `wc_main`'s frame condition at
the start's `FS` and `wc_main`'s entry invariants from `mWC … Jr`, `mWC … Jr1`. -/
def GcMH (fs : List TermRun.Frame) (ms0 : MemSide isaLSE2) (R : Region) (F : MachineData → Prop) (q : Call) :
    Prop :=
  fs = [] ∧ q.OKB ms0 (Ly).lab ∧ ∃ (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS)
    (Jr Jr1 : FAS → Spike.Lib.Ctl → Prop), R = wARH (wcR (swR v (-helloLsw) 0) helloD) ∧
    F = (fun m => wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m ∧
      CallerCells (wcR (swR v (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
      WcCtxH ms0 (Ly).lab (wcR (swR v (-helloLsw) 0) helloD) (wcJ0 (mWC (Ly).lab σC Jr).J σ1)
        (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) q m) ∧
    q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec

/-- **The box store's landings** (`Land3.hwr_stH`'s `Gs` at `MainWcPS.hWs`): `bXH` at `refH []` in `wc_main`'s
region and frame condition at the start's `FS`, under main's thread pointer, for one cell. -/
def GsH (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) : Prop :=
  ∃ (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS) (Jr1 : FAS → Spike.Lib.Ctl → Prop),
    Lnd = fun l A n s c => n = 1 ∧
      At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
        (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
        (bXH (refH (asm := asm) hpw i0 E rd ls []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) l A) s c ∧ TP (TV) s

/-- **The root's context** (wake's `CtxR`): `wc_rodata`'s counter add (`GcRdH`, under main's frame), or
`wc_main`'s (`GcMH`, at no frames), both under main's thread pointer, or the box's store at `GsH`. -/
def CtxRH : FragS isaLSE2 := fun s c fs =>
  (CtrAtF (refH (asm := asm) hpw i0 E rd ls) (Ly).exe (Ly).endPc (GcRdH hpw i0) s c fs ∧ TP (TV) s) ∨
    (CtrAtF (refH (asm := asm) hpw i0 E rd ls) (Ly).exe (Ly).endPc (GcMH hpw i0) s c fs ∧ TP (TV) s) ∨
    StAt (refH (asm := asm) hpw i0 E rd ls []) helloSrc (LB) (GsH (asm := asm) hpw i0 E rd ls) s c fs

/-! ## The start's counter adds are in the context -/

/-- **The counter word is unloaded under the start's `FS`** at the root's reference side (`WordsNone`, the counter
inside `.data`). -/
theorem ctr_none_FS (hc : Spike.Lib.A64.Rt.CtrZ o) {fs : List TermRun.Frame} {X} {k0 v : BitVec 64} :
    ∀ m, FS (Ly) (RS) helloLsw k0 v m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 ({ refH (asm := asm) hpw i0 E rd ls fs with xa := X } : MemSide
          isaLSE2).ctr) 8 =
        none := by
  intro m hm
  obtain ⟨hc1, hc2, -⟩ := Spike.Lib.A64.Rt.ArenaW.ctr_item_of_placeW (Spike.Lib.PlaceW.link IH hpw) hc
  have hc1' : (Ly).Λ.data.lo ≤ Scc.Cert.PlaceOK.heapUseOf (Ly).Λ := hc1
  have hc2' : Scc.Cert.PlaceOK.heapUseOf (Ly).Λ + 8 ≤ (Ly).Λ.data.lo + (Ly).Λ.data.size := hc2
  have hdb : (Ly).Λ.data.lo + (Ly).Λ.data.size ≤ 2 ^ 32 :=
    Spike.Lib.A64.Rt.ArenaW.data_below_of_placeW (Spike.Lib.PlaceW.link IH hpw)
  show Mem.loadInt m.dmem (BitVec.ofNat 64 (Scc.Cert.PlaceOK.heapUseOf (Ly).Λ)) 8 = none
  refine hm.1.wn _ (.inr ?_)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold Spike.Lib.DmemPriv.WordIn Scc.Sem.Range.contains; omega

/-- **The start's `FS` at the first stack's top is stable** in `swR top (-helloLsw) 0` (`wordsNoneP_swFSL_fstable`,
as `StartH0C.hello_hab_closed`). -/
theorem fstable_FS :
    (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).OK ∧
      (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).base.toNat % 16 = 0 ∧
      FStable (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0)
        (FS (Ly) (RS) helloLsw 0#64 (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64)) := by
  have hwf := Spike.Lib.PlaceW.wf_link_of_placeW IH hpw
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hok : (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0).OK := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ (by decide) (by decide)
  refine ⟨hok, by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_h16 _, ?_⟩
  exact Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable
    (a := Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)))
    (v := Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) hwf hsub hok (by decide) (by decide)
    (by rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rS0_subRD _ (by decide) (by decide))
    (by rw [Spike.Lib.A64.Rt.pinA_lab0]; exact Spike.Lib.A64.Rt.rt_hfit _)
    (by rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.stacksA_lab0]
        exact Spike.Lib.A64.Rt.rt_houtD _ (by decide) (by decide))
    (Spike.Lib.A64.Rt.fitS_of_sub _ hsub)

/-- **`HrdS.hrd_WSHF`'s `hctx` at `CtxRH`**: a counter add of a buffer call from `wc_rodata` returning to `.sp0`,
under main's frame and thread pointer (the root's `hrd` is asked only there, `WakeWc.tpG`), is `CtxRH`'s `wc_rodata`
disjunct (`GcRdH` by construction; `CtrOkS` by `fstable_aRH` at the
first stack's top and `WordsNone` at the counter). -/
theorem hctx_rdH (hc : Spike.Lib.A64.Rt.CtrZ o) {ms : MemSide isaLSE2}
    (hms : ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := ms.xa }) (v : BitVec 64) (m0 : MachineData) (σC :
        FAS) :
    ∀ q : Call, q.OK ms (Ly).lab → q.ra = ((Ly).lab ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0)))
        (fun m => mF (swR v (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 m ∧
          RdCtx ms (Ly).lab (mR (swR v (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0 (J') σC) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRH (asm := asm) hpw i0 E rd ls s c [FR] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refH (asm := asm) hpw i0 E rd ls [FR] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, v, m0, σC, rfl, rfl, hra⟩, ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
    case neg => exact fun m _ hm => (hv hm.1.1.2.1.1).elim
    subst hv
    obtain ⟨hok, hal, hF0⟩ := fstable_FS hpw i0
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.Hello1.mR_ok hok hal hF0
      (by show (-helloLsw : Int) ≤ -288; decide) (by show (0 : Int) ≤ 0; decide) m0 σC
    exact fstable_aRH hR hF (by show (-208 : Int) ≤ -208; decide) (by show (0 : Int) ≤ 0; decide)
  · exact ctr_none_FS (asm := asm) hpw i0 E rd ls hc m hm.1.1

/-- **`WcWfR.wcPreW_WSgH`'s `hctx` at `CtxRH`**: a counter add of a box call from `wc_main` returning to `.sp0`,
at no frames, under main's thread pointer, is `CtxRH`'s `wc_main` disjunct (`GcMH` by construction; `CtrOkS` by
`fstable_wARH` at the first stack's top and `WordsNone` at the counter). -/
theorem hctx_mainH (hc : Spike.Lib.A64.Rt.CtrZ o) {ms : MemSide isaLSE2}
    (hms : ms = { refH (asm := asm) hpw i0 E rd ls [] with xa := ms.xa }) (v : BitVec 64) (σC : FAS) (m1 : MachineData)
    (σ1 : FAS) (Jr Jr1 : FAS → Spike.Lib.Ctl → Prop) :
    ∀ q : Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (swR v (-helloLsw) 0) helloD))
        (fun m => wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m ∧
          CallerCells (wcR (swR v (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
          WcCtxH ms (Ly).lab (wcR (swR v (-helloLsw) 0) helloD) (wcJ0 (mWC (Ly).lab σC Jr).J σ1)
            (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxRH (asm := asm) hpw i0 E rd ls s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { refH (asm := asm) hpw i0 E rd ls [] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inr (.inl ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, v, σC, m1, σ1, Jr, Jr1, rfl, rfl, hra⟩,
    ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩)
  · by_cases hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64
    case neg => exact fun m _ hm => (hv hm.1.1.2.1.1).elim
    subst hv
    obtain ⟨hok, hal, hF0⟩ := fstable_FS hpw i0
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF0
      (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
    exact fstable_wARH hR hF (by show (-helloD : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
  · exact ctr_none_FS (asm := asm) hpw i0 E rd ls hc m hm.1.1

/-- **`Land3.hwr_stH`'s `hCtx` at `CtxRH`**: the box's store at `GsH` is `CtxRH`'s store disjunct. -/
theorem hctx_stH :
    ∀ s c, StAt (refH (asm := asm) hpw i0 E rd ls []) helloSrc (LB) (GsH (asm := asm) hpw i0 E rd
        ls) s c [] → CtxRH (asm := asm) hpw i0 E rd ls s c [] :=
  fun _ _ h => .inr (.inr h)

/-! ## At the root's memory sides (non-vacuity) -/

/-- **`hctx_rdH` at the root's memory side** `msUH … I … [FR]` (`StartH0U.hst0_ofHU_i0`'s `hrd`'s, any fragment
`I`): exactly `hrd_WSHF`'s `hctx` there under main's thread pointer, no premise left but the counter's word in
`.data` (`CtrZ`). -/
theorem hctx_rdU (hc : Spike.Lib.A64.Rt.CtrZ o) (I : Spike.Lib.A64ConsumerS.InvS) (v : BitVec 64) (m0 : MachineData)
    (σC : FAS) :
    ∀ q : Call, q.OK (msUH (asm := asm) hpw i0 E rd I ls [FR]) (Ly).lab → q.ra = ((Ly).lab
        ".L19_wc_rodata.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0)))
        (fun m => mF (swR v (-helloLsw) 0) (FS (Ly) (RS) helloLsw 0#64 v) m0 σC m ∧
          CallerCells (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 m ∧
          RdCtx (msUH (asm := asm) hpw i0 E rd I ls [FR]) (Ly).lab (mR (swR v (-helloLsw) 0)) (mRdJ0 (J') σC) (mRdJ0
              (J') σC)
            q m)
        (N (Ly).lab (msUH (asm := asm) hpw i0 E rd I ls [FR]) q .rmw) s c → TP (TV) s → CtxRH (asm :=
            asm) hpw i0 E rd ls s c [FR] :=
  hctx_rdH hpw i0 E rd ls hc rfl v m0 σC

/-- **`hctx_mainH` at the root's memory side** `tpXa (msUH … I … []) t` (`MainWcPS.hWp`'s at `StartH0U`'s `hPw`,
any fragment `I`, any `t`): exactly `wcPreW_WSgH`'s `hctx` there, no premise left but `CtrZ`. -/
theorem hctx_mainU (hc : Spike.Lib.A64.Rt.CtrZ o) (I : Spike.Lib.A64ConsumerS.InvS) (t : UInt64) (v : BitVec 64)
    (σC : FAS) (m1 : MachineData) (σ1 : FAS) (Jr Jr1 : FAS → Spike.Lib.Ctl → Prop) :
    ∀ q : Call, q.OKB (tpXa (msUH (asm := asm) hpw i0 E rd I ls []) t) (Ly).lab →
      q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (swR v (-helloLsw) 0) helloD))
        (fun m => wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m ∧
          CallerCells (wcR (swR v (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
          WcCtxH (tpXa (msUH (asm := asm) hpw i0 E rd I ls []) t) (Ly).lab (wcR (swR v (-helloLsw) 0) helloD)
            (wcJ0 (mWC (Ly).lab σC Jr).J σ1) (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) q m)
        (N (Ly).lab (tpXa (msUH (asm := asm) hpw i0 E rd I ls []) t) q .rmw) s c → TP (TV) s → CtxRH (asm :=
            asm) hpw i0 E rd ls s c [] :=
  hctx_mainH hpw i0 E rd ls hc rfl v σC m1 σ1 Jr Jr1

end Spike.Lib.A64.HelloPh.Land

/-- info: 'Spike.Lib.A64.WakeCtr.CtrOk.toS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakeCtr.CtrOk.toS

/-- info: 'Spike.Lib.A64.HelloPh.Land.ctrAtF_of_ctrAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.ctrAtF_of_ctrAt

/-- info: 'Spike.Lib.A64.HelloPh.Land.ctr_none_FS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.ctr_none_FS

/-- info: 'Spike.Lib.A64.HelloPh.Land.fstable_FS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.fstable_FS

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_rdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_rdH

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_mainH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_mainH

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_stH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_stH

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_rdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_rdU

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_mainU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_mainU
