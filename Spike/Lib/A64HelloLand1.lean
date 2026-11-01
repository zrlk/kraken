/-
**hello.w's level-1 context** (AArch64; the level-1 twin of
`A64HelloLand`'s `CtxRH`): the context `Ctx1 l b n` that `HelloWf.W1H` asks at every write of the counter word at
level 1, after rodata's allocation of `l` at `b` with `n` cells, and the level's obligations into it.

Under level 0 ends at rodata's landing, and `wc_main`'s box allocation is inside level 1: its counter add
(`GcMH`, at no frames, under main's thread pointer) and the box's initialising store (`StAt`). Both are stated
against a reference memory side at the level's labels `upd LB l b` and sizes `updN (ls0T ls) l n` (`ref1H`); the
level-0 `refH` is at `LB` and cannot be reused. Rodata's counter add (`GcRdH`) is level 0's, so it is not here.

- `ref1H`: the level's reference side (`msOfA` at the updated placement, no allocation fragment).
- `mwH`, `Jr1LH`, `GcM1H`, `GsH1`, `CtxR1H`: main's thread word; `Jr1H` on rodata's slice label; `wc_main`'s box
  call (`GcMH` pinned as its only producer supplies it: the first stack's top, the TCB at the caller's slot `-80`,
  `wc_main`'s entry at `Level1I`'s `JrRL` and its caller's at `Jr1LH`); the box store's landings at `ref1H … []`
  (`wc_main`'s entry pinned: `Jr1LH` and the TCB at the caller's slot `-80`); the context: `wc_main`'s counter add
  under main's thread pointer, or the box's store.
- `GcM1H.gcMH`: `GcM1H` is a `GcMH`.
- `hctx_main1H`: `WcWfR.wcPreW_WSgH`'s `hctx` at `CtxR1H` (as `hctx_mainH`, at `ref1H`), at the pinned call.
- `hctx_st1H`: `Land3.hwr_stH`'s `hCtx` at `CtxR1H`.
- `hctx_main1U` (non-vacuity): `hctx_main1H` at the level's memory sides themselves (`tpXa (msOfA … I (upd LB l b)
  (updN (ls0T ls) l n) []) t`, any fragment `I`), no premise left but the counter add's state.
-/
import Spike.Lib.A64HelloLand
import Spike.Lib.A64HelloJr1
import Spike.Lib.A64HelloJr1L
import Spike.Lib.HelloGOf2H

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
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0 JrT)
open Spike.Lib.A64.Flow.HelloWc (wARH WcCtxH bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.Alloc (Call N)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.WakeCtr (StAt)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.A64.Flow.HelloJr1 (Jr1H SlRegs JrRL)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

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
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The level's memory sides at a fragment `I`, the frames `fs`. -/
local notation "MS1" => fun (I : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
  (fs : List TermRun.Frame) => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AR) I
    (Spike.Lib.A64ConsumerA.upd (LB) l b) (Spike.Lib.A64ConsumerA.updN (ls0T ls) l n) fs

/-- **The level's reference memory side** after rodata's allocation of `l` at `b`, `n` cells, at the frames `fs`:
the root's memory side at the updated placement with no allocation fragment (`refH`'s twin; the fragment enters
only `xa`). -/
noncomputable abbrev ref1H (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) : MemSide isaLSE2 :=
  (MS1) (fun _ _ _ _ _ => False) l b n fs

/-- main's thread word `me` (`c0S`'s, `C0S.c0S_env`): a locative to main's thread-id label. -/
abbrev mwH : TermRun.Word := TermRun.cst (.loc ⟨Spike.Lib.WakeT1.mainTidLbl 2, 0⟩ 0)

/-- **`scc_rt_main` at the box's `new` on rodata's slice** (`HelloJr1.Jr1H` with its label `l`, the one rodata
allocated at `b`): the control `c0H` on `slW l` and `me`'s word `mwH`, the slice's registers at `upd LB l b`. -/
def Jr1LH (l : WeakMem.AllocLabel) (b : Nat) (σ : FAS) (c : Spike.Lib.Ctl) : Prop :=
  c = Spike.Lib.HelloMainPreSrc.c0H (TermRun.cst (.loc ⟨l, 0⟩ 0)) (TermRun.cst (.num 2)) (TermRun.cst (.num 13)) mwH ∧
    SlRegs (Spike.Lib.A64ConsumerA.upd (LB) l b) l σ

/-- `Jr1LH` is `Jr1H` at the level's labels. -/
theorem jr1LH_jr1H {l : WeakMem.AllocLabel} {b : Nat} {σ : FAS} {c : Spike.Lib.Ctl} (h : Jr1LH hpw i0 l b σ c) :
    Jr1H (Spike.Lib.A64ConsumerA.upd (LB) l b) mwH σ c :=
  ⟨l, h⟩

/-- **`wc_main`'s box call at level 1** (`GcMH` pinned): `GcMH` at the first stack's top, the caller's slot `-80`
holding main's TCB `pinA + 8`, `wc_main`'s entry invariant at `Level1I`'s `Jr` (`JrT (JrRL (upd LB l b) c0S.env l)`,
`wc_rodata`'s return on the slice at `l`) and its caller's at `Jr1LH l b`. These are the values its only producer
(`MainWcL1Wi.hWp_L1`, through `hctx_main1H`) supplies, and the ones the allocator's tail from `n4` needs (the
heap abort's control facts `HabCtlA.habCtlHA_jr1L`, the box landing `MainWcL1A.hxa_IU`, `wc_main`'s `hWp`/`hWs` at
`MainWcL1Wj`). -/
def GcM1H (l : WeakMem.AllocLabel) (b : Nat) (fs : List TermRun.Frame) (ms0 : MemSide isaLSE2) (R : Region)
    (F : MachineData → Prop) (q : Call) : Prop :=
  fs = [] ∧ q.OKB ms0 (Ly).lab ∧ ∃ (σC : FAS) (m1 : MachineData) (σ1 : FAS),
    σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64 ∧ R = wARH (wcR (swR (TOP) (-helloLsw) 0) helloD) ∧
    F = (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
      CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
      WcCtxH ms0 (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
        (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
          (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
        (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m) ∧
    q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec

/-- **`GcM1H` is a `GcMH`** (witnesses `TOP`, `JrT (JrRL …)`, `Jr1LH`). -/
theorem GcM1H.gcMH {l : WeakMem.AllocLabel} {b : Nat} {fs : List TermRun.Frame} {ms0 : MemSide isaLSE2}
    {R : Region} {F : MachineData → Prop} {q : Call} (h : GcM1H hpw i0 l b fs ms0 R F q) : GcMH hpw i0 fs ms0 R F q :=
  let ⟨hfs, hq, σC, m1, σ1, _, hR, hF, hra⟩ := h
  ⟨hfs, hq, _, σC, m1, σ1, _, _, hR, hF, hra⟩

/-- **The box store's landings at level 1** (`GsH`'s twin at `ref1H`): `bXH` at `ref1H l b n []` in `wc_main`'s
region and frame condition at the start's `FS`, under main's thread pointer, for one cell. `wc_main`'s entry
invariant is pinned (`HelloJr1`): the caller's `Jr1` is `Jr1LH l b` (`Jr1H` at the level's labels `upd LB l b` and
`me`'s word `mwH`, on rodata's slice label `l` itself), and the caller's slot `-80` (`mWC`'s `x4`) holds main's
TCB, `pinA + 8`. -/
def GsH1 (l : WeakMem.AllocLabel) (b n : Nat) (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isaLSE2) : Prop :=
  ∃ (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS),
    σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64 ∧
    Lnd = fun l' A n' s c => n' = 1 ∧
      At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
        (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
        (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l' A) s c ∧ TP (TV) s

/-- **The level-1 context** (`HelloWf.W1H`'s `Ctx1`): `wc_main`'s counter add (`GcM1H`, at no frames) under main's
thread pointer, or the box's store at `GsH1`, both at `ref1H l b n`. -/
def CtxR1H (l : WeakMem.AllocLabel) (b n : Nat) : FragS isaLSE2 := fun s c fs =>
  (CtrAtF (ref1H (asm := asm) hpw i0 E rd ls l b n) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c fs ∧ TP (TV) s) ∨
    StAt (ref1H (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b) (GsH1 (asm := asm)
        hpw i0 E rd ls l b n)
      s c fs

/-! ## The level's obligations into the context -/

/-- **`WcWfR.wcPreW_WSgH`'s `hctx` at `CtxR1H`**: a counter add of a box call from `wc_main` returning to `.sp0`,
at no frames, under main's thread pointer, at the first stack's top, the caller's slot `-80` main's TCB (`hslot`),
`wc_main`'s entry at `JrT (JrRL (upd LB l b) c0S.env l)` and its caller's at `Jr1LH l b`, is `CtxR1H`'s counter
disjunct (`GcM1H` by construction; `CtrOkS` by `fstable_wARH` at the first stack's top and `WordsNone` at the
counter, as `hctx_mainH`). -/
theorem hctx_main1H (hc : Spike.Lib.A64.Rt.CtrZ o) (l : WeakMem.AllocLabel) (b n : Nat) {ms : MemSide isaLSE2}
    (hms : ms = { ref1H (asm := asm) hpw i0 E rd ls l b n [] with xa := ms.xa }) (σC : FAS)
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) :
    ∀ q : Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (swR (TOP) (-helloLsw) 0) helloD))
        (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
          CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
          WcCtxH ms (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
            (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
              (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
            (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { ref1H (asm := asm) hpw i0 E rd ls l b n [] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩,
    ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · obtain ⟨hok, hal, hF0⟩ := fstable_FS hpw i0
    obtain ⟨hR, -, hF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF0
      (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
    exact fstable_wARH hR hF (by show (-helloD : Int) ≤ -304; decide) (by show (0 : Int) ≤ 0; decide)
  · -- the counter word is the arena's, whatever the placement (`ctr_none_FS`)
    exact ctr_none_FS (asm := asm) hpw i0 E rd ls hc (fs := []) (X := X) m hm.1.1

/-- **`GcM1H` is inhabited at the level's call** (the producer's values, `hctx_main1H`'s): at the level's memory
side, a box call returning to `.sp0` from the caller `σC` whose slot `-80` holds main's TCB (`hslot`; at the root
`Level1I.slot80_rdJ` from rodata's entry, the case split of `Level1HA.hB_landA`), any `m1`, `σ1`. -/
example (I : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat) (t : UInt64) (σC : FAS)
    (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) (q : Call)
    (hq : q.OKB (tpXa ((MS1) I l b n []) t) (Ly).lab) (hra : q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec) :
    GcM1H hpw i0 l b [] (tpXa ((MS1) I l b n []) t) (wARH (wcR (swR (TOP) (-helloLsw) 0) helloD))
      (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
        CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
        WcCtxH (tpXa ((MS1) I l b n []) t) (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
          (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
            (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m) q :=
  ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩

/-- **`Land3.hwr_stH`'s `hCtx` at `CtxR1H`**: the box's store at `GsH1` is `CtxR1H`'s store disjunct. -/
theorem hctx_st1H (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c, StAt (ref1H (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.A64ConsumerA.upd (LB) l b)
      (GsH1 (asm := asm) hpw i0 E rd ls l b n) s c [] → CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] :=
  fun _ _ h => .inr h

/-! ## At the level's memory sides (non-vacuity) -/

/-- **`hctx_main1H` at the level's memory side** `tpXa (msOfA … I (upd LB l b) (updN (ls0T ls) l n) []) t` (any
fragment `I`, any `t`): exactly `wcPreW_WSgH`'s `hctx` there at the pinned call, no premise left but `CtrZ` and
the caller's slot `-80`. -/
theorem hctx_main1U (hc : Spike.Lib.A64.Rt.CtrZ o) (I : Spike.Lib.A64ConsumerS.InvS) (l : WeakMem.AllocLabel)
    (b n : Nat) (t : UInt64) (σC : FAS) (hslot : σC.slot (-80) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData)
    (σ1 : FAS) :
    ∀ q : Call, q.OKB (tpXa ((MS1) I l b n []) t) (Ly).lab →
      q.ra = ((Ly).lab ".L22_wc_main.sp0").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (swR (TOP) (-helloLsw) 0) helloD))
        (fun m => wcF (swR (TOP) (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 (TOP)) m1 σ1 m ∧
          CallerCells (wcR (swR (TOP) (-helloLsw) 0) helloD) (-144) (-160) 0 m ∧
          WcCtxH (tpXa ((MS1) I l b n []) t) (Ly).lab (wcR (swR (TOP) (-helloLsw) 0) helloD)
            (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.A64ConsumerA.upd (LB) l b) Spike.Lib.A64.HelloPh.C0S.c0S.env l)
              (TV) (swR (TOP) (-helloLsw) 0))).J σ1)
            (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
        (N (Ly).lab (tpXa ((MS1) I l b n []) t) q .rmw) s c → TP (TV) s →
        CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] :=
  hctx_main1H hpw i0 E rd ls hc l b n rfl σC hslot m1 σ1

end Spike.Lib.A64.HelloPh.Land

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_main1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_main1H

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_st1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_st1H

/-- info: 'Spike.Lib.A64.HelloPh.Land.hctx_main1U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.hctx_main1U

/-- info: 'Spike.Lib.A64.HelloPh.Land.jr1LH_jr1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.jr1LH_jr1H

/-- info: 'Spike.Lib.A64.HelloPh.Land.GcM1H.gcMH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Land.GcM1H.gcMH
