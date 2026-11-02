/-
**hello.w's level-1 context** (x86-64; the twin of `Spike/Lib/A64HelloLand1.lean`'s live part): the context
`Ctx1 l b n` that `HelloWf.W1H` asks at every write of the counter word at level 1, after rodata's allocation of
`l` at `b` with `n` cells, and the level's obligations into it.

Level 0 ends at rodata's landing, and `wc_main`'s box allocation is inside level 1: its counter add (at no frames,
under main's thread pointer) and the box's initialising store (`StAt`). Both are stated against a reference memory
side at the level's labels `upd LB l b` and sizes `updN (ls0T ls) l n` (`ref1H`); the level-0 `refH` is at `LB`
and cannot be reused. Rodata's counter add is level 0's, so it is not here.

- `ref1H`: the level's reference side (`msOfA` at the updated placement, no allocation fragment).
- `mwH`, `Jr1LH`, `GcM1H`, `GsH1`, `CtxR1H`: main's thread word; `Jr1L` on rodata's slice label at the level's
  labels; `wc_main`'s box call (pinned as its only producer supplies it: the first stack's top, the TCB at the
  caller's slot `-16`, `wc_main`'s entry at `JrT (JrRL …)` and its caller's at `Jr1LH`); the box store's landings
  at `ref1H … []` (`wc_main`'s entry pinned: `Jr1LH` and the TCB at the caller's slot `-16`); the context:
  `wc_main`'s counter add under main's thread pointer, or the box's store.
- `jr1LH_rbp`, `jr1LH_loc`: `Jr1LH`'s `%rbp`; `MainWcPS.hloc` at `Jr1LH` (from `JrT (JrRL …)` at `RM`).
- `hctx_main1H`: `WcWfR.wcPreW_WSgH`'s `hctx` at `CtxR1H` (at `ref1H`), at the pinned call.
- `hctx_st1H`: `Land3.hwr_stH`'s `hCtx` at `CtxR1H`.

## Differences from the AArch64 version

- `scc_rt_main` is entered by a `call`, so its region is `MainGlue.RS helloLsw TOP` (AArch64:
  `swR TOP (-helloLsw) 0`), `wc_main`'s is `wcR (RS helloLsw TOP) helloD` with `hi = 8`, the call's `CallerCells`
  reach `8` (AArch64: `0`), and the box's landing `bXH` is on the frame at the saved `%rbp`, `.fp (-8)` (as
  `Land3.hwr_stH`'s `hGs`).
- main's TCB reaches `wc_main` as `%r8` from the caller's slot `-16` (`Hello1.mWC`; AArch64: `x4`, slot `-80`), and
  the thread pointer is `tpOf (tcbS Ly)` (`fsBase`).
- `Jr1LH l b` is `HelloJr1.Jr1L (upd LB l b) mwH l` (AArch64 spells it out) with `%rbp` at `RM.addr (-8)`
  (`HelloM.JrT`'s, kept by the local run to the box's `new`): `RootHP.GJ1RH` pins `%rbp` at the box's landing
  (AArch64's ghost has no such pin), so `jr1LH_rbp` and `jr1LH_loc` are stated here.
- The box call returns to `.Lwc_main.x22` (`HelloWc`'s box call's `ra`; AArch64 `.L22_wc_main.sp0`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `GcM1H.gcMH`, `jr1LH_jr1H`,
  `hctx_main1U`.
-/
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloJr1L
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64HelloC0S

namespace Spike.Lib.X64.HelloPh.Land

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (Region MemSide FragS Frag PlaceWX)
open Spike.Lib.X64 (swR At FStable)
open Spike.Lib.X64.Flow.Ret0 (CallerCells pinA tpOf)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0 JrT)
open Spike.Lib.X64.Flow.HelloWc (wARH WcCtxH bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.Alloc (Call N)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.WakeCtr (StAt)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64.Flow.HelloJr1 (Jr1L JrRL)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

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

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RM" => RS helloLsw (TOP)

set_option hygiene false in
/-- The level's memory sides at a fragment `I`, the frames `fs`. -/
local notation "MS1" => fun (I : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
  (fs : List TermRun.Frame) => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (AR) I
    (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-- **The level's reference memory side** after rodata's allocation of `l` at `b`, `n` cells, at the frames `fs`:
the root's memory side at the updated placement with no allocation fragment (`refH`'s twin; the fragment enters
only `xa`). -/
noncomputable abbrev ref1H (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) : MemSide isa :=
  (MS1) (fun _ _ _ _ _ => False) l b n fs

/-- main's thread word `me` (`c0S`'s, `C0S.c0S_env`): a locative to main's thread-id label. -/
abbrev mwH : TermRun.Word := TermRun.cst (.loc ⟨Spike.Lib.X64WakeSrcDefs.mainTidLbl 2, 0⟩ 0)

/-- **`scc_rt_main` at the box's `new` on rodata's slice** (`HelloJr1.Jr1L` at the label `l`, the one rodata
allocated at `b`): the control `c0H` on `slW l` and `me`'s word `mwH`, the slice's registers at `upd LB l b`, and
`%rbp` at `scc_rt_main`'s saved `%rbp` (`RM.addr (-8)`, as `HelloM.JrT` records it). -/
def Jr1LH (l : WeakMem.AllocLabel) (b : Nat) (σ : FAS) (c : Spike.Lib.Ctl) : Prop :=
  Jr1L (Spike.Lib.X64ConsumerA.upd (LB) l b) mwH l σ c ∧ σ.regs.get64 .rbp = (RM).addr (-8)

/-- **`%rbp` at `Jr1LH`**: `scc_rt_main`'s saved `%rbp`. -/
theorem jr1LH_rbp {l : WeakMem.AllocLabel} {b : Nat} {σ : FAS} {c : Spike.Lib.Ctl} (h : Jr1LH hpw i0 l b σ c) :
    σ.regs.get64 .rbp = (RM).addr (-8) :=
  h.2

/-- **`MainWcPS.hloc` at `Jr1LH`** (`HelloJr1.jr1L_loc`, `%rbp` from `JrT`'s at `RM`): from `wc_rodata`'s return on
the slice at `l` the source reaches the box's `new` on `slW l`, the registers unchanged. -/
theorem jr1LH_loc {env : TermRun.Env} {tm : Ty} {l : WeakMem.AllocLabel} {b : Nat}
    (hme : TermRun.evalAt env (.var "me") = some (tm, [mwH])) (σ : FAS) (c : Spike.Lib.Ctl)
    (h : JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b) env l) (TV) (RM) σ c) :
    ∃ c', Spike.Lib.LocalRun helloSrc c c' ∧ Jr1LH hpw i0 l b σ c' := by
  obtain ⟨c', hr, hj⟩ := Spike.Lib.X64.Flow.HelloJr1.jr1L_loc hme σ c h
  exact ⟨c', hr, hj, h.2.2.2⟩

/-- **`wc_main`'s box call at level 1**: at no frames, a box allocation (`Call.OKB`) returning to
`.Lwc_main.x22`, at the first stack's top, the caller's slot `-16` holding main's TCB `pinA + 8`, in the region
`wARH (wcR RM helloD)` with `wc_main`'s frame condition at the start's `FS`, `wc_main`'s entry invariant at
`JrT (JrRL (upd LB l b) c0S.env l)` (`wc_rodata`'s return on the slice at `l`) and its caller's at `Jr1LH l b`.
These are the values its only producer supplies (through `hctx_main1H`). -/
def GcM1H (l : WeakMem.AllocLabel) (b : Nat) (fs : List TermRun.Frame) (ms0 : MemSide isa) (R : Region)
    (F : MachineData → Prop) (q : Call) : Prop :=
  fs = [] ∧ q.OKB ms0 (Ly).lab ∧ ∃ (σC : FAS) (m1 : MachineData) (σ1 : FAS),
    σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64 ∧ R = wARH (wcR (RM) helloD) ∧
    F = (fun m => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1 m ∧
      CallerCells (wcR (RM) helloD) (-144) (-160) 8 m ∧
      WcCtxH ms0 (Ly).lab (wcR (RM) helloD)
        (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b)
          Spike.Lib.X64.HelloPh.C0S.c0S.env l) (TV) (RM))).J σ1)
        (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m) ∧
    q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec

/-- **The box store's landings at level 1** (at `ref1H`): `bXH` at `ref1H l b n []` on `wc_main`'s frame at the
saved `%rbp` and its frame condition at the start's `FS`, under main's thread pointer, for one cell. `wc_main`'s
entry invariant is pinned: the caller's `Jr1` is `Jr1LH l b`, and the caller's slot `-16` (`mWC`'s `%r8`) holds
main's TCB, `pinA + 8`. -/
def GsH1 (l : WeakMem.AllocLabel) (b n : Nat) (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isa) : Prop :=
  ∃ (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS),
    σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64 ∧
    Lnd = fun l' A n' s c => n' = 1 ∧
      At (Ly).exe (Ly).endPc ((wcR (RS helloLsw v) helloD).fp (-8))
        (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
        (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l' A) s c ∧ TP (TV) s

/-- **The level-1 context** (`HelloWf.W1H`'s `Ctx1`): `wc_main`'s counter add (`GcM1H`, at no frames) under main's
thread pointer, or the box's store at `GsH1`, both at `ref1H l b n`. -/
def CtxR1H (l : WeakMem.AllocLabel) (b n : Nat) : FragS isa := fun s c fs =>
  (CtrAtF (ref1H (asm := asm) hpw i0 E rd ls l b n) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c fs ∧ TP (TV) s) ∨
    StAt (ref1H (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (GsH1 (asm := asm) hpw i0 E rd ls l b n) s c fs

/-! ## The level's obligations into the context -/

/-- **`WcWfR.wcPreW_WSgH`'s `hctx` at `CtxR1H`**: a counter add of a box call from `wc_main` returning to
`.Lwc_main.x22`, at no frames, under main's thread pointer, at the first stack's top, the caller's slot `-16`
main's TCB (`hslot`), `wc_main`'s entry at `JrT (JrRL (upd LB l b) c0S.env l)` and its caller's at `Jr1LH l b`,
is `CtxR1H`'s counter disjunct (`GcM1H` by construction; `CtrOkS` by `fstable_wARH` at the first stack's top and
`WordsNoneP` at the counter, `ctr_none_FS`). -/
theorem hctx_main1H (hc : Spike.Lib.X64.Rt.CtrZ o) (l : WeakMem.AllocLabel) (b n : Nat) {ms : MemSide isa}
    (hms : ms = { ref1H (asm := asm) hpw i0 E rd ls l b n [] with xa := ms.xa }) (σC : FAS)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) :
    ∀ q : Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (RM) helloD))
        (fun m => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1 m ∧
          CallerCells (wcR (RM) helloD) (-144) (-160) 8 m ∧
          WcCtxH ms (Ly).lab (wcR (RM) helloD)
            (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b)
              Spike.Lib.X64.HelloPh.C0S.c0S.env l) (TV) (RM))).J σ1)
            (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { ref1H (asm := asm) hpw i0 E rd ls l b n [] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩,
    ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · obtain ⟨-, hR0, hF0⟩ := fstable_FS hpw i0
    obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hR0 hF0
      (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
    exact fstable_wARH hR hF (by show (-helloD : Int) ≤ -304; decide) (by show (8 : Int) ≤ 8; decide)
  · -- the counter word is the arena's, whatever the placement (`ctr_none_FS`)
    exact ctr_none_FS (asm := asm) hpw i0 E rd ls hc (fs := []) (X := X) m hm.1.1

/-- **`GcM1H` is inhabited at the level's call** (the producer's values, `hctx_main1H`'s): at the level's memory
side, a box call returning to `.Lwc_main.x22` from the caller `σC` whose slot `-16` holds main's TCB (`hslot`),
any `m1`, `σ1`. -/
example (I : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat) (t : UInt64) (σC : FAS)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) (q : Call)
    (hq : q.OKB (Spike.Lib.X64.KeepTP.tpXa ((MS1) I l b n []) t) (Ly).lab)
    (hra : q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec) :
    GcM1H hpw i0 l b [] (Spike.Lib.X64.KeepTP.tpXa ((MS1) I l b n []) t) (wARH (wcR (RM) helloD))
      (fun m => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1 m ∧
        CallerCells (wcR (RM) helloD) (-144) (-160) 8 m ∧
        WcCtxH (Spike.Lib.X64.KeepTP.tpXa ((MS1) I l b n []) t) (Ly).lab (wcR (RM) helloD)
          (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b)
            Spike.Lib.X64.HelloPh.C0S.c0S.env l) (TV) (RM))).J σ1)
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m) q :=
  ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩

/-- **`Land3.hwr_stH`'s `hCtx` at `CtxR1H`**: the box's store at `GsH1` is `CtxR1H`'s store disjunct. -/
theorem hctx_st1H (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c, StAt (ref1H (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (GsH1 (asm := asm) hpw i0 E rd ls l b n) s c [] → CtxR1H (asm := asm) hpw i0 E rd ls l b n s c [] :=
  fun _ _ h => .inr h

end Spike.Lib.X64.HelloPh.Land

/-- info: 'Spike.Lib.X64.HelloPh.Land.hctx_main1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.hctx_main1H

/-- info: 'Spike.Lib.X64.HelloPh.Land.hctx_st1H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.hctx_st1H

/-- info: 'Spike.Lib.X64.HelloPh.Land.jr1LH_rbp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.jr1LH_rbp

/-- info: 'Spike.Lib.X64.HelloPh.Land.jr1LH_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.jr1LH_loc
