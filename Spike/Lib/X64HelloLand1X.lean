/-
**hello.w's level-1 context at the root data's owned words** (x86-64; `X64HelloLand1`'s context at `ownGHXW`):
the root data's own map is `HelloPh.ownGHXW` (`ownGH` with both TCB self words appended, `X64HelloOwnSX`), so the
level-1 reference side and the context built on it are restated at that own map. `Jr1LH` and `GcM1H` do not read
the reference side and are reused.

- `ref1HX`: `ref1H` with the own map `ownGHXW`; `ref1HX_eq`: it is `ref1H` with that own field.
- `GsH1X`, `CtxR1HX`: `GsH1`, `CtxR1H` at `ref1HX`.
- `hctx_main1HX`: `hctx_main1H` at `ref1HX`/`CtxR1HX` (the counter word does not depend on the own map,
  `ctr_none_FS`).
- `hctx_st1HX`: `hctx_st1H` at `ref1HX`/`GsH1X`/`CtxR1HX`.

## Differences from the AArch64 version

Unlike AArch64, whose level-1 side owns `ownGH` only, x86-64's root data owns both TCB self words (`ownGHXW`), so
the level-1 side is stated at `ownGHXW` here.
-/
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloOwnSX

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
/-- The root data's owned words (`ownGH` and both TCB self words). -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
/-- The level's memory sides at a fragment `I`, the frames `fs`, at the owned words `OX`. -/
local notation "MS1X" => fun (I : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat)
  (fs : List TermRun.Frame) => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
    ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
    (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
    (fun s _ => (OX) s) (AR) I
    (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) fs

/-- **The level's reference memory side at the root data's owned words** after rodata's allocation of `l` at `b`,
`n` cells, at the frames `fs` (`ref1H` with the own map `ownGHXW`). -/
noncomputable abbrev ref1HX (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) : MemSide isa :=
  (MS1X) (fun _ _ _ _ _ => False) l b n fs

/-- **`ref1HX` is `ref1H` with the own map `ownGHXW`** (every other field agrees). -/
theorem ref1HX_eq (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) :
    ref1HX (asm := asm) hpw i0 E rd ls l b n fs =
      { ref1H (asm := asm) hpw i0 E rd ls l b n fs with own := fun s => (OX) s } :=
  rfl

/-- **The box store's landings at level 1, at `ref1HX`** (`GsH1` at `ref1HX`). -/
def GsH1X (l : WeakMem.AllocLabel) (b n : Nat) (Lnd : WeakMem.AllocLabel → Nat → Nat → Frag isa) : Prop :=
  ∃ (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS),
    σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64 ∧
    Lnd = fun l' A n' s c => n' = 1 ∧
      At (Ly).exe (Ly).endPc ((wcR (RS helloLsw v) helloD).fp (-8))
        (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
        (bXH (ref1HX (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l' A) s c ∧ TP (TV) s

/-- **The level-1 context at the root data's owned words** (`CtxR1H` at `ref1HX`): `wc_main`'s counter add
(`GcM1H`, at no frames) under main's thread pointer, or the box's store at `GsH1X`, both at `ref1HX l b n`. -/
def CtxR1HX (l : WeakMem.AllocLabel) (b n : Nat) : FragS isa := fun s c fs =>
  (CtrAtF (ref1HX (asm := asm) hpw i0 E rd ls l b n) (Ly).exe (Ly).endPc (GcM1H hpw i0 l b) s c fs ∧ TP (TV) s) ∨
    StAt (ref1HX (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (GsH1X (asm := asm) hpw i0 E rd ls l b n) s c fs

/-! ## The level's obligations into the context -/

/-- **`hctx_main1H` at `CtxR1HX`** (at `ref1HX`): a counter add of a box call from `wc_main` returning to
`.Lwc_main.x22`, at no frames, under main's thread pointer, at the first stack's top, the caller's slot `-16`
main's TCB (`hslot`), is `CtxR1HX`'s counter disjunct (the counter word does not read the own map,
`ctr_none_FS`). -/
theorem hctx_main1HX (hc : Spike.Lib.X64.Rt.CtrZ o) (l : WeakMem.AllocLabel) (b n : Nat) {ms : MemSide isa}
    (hms : ms = { ref1HX (asm := asm) hpw i0 E rd ls l b n [] with xa := ms.xa }) (σC : FAS)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) :
    ∀ q : Call, q.OKB ms (Ly).lab → q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec →
      ∀ s c, At (Ly).exe (Ly).endPc (wARH (wcR (RM) helloD))
        (fun m => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1 m ∧
          CallerCells (wcR (RM) helloD) (-144) (-160) 8 m ∧
          WcCtxH ms (Ly).lab (wcR (RM) helloD)
            (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b)
              Spike.Lib.X64.HelloPh.C0S.c0S.env l) (TV) (RM))).J σ1)
            (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m)
        (N (Ly).lab ms q .rmw) s c → TP (TV) s → CtxR1HX (asm := asm) hpw i0 E rd ls l b n s c [] := by
  obtain ⟨X, rfl⟩ : ∃ X, ms = { ref1HX (asm := asm) hpw i0 E rd ls l b n [] with xa := X } := ⟨_, hms⟩
  intro q hq hra s c hAt htp
  refine .inl ⟨⟨_, _, _, q, rfl, ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩,
    ⟨hq.toS, ?_, fun m hm => ?_⟩, hAt⟩, htp⟩
  · obtain ⟨-, hR0, hF0⟩ := fstable_FS hpw i0
    obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hR0 hF0
      (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
    exact fstable_wARH hR hF (by show (-helloD : Int) ≤ -304; decide) (by show (8 : Int) ≤ 8; decide)
  · -- the counter word is the arena's, whatever the placement and the own map (`ctr_none_FS`)
    exact ctr_none_FS (asm := asm) hpw i0 E rd ls hc (fs := []) (X := X) m hm.1.1

/-- **`GcM1H` is inhabited at the level's call at `ref1HX`** (the producer's values, `hctx_main1HX`'s). -/
example (I : Spike.Lib.X64ConsumerS.InvS) (l : WeakMem.AllocLabel) (b n : Nat) (t : UInt64) (σC : FAS)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) (m1 : MachineData) (σ1 : FAS) (q : Call)
    (hq : q.OKB (Spike.Lib.X64.KeepTP.tpXa ((MS1X) I l b n []) t) (Ly).lab)
    (hra : q.ra = ((Ly).lab ".Lwc_main.x22").toBitVec) :
    GcM1H hpw i0 l b [] (Spike.Lib.X64.KeepTP.tpXa ((MS1X) I l b n []) t) (wARH (wcR (RM) helloD))
      (fun m => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1 m ∧
        CallerCells (wcR (RM) helloD) (-144) (-160) 8 m ∧
        WcCtxH (Spike.Lib.X64.KeepTP.tpXa ((MS1X) I l b n []) t) (Ly).lab (wcR (RM) helloD)
          (wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b)
            Spike.Lib.X64.HelloPh.C0S.c0S.env l) (TV) (RM))).J σ1)
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) q m) q :=
  ⟨rfl, hq, σC, m1, σ1, hslot, rfl, rfl, hra⟩

/-- **`ref1HX` is inhabited** at any allocation and frames (its labels are `upd LB l b`). -/
example (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) :
    (ref1HX (asm := asm) hpw i0 E rd ls l b n fs).own = fun s => (OX) s :=
  rfl

/-- **`GsH1X` is inhabited**: at the landings' own shape, from a caller whose slot `-16` holds main's TCB. -/
example (l : WeakMem.AllocLabel) (b n : Nat) (v : BitVec 64) (σC : FAS) (m1 : MachineData) (σ1 : FAS)
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) :
    GsH1X (asm := asm) hpw i0 E rd ls l b n fun l' A n' s c => n' = 1 ∧
      At (Ly).exe (Ly).endPc ((wcR (RS helloLsw v) helloD).fp (-8))
        (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
        (bXH (ref1HX (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab
          (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l' A) s c ∧ TP (TV) s :=
  ⟨v, σC, m1, σ1, hslot, rfl⟩

/-- **`hctx_st1H` at `CtxR1HX`**: the box's store at `GsH1X` is `CtxR1HX`'s store disjunct. -/
theorem hctx_st1HX (l : WeakMem.AllocLabel) (b n : Nat) :
    ∀ s c, StAt (ref1HX (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (GsH1X (asm := asm) hpw i0 E rd ls l b n) s c [] → CtxR1HX (asm := asm) hpw i0 E rd ls l b n s c [] :=
  fun _ _ h => .inr h

/-- **`CtxR1HX` is inhabited at a store** (`hctx_st1HX`): any `StAt` at `GsH1X` lands in it. -/
example (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Spike.Lib.Ctl)
    (h : StAt (ref1HX (asm := asm) hpw i0 E rd ls l b n []) helloSrc (Spike.Lib.X64ConsumerA.upd (LB) l b)
      (GsH1X (asm := asm) hpw i0 E rd ls l b n) s c []) :
    CtxR1HX (asm := asm) hpw i0 E rd ls l b n s c [] :=
  hctx_st1HX hpw i0 E rd ls l b n s c h

end Spike.Lib.X64.HelloPh.Land

/-- info: 'Spike.Lib.X64.HelloPh.Land.ref1HX_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.ref1HX_eq

/-- info: 'Spike.Lib.X64.HelloPh.Land.hctx_main1HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.hctx_main1HX

/-- info: 'Spike.Lib.X64.HelloPh.Land.hctx_st1HX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Land.hctx_st1HX
