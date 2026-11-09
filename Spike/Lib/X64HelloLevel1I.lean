/-
**hello's level 1 at the root's choices** (x86-64; the twin of `Spike/Lib/A64HelloLevel1I.lean`'s live part): the
level `HelloWf.W1Hg` at the root's choices (context `Land.CtxR1H`, frame `frH c0S.env`, the start's facts `X0WH`)
and, at rodata's entry `J1 := mRdJ0 J'`, main's TCB in the caller's slot (the landing's `hJ1`, asked by the
level-1 instances that pin `wc_main`'s caller, as `Land.GsH1` does).

- `W1Rg`: the level at the root's choices at any owned words `own` (`HelloWf.W1Hg own`); `XR`: its per-state
  facts at the root's choices.
- `slot16_rdJ`: at rodata's entry `J1 := mRdJ0 J'` the caller's slot `-16` is main's TCB `pinA + 8`.

## Differences from the AArch64 version

- `slot16_rdJ` is AArch64's `slot80_rdJ`: x86-64's `mNC` keeps the entry's `%rdi` (`MainGlue.JS`'s thread pointer
  `tpOf (tcbS Ly)`, `StartE.mainE0`) at slot `-16` (AArch64 `x0` at slot `-80`). `J'` is `rdJH` at any region `R`
  (x86-64's `rdJH` takes `scc_rt_main`'s region, `StartWcS`; AArch64's has none).
- Imports only what the live part uses (`Land1`, `W1H`, `StartH0H1`, with `StartGlue` and `ClH`
  for `X0WH` and `ClH`); AArch64's `Level1T`, `StartH0CL`,
  `StartH0B` and `H1Gfp` imports serve its landing segment only.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hB_land`, `h1_level1`.
- The level is generic in the owned words (`W1Rg`; AArch64's `W1R` is at `ownGH` only), so that `ownGHXW`, which
  carries main's and the worker's TCB words, is an instance; the root's level 1 is at `ownGHXW`.
-/
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloW1H
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.X64HelloStartGlue
import Spike.Lib.X64HelloClH

namespace Spike.Lib.X64.HelloPh.Level1I

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (FragS PlaceWX)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.Flow.Hello1 (mRdJ0)
open Spike.Lib.X64.WakePh.MainGlue (JS)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloSrc (helloSrc)

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
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site's label. -/
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

/-- **The level at the root's choices at the owned words `own`**: `W1Hg own` with the context `CtxR1H`, the
frame `FR`, the start's facts. -/
abbrev W1Rg (own : Spike.Lib.X64Consumer.Own) : WeakMem.AllocLabel → Nat → Nat → FragS isa :=
  Spike.Lib.X64.HelloWf.W1Hg own (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
    (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls) (FR) (X0WH (Ly) (AX))

/-- **The level's per-state facts** (`h1StmtHF_of_segWS`'s `X`): the start's `X0WH`. -/
abbrev XR : WeakMem.AllocLabel → Nat → Nat → FragS isa := fun _ _ _ s _ _ => X0WH (Ly) (AX) s

/-- **The landing's `hJ1` at rodata's entry `J1 := mRdJ0 J'`**: the caller `σC` at `wc_rodata`'s call is at `mNC`,
whose slot `-16` holds the entry's `%rdi`, main's TCB `pinA + 8` (`JS`, `StartE.mainE0`). -/
theorem slot16_rdJ (R : Spike.Lib.Region) : ∀ σC σ c, mRdJ0 (rdJH (Ly).lab R (JS (Ly) 0#64 c0S)) σC σ c →
    σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64 := by
  rintro σC σ c ⟨-, -, c', σe, ⟨-, hx0⟩, -, -, h16, -⟩
  rw [h16, hx0]
  apply BitVec.eq_of_toNat_eq
  simp [Spike.Lib.X64.Flow.Ret0.tpOf, BitVec.toNat_add]

end Spike.Lib.X64.HelloPh.Level1I

/-! ## Axiom guards -/

/-- info: 'Spike.Lib.X64.HelloPh.Level1I.slot16_rdJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1I.slot16_rdJ
