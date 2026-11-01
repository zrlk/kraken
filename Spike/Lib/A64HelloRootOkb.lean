/-
**hello.w's box side and its box-call premises** (AArch64; the root's `msB`, `hokb`, `hg`; the hello twin of
wake's `WakeRoot.hokb_R`, `wake_h1`'s premises `hokb`/`hg` discharged by `WakeBoxW.okb_ms1`).

The root's base (`RootRest`) names a box side `msB l b n` — the memory side at which `wc_main`'s box call is made,
after rodata's allocation of `l` at `b` with `n` cells — and asks that the box call's premises (`Call.OKB`) carry
from it to `h2`'s memory side (`H2Rt.ms2H … l b n l' b' n' []`) at every `Fresh2H` index, and that the two sides
share the arena's geometry.

- `msBH`: the box side, level 1's reference side `Land.ref1H … (fun _ => True) ls l b n []` (the side `h1`'s
  box landings `BoxMH` are stated at, `RootL1U`/`RootHP`), i.e. `ms2H`'s data at the once-extended placement.
- `hokb_H`: the root's `hokb` at `msB := msBH`: `WakeBoxW.okb_ms1` at the placement `upd LB l b`, the fresh label
  `l'` at `b'` with `n'` cells (`Fresh2H`'s last two conjuncts), the arena's facts from the counter's zeroed item
  (`ArenaW.arOf_ok`, as `WakeOD.hok_W`) and its box rows (`WakeOD.arW_newOk`).
- `hg_H`: the root's `hg` at `msB := msBH` (`rfl`: both sides read the geometry off `arW`).

Deviations from wake: wake's box side is `h0`'s `msOfA` and its fresh label is the box's first allocation
(`okb_ms1` at `L0T`); hello's box call is level 1's, so `okb_ms1` runs at the once-extended placement and sizes.
`hokb_H` carries the counter's zeroed item `hc` (a root premise, `RootLit.hc_H`) for `Arena.OK`.
-/
import Spike.Lib.A64HelloLand1
import Spike.Lib.A64HelloH2Rt
import Spike.Lib.A64WakeBoxW

namespace Spike.Lib.A64.HelloPh.RootOkb

variable {asm : String}

open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (MemSide PlaceW)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.WakeLoadT (L0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat) (E : Scc.Sem.Entry) (ls : Lsize)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH0" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp (IH0)

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW hp (IH0)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "MS2" => Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hp (IH0) E ls

/-- **The root's box side** (`RootRest.msB`; wake's `wake_h1` `ms0`): level 1's reference memory side after
rodata's allocation of `l` at `b` with `n` cells, every word admitted, at no frames (`Land.ref1H`). -/
noncomputable abbrev msBH (l : WeakMem.AllocLabel) (b n : Nat) : MemSide isaLSE2 :=
  Spike.Lib.A64.HelloPh.Land.ref1H (asm := asm) hp i0 E (fun _ => True) ls l b n []

/-- **The root's `hokb` at `msBH`** (wake's `WakeRoot.hokb_R`, `WakeBoxW.okb_ms1`): the box call's premises at
level 1's side carry to `h2`'s, given the counter's zeroed item. -/
theorem hokb_H (hc : Spike.Lib.A64.Rt.CtrZ o) :
    ∀ l b n l' b' n', Spike.Lib.A64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      ∀ q : Spike.Lib.A64.Alloc.Call, q.OKB (msBH (asm := asm) hp i0 E ls l b n) (Ly).lab →
        q.OKB (MS2 l b n l' b' n' []) (Ly).lab := by
  intro l b n l' b' n' hf q h
  have h0 := Spike.Lib.A64.Rt.ArenaW.arOf_ok (PlaceW.link (IH0) hp) hc
  have hok : (AW).OK := ⟨h0.ctr_out, h0.units, h0.off, h0.units_lt, h0.cells_lt, h0.ctr_lt⟩
  exact Spike.Lib.WakeBoxW.okb_ms1 hok (Spike.Lib.WakeOD.arW_newOk hp (IH0)) hf.2.2.1 hf.2.2.2 h

/-- **The root's `hg` at `msBH`** (wake's `wake_h1` premise `hg`, `rfl` at `h0`'s `msOfA`): `h2`'s side and the
box side read the arena's geometry off `arW`. -/
theorem hg_H :
    ∀ l b n l' b' n', Spike.Lib.A64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      (MS2 l b n l' b' n' []).heap = (msBH (asm := asm) hp i0 E ls l b n).heap ∧
        (MS2 l b n l' b' n' []).cells = (msBH (asm := asm) hp i0 E ls l b n).cells ∧
        (MS2 l b n l' b' n' []).off = (msBH (asm := asm) hp i0 E ls l b n).off ∧
        (MS2 l b n l' b' n' []).units = (msBH (asm := asm) hp i0 E ls l b n).units :=
  fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end Spike.Lib.A64.HelloPh.RootOkb

/-- info: 'Spike.Lib.A64.HelloPh.RootOkb.hokb_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootOkb.hokb_H

/-- info: 'Spike.Lib.A64.HelloPh.RootOkb.hg_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootOkb.hg_H
