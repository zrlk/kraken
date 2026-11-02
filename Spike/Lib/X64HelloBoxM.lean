/-
**hello.w on x86-64: main's id at its TCB at the box's level** (the twin of
`Spike.Lib.A64HelloBoxM`, live part: `hCI`'s second half).

- `hmt_H`: main's id at its TCB at the level's labels `upd LB l b`, for `l`
  fresh at `LB` (`WakeHClW.hme_W`'s twin). `l` is fresh at `LB`, so it is not
  main's id label.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The layout is `RuntimeLayout.ofPlaceWX` at `X64HelloImms.immsH`, and the
  labels are `X64WakeLoadT.L0T`/`X64ConsumerA.upd` (AArch64: `ofPlaceW`,
  `C0S.immsH`, `WakeLoadT.L0T`, `A64ConsumerA.upd`). The statement and proof
  are otherwise AArch64's.
- Only `hmt_H` is twinned. AArch64's `boxMH_landingH` and `hCI_H` are dead in
  the hello proof, so this module imports neither `X64HelloH2G` nor
  `HelloGOf2H`.
-/
import Spike.Lib.X64HelloBox
import Spike.Lib.X64WakeLoadT

namespace Spike.Lib.X64.HelloPh.Box

open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.PlaceWX
open Spike.Lib.X64WakeLoadT (L0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

/-- **main's id at its TCB** at the level's labels `upd LB l b` (`WakeHClW.hme_W`'s twin; `l` fresh at `LB`, so not
main's id label). -/
theorem hmt_H {l : WeakMem.AllocLabel} {b : Nat} (hl : (LB) l = none) :
    Spike.Lib.X64ConsumerA.upd (LB) l b (Spike.Lib.X64WakeT1.mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
  have hp0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw IH
  have hsm := (Ly).words_small _ (Ly).pin_mem
  have hme : (LB) (Spike.Lib.X64WakeT1.mainTidLbl 2) = some ((Ly).pinA.toNat + 8) := by
    simp only [Spike.Lib.X64WakeLoadT.L0T, Spike.Lib.X64ConsumerA.upd, ↓reduceIte, Spike.Lib.X64WakeLoadT.tcb0,
      Option.some.injEq]
    omega
  have hne : Spike.Lib.X64WakeT1.mainTidLbl 2 ≠ l := by intro h; rw [h, hl] at hme; cases hme
  show (if _ = l then _ else _) = _
  split
  · exact absurd ‹_› hne
  · exact hme

end Spike.Lib.X64.HelloPh.Box

/-- info: 'Spike.Lib.X64.HelloPh.Box.hmt_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Box.hmt_H
