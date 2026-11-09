/-
**hello's child-state facts at the root, x86-64** (the twin of `Spike/Lib/A64HelloChildRoot.lean`): the layout
and guarantee facts the child's state and its `.pin` stores ask, at `PlaceWX`'s layout
`RuntimeLayout.ofPlaceWX hpw i` and hello's guarantee `X64HelloGOf2H.gWH`, for any immediates `i`.

- `hpin2_H`: the pinned region reaches `pinA + 200` (wake's `X64.WakePh.StartPlaceLy.hpin2_W`), from the `.zero`
  after `scc_rt_pinned` having 200 bytes or more.
- `gWH_pin24`, `gWH_pin168`, `hG_childH'`: any value, in particular `1`, at main's permit word `pinA + 24` and the
  second TCB's word `pinA + 168` under `gWH`: both words are off the two pinned limit words `pinA + 16` and
  `lim2AH = pinA + 152`.
- `meW_H`: main's id at its TCB in the start's labels, `L0T (mainTidLbl 2) = some (pinA + 8)`.

Unlike AArch64: the layout is `ofPlaceWX` over `PlaceWX` and the labels are `X64WakeLoadT.L0T`; the
`pinA + 160` forms (`gWH_pin160`, `hG_childH`), which nothing on this path uses, are not stated; `meW_H` is proved
here from `L0T`'s definition (AArch64: wake's `WakeHClW.hme_W`, whose x86-64 counterpart states it of the
wake fragment's data instead).
-/
import Spike.Lib.X64HelloGOf2H
import Spike.Lib.X64WakeStartPlaceLy
import Spike.Lib.X64WakeLoadT

namespace Spike.Lib.X64.HelloPh.ChildRoot

open Kraken Kraken.Promising
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloGOf2H (gWH GOf2H lim2AH lim2OffH gOf2H_ne pin_ne2H)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw i

/-- **`hpin2` at `PlaceWX`'s layout** (wake's `StartPlaceLy.hpin2_W`): the pinned region reaches `pinA + 200`
once the `.zero` after `scc_rt_pinned` has 200 bytes. -/
theorem hpin2_H {n : Nat}
    (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some n)
    (hn : 200 ≤ n) : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size :=
  Spike.Lib.X64.WakePh.StartPlaceLy.hpin2_W hpw i hz hn

/-- **Main's permit word `pinA + 24` takes any value under `gWH`**: it is neither limit word. -/
theorem gWH_pin24 (cT : Loc) (v : Val) : gWH hpw i cT ⟨(Ly).pinA + 24#64, 8⟩ v :=
  Spike.Lib.WakeG.wakeG_of (gOf2H_ne (Spike.Lib.X64.PhRec.pin_ne (by decide)) (pin_ne2H (by decide)) v)

/-- **The second TCB's word `pinA + 168` takes any value under `gWH`** (the second TCB at `pinA + 144`): it is
neither limit word. -/
theorem gWH_pin168 (cT : Loc) (v : Val) : gWH hpw i cT ⟨(Ly).pinA + 168#64, 8⟩ v :=
  Spike.Lib.WakeG.wakeG_of (gOf2H_ne (Spike.Lib.X64.PhRec.pin_ne (by decide)) (pin_ne2H (by decide)) v)

/-- **The child's `hG` at `gWH`**: `1` at main's permit word or the second TCB's word `pinA + 168`. -/
theorem hG_childH' (cT : Loc) {a : BitVec 64} (ha : a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 168#64) :
    gWH hpw i cT ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128) := by
  rcases ha with rfl | rfl
  · exact gWH_pin24 hpw i cT _
  · exact gWH_pin168 hpw i cT _

/-- **Main's id at its TCB** in the start's labels. -/
theorem meW_H :
    Spike.Lib.X64WakeLoadT.L0T (Ly).Λ (Spike.Lib.X64WakeT1.mainTidLbl 2) = some ((Ly).pinA + 8#64).toNat := by
  have hp0 := Spike.Lib.PlaceWX.pinA_toNat_ofPlaceWX hpw i
  have hsm := (Ly).words_small _ (Ly).pin_mem
  simp only [Spike.Lib.X64WakeLoadT.L0T, Spike.Lib.X64ConsumerA.upd, ↓reduceIte, Spike.Lib.X64WakeLoadT.tcb0,
    BitVec.toNat_add, BitVec.toNat_ofNat, Option.some.injEq]
  omega

end Spike.Lib.X64.HelloPh.ChildRoot

/-- info: 'Spike.Lib.X64.HelloPh.ChildRoot.hpin2_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ChildRoot.hpin2_H

/-- info: 'Spike.Lib.X64.HelloPh.ChildRoot.hG_childH'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ChildRoot.hG_childH'

/-- info: 'Spike.Lib.X64.HelloPh.ChildRoot.meW_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.ChildRoot.meW_H
