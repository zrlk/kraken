/-
**hello's child-state facts at the root** (AArch64; HelloChildSt rows hpin2, hG, meW): the layout
and guarantee facts `HelloChildSt.childSt_IH` and the child's `.pin` stores ask, at `PlaceW`'s layout
`RuntimeLayout.ofPlaceW hpw i` and hello's guarantee `HelloGOf2H.gWH`, for any immediates `i` (the root binds
`C0S.immsH Λ0 i0`).

- `hpin2_H`: the pinned region reaches `pinA + 200` (wake's `StartPlaceLy.hpin2_W`), from the `.zero` after
  `scc_rt_pinned` having 200 bytes or more; at hello's certificate that `.zero` is `CertFacts.pinZ_helloCert`
  (`163840` bytes; the certificate cannot be imported here, as wake's `SccCertificate` is in this closure).
- `gWH_pin24`, `gWH_pin160`, `hG_childH`: any value, in particular `1`, at main's permit word `pinA + 24` and the
  second TCB's word `pinA + 160` under `gWH` (twin of `WakeGOf2.gOf2_ne`: both words are off the two pinned limit
  words `pinA + 16` and `lim2AH = pinA + 152`).
- `gWH_pin168`, `hG_childH'`: the same at the second TCB's word `pinA + 168` (the second TCB at `pinA + 144`, as
  `HelloChildStW.childPrem_St` now asks); the `pinA + 160` forms stay until nothing uses them.
- `meW_H`: main's id at its TCB in the start's labels, `L0T (mainTidLbl 2) = some (pinA + 8)` (wake's
  `WakeHClW.hme_W`, generic in the immediates).
-/
import Spike.Lib.HelloGOf2H
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeHClW

namespace Spike.Lib.A64.HelloPh.ChildRoot

open Kraken Kraken.Promising
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloGOf2H (gWH GOf2H lim2AH lim2OffH gOf2H_ne pin_ne2H)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hpw i

/-- **`hpin2` at `PlaceW`'s layout** (wake's `StartPlaceLy.hpin2_W`): the pinned region reaches `pinA + 200` once
the `.zero` after `scc_rt_pinned` has 200 bytes; at hello's certificate `hz` is `CertFacts.pinZ_helloCert`,
`hn` by `decide`. -/
theorem hpin2_H {n : Nat}
    (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some n)
    (hn : 200 ≤ n) : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size :=
  Spike.Lib.A64.WakePh.StartPlaceLy.hpin2_W hpw i hz hn

/-- **Main's permit word `pinA + 24` takes any value under `gWH`**: it is neither limit word. -/
theorem gWH_pin24 (cT : Loc) (v : Val) : gWH hpw i cT ⟨(Ly).pinA + 24#64, 8⟩ v :=
  Spike.Lib.WakeG.wakeG_of (gOf2H_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) (pin_ne2H (by decide)) v)

/-- **The second TCB's word `pinA + 160` takes any value under `gWH`**: it is neither limit word. -/
theorem gWH_pin160 (cT : Loc) (v : Val) : gWH hpw i cT ⟨(Ly).pinA + 160#64, 8⟩ v :=
  Spike.Lib.WakeG.wakeG_of (gOf2H_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) (pin_ne2H (by decide)) v)

/-- **`HelloChildSt.childSt_IH`'s `hG` at `gWH`**: `1` at main's permit word or the second TCB's word. -/
theorem hG_childH (cT : Loc) {a : BitVec 64} (ha : a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 160#64) :
    gWH hpw i cT ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128) := by
  rcases ha with rfl | rfl
  · exact gWH_pin24 hpw i cT _
  · exact gWH_pin160 hpw i cT _

/-- **The second TCB's word `pinA + 168` takes any value under `gWH`** (the second TCB at `pinA + 144`): it is
neither limit word. -/
theorem gWH_pin168 (cT : Loc) (v : Val) : gWH hpw i cT ⟨(Ly).pinA + 168#64, 8⟩ v :=
  Spike.Lib.WakeG.wakeG_of (gOf2H_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) (pin_ne2H (by decide)) v)

/-- **`HelloChildStW.childPrem_St`'s `hG` at `gWH`**: `1` at main's permit word or the second TCB's word
`pinA + 168`. -/
theorem hG_childH' (cT : Loc) {a : BitVec 64} (ha : a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 168#64) :
    gWH hpw i cT ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128) := by
  rcases ha with rfl | rfl
  · exact gWH_pin24 hpw i cT _
  · exact gWH_pin168 hpw i cT _

/-- **Main's id at its TCB** in the start's labels (wake's `WakeHClW.hme_W`). -/
theorem meW_H : Spike.Lib.WakeLoadT.L0T (Ly).Λ (Spike.Lib.WakeT1.mainTidLbl 2) = some ((Ly).pinA + 8#64).toNat :=
  Spike.Lib.WakeHClW.hme_W hpw i

end Spike.Lib.A64.HelloPh.ChildRoot

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.hpin2_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.hpin2_H

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin24

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin160' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin160

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.hG_childH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.hG_childH

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.meW_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.meW_H

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin168' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.gWH_pin168

/-- info: 'Spike.Lib.A64.HelloPh.ChildRoot.hG_childH'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.ChildRoot.hG_childH'
