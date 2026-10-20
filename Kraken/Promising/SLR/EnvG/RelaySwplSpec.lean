/-
**Part 2: the `swpl` relay — program,
environment and the release VC** (on `EnvGTC`, `EnvG/RmwGhostTake.lean`).

The three-thread relay of `EnvG/RelaySpec.lean` with the relay's
release done by a **release-only swap** `swpl w6, w7, [x2]` instead of
`stlr w6, [x2]` (`mp_relay3_swpl.kl`). The relay **takes** `Dt` at its
`ldar` of `f1`, stores `43` to it, and gives all of `Dt` away at the `swpl`
of `f2` (plan `mpPlan rp.Q`: `F2 := 1` gives `[Dt]`).

On the relay proof's `EnvGT` this release is out of reach (`KNOWN_GAPS.md`):
`RmwOk`'s claim condition is false for an armv8 `.rel` RMW at an anchor ghost
with update slots, and the link's `RelRmwGiveOk` with a non-empty give list is
not provable. On `EnvGTC` the swap claims nothing (`claimSlotsC_armv8_rel`)
and the plan gives from the relay's own resource, so the permission is
`vc_r3`'s argument (`flag43` of all of `Dt` at every anchor and fresh `tw`).

Reused unchanged from the relay proof (`RelaySpec.lean`): `RP`, `flag43`, `RK1`–`RK4`,
and the VCs of the `ldar` (`vc_r1`) and the `str` (`vc_r2`): `EnvGTC`'s loads
and stores are `EnvGT`'s definitionally, so `vc_r1c`/`vc_r2c` are those
proofs at the new environment.

- `relaySwpl`: the relay program (`spin: ldar; cbz; mov; str; mov; swpl`).
- `ERC rp tid`: `EnvGTC` with the plan `mpPlan rp.Q`.
- **`vc_r3c`** (`swpl w6, w7, [x2]`, any operation writing `1`): permitted on
  `EnvGTC`; every outcome (success or not) keeps the token `W2`.

Phase-1 limits (single-access trees, read-side acquire only, takes only at
non-forwarded acquire loads) apply; none is binding. The swap is a release
*RMW*, which phase 1 handles only on the claim-conditional environments.
-/
import Kraken.Promising.SLR.EnvG.RelaySpec
import Kraken.Promising.SLR.EnvG.RmwGhostVCGen

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.TakeSmoke Kraken.Promising.SLR.EnvG.TakeMp Kraken.Promising.SLR.EnvG.MpSmoke

/-! ## The relay program -/

/-- **The relay by swap**: spin on an acquire load of `f1` (`X0`) until
non-zero, store `43` to the data (`X1`), release `f2` (`X2`) with a
release-only swap `swpl` (the old value goes to `w7`). -/
def relaySwpl : Program := parseAArch64("
spin:
    ldar w3, [x0]
    cbz w3, spin
    mov w5, #43
    str w5, [x1]
    mov w6, #1
    swpl w6, w7, [x2]
done_y:
")

/-- info: 8 -/
#guard_msgs in
#eval relaySwpl.length

/-! ## The environment -/

/-- The relay's environment: taking loads, claim-conditional RMWs, the plan
`F2 := 1` gives `[Dt]`. -/
abbrev ERC (rp : RP) (tid : Nat) : SharedEnv := EnvGTC isa Arch.armv8 tid (mpPlan rp.Q)

/-! ## The VCs -/

/-- **VC R1 on `EnvGTC`** (`ldar w3, [x0]`): `vc_r1` (`EnvGTC`'s loads are
`EnvGT`'s). -/
theorem vc_r1c {rp : RP} (tid : Nat) (σ : State isa) (h : RK1 rp σ) :
    ∀ v (σ' : State isa), (ERC rp tid).step (.load .acq false rp.f1 4) σ v σ' →
      (BitVec.setWidth 32 v = 0 → RK1 rp σ') ∧ (BitVec.setWidth 32 v ≠ 0 → RK2 rp σ') :=
  vc_r1 tid σ h

/-- **VC R2 on `EnvGTC`** (`str w5, [x1]`): `vc_r2` (`EnvGTC`'s stores are
`EnvG`'s). -/
theorem vc_r2c {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : State isa) (h : RK2 rp σ) :
    (ERC rp tid).ok (.store .plain false rp.d 4 43#128) σ ∧
      ∀ b (σ' : State isa), (ERC rp tid).step (.store .plain false rp.d 4 43#128) σ b σ' → RK3 rp σ' :=
  vc_r2 hL tid σ h

/-- **VC R3 by `swpl`** (`swpl w6, w7, [x2]`, an operation writing `1` to
`f2`): the planned release is permitted on `EnvGTC` (`F2` held; at every
anchor, read and fresh `tw`, `flag43` of all of `Dt`, given from the relay's
own resource), and every outcome keeps the token `W2` (a release-only swap
claims nothing). -/
theorem vc_r3c {rp : RP} (hL : MpLocs rp.Q) (tid : Nat) (σ : State isa) (h : RK3 rp σ)
    (op : Val → Option Val) (hop : ∀ x y, op x = some y → y = 1#128) :
    (ERC rp tid).ok (.rmw .rel rp.f2 4 op) σ ∧
      ∀ old (σ' : State isa), (ERC rp tid).step (.rmw .rel rp.f2 4 op) σ old σ' → RK4 rp σ' := by
  obtain ⟨⟨hrel, hF, hW⟩, hq, ts, hX, hmax, hts⟩ := h
  have hne : rp.Q.Fl ≠ rp.Q.Dt := hL.fl_dt
  have hWd : rp.Q.W ≠ rp.Q.Dt := hL.wd
  refine ⟨⟨hF, fun c g tr old new _ _ hon => ?_⟩, ?_⟩
  · obtain rfl := hop _ _ hon
    refine ⟨fun hr => by simp [mpPlan] at hr, fun _ => ⟨rfl, ?_, ?_, fun _ hwb => ?_⟩⟩
    · rw [hrel]; exact flag43_impure (by decide)
    · simp [mpPlan, hne]
    · have hlt := hwb.rel rfl
      rw [hrel]
      refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX,
        fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
      simp only [Time, View] at *; omega
  · intro old σ' hs
    obtain ⟨c, tr, -, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsTC hs
    unfold RK4
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨_, -, hr⟩, -⟩
    · rw [hr]; exact hW
    · obtain rfl := hop _ _ hon
      rw [hr, claimSlotsC_armv8_rel]
      simp [mpPlan, hWd, hW, Res.op_unit]

#print axioms vc_r1c
#print axioms vc_r2c
#print axioms vc_r3c

end Kraken.Promising.SLR.EnvG.Relay
