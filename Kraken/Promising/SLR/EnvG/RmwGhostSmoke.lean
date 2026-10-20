/-
**Claim-conditional RMW smoke test**: the MP writer's release by a **release-only swap**
(`swpl w3, _, [x0]` instead of `stlr w3, [x0]`), giving all of `Dt` away, as
a VC of the claim-conditional environment `EnvGC` (`EnvG/RmwGhost.lean`),
on MP's plan and predicates (`MpSmoke.lean`, `SLR/MpInv.lean`).

On the existing `EnvG` this VC is out of reach:
- `RmwOk`'s claim condition `claimedSlots g Fl tr ≠ [] → ClaimOk armv8 .rel …`
  must hold at every anchor ghost and every read, and `ClaimOk` is false for
  `.rel` (`claimOk_rel_false`);
- the link needs `RelRmwGiveOk` with `gives = [Dt] ≠ []`, which quantifies
  over all erasure ghosts.

On `EnvGC` the RMW claims nothing (`.rel` never claims), so the permission is
`vc_w2`'s proof: the release obligation is for `pl.give Fl 1 σ.cl σ.r`. The
outcome's resource is `pl.after` (no claimed part), so the token `W` is
kept. The swap's operation is abstract (`hop`: it writes `1`).

Also: the release swap and fetch-add pass `dirs_phase1R`, the shape
`ofSafelyEnvGRC` asks for (`RmwRelSmoke.lean`).
-/
import Kraken.Promising.SLR.EnvG.RmwGhostA64
import Kraken.Promising.SLR.EnvG.MpSmoke
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.RmwGhostSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.EnvG.MpSmoke

/-- The claim-conditional environment of the MP thread `tid`. -/
abbrev EC (P : Params) (tid : Nat) : SharedEnv := EnvGC isa Arch.armv8 tid (mpPlan P)

/-- `EnvGC`'s RMW permission and outcome, unfolded (as `EnvG/Simp.lean`). -/
@[simp] theorem envGC_ok_rmw {A : Arch} {tid : Nat} {pl : Plan} (σ : State isa) (k : RmwKind) (addr : BitVec 64)
    (n : Nat) (op : Val → Option Val) :
    (EnvGC isa A tid pl).ok (.rmw k addr n op) σ = RmwOkC A tid pl σ k ⟨addr, n⟩ op := rfl

/-- On armv8 a release-only RMW's resource after a successful outcome has no
claimed part. -/
theorem claimSlotsC_rel {vs : Views} {g : Ghost} {l : Loc} {tr : Time} :
    claimSlotsC Arch.armv8 .rel vs g l tr = [] :=
  claimSlotsC_of_not claimOk_rel_false

/-- **VC W2 by `swpl`** (a release-only swap writing `1` to `Fl`, giving
`Dt` away): permitted on `EnvGC`, and every outcome keeps the token `W`. -/
theorem vc_w2_swpl {P : Params} (hL : MpLocs P) (tid : Nat) (σ : State isa) (h : W2 P σ)
    (op : Val → Option Val) (hop : ∀ x y, op x = some y → y = 1#128) :
    (EC P tid).ok (.rmw .rel P.f 4 op) σ ∧
      ∀ old (σ' : State isa), (EC P tid).step (.rmw .rel P.f 4 op) σ old σ' → W3 P σ' := by
  obtain ⟨⟨hrel, hpure⟩, hq, ⟨ts, hX, hmax, hts⟩, hW, hF⟩ := h
  have hne : P.Fl ≠ P.Dt := hL.fl_dt
  have hWd : P.W ≠ P.Dt := hL.wd
  refine ⟨⟨hF, fun c g tr old new _ _ hon => ?_⟩, ?_⟩
  · obtain rfl := hop _ _ hon
    refine ⟨fun hr => by simp [mpPlan] at hr, fun _ => ⟨rfl, ?_, ?_, fun _ hwb => ?_⟩⟩
    · rw [hrel]; exact flagPred_impure (by decide)
    · simp [mpPlan, hne]
    · have hlt := hwb.rel rfl
      rw [hrel]
      refine fun _ => ⟨by simp [mpPlan, hq], ts, by simpa [mpPlan] using hX,
        fun p hp => hmax p (by simpa [mpPlan] using hp), ?_⟩
      simp only [Time, View] at *; omega
  · intro old σ' hs
    obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
    have hW' : WorldW P σ'.g := by unfold WorldW; rw [hanc.rel]; exact ⟨hrel, hpure⟩
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨_, -, hr⟩, -⟩
    · exact ⟨hW', by rw [hr]; exact hW⟩
    · obtain rfl := hop _ _ hon
      refine ⟨hW', ?_⟩
      rw [hr, claimSlotsC_rel]
      simp [mpPlan, hWd, hW, Res.op_unit]

end Kraken.Promising.SLR.EnvG.RmwGhostSmoke

namespace Kraken.Promising.AArch64.EnvG.RmwGhostSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- The relay's release by swap (`mp_relay3_swpl.kl`'s relay tail). -/
def relaySwpl : Program := parseAArch64("
    mov w3, #1
    swpl w3, w2, [x0]
")

/-- It has the shape `ofSafelyEnvGRC` asks for. -/
example [layout : _root_.Layout] (A : Arch) : DirsPhase1R A (layout relaySwpl) := by dirs_phase1R relaySwpl

end Kraken.Promising.AArch64.EnvG.RmwGhostSmoke
