/-
**The x64 `lock cmpxchg` spinlock on `EnvG`: the acquire VC**, for the worker of `spinlock_cmpxchg2.kl` (`cmpxWorkerG`,
`EnvG/X64CmpxVCGen.lean`) under `Arch.tso`.

Everything but the acquire is the xchg spinlock's (`EnvG/X64SpinVC.lean`,
reused unchanged): the plan `xlockPlan`, the table predicates `Fr`, `H1`,
`H2`, `H3`, `QEnd`, and the VCs `vc_ld_c`, `vc_st_c`, `vc_rel`. Only the
acquire differs:

- `lock cmpxchgl %ecx, (Lk)` with `eax = 0`, `ecx = 1`: operation `cmpxOp`
  (write `1` iff the old low word is `0`, otherwise **fail** and write
  nothing).
- `vc_cmpx`: permitted from `Fr` (the success outcome writes the pure value
  `1`, never a planned release: as `vc_xchg`), and every outcome either
  **fails** (non-zero low word; the resource is unchanged, so `Fr` is kept
  outright: no claimed junk, unlike a failed `xchg`) or succeeds (low word
  `0`, `H1`, by `World.lock_claim'` as `vc_xchg`).

A failing release-kind RMW is outside `Phase1ShapeR` (release-RMW limit 1); the
rule goes through the `F` link (`EnvG/X64RmwFail.lean`), so Theorem 1′ for it
is the open `Theorem1FChain`.
-/
import Kraken.Promising.SLR.EnvG.X64SpinVC
import Kraken.Promising.SLR.EnvG.RmwFailFwd

namespace Kraken.Promising.X64.EnvG.Cmpx

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin
open Kraken.Promising.X64.EnvG.Spin

/-- The `lock cmpxchgl %ecx, (Lk)` operation with `eax = 0`, `ecx = 1`. -/
abbrev cmpxOp : Val → Option Val := rmwOp128 .W32 fun x => if x == 0#32 then some 1#32 else none

theorem cmpxOp_some {old new : Val} (h : cmpxOp old = some new) : BitVec.setWidth 32 old = 0 ∧ new = 1#128 := by
  simp [cmpxOp, rmwOp128, Width.bits] at h
  exact ⟨h.1, h.2.symm⟩

theorem cmpxOp_none {old : Val} (h : cmpxOp old = none) : BitVec.setWidth 32 old ≠ 0 := by
  intro h0
  simp [cmpxOp, rmwOp128, Width.bits, h0] at h

/-- **A failed RMW leaves the forwarding items alone** (its views are the
read's, after the optional fence). The x64 instance of
`envG_rmw_fail_getFwd` (`EnvG/RmwFailFwd.lean`). -/
theorem rmw_fail_getFwd {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : EStateX} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (Kraken.Promising.SLR.EnvG isa A tid pl).step (.rmw k addr n op) σ old σ') (hop : op old = none)
    (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l :=
  envG_rmw_fail_getFwd h hop l

variable {P : Sys} {tid : Nat}

/-- **VC `lock cmpxchgl %ecx, (%rdi)`** (`eax = 0`, `ecx = 1`): permitted (a
lock share, a pure written value `1`, the claim condition: acquire-release),
and every outcome either fails on a non-zero low word (`Fr` kept: the
resource is unchanged) or takes the lock (`H1`). -/
theorem vc_cmpx (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) :
    (EG P tid).ok (.rmw .acqRel P.Lk.addr P.Lk.bytes cmpxOp) σ ∧
      ∀ old (σ' : EStateX), (EG P tid).step (.rmw .acqRel P.Lk.addr P.Lk.bytes cmpxOp) σ old σ' →
        (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  obtain ⟨hW, hf, hfw, hz⟩ := h
  refine ⟨⟨?_, fun c g tr old new _ _ hop => ⟨fun _ => .inl rfl, fun _ => ?_, fun hr => ?_⟩⟩, ?_⟩
  · show 0 < (σ.r.wr P.Lk).q
    have := one_div_pos hN0; have := hf.2.2; grind
  · obtain ⟨-, rfl⟩ := cmpxOp_some hop
    rw [hW.1]; exact lockPred_pure (by decide)
  · obtain ⟨-, rfl⟩ := cmpxOp_some hop
    rw [xlockPlan_rel_one] at hr; cases hr
  intro old σ' hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, hvr, hvw, hbr⟩ := rmw_factsX hs tso_acq tso_notPlain rfl hfw
  rcases hbr with ⟨hop, hr⟩ | ⟨new, tw, hop, hcoh, ⟨_, -, hr⟩, hun, -⟩
  · -- the comparison fails: nothing is written, the resource is unchanged
    refine .inl ⟨cmpxOp_none hop, hW.mono hanc.ghost, hr ▸ hf, fun f hf' => hfw f ?_, ?_⟩
    · rw [rmw_fail_getFwd hs hop] at hf'; exact hf'
    · rw [hr]; exact hz.mono (hvle.coh _)
  obtain ⟨h0, rfl⟩ := cmpxOp_some hop
  have hr' : σ'.r = (σ.r.op (Res.prod ((claimedSlots σ'.g P.Lk tr).map (·.res)))).addW P.Lk (1#128, tw) := by
    rw [hr, Plan.afterRmw, Plan.after, xlockPlan_rel_one]; rfl
  have hz' : LkLe P σ'.r σ'.vs := by rw [hr']; exact LkLe.join hf hz (hvle.coh _) hcoh
  refine .inr ⟨h0, hW.mono hanc.ghost, hz', ?_⟩
  obtain ⟨rF, E'⟩ := hanc.erase
  obtain ⟨R, R', hprod, hgb⟩ := World.lock_claim' (hW.mono hanc.ghost) E' hrd h0 hun
  have hr'' : σ'.r = (σ.r.op (R.op R')).addW P.Lk (1#128, tw) := by rw [hr', hprod]
  rcases hgb with ⟨k, S, ts, hpool, hX, hmax, hk, hts⟩ | hbad
  · exact ⟨S, k, R, σ.r, R', tw, hr'', hf, hpool,
      .inl ⟨ts, hX, hmax, hk, Nat.le_trans hts hvr, Nat.le_trans hts hvw⟩⟩
  · obtain ⟨S, hpool⟩ := hbad.2
    exact ⟨S, 0, R, σ.r, R', tw, hr'', hf, hpool, .inr hbad⟩

/-! ## At an address and operation given by equations -/

variable {a : BitVec 64}

theorem vc_cmpx_ok_at (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) {op : Val → Option Val}
    (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes) (hop : op = cmpxOp) : (EG P tid).ok (.rmw .acqRel a 4 op) σ := by
  subst ha hop; rw [hn]; exact (vc_cmpx hN0 σ h).1

theorem vc_cmpx_at (hN0 : 0 < P.N) (σ : EStateX) (h : Fr P tid σ) {op : Val → Option Val}
    (ha : a = P.Lk.addr) (hn : 4 = P.Lk.bytes) (hop : op = cmpxOp) :
    ∀ old (σ' : EStateX), (EG P tid).step (.rmw .acqRel a 4 op) σ old σ' →
      (BitVec.setWidth 32 old ≠ 0 ∧ Fr P tid σ') ∨ (BitVec.setWidth 32 old = 0 ∧ H1 P tid σ') := by
  subst ha hop; rw [hn]; exact (vc_cmpx hN0 σ h).2

end Kraken.Promising.X64.EnvG.Cmpx
