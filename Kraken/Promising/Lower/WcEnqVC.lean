/-
**The verification conditions of WeakCore's
`enq`** (`WcMsq.wcEnqFrag`: `MsqPilot`'s `enqFrag` with plain `ldr` in place of
the two `ldar`s) on msqueue2's enqueuer environment `EE2 P` (`EnvGCAdj` on
`planE2`, thread `0`, `Arch.armv8`). The protocol
(`form2`, `ghost2`, `planE2`) and the enqueuer's predicates (`EL'`, `Linked`,
`PhOk`, `EnvG/MsQueue2VC.lean`) are used unchanged.

What differs from msqueue2's `vc_e_*2`: the `ldar` of `tail` records its read
`a ≤ vwNew` (`EL1'`/`EL2'`); a plain read raises only `vrOld`
(`LoadViews.vrOld`), so here `a ≤ vrOld ∨ a ≤ vwNew` (`EL1w`/`EL2w`; the second
case when forwarded, by `FwdT`). Only the successful link `casal` used
`a ≤ vwNew`: its `LinkS` needs the `tail` read below the link write `tw`, and
`vrOld < tw` holds as well (`WriteBound.rel`, an acquire-release RMW). The
helping `casal` (`vc_e_fixw`) only needs the two reads.
-/
import Kraken.Promising.Lower.WcMsqProg
import Kraken.Promising.SLR.EnvG.MsQueue2VCGen

namespace Kraken.Promising.Lower.WcMsq

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_mono prefix_append)

variable {P : Params2} {ph : Ph} {σ σ' : State isa}

/-- **After `ldr x3, [x1]`** of `y3` (`tail`, read plain at `a`: below
`vrOld`, or below `vwNew` if forwarded). -/
def EL1w (P : Params2) (ph : Ph) (y3 : Val) (σ : State isa) : Prop :=
  EL' P ph σ ∧ ∃ a, σ.snap.mem.read? P.tail a = some y3 ∧ (a ≤ σ.vs.vrOld ∨ a ≤ σ.vs.vwNew)

/-- **After `ldr x4, [x8]`** of `y4` (the link `[y3 + 8]`). -/
def EL2w (P : Params2) (ph : Ph) (y3 y4 : Val) (σ : State isa) : Prop :=
  EL' P ph σ ∧ ∃ a b, σ.snap.mem.read? P.tail a = some y3 ∧ (a ≤ σ.vs.vrOld ∨ a ≤ σ.vs.vwNew) ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ b = some y4

theorem EL1w.fence (hph : PhOk P ph) {y3 : Val} (h : EL1w P ph y3 σ) (hf : FenceLe σ σ') : EL1w P ph y3 σ' := by
  obtain ⟨h1, a, h2, h3⟩ := h
  have hro : σ'.vs.vrOld = σ.vs.vrOld := by rw [hf.vs]
  exact ⟨h1.fence hph hf, a, hf.snap ▸ h2, h3.imp (fun h => hro ▸ h) fun h => Nat.le_trans h hf.vwNew⟩

theorem EL2w.fence (hph : PhOk P ph) {y3 y4 : Val} (h : EL2w P ph y3 y4 σ) (hf : FenceLe σ σ') :
    EL2w P ph y3 y4 σ' := by
  obtain ⟨h1, a, b, h2, h3, h4⟩ := h
  have hro : σ'.vs.vrOld = σ.vs.vrOld := by rw [hf.vs]
  exact ⟨h1.fence hph hf, a, b, hf.snap ▸ h2, h3.imp (fun h => hro ▸ h) fun h => Nat.le_trans h hf.vwNew,
    hf.snap ▸ h4⟩

/-- **VC `ldr x3, [x1]`**: `tail` read (plain). -/
theorem vc_e_ldr_tail (hph : PhOk P ph) (σ : State isa) (h : EL' P ph σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE2 P).step (.load .plain xcl P.tail.addr P.tail.bytes) σ v σ' → EL1w P ph v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE2 P) hs
  refine ⟨h.load hph hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, hlv, -⟩ := hf
  refine ⟨tr, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs P.tail tr
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact .inr (Nat.le_trans (h.1.2.2.2 f hf) hlv.mono.vwNew)
  · exact .inl (hlv.vrOld hfw)

/-- **VC `ldr x4, [x8]`** (`x8 = x3 + 8`): the link read (plain). -/
theorem vc_e_ldr_link (hph : PhOk P ph) (σ : State isa) {y3 : Val} (h : EL1w P ph y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE2 P).step (.load .plain xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' →
      EL2w P ph y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE2 P) hs
  obtain ⟨hel, a, ha, hav⟩ := h
  refine ⟨hel.load hph hf, ?_⟩
  obtain ⟨hanc, -, -, tr, hrd, hlv, -⟩ := hf
  exact ⟨a, tr, hanc.read? ha, hav.imp (fun h => Nat.le_trans h hlv.mono.vrOld)
    (fun h => Nat.le_trans h hlv.mono.vwNew), hrd.val⟩

/-- **VC `casal x5, x4, [x1]`** (helping: `x5 = x3`, `x4 ≠ 0`): permitted
(`Prov`), `EL'` after it (`vc_e_fix2`'s proof; the reads only). -/
theorem vc_e_fixw (hL : QLocs2 P) (hph : PhOk P ph) (σ : State isa) {y3 y4 : Val} (h : EL2w P ph y3 y4 σ)
    (hnz : BitVec.setWidth 64 y4 ≠ 0) :
    (EE2 P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ ∧
      ∀ old (σ' : State isa), (EE2 P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ old σ' → EL' P ph σ' := by
  obtain ⟨hel, a, b, h1, -, h2⟩ := h
  have hW := hel.1.1
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hel.1.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_,
    gives_tail hL _ _, fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => hel.rmw_tail hL hph (envGCAdj_step_iff.mp hs)⟩
  · rw [e, planE2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_w hq]
    exact form2_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.q1.head_tail)
      fun _ => .inr (prov_of_reads hanc (.inr rfl) h1 h2 hnz _)

/-- **VC `casal x5, x2, [x8]`** (the link): permitted as `vc_e_link2`; it
fails (`EL'`) or succeeds (`Linked`: the `tail` read is below the link write,
by `vrOld < tw` (`WriteBound.rel`) or `vwNew < tw`). -/
theorem vc_e_linkw (hL : QLocs2 P) (hph : PhOk P ph) (σ : State isa) {y3 y4 : Val} (h : EL2w P ph y3 y4 σ) :
    (EE2 P).ok (.rmw .acqRel (BitVec.setWidth 64 y3 + 8) 8 (casOp64 0 ph.n)) σ ∧
      ∀ old (σ' : State isa), (EE2 P).step (.rmw .acqRel (BitVec.setWidth 64 y3 + 8) 8 (casOp64 0 ph.n)) σ old σ' →
        (BitVec.setWidth 64 old ≠ 0 ∧ EL' P ph σ') ∨ (BitVec.setWidth 64 old = 0 ∧ Linked P ph σ') := by
  obtain ⟨⟨hcom, ⟨O, J, hOJ, hOq, d, td, hX, hm, htd, hD⟩, hXph⟩, a, b, h1, hav, -⟩ := h
  have hW := hcom.1
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun hr => ?_⟩⟩, ?_⟩
  · by_cases hq : P.IsW ⟨BitVec.setWidth 64 y3 + 8, 8⟩
    · rw [planE2_rel, decide_eq_false_iff_not] at hr; exact absurd hq hr
    · rw [hW.rel_ne hq]; exact Pred.emp_pure _
  · have hq : P.IsW ⟨BitVec.setWidth 64 y3 + 8, 8⟩ := by rw [planE2_rel] at hr; simpa using hr
    obtain ⟨hz, rfl⟩ := casOp64_some hon
    refine ⟨by decide, hW.impure hq _, fun hm => hph.δ8 _ (gives_ph hL hph hm), fun htr hwb hadj => ?_⟩
    rw [hW.rel_w hq, planE2_give]
    obtain ⟨rF, E⟩ := hanc.erase
    obtain ⟨ha, h1'⟩ := read_at_append hanc h1
      ⟨⟨BitVec.setWidth 64 y3 + 8, 8⟩, BitVec.setWidth 128 ph.n, 0⟩
    have hTL : TailLoc P _ _ ⟨BitVec.setWidth 64 y3 + 8, 8⟩ := ⟨a, y3, ha, h1', rfl⟩
    intro _
    refine ⟨_, 0, Memory.get?_append_last _ _, fun hl => ⟨?_, hTL, tr, old, htr,
      read?_mono (prefix_append _ _) hrd.val, hz, noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _⟩,
      fun _ => .inr hTL, fun _ => .inr (.inr hTL)⟩
    have hV : σ.vs.vwOld < c.mem.last + 1 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel (by decide))
    have hNF : ∀ Dp : Val → Prop, ph.Dp = Dp →
        NodeFrozenAt ph.δ Dp (Res.only ((planE2 P).gives ⟨BitVec.setWidth 64 y3 + 8, 8⟩
          (BitVec.setWidth 128 ph.n)) σ.r) (c.mem.last + 1) := by
      rintro Dp rfl
      refine ⟨O, J, ?_, hOq, d, td, hX, hm, Nat.lt_of_le_of_lt htd hV, hD⟩
      rw [gives_link hL hph hl]; simp only [Res.only, List.mem_singleton, ↓reduceIte]; exact hOJ
    rcases hph.1 with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3, e4⟩
    · refine .inl ⟨by rw [e1]; simp, ?_⟩
      have := hNF _ e3; rw [e2] at this; exact this
    · refine .inr ⟨by rw [e1]; simp, ?_, (e4 σ hXph).msg hanc _⟩
      have := hNF _ e3; rw [e2] at this; exact this
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  have hcom' := hcom.rmw hs'
  have hX' := hph.2.rmw hXph hs' rfl fun new hn => by
    obtain ⟨-, rfl⟩ := casOp64_some hn; exact xok_obl hL hph _
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -, hr⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, -, -, -, -⟩
  · exact .inl ⟨casOp64_none hon, hcom', ⟨O, J, by rw [hr]; exact hOJ, hOq, d, td, hX, hm,
      Nat.le_trans htd hvle.vwOld, hD⟩, hX'⟩
  · obtain ⟨hz, rfl⟩ := casOp64_some hon
    have hat : a < tw := hav.elim
      (fun h => Nat.lt_of_le_of_lt h (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_left _ _)) (hwb.rel (by decide))))
      fun h => Nat.lt_of_le_of_lt h hwb.vwNew
    exact .inr ⟨hz, hcom', hX', tw, _, _, 0, Treiber.WriteSnap.get?_new hws, by simp, a, y3, hat,
      read?_mono (rmw_snap_prefix hs') h1, rfl⟩

end Kraken.Promising.Lower.WcMsq
