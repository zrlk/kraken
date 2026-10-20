/-
**The verification conditions of WeakCore's
`deq`** (`wcDeqFrag`, `Lower/WcMsqProg.lean`) on msqueue2's dequeuer
environment `ED2 P` (`EnvGCAdj` on `planD2`, thread `1`, `Arch.armv8`). The
protocol (`form2`, `ghost2`, `planD2`) is used unchanged.

What differs from msqueue2's `vc_d_*2` (`EnvG/MsQueue2VC.lean`):

- the loads of `head` and of the link are plain `ldr`s. A plain read raises
  only `vrOld` (`LoadViews.vrOld`), not `vrNew`, so the link read is recorded
  at `tr0 ≤ vrOld ∨ tr0 ≤ vrNew` (`DQ3w`; the second case when forwarded);
- there is no `head = tail` check: the `head` `casal`'s release obligation is
  `HeadF` exactly as in `vc_d_cas2` (it only needs the two reads);
- the payload is loaded **after** the `casal`. Its window reaches the link
  message because the `casal`'s write `tw` is above `vrOld` (`WriteBound.rel`)
  and an acquire-release RMW raises `vrNew` to the coherence view of its
  location (`rmw_acqRel_coh_le_vrNew`, below), which is at least `tw`. So the
  payload read is below no write of the data word up to `tr0`, msqueue1's
  `DoneAt`, and the dequeue is msqueue2's `Deq`.

`rmw_acqRel_coh_le_vrNew` is a fact of `EnvGC`'s RMW step (`RmwOutC`:
`σ'.vs = (rmwAfter …).views`, the machine's `rmwPost`) that `RmwFactsC` does
not export; a candidate for export.
-/
import Kraken.Promising.Lower.WcMsqProg

namespace Kraken.Promising.Lower.WcMsq

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_mono prefix_append)

/-- **An acquire-release RMW raises `vrNew` to its location's coherence
view** (`Arch.armv8`, a successful RMW of `EnvGC`): the machine's `rmwPost`
(`vrNew := max vrNew (getCoh l)`). -/
theorem rmw_acqRel_coh_le_vrNew {I : ISA} {tid : Nat} {pl : Plan} {σ σ' : State I} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old new : Val}
    (h : (EnvGC I Arch.armv8 tid pl).step (.rmw .acqRel addr n op) σ old σ') (hon : op old = some new) :
    σ'.vs.getCoh ⟨addr, n⟩ ≤ σ'.vs.vrNew := by
  obtain ⟨c, x, -, -, hold, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.armv8 tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hn, -⟩ | ⟨new', cx', tw, -, -, -, -, -, -, hvs, -⟩
  · simp [hn] at hon
  · rw [hvs]
    exact Nat.le_max_right _ _

variable {P : Params2} {Y : State isa → Prop}

/-- **After `ldr x5, [x8]`** (the link `[y3 + 8]`, read plain at `tr0`):
`DQ3` with `tr0` below `vrOld` (or `vrNew`, if forwarded). -/
def DQ3w (P : Params2) (Y : State isa → Prop) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD2 P σ ∧ Y σ ∧ ∃ a tr0, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ (tr0 ≤ σ.vs.vrOld ∨ tr0 ≤ σ.vs.vrNew)

/-- **After the successful `casal x6, x5, [x0]`**: the reads, the link read
below `vrNew`, the own swing of `head` at `tw ≤ vwOld` to `y5`, and every
earlier dequeue `F x0` below `tw`. -/
def SwD (P : Params2) (y3 y5 : Val) (F : BitVec 64 → Prop) (σ : State isa) : Prop :=
  ComD2 P σ ∧ ∃ a tr0 tw vh w, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ BitVec.setWidth 64 y5 ≠ 0 ∧
    tr0 ≤ σ.vs.vrNew ∧ σ.snap.mem.get? tw = some ⟨P.head, vh, w⟩ ∧
    BitVec.setWidth 64 vh = BitVec.setWidth 64 y5 ∧ tw ≤ σ.vs.vwOld ∧
    ∀ x0, F x0 → ∃ V1 < tw, Deq σ.snap.mem P V1 x0

theorem DQ3w.fence (hY : YOk P Y) {y3 y5 : Val} {σ σ' : State isa} (h : DQ3w P Y y3 y5 σ) (hf : FenceLe σ σ') :
    DQ3w P Y y3 y5 σ' := by
  obtain ⟨h1, hy, a, tr0, h2, h3, h4⟩ := h
  have hro : σ'.vs.vrOld = σ.vs.vrOld := by rw [hf.vs]
  exact ⟨h1.fence hf, hY.fence hy hf, a, tr0, hf.snap ▸ h2, hf.snap ▸ h3,
    h4.imp (fun h => hro ▸ h) fun h => Nat.le_trans h hf.vrNew⟩

theorem SwD.fence {y3 y5 : Val} {F : BitVec 64 → Prop} {σ σ' : State isa} (h : SwD P y3 y5 F σ)
    (hf : FenceLe σ σ') : SwD P y3 y5 F σ' := by
  obtain ⟨h1, a, tr0, tw, vh, w, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hwo : σ'.vs.vwOld = σ.vs.vwOld := by rw [hf.vs]
  exact ⟨h1.fence hf, a, tr0, tw, vh, w, hf.snap ▸ h2, hf.snap ▸ h3, h4, Nat.le_trans h5 hf.vrNew,
    hf.snap ▸ h6, h7, hwo ▸ h8, hf.snap ▸ h9⟩

/-- **VC `ldr x3, [x0]`**: `head` read (plain). -/
theorem vc_d_ldr_head (hY : YOk P Y) (σ : State isa) (h : ComD2 P σ) (hy : Y σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED2 P).step (.load .plain xcl P.head.addr P.head.bytes) σ v σ' → DQ1 P Y v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  refine ⟨h.load hf, hY.load hy hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **VC `ldr x5, [x8]`** (`x8 = x3 + 8`): the link read, plain (`DQ3w`). -/
theorem vc_d_ldr_link (hY : YOk P Y) (σ : State isa) {y3 : Val} (h : DQ1 P Y y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED2 P).step (.load .plain xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' →
      DQ3w P Y y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, hy, a, ha⟩ := h
  refine ⟨hc.load hf, hY.load hy hf, a, ?_⟩
  obtain ⟨hanc, -, -, tr0, hrd, hlv, -⟩ := hf
  refine ⟨tr0, hanc.read? ha, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact .inr (Nat.le_trans (hc.2.2.2.2.2 _ f hf) hlv.mono.vrNew)
  · exact .inl (hlv.vrOld hfw)

/-- **VC `casal x6, x5, [x0]`** (`x6 = x3`, `x5 ≠ 0`, no `head = tail`
check): permitted (`HeadF`, as `vc_d_cas2`); after it `ComD2` and `Y`, and
on success `SwD` with every `First` of the state before it below the swing. -/
theorem vc_d_casw (hL : QLocs2 P) (hY : YOk P Y) (σ : State isa) {y3 y5 : Val} (h : DQ3w P Y y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) :
    (ED2 P).ok (.rmw .acqRel P.head.addr P.head.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED2 P).step (.rmw .acqRel P.head.addr P.head.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' →
        ComD2 P σ' ∧ Y σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 →
          SwD P y3 y5 (fun x0 => First P x0 σ) σ') := by
  obtain ⟨hc, hy, a, tr0, h1, h2, h3⟩ := h
  have hW := hc.1
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsW P.head := .inl rfl
  refine ⟨⟨hc.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planD2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planD2_gives]; simp
  · obtain ⟨ho, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    refine form2_ht hL _ (.inl rfl) (fun _ => ?_) fun hx => absurd hx hL.q1.head_tail
    obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 y5), 1⟩
    exact ⟨by simpa using hnz, tr, old, tr0, y5, htr, read?_mono (prefix_append _ _) hrd.val,
      noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _, hb, by rw [ho]; exact h2', by simp⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', hY.rmw hy hs', fun heq => ?_⟩
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, hwb, hcoh, hvw, -, -, -⟩
  · exact absurd heq (casOp64_none hon)
  have hvr := rmw_acqRel_coh_le_vrNew hs' hon
  obtain ⟨-, rfl⟩ := casOp64_some hon
  have hrel := hwb.rel (by decide)
  have hpre := rmw_snap_prefix hs'
  refine ⟨hc.rmw hs', a, tr0, tw, _, 1, read?_mono hpre h1, read?_mono hpre h2, hnz, ?_,
    Treiber.WriteSnap.get?_new hws, by simp, hvw (by decide), fun x0 ⟨V1, hd1, hv1⟩ =>
      ⟨V1, Nat.lt_of_le_of_lt hv1 (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hrel), hd1.mono hpre⟩⟩
  rcases h3 with h3 | h3
  · have : σ.vs.vrOld < tw :=
      Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hrel
    exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt h3 this)) (Nat.le_trans hcoh hvr)
  · exact Nat.le_trans h3 hvle.vrNew

/-- **VC `ldr w1, [x5]`** (the payload, after the swing): its window covers
the link read, so the dequeue is a `Deq` at the swing (`First`), above every
earlier dequeue (`DoneD2`). -/
theorem vc_d_ldr_payload (hY : YOk P Y) (σ : State isa) {y3 y5 : Val} {F : BitVec 64 → Prop}
    (h : SwD P y3 y5 F σ) (hy : Y σ) {xcl : Bool} :
    ∀ u (σ' : State isa), (ED2 P).step (.load .plain xcl (BitVec.setWidth 64 y5) 4) σ u σ' →
      ComD2 P σ' ∧ Y σ' ∧ First P (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ' ∧
        ∀ x0, F x0 → DoneD2 σ'.snap.mem P x0 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, tr0, tw, vh, w, h1, h2, hnz, h3, hg, hvh, hvw, hF⟩ := h
  refine ⟨hc.load hf, hY.load hy hf, ?_⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  have hpre := Treiber2.AnchorOk.prefix hanc
  have hdone : DoneAt σ'.snap.mem P.toParams y3 y5 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) := by
    refine ⟨a, tr0, tl, u, hanc.read? h1, hanc.read? h2, hnz, hrd.val, fun p wm ha hb hg hl => ?_, rfl⟩
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, ha, Nat.le_trans hb (Nat.le_trans h3
      (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y5, 4⟩)), hg, hl⟩
    rw [hrd.window] at this; cases this
  have hdq : Deq σ'.snap.mem P tw (BitVec.setWidth 64 (BitVec.setWidth 32 u)) :=
    ⟨y3, y5, vh, w, hdone, Memory.get?_of_prefix hpre.2 hg, hvh⟩
  refine ⟨⟨tw, hdq, by rw [hlv.vwOld]; exact hvw⟩, fun x0 hx0 => ?_⟩
  obtain ⟨V1, hV1, hd1⟩ := hF x0 hx0
  exact ⟨V1, tw, hV1, hd1.mono hpre, hdq⟩

end Kraken.Promising.Lower.WcMsq
