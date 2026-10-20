/-
Part 3: **the dequeuers' verification conditions
of `msqueue3.kl`** on `EnvGCAdj`, AArch64 (`Arch.armv8`), for a dequeuer
of any thread id `k` on `planD2 P`.

These are msqueue2's dequeuer VCs (`EnvG/MsQueue2VC.lean`, thread `1`), for
one dequeue and with the thread id a parameter:

- `ComD3 P k`: msqueue2's `ComD2` with the identity `IdD P k` in place of
  the acquire ids: thread `1` holds the acquire id `0` of every queue word,
  thread `2` the token `tokD2` whole (`EnvG/MsQueue3Ghost.lean`);
- `DQ1'`, `DQ3'`, `DQ4'` after the reads of `head`, `[y3 + 8]` and `[y5]`;
- `vc_d3_cas`: the `head` `casal` releases `HeadF` (the overwritten
  message is adjacent) and, on success, records the dequeuer's own swing
  message with writer `k` (`DoneK`, `EnvG/MsQueue3Final.lean`). A competing
  dequeuer's success needs nothing here: a failing `casal` writes nothing
  and the code retries.

The enqueuer's VCs are msqueue2's, unchanged (the enqueuer's code is
`enq2Prog`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue3Final
import Kraken.Promising.SLR.EnvG.MsQueue2VC

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none read?_of_get? get?_of_read? initVal_eq
  get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_le_last read?_mono rmw_success_fwd prefix_append)

/-- Dequeuer `k`'s environment. -/
noncomputable abbrev ED3 (P : Params2) (k : Nat) : SharedEnv := EnvGCAdj isa Arch.armv8 k (planD2 P)

/-- **Dequeuer `k`'s identity** on its resource: thread `1` holds the
acquire id `0` of every queue word, thread `2` the token `tokD2` whole. -/
def IdD (P : Params2) (k : Nat) (r : Res) : Prop :=
  (k = 1 → ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∧ (k = 2 → 1 ≤ (r.wr (tokD2 P)).q)

/-- **Dequeuer `k`'s common facts** (msqueue2's `ComD2`, identity
`IdD`). -/
def ComD3 (P : Params2) (k : Nat) (σ : State isa) : Prop :=
  GW2 P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ 0 < (σ.r.wr P.tail).q ∧ IdD P k σ.r ∧ InitV2 σ.snap.mem P ∧ FwdAll σ

/-- **After `ldar x3, [x0]`** of `y3`. -/
def DQ1' (P : Params2) (k : Nat) (y3 : Val) (σ : State isa) : Prop :=
  ComD3 P k σ ∧ ∃ a, σ.snap.mem.read? P.head a = some y3

/-- **After `ldar x5, [x8]`** of `y5`. -/
def DQ3' (P : Params2) (k : Nat) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD3 P k σ ∧ ∃ a tr0, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ tr0 ≤ σ.vs.vrNew

/-- **After `ldr w7, [x5]`**. -/
def DQ4' (P : Params2) (k : Nat) (y3 y5 : Val) (x : BitVec 64) (σ : State isa) : Prop :=
  ComD3 P k σ ∧ DoneAt σ.snap.mem P.toParams y3 y5 x

/-- **`ddoneN`** with `X10 = x`. -/
def Dn3 (P : Params2) (k : Nat) (x : BitVec 64) (σ : State isa) : Prop := ComD3 P k σ ∧ DoneK σ.snap.mem P k x

section DeqKeep

variable {P : Params2} {k : Nat} {σ σ' : State isa}

theorem ComD3.fence (h : ComD3 P k σ) (hf : FenceLe σ σ') : ComD3 P k σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.r ▸ h4, hf.snap ▸ h5, fun l f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hf.vrNew

theorem ComD3.load {kl : LoadKind} {l : Loc} {v : Val} (h : ComD3 P k σ)
    (hf : LoadFacts Arch.armv8 k σ σ' kl l v) : ComD3 P k σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, hr ▸ h4, h5.of_init hanc.snap.init, fun l f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hlv.mono.vrNew

theorem ComD3.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComD3 P k σ)
    (hs : (EnvGC isa Arch.armv8 k (planD2 P)).step (.rmw .acqRel addr n op) σ old σ') : ComD3 P k σ' := by
  obtain ⟨h1, h2, h3, ⟨h4a, h4b⟩, h5, h6⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, ⟨fun hk x hx => ?_, fun hk => ?_⟩, h5.of_init (rmw_snap_init hs), ?_⟩
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h2
    · apply q_op_pos; rw [afterD2_q]; exact h2
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h3
    · apply q_op_pos; rw [afterD2_q]; exact h3
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h4a hk x hx
    · show 1 ≤ ((planD2 P).after _ new tw Pc σ.r).acq x 0 + C.acq x 0
      rw [afterD2_acq]; have := h4a hk x hx; omega
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h4b hk
    · apply q_op_ge_one; rw [afterD2_q]; exact h4b hk
  · intro l f hfw
    rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : l = ⟨addr, n⟩
    · subst hl; exact rmw_success_fwd hs hnew f hfw
    · rw [rmw_success_getFwd_ne hs hnew hl] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew

theorem DQ1'.fence {y3 : Val} (h : DQ1' P k y3 σ) (hf : FenceLe σ σ') : DQ1' P k y3 σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

theorem DQ3'.fence {y3 y5 : Val} (h : DQ3' P k y3 y5 σ) (hf : FenceLe σ σ') : DQ3' P k y3 y5 σ' := by
  obtain ⟨h1, a, tr0, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, a, tr0, hf.snap ▸ h2, hf.snap ▸ h3, Nat.le_trans h4 hf.vrNew⟩

theorem DQ4'.fence {y3 y5 : Val} {x : BitVec 64} (h : DQ4' P k y3 y5 x σ) (hf : FenceLe σ σ') :
    DQ4' P k y3 y5 x σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

theorem Dn3.fence {x : BitVec 64} (h : Dn3 P k x σ) (hf : FenceLe σ σ') : Dn3 P k x σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

end DeqKeep

/-! ## The dequeuer -/

section Deq

variable {P : Params2} {k : Nat}

/-- **VC `ldar x3, [x0]`**: `head` read. -/
theorem vc_d3_ldar_head (σ : State isa) (h : ComD3 P k σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED3 P k).step (.load .acq xcl P.head.addr P.head.bytes) σ v σ' → DQ1' P k v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  refine ⟨h.load hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **A load keeps `DQ1'`** (`ldar x4, [x1]`). -/
theorem vc_d3_load (σ : State isa) {y3 : Val} (h : DQ1' P k y3 σ) {kl : LoadKind} {xcl : Bool}
    {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (ED3 P k).step (.load kl xcl a n) σ v σ' → DQ1' P k y3 σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, ha⟩ := h
  refine ⟨hc.load hf, a, ?_⟩
  obtain ⟨hanc, -⟩ := hf
  exact hanc.read? ha

/-- **VC `ldar x5, [x8]`** (`x8 = x3 + 8`): the link read at `tr0 ≤ vrNew`. -/
theorem vc_d3_ldar_link (σ : State isa) {y3 : Val} (h : DQ1' P k y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED3 P k).step (.load .acq xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' →
      DQ3' P k y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, ha⟩ := h
  refine ⟨hc.load hf, a, ?_⟩
  obtain ⟨hanc, -, -, tr0, hrd, hlv, -⟩ := hf
  refine ⟨tr0, hanc.read? ha, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (hc.2.2.2.2.2 _ f hf) hlv.mono.vrNew
  · exact (hlv.acq (by decide) hfw).1

/-- **VC `casal x6, x5, [x1]`** (helping: `x6 = x3`, `x5 ≠ 0`): permitted
(`Prov` from `head`), `ComD3` after it. -/
theorem vc_d3_help (hL : QLocs2 P) (σ : State isa) {y3 y5 : Val} (h : DQ3' P k y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) :
    (ED3 P k).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED3 P k).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' → ComD3 P k σ' := by
  obtain ⟨hc, a, tr0, h1, h2, -⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hc.2.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => hc.rmw (envGCAdj_step_iff.mp hs)⟩
  · rw [e, planD2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.impure hq new
  · rw [e, planD2_gives]; simp
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hc.1.rel_w hq]
    exact form2_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.q1.head_tail)
      fun _ => .inr (prov_of_reads hanc (.inl rfl) h1 h2 hnz _)

/-- **VC `ldr w7, [x5]`** (`x5 ≠ 0`): its window covers the link read
(`DQ4'`). -/
theorem vc_d3_ldr (σ : State isa) {y3 y5 : Val} (h : DQ3' P k y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) {xcl : Bool} :
    ∀ u (σ' : State isa), (ED3 P k).step (.load .plain xcl (BitVec.setWidth 64 y5) 4) σ u σ' →
      DQ4' P k y3 y5 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, a, tr0, h1, h2, h3⟩ := h
  refine ⟨hc.load hf, ?_⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨a, tr0, tl, u, hanc.read? h1, hanc.read? h2, hnz, hrd.val, fun p wm ha hb hg hl => ?_, rfl⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, ha, Nat.le_trans hb (Nat.le_trans h3
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y5, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **VC `casal x6, x5, [x0]`** (`x6 = x3`): permitted (`HeadF`: the
overwritten message is adjacent); after it `ComD3`, and on success its own
swing (writer `k`) records the dequeue (`DoneK`). -/
theorem vc_d3_cas (hL : QLocs2 P) (σ : State isa) {y3 y5 : Val} {x : BitVec 64} (h : DQ4' P k y3 y5 x σ) :
    (ED3 P k).ok (.rmw .acqRel P.head.addr P.head.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED3 P k).step (.rmw .acqRel P.head.addr P.head.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' →
        ComD3 P k σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 → DoneK σ'.snap.mem P k x) := by
  obtain ⟨hc, hd⟩ := h
  obtain ⟨a, tr0, tl, u, h1, h2, hnz, -⟩ := id hd
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
    obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 y5), k⟩
    exact ⟨by simpa using hnz, tr, old, tr0, y5, htr, read?_mono (prefix_append _ _) hrd.val,
      noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _, hb, by rw [ho]; exact h2', by simp⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', fun heq => ?_⟩
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, -, -, -, -, -, -⟩
  · exact absurd heq (casOp64_none hon)
  obtain ⟨-, rfl⟩ := casOp64_some hon
  exact ⟨tw, y3, y5, _, hd.mono (rmw_snap_prefix hs'), Treiber.WriteSnap.get?_new hws, by simp⟩

end Deq

end Kraken.Promising.SLR.EnvG.MsQueue
