/-
**Msqueue3 part 3: the per-access verification
conditions of `msqueue3.kl`'s try-once dequeuers** on `EnvGCAdj`, x64
(`Arch.tso`): dequeuer `w ∈ {1, 2}` is thread `w` on `planD3 P w`
(`EnvG/X64MsQueue3Ghost.lean`). The enqueuer is `msqueue2.kl`'s, with its
VCs (`EnvG/X64MsQueue2VC.lean`) at parameters with `P.trk = true`.

`X64MsQueue2VC`'s dequeuer VCs generalised to thread `w`, with the pop token
in place of the frame `Y`: the loop at `deq` holds `L0` (the common facts
`ComD3` and the pop token whole); the reads give `L1`, `L2`, `L3` (as
`D1`–`D3`); the helping swing of `tail` keeps `L0`; the swing of `head`
releases `HeadF` with the pop token in the slot (`Params.HW`) and records
the dequeue (`Deq3`); a failed swing keeps `L0`; the empty exit keeps the
pop token (`DoneD3`'s first disjunct).
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3Final

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono read?_le_last
  prefix_append get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 cmpxOp64_casMatch)
open Kraken.Promising.X64.EnvG.Treiber2X (rmw_success_fwd_tso)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- Dequeuer `w`'s environment (thread `w`). -/
noncomputable abbrev ED3 (P : Params) (w : Nat) : SharedEnv := EnvGCAdj isa Arch.tso w (planD3 P w)

/-! ## The dequeuer's predicates -/

/-- **Dequeuer `w`'s common facts**: the ghost facts, a positive share of
`head` and `tail`, (dequeuer `1`) the acquire id `0` of every queue word, the
initial values, every forwarding item at or below `vrNew`, its mark whole. -/
def ComD3 (P : Params) (w : Nat) (σ : EStateX) : Prop :=
  GW P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ 0 < (σ.r.wr P.tail).q ∧ (w = 1 → ∀ x, P.IsW x → 1 ≤ σ.r.acq x 0) ∧
    InitV σ.snap.mem P ∧ FwdAll σ ∧ TokFrozen (markT P w) σ.r

/-- **At `deq`**: the common facts and the pop token whole. -/
def L0 (P : Params) (w : Nat) (σ : EStateX) : Prop := ComD3 P w σ ∧ TokFrozen (P.popTok w) σ.r

/-- **After `movq (head),%rbx`** of `y3`, read at `tA ≤ vrNew`. -/
def L1 (P : Params) (w : Nat) (y3 : Val) (σ : EStateX) : Prop :=
  L0 P w σ ∧ ∃ tA, σ.snap.mem.read? P.head tA = some y3 ∧ tA ≤ σ.vs.vrNew

/-- **After `movq (tail),%rdx`** of `yt`, read at `tB ≤ vrNew`, its window
up to `tA`. -/
def L2 (P : Params) (w : Nat) (y3 yt : Val) (σ : EStateX) : Prop :=
  L0 P w σ ∧ ∃ tA tB, σ.snap.mem.read? P.head tA = some y3 ∧ σ.snap.mem.read? P.tail tB = some yt ∧
    tB ≤ σ.vs.vrNew ∧ (tB < tA → NoMsgIn σ.snap.mem P.tail tB (tA + 1))

/-- **After `movq (%rbx),%rcx`** of `u`, its window up to `tB`. -/
def L3 (P : Params) (w : Nat) (y3 yt u : Val) (σ : EStateX) : Prop :=
  L0 P w σ ∧ ∃ tA tB tl, σ.snap.mem.read? P.head tA = some y3 ∧ σ.snap.mem.read? P.tail tB = some yt ∧
    (tB < tA → NoMsgIn σ.snap.mem P.tail tB (tA + 1)) ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ tl = some u ∧
    NoMsgIn σ.snap.mem ⟨BitVec.setWidth 64 y3, 8⟩ tl (tB + 1)

/-- **`ddone`** with `r12 = x`. -/
def Dn3 (P : Params) (w : Nat) (x : BitVec 64) (σ : EStateX) : Prop :=
  ComD3 P w σ ∧ DoneD3 σ.snap.mem P w σ.r x

section DeqKeep

variable {P : Params} {w : Nat} {σ σ' : EStateX}

theorem afterD3_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.popTok w) :
    (((planD3 P w).after l v tw cl r).wr x).q = (r.wr x).q := by
  have hg : x ∉ (planD3 P w).gives l v := by rw [planD3_gives]; split <;> simp [hx]
  unfold Plan.after
  split
  · rw [Res.addW_q, planD3_keep, drop_wr hg]
  · rw [Res.addW_q]

theorem afterD3_acq (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.popTok w)
    (ι : PredId) : ((planD3 P w).after l v tw cl r).acq x ι = r.acq x ι := by
  have hg : x ∉ (planD3 P w).gives l v := by rw [planD3_gives]; split <;> simp [hx]
  unfold Plan.after
  split
  · rw [Res.addW_acq, planD3_keep]; simp only [Res.drop, hg, ↓reduceIte]
  · rw [Res.addW_acq]

/-- A location other than the pop token keeps its fraction over an RMW. -/
theorem q_rmw3 {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} {x : Loc}
    (hs : (EnvGC isa Arch.tso w (planD3 P w)).step (.rmw .acqRel addr n op) σ old σ') (hx : x ≠ P.popTok w) :
    (σ.r.wr x).q ≤ (σ'.r.wr x).q := by
  rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
  · grind
  · show _ ≤ (((planD3 P w).after _ new tw Pc σ.r).wr x).q + (C.wr x).q
    rw [afterD3_q _ _ _ _ _ hx]
    have := (C.wr x).nonneg
    grind

theorem ComD3.fence (h : ComD3 P w σ) (hf : FenceLe σ σ') : ComD3 P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.r ▸ h4, hf.snap ▸ h5, fun l f hfw => ?_, by
    unfold TokFrozen; rw [hf.r]; exact h7⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hf.vrNew

theorem ComD3.load {k : LoadKind} {l : Loc} {v : Val} (h : ComD3 P w σ) (hf : LoadFacts Arch.tso w σ σ' k l v) :
    ComD3 P w σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, hr ▸ h4, h5.of_init hanc.snap.init, fun l f hfw => ?_, by
    unfold TokFrozen; rw [hr]; exact h7⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hlv.mono.vrNew

theorem ComD3.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComD3 P w σ)
    (hw : w ≤ 2) (hs : (EnvGC isa Arch.tso w (planD3 P w)).step (.rmw .acqRel addr n op) σ old σ') :
    ComD3 P w σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, ?_, h5.of_init (rmw_snap_prefix hs).1, ?_, ?_⟩
  · have := q_rmw3 hs (popTok_ne_8 P w _).symm (x := P.head); grind
  · have := q_rmw3 hs (popTok_ne_8 P w _).symm (x := P.tail); grind
  · intro hw1 x hx
    have hxp : x ≠ P.popTok w := fun he => not_isW_popTok P w (he ▸ hx)
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h4 hw1 x hx
    · show 1 ≤ ((planD3 P w).after _ new tw Pc σ.r).acq x 0 + C.acq x 0
      rw [afterD3_acq _ _ _ _ _ hxp]; have := h4 hw1 x hx; omega
  · intro l f hfw
    rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : l = ⟨addr, n⟩
    · subst hl; exact rmw_success_fwd_tso hs hnew f hfw
    · rw [rmw_success_getFwd_ne_tso hs hnew hl] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
  · unfold TokFrozen at *
    have := q_rmw3 hs (markT_ne_popTok P w w hw); grind

theorem L0.fence (h : L0 P w σ) (hf : FenceLe σ σ') : L0 P w σ' :=
  ⟨h.1.fence hf, by unfold TokFrozen; rw [hf.r]; exact h.2⟩

theorem L0.load {k : LoadKind} {l : Loc} {v : Val} (h : L0 P w σ) (hf : LoadFacts Arch.tso w σ σ' k l v) :
    L0 P w σ' :=
  ⟨h.1.load hf, by obtain ⟨-, hr, -⟩ := hf; unfold TokFrozen; rw [hr]; exact h.2⟩

/-- An RMW to `tail`, or a failed one, keeps `L0`. -/
theorem L0.rmw {addr : BitVec 64} {op : Val → Option Val} {old : Val} (h : L0 P w σ) (hw : w ≤ 2)
    (hs : (EnvGC isa Arch.tso w (planD3 P w)).step (.rmw .acqRel addr 8 op) σ old σ')
    (hk : ⟨addr, 8⟩ ≠ P.head ∨ op old = none) : L0 P w σ' := by
  refine ⟨h.1.rmw hw hs, ?_⟩
  unfold TokFrozen
  rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hon, hr⟩ <;> rw [hr]
  · exact h.2
  · rcases hk with hk | hk
    · apply q_op_ge_one
      have hg : P.popTok w ∉ (planD3 P w).gives ⟨addr, 8⟩ new := by rw [planD3_gives]; simp [hk]
      have hne : P.popTok w ≠ ⟨addr, 8⟩ := popTok_ne_8 P w addr
      unfold Plan.after
      split
      · rw [Res.addW_q, planD3_keep, drop_wr hg]; exact h.2
      · rw [Res.addW_q]; exact h.2
    · rw [hk] at hon; cases hon

theorem L3.back {y3 yt u : Val} (h : L3 P w y3 yt u σ) : L0 P w σ := h.1

theorem L1.fence {y3 : Val} (h : L1 P w y3 σ) (hf : FenceLe σ σ') : L1 P w y3 σ' := by
  obtain ⟨h1, tA, h2, h3⟩ := h
  exact ⟨h1.fence hf, tA, hf.snap ▸ h2, Nat.le_trans h3 hf.vrNew⟩

theorem L2.fence {y3 yt : Val} (h : L2 P w y3 yt σ) (hf : FenceLe σ σ') : L2 P w y3 yt σ' := by
  obtain ⟨h1, tA, tB, h2, h3, h4, h5⟩ := h
  exact ⟨h1.fence hf, tA, tB, hf.snap ▸ h2, hf.snap ▸ h3, Nat.le_trans h4 hf.vrNew, hf.snap ▸ h5⟩

theorem L3.fence {y3 yt u : Val} (h : L3 P w y3 yt u σ) (hf : FenceLe σ σ') : L3 P w y3 yt u σ' := by
  obtain ⟨h1, h⟩ := h
  exact ⟨h1.fence hf, hf.snap ▸ h⟩

theorem Dn3.fence {x : BitVec 64} (h : Dn3 P w x σ) (hf : FenceLe σ σ') : Dn3 P w x σ' :=
  ⟨h.1.fence hf, by unfold Dn3 DoneD3 TokFrozen at *; rw [hf.snap, hf.r]; exact h.2⟩

end DeqKeep

/-! ## The dequeuer -/

section Deq

variable {P : Params} {w : Nat}

/-- The read time of an acquire load is at or below `vrNew` (`FwdAll` if
forwarded). -/
theorem deq3_read_le {σ σ' : EStateX} {l : Loc} {v : Val} (h : ComD3 P w σ) {xcl : Bool}
    (hs : (ED3 P w).step (.load .plain xcl l.addr l.bytes) σ v σ') :
    ∃ tr, σ'.snap.mem.read? l tr = some v ∧ tr ≤ σ'.vs.vrNew ∧
      σ'.snap.mem.writeIn l tr (readBound Arch.tso σ.vs .plain l) = false ∧ σ.vs.vrNew ≤ σ'.vs.vrNew := by
  have hf := step_loadFacts (pl := planD3 P w) hs
  obtain ⟨-, -, -, tr, hrd, hlv, -⟩ := hf
  refine ⟨tr, hrd.val, ?_, hrd.window, hlv.mono.vrNew⟩
  by_cases hfw : Fwded σ.vs l tr
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (h.2.2.2.2.2.1 _ f hf) hlv.mono.vrNew
  · exact (hlv.acq (by decide) hfw).1

/-- **VC `movq (head),%rbx`**: `head` read. -/
theorem vc3_load_head (σ : EStateX) (h : L0 P w σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED3 P w).step (.load .plain xcl P.head.addr P.head.bytes) σ v σ' → L1 P w v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD3 P w) hs
  obtain ⟨tA, hr, hle, -⟩ := deq3_read_le h.1 hs
  exact ⟨h.load hf, tA, hr, hle⟩

/-- **VC `movq (tail),%rdx`**: `tail` read, its window covering `tA`. -/
theorem vc3_load_tail (σ : EStateX) {y3 : Val} (h : L1 P w y3 σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED3 P w).step (.load .plain xcl P.tail.addr P.tail.bytes) σ v σ' → L2 P w y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD3 P w) hs
  obtain ⟨hc, tA, hA, hAle⟩ := h
  obtain ⟨tB, hr, hle, hwin, -⟩ := deq3_read_le hc.1 hs
  obtain ⟨hanc, -⟩ := id hf
  refine ⟨hc.load hf, tA, tB, hanc.read? hA, hr, hle, fun hlt => ?_⟩
  have := noMsgIn_of_window hwin
  intro p wm h1 h2 hg
  exact this p wm h1 (by have := le_readBound_vrNew Arch.tso σ.vs .plain P.tail; omega_t) hg

/-- **VC `movq (%rbx),%rcx`**: the link read, its window covering `tB`. -/
theorem vc3_load_link (σ : EStateX) {y3 yt : Val} (h : L2 P w y3 yt σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED3 P w).step (.load .plain xcl (BitVec.setWidth 64 y3) 8) σ v σ' →
      L3 P w y3 yt v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD3 P w) hs
  obtain ⟨hc, tA, tB, hA, hB, hBle, hwinB⟩ := h
  obtain ⟨hanc, -, -, tl, hrd, -⟩ := id hf
  have hpre := TreiberCommon.AnchorOk.prefix hanc
  refine ⟨hc.load hf, tA, tB, tl, hanc.read? hA, hanc.read? hB, fun hlt => ?_, hrd.val, ?_⟩
  · exact (hwinB hlt).mono hpre (by have := read?_le_last hA; omega_t)
  · have := noMsgIn_of_window hrd.window
    intro p wm h1 h2 hg
    exact this p wm h1 (by
      have := le_readBound_vrNew Arch.tso σ.vs .plain ⟨BitVec.setWidth 64 y3, 8⟩; omega_t) hg

/-- **A load keeps `L3`** (the re-check `cmpq %rbx,(head)`). -/
theorem vc3_load3 (σ : EStateX) {y3 yt u : Val} (h : L3 P w y3 yt u σ) {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {m : Nat} : ∀ v (σ' : EStateX), (ED3 P w).step (.load k xcl a m) σ v σ' → L3 P w y3 yt u σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD3 P w) hs
  obtain ⟨hc, tA, tB, tl, hA, hB, hw1, hl, hw2⟩ := h
  obtain ⟨hanc, -⟩ := id hf
  have hpre := TreiberCommon.AnchorOk.prefix hanc
  refine ⟨hc.load hf, tA, tB, tl, hanc.read? hA, hanc.read? hB,
    fun hlt => (hw1 hlt).mono hpre (by have := read?_le_last hA; omega_t), hanc.read? hl,
    hw2.mono hpre (by have := read?_le_last hB; omega_t)⟩

/-- **VC `lock cmpxchgq %rcx,(tail)`** (helping: `rax = rbx`, `rcx ≠ 0`):
permitted (`TailF`), `L0` after it. -/
theorem vc3_help (hL : QLocs P) (hw : w ≤ 2) (σ : EStateX) {y3 yt u : Val} (h : L3 P w y3 yt u σ)
    (hnz : BitVec.setWidth 64 u ≠ 0) :
    (ED3 P w).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (ED3 P w).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ old σ' → L0 P w σ' := by
  obtain ⟨hc, tA, tB, tl, -, -, -, hl, -⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hc.1.2.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => hc.rmw hw (envGCAdj_step_iff.mp hs) (.inl (Ne.symm
      hL.head_tail))⟩
  · rw [e, planD3_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.1.impure hq new
  · rw [e, planD3_gives]; simp [Ne.symm hL.head_tail]
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hc.1.1.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    exact form_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.head_tail)
      (fun _ => tailF_of hanc E (hc.1.1.mono hanc.ghost) htr hrd.val hadj (by rw [hx]) hl hnz _)
      fun hx => absurd hx.symm hL.head_tail

/-- **VC `lock cmpxchgq %rcx,(head)`** (the swing: `rax = rbx ≠ rdx`):
permitted (`HeadF`; the slot gets the pop token); on success the dequeue
(`Deq3`), on failure `L0`. -/
theorem vc3_pop (hL : QLocs P) (hw : w = 1 ∨ w = 2) (σ : EStateX) {y3 yt u : Val}
    (h : L3 P w y3 yt u σ) (hne : BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 y3) :
    (ED3 P w).ok (.rmw .acqRel P.head.addr P.head.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (ED3 P w).step (.rmw .acqRel P.head.addr P.head.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ old σ' →
        ComD3 P w σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 →
          ∃ V, Deq3 σ'.snap.mem P w V (BitVec.setWidth 64 u)) ∧
          (BitVec.setWidth 64 old ≠ BitVec.setWidth 64 y3 → L0 P w σ') := by
  have hw2 : w ≤ 2 := by omega
  obtain ⟨hc, tA, tB, tl, hA, hB, hw1, hl, hw2'⟩ := h
  have hW := hc.1.1
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsW P.head := .inl rfl
  refine ⟨⟨hc.1.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planD3_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planD3_gives]; simp [Params.popTok, Params.head]; omega
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    refine form_ht hL _ (.inl rfl) (fun _ => ?_) (fun hx => absurd hx hL.head_tail)
      fun _ => .inr ⟨hw, ?_⟩
    · obtain ⟨hAl, hA'⟩ := read_at_append hanc hA ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), w⟩
      obtain ⟨hBl, hB'⟩ := read_at_append hanc hB ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), w⟩
      obtain ⟨hll, hl'⟩ := read_at_append hanc hl ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), w⟩
      have hz : (⟨BitVec.setWidth 64 old, 8⟩ : Loc) = ⟨BitVec.setWidth 64 y3, 8⟩ := by rw [hx]
      refine ⟨tr, old, htr, read?_mono (prefix_append _ _) hrd.val,
        noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _, tA, y3, tB, yt, tl, u, hAl, hA', hx.symm, hBl, hB',
        by rw [hx]; exact hne, fun hlt => ?_, hll, by rw [hz]; exact hl', by simp, ?_⟩
      · exact noMsgIn_at_append hanc (by have := read?_le_last hA; omega_t) (hw1 hlt) _
      · rw [hz]; exact noMsgIn_at_append hanc (by have := read?_le_last hB; omega_t) hw2' _
    · rw [e, planD3_give, planD3_gives]
      have h2 := hc.2; unfold TokFrozen at h2
      simpa [Res.only] using h2
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.1.rmw hw2 hs', fun heq => ?_, fun hne' => ?_⟩
  · obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
    rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, -⟩
    · exact absurd heq ((cmpxOp64_casMatch _ _).none _ hon)
    obtain ⟨-, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    exact ⟨tw, _, TreiberCommon.WriteSnap.get?_new hws, by simp⟩
  · refine hc.rmw hw2 hs' (.inr ?_)
    cases hon : cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u) old with
    | none => rfl
    | some new => exact absurd ((cmpxOp64_casMatch _ _).some _ _ hon).1 hne'

end Deq

end Kraken.Promising.X64.EnvG.MsQueue3X
