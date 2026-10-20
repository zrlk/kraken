/-
Msqueue2 part 4: **the per-access verification
conditions of `msqueue2.kl`** on `EnvGCAdj`, AArch64 (`Arch.armv8`): the
enqueuer is thread `0` on `planE2 P`, the dequeuer thread `1` on `planD2 P`
(`EnvG/MsQueue2Ghost.lean`).

**The enqueuer** runs two phases (`Ph`: node `n`, data word `δ`, its
property `Dp`, and a frame fact `X`): phase 1 enqueues `n1` (`X`: `n2`'s
data word untouched, `Fresh`), phase 2 `n2` (`X`: the enqueuer's own link
message of `n1`, `LinkS`). Per phase: `Start` (the data word `Fresh`),
`EL'` (`enq_loop`: the data word `Written`), `EL1'`/`EL2'` (after the reads
of `tail` and `[y3 + 8]`), `Linked` (after the link: `LinkS` of `n`). The
link `casal` releases `LinkF` at a link word (the slot freezes `δ`; the
address is a `TailLoc`; the overwritten `0` is adjacent, `noMsgIn_of_adj`;
in phase 2 `LinkS` of `n1` gives `LinkMsg`), and `TailLoc` at `head`/`tail`.
The swing releases `SwingF`, the helping `casal` `Prov`.

**The dequeuer** runs two dequeues with a frame fact `Y` (`True`, then
`First x10`: the first dequeue's `Deq` at a swing below `vwOld`): `DQ1`,
`DQ3`, `DQ4` as msqueue1's `D1`, `D3`, `D4`; its `head` `casal` releases
`HeadF` (the overwritten message is adjacent) and records its own message
(`Deq`, `vc_d_cas2`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Final

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none read?_of_get? get?_of_read? initVal_eq
  get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_le_last read?_mono rmw_success_fwd prefix_append)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The enqueuer's environment (thread `0`). -/
noncomputable abbrev EE2 (P : Params2) : SharedEnv := EnvGCAdj isa Arch.armv8 0 (planE2 P)

/-- The dequeuer's environment (thread `1`). -/
noncomputable abbrev ED2 (P : Params2) : SharedEnv := EnvGCAdj isa Arch.armv8 1 (planD2 P)

/-! ## Helpers -/

theorem Perm.op_addW {O J : Perm} (hO : 0 < O.q) (p : Val × Time) : (O.op J).addW p = (O.addW p).op J := by
  refine Perm.ext rfl ?_
  funext p'
  have h1 : 0 < (O.op J).q := q_op_pos hO
  apply propext
  simp only [Perm.addW, Perm.op]
  constructor
  · rintro ((h | h) | ⟨-, rfl⟩)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr ⟨hO, rfl⟩)
  · rintro ((h | ⟨-, rfl⟩) | h)
    · exact .inl (.inl h)
    · exact .inr ⟨h1, rfl⟩
    · exact .inl (.inr h)

theorem drop_wr {L : List Loc} {x : Loc} (h : x ∉ L) (r : Res) : (Res.drop L r).wr x = r.wr x := by
  simp [Res.drop, h]

/-- **An enqueuer RMW not giving `δ` adds to `δ`'s permission.** -/
theorem wr_rmw_frame {P : Params2} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 0 (planE2 P)).step (.rmw k addr n op) σ old σ')
    {δ : Loc} (hδ : δ ≠ ⟨addr, n⟩) (hg : ∀ new, op old = some new → δ ∉ (planE2 P).gives ⟨addr, n⟩ new) :
    ∃ C : Perm, σ'.r.wr δ = (σ.r.wr δ).op C := by
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨Pc, -, hr⟩, -⟩
  · exact ⟨Perm.unit, by rw [hr, Perm.op_unit]⟩
  · refine ⟨(Res.prod ((claimSlotsC Arch.armv8 k σ.vs σ'.g ⟨addr, n⟩ tr).map (·.res))).wr δ, ?_⟩
    rw [hr]
    show (((planE2 P).after _ new tw Pc σ.r).wr δ).op _ = _
    congr 1
    unfold Plan.after
    split
    · rw [Res.addW_wr_ne _ _ hδ, planE2_keep, drop_wr (hg new hon)]
    · rw [Res.addW_wr_ne _ _ hδ]

/-- The message appended at the anchor, read back. -/
theorem read_at_append2 {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {x : Loc} {a : Time} {y : Val} (h : σ.snap.mem.read? x a = some y) (w : Msg) :
    a < c.mem.last + 1 ∧ (c.mem.append w).1.read? x a = some y :=
  read_at_append hanc h w

/-- `NoMsgIn` of an RMW's message from adjacency at the anchor (as
`noTopIn_of_adj`). -/
theorem noMsgIn_of_adj {P : Params2} {tid : Nat} {c : Config isa} {g : Ghost} {tr : Time} (hW : GW2 P g)
    {rF : Nat → Res} {T : Nat → Prop} (E : Erase rF g T c) {x : Loc} (hx : P.IsW x)
    (hadj : AdjAt tid c g x tr (c.mem.last + 1)) (w : Msg) :
    NoMsgIn (c.mem.append w).1 x tr (c.mem.last + 1) := by
  have hwi := hadj.lastAt E (hW.impure hx)
  intro p wm h1 h2 hg hl
  have hle : p ≤ c.mem.last := by omega_t
  rw [Memory.get?_append_of_le _ _ _ hle] at hg
  have : c.mem.writeIn x tr (c.mem.last + 1 - 1) = true :=
    (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, h1, by omega_t, hg, hl⟩
  rw [hwi] at this; cases this

/-! ## The enqueuer's predicates -/

/-- The enqueuer's forwarding item of `tail` at or below `vwNew` (its `tail`
writes are acquire-release RMWs, `rmw_success_fwdW`): a forwarded `ldar` of
`tail` is below every later write. -/
def FwdT (P : Params2) (σ : State isa) : Prop := ∀ f, σ.vs.getFwd P.tail = some f → f.time ≤ σ.vs.vwNew

/-- **The enqueuer's common facts.** -/
def ComE2 (P : Params2) (σ : State isa) : Prop :=
  GW2 P σ.g ∧ (∀ a, 0 < (σ.r.wr ⟨a, 8⟩).q) ∧ 1 ≤ (σ.r.wr P.tokE).q ∧ FwdT P σ

/-- A data word not yet written: a whole part with writes at `0`. -/
def Fresh (δ : Loc) (σ : State isa) : Prop := ∃ O J : Perm, σ.r.wr δ = O.op J ∧ O.q = 1 ∧ ∀ p, O.X p → p.2 = 0

/-- A data word written (msqueue1's `DatOK` at `δ`, `Dp`). -/
def Written (δ : Loc) (Dp : Val → Prop) (σ : State isa) : Prop :=
  ∃ O J : Perm, σ.r.wr δ = O.op J ∧ O.q = 1 ∧
    ∃ d td, O.X (d, td) ∧ (∀ p, O.X p → p.2 ≤ td) ∧ td ≤ σ.vs.vwOld ∧ Dp d

/-- The enqueuer's own link message of `n`. -/
def LinkS (P : Params2) (n : BitVec 64) (σ : State isa) : Prop :=
  ∃ V' x' v' w', σ.snap.mem.get? V' = some ⟨x', v', w'⟩ ∧ BitVec.setWidth 64 v' = n ∧ TailLoc P σ.snap.mem V' x'

/-- **A phase of the enqueuer.** -/
structure Ph where
  n : BitVec 64
  δ : Loc
  Dp : Val → Prop
  X : State isa → Prop

/-- Phase 1: `n1`, `n2`'s data word untouched. -/
def ph1 (P : Params2) : Ph := ⟨P.n1, P.dat, D, Fresh P.dat2⟩
/-- Phase 2: `n2`, the own link message of `n1`. -/
def ph2 (P : Params2) : Ph := ⟨P.n2, P.dat2, D2, LinkS P P.n1⟩

/-- **The frame fact `X` of a phase writing `δ`** survives fences, loads,
the store to `δ` and RMWs not giving `n2`'s data word (unless `δ` is it). -/
structure XOk (P : Params2) (δ : Loc) (X : State isa → Prop) : Prop where
  fence : ∀ {σ σ' : State isa}, X σ → FenceLe σ σ' → X σ'
  load : ∀ {σ σ' : State isa} {k : LoadKind} {l : Loc} {v : Val}, X σ → LoadFacts Arch.armv8 0 σ σ' k l v → X σ'
  store : ∀ {σ σ' : State isa} {v : Val} {b : Bool}, X σ →
    (EE2 P).step (.store .plain false δ.addr δ.bytes v) σ b σ' → X σ'
  rmw : ∀ {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val},
    X σ → (EnvGC isa Arch.armv8 0 (planE2 P)).step (.rmw k addr n op) σ old σ' → n = 8 →
    (∀ new, op old = some new → P.dat2 ∉ (planE2 P).gives ⟨addr, n⟩ new ∨ δ = P.dat2) → X σ'

/-- **A phase's facts**: its node, data word and property, and its frame. -/
def PhOk (P : Params2) (ph : Ph) : Prop :=
  ((ph.n = P.n1 ∧ ph.δ = P.dat ∧ ph.Dp = D) ∨
    (ph.n = P.n2 ∧ ph.δ = P.dat2 ∧ ph.Dp = D2 ∧ ∀ σ, ph.X σ → LinkS P P.n1 σ)) ∧ XOk P ph.δ ph.X

/-- **A phase's start**. -/
def Start (P : Params2) (ph : Ph) (σ : State isa) : Prop := ComE2 P σ ∧ Fresh ph.δ σ ∧ ph.X σ
/-- **`enq_loop`**. -/
def EL' (P : Params2) (ph : Ph) (σ : State isa) : Prop := ComE2 P σ ∧ Written ph.δ ph.Dp σ ∧ ph.X σ
/-- **After `ldar x3, [x1]`** of `y3` (read at or below `vwNew`). -/
def EL1' (P : Params2) (ph : Ph) (y3 : Val) (σ : State isa) : Prop :=
  EL' P ph σ ∧ ∃ a, σ.snap.mem.read? P.tail a = some y3 ∧ a ≤ σ.vs.vwNew
/-- **After `ldar x4, [x8]`** of `y4`. -/
def EL2' (P : Params2) (ph : Ph) (y3 y4 : Val) (σ : State isa) : Prop :=
  EL' P ph σ ∧ ∃ a b, σ.snap.mem.read? P.tail a = some y3 ∧ a ≤ σ.vs.vwNew ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ b = some y4
/-- **After the link**. -/
def Linked (P : Params2) (ph : Ph) (σ : State isa) : Prop := ComE2 P σ ∧ ph.X σ ∧ LinkS P ph.n σ

section EnqKeep

variable {P : Params2} {σ σ' : State isa}

theorem ComE2.fence (h : ComE2 P σ) (hf : FenceLe σ σ') : ComE2 P σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, fun f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h4 f hfw) hf.vwNew

theorem ComE2.load {k : LoadKind} {l : Loc} {v : Val} (h : ComE2 P σ) (hf : LoadFacts Arch.armv8 0 σ σ' k l v) :
    ComE2 P σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, fun f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h4 f hfw) hlv.mono.vwNew

theorem afterE2_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (h1 : x ≠ P.dat) (h2 : x ≠ P.dat2) :
    (((planE2 P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planE2_keep, drop_wr (planE2_gives_sub P l v h1 h2)]
  · rw [Res.addW_q]

/-- **A successful armv8 acquire-release RMW** leaves its forwarding item at
or below `vwNew` (as `rmw_success_fwd`). -/
theorem rmw_success_fwdW {tid : Nat} {pl : Plan} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.armv8 tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) : ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.time ≤ σ'.vs.vwNew := by
  obtain ⟨c, x, -, -, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.armv8 tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  intro f hf
  obtain ⟨-, hwv⟩ := writeSuccs_at Arch.armv8 tid hc hev
  obtain ⟨f0, hf0, ht0⟩ := hwv.fwd
  have hcoh := hwv.coh
  rw [hvs] at hf ⊢
  simp only [rmwAfter, rmwPost, show Arch.armv8.rmwFence = false from rfl,
    show (Arch.armv8.rmwKind .acqRel == .acqRel) = true from rfl, Bool.not_false, Bool.and_self, ↓reduceIte,
    Bool.false_eq_true] at hf ⊢
  change cx'.views.getFwd ⟨addr, n⟩ = some f at hf
  rw [hf0] at hf
  cases hf
  rw [ht0]
  exact Nat.le_trans hcoh (Nat.le_max_right _ _)

theorem ComE2.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComE2 P σ)
    (hs : (EnvGC isa Arch.armv8 0 (planE2 P)).step (.rmw .acqRel addr n op) σ old σ') : ComE2 P σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, fun f hf => ?_⟩
  rotate_right
  · rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hf
      exact Nat.le_trans (h4 f hf) (rmw_vle hs).vwNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : P.tail = ⟨addr, n⟩
    · rw [hl] at hf; exact rmw_success_fwdW hs hnew f hf
    · rw [rmw_success_getFwd_ne hs hnew hl] at hf
      exact Nat.le_trans (h4 f hf) (rmw_vle hs).vwNew
  all_goals rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
  · exact h2
  · intro a
    apply q_op_pos
    rw [afterE2_q _ _ _ _ _ (dat_ne_of_8 P.toParams) (dat2_ne_of_8 P)]; exact h2 a
  · exact h3
  · apply q_op_ge_one
    rw [afterE2_q _ _ _ _ _ (Ne.symm (dat_tokE P.toParams)) (Ne.symm (dat2_tokE P))]; exact h3

theorem Fresh.frame {δ : Loc} (h : Fresh δ σ) (hc : ∃ C : Perm, σ'.r.wr δ = (σ.r.wr δ).op C) : Fresh δ σ' := by
  obtain ⟨O, J, hOJ, hq, hX⟩ := h
  obtain ⟨C, hC⟩ := hc
  exact ⟨O, J.op C, by rw [hC, hOJ, Perm.op_assoc], hq, hX⟩

theorem Written.frame {δ : Loc} {Dp : Val → Prop} (h : Written δ Dp σ) (hc : ∃ C : Perm, σ'.r.wr δ = (σ.r.wr δ).op C)
    (hv : σ.vs.vwOld ≤ σ'.vs.vwOld) : Written δ Dp σ' := by
  obtain ⟨O, J, hOJ, hq, d, td, hX, hm, htd, hD⟩ := h
  obtain ⟨C, hC⟩ := hc
  exact ⟨O, J.op C, by rw [hC, hOJ, Perm.op_assoc], hq, d, td, hX, hm, Nat.le_trans htd hv, hD⟩

theorem same_frame {δ : Loc} (h : σ'.r = σ.r) : ∃ C : Perm, σ'.r.wr δ = (σ.r.wr δ).op C :=
  ⟨Perm.unit, by rw [h, Perm.op_unit]⟩

theorem LinkS.mono {n : BitVec 64} (h : LinkS P n σ) (hp : σ.snap.mem.Prefix σ'.snap.mem) : LinkS P n σ' :=
  let ⟨V', x', v', w', hg, hv, ht⟩ := h
  ⟨V', x', v', w', Memory.get?_of_prefix hp.2 hg, hv, ht.mono hp⟩

/-- `Fresh` of `n2`'s data word is phase 1's frame. -/
theorem dat_dat2 {P : Params2} (hL : QLocs2 P) : P.dat ≠ P.dat2 := by
  simp only [Params.dat, Params2.dat2, ne_eq, Loc.mk.injEq, and_true]; exact hL.n12

theorem xok_fresh2 {P : Params2} (hL : QLocs2 P) : XOk P P.dat (Fresh P.dat2) where
  fence h hf := by unfold Fresh; rw [hf.r]; exact h
  load h hf := h.frame (same_frame hf.2.1)
  store h hs := by
    obtain ⟨c, tw, -, -, -, -, -, ⟨_, -, hr⟩, -⟩ := step_storeFacts (pl := planE2 P) hs
    refine h.frame ⟨Perm.unit, ?_⟩
    rw [hr, Perm.op_unit]
    unfold Plan.after
    rw [planE2_rel]
    simp only [not_isW_dat P, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact Res.addW_wr_ne _ _ (Ne.symm (dat_dat2 hL))
  rmw h hs hn hg := h.frame (wr_rmw_frame hs (by rw [hn]; exact (dat2_ne_of_8 P).symm) fun new hn => (hg new hn).resolve_right (dat_dat2 hL))

/-- The own link message of `n1` is phase 2's frame. -/
theorem xok_link1 (P : Params2) : XOk P P.dat2 (LinkS P P.n1) where
  fence h hf := by unfold LinkS; rw [hf.snap]; exact h
  load h hf := h.mono (Treiber2.AnchorOk.prefix hf.1)
  store h hs := by
    obtain ⟨c, tw, hanc, hws, -⟩ := step_storeFacts (pl := planE2 P) hs
    exact h.mono ((Treiber2.AnchorOk.prefix hanc).trans (Treiber2.WriteSnap.prefix hws))
  rmw h hs _ _ := h.mono (rmw_snap_prefix hs)

end EnqKeep

/-! ## Phase and plan facts -/

section PhFacts

variable {P : Params2} {ph : Ph}

theorem isW_bytes {x : Loc} (h : P.IsW x) : x.bytes = 8 := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem PhOk.δb (h : PhOk P ph) : ph.δ.bytes = 4 := by
  rcases h.1 with ⟨-, e, -⟩ | ⟨-, e, -⟩ <;> rw [e] <;> rfl

theorem PhOk.δ8 (h : PhOk P ph) (a : BitVec 64) : (⟨a, 8⟩ : Loc) ≠ ph.δ := fun he => by
  have := congrArg Loc.bytes he; rw [h.δb] at this; simp at this

theorem PhOk.δW (h : PhOk P ph) : ¬ P.IsW ph.δ := fun hw => by
  have := isW_bytes hw; rw [h.δb] at this; simp at this

theorem PhOk.δtok (h : PhOk P ph) : ph.δ ≠ P.tokE := fun he => by
  have := congrArg Loc.bytes he; rw [h.δb] at this; simp [Params.tokE] at this

theorem gives_W {l : Loc} {v : Val} {x : Loc} (h : x ∈ (planE2 P).gives l v) : P.IsW l := by
  unfold Plan.gives at h
  cases hf : (planE2 P).find? l v with
  | none => rw [hf] at h; simp at h
  | some e => obtain ⟨rfl, -, hw, -⟩ := planE2_find_mem hf; exact hw

/-- At a link the enqueuer's release of its phase's node gives the data
word. -/
theorem gives_link (hL : QLocs2 P) (hph : PhOk P ph) {l : Loc} (hl : P.IsL l) :
    (planE2 P).gives l (BitVec.setWidth 128 ph.n) = [ph.δ] := by
  rw [planE2_gives hL (isW_of_isL P hl)]
  unfold gE
  rcases hph.1 with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩ <;> rw [e1, e2] <;> simp [hl, hL.n1v_ne_n2v.symm]

theorem gives_ph (hL : QLocs2 P) (hph : PhOk P ph) {l x : Loc}
    (h : x ∈ (planE2 P).gives l (BitVec.setWidth 128 ph.n)) : x = ph.δ := by
  have hw := gives_W h
  by_cases hl : P.IsL l
  · rw [gives_link hL hph hl] at h; exact List.mem_singleton.mp h
  · rw [planE2_gives hL hw] at h; simp [gE, hl] at h

theorem xok_obl (hL : QLocs2 P) (hph : PhOk P ph) (l : Loc) :
    P.dat2 ∉ (planE2 P).gives l (BitVec.setWidth 128 ph.n) ∨ ph.δ = P.dat2 := by
  rcases hph.1 with ⟨-, e2, -⟩ | ⟨-, e2, -⟩
  · exact .inl fun h => dat_dat2 hL ((gives_ph hL hph h).trans e2).symm
  · exact .inr e2

theorem gives_tail (hL : QLocs2 P) (x : Loc) (v : Val) : x ∉ (planE2 P).gives P.tail v := by
  rw [planE2_gives hL (.inr (.inl rfl))]; simp [gE, hL.not_isL_tail]

end PhFacts

/-! ## The release facts -/

section Rel

variable {P : Params2}

/-- **`form2` of a message to `head`/`tail`**. -/
theorem form2_ht (hL : QLocs2 P) {m : Memory} {l : Loc} {v : Val} {w : Nat} (R : Res) (hl : l = P.head ∨ l = P.tail)
    (hh : l = P.head → HeadF P (m.append ⟨l, v, w⟩).1 (m.last + 1) v)
    (ht : l = P.tail → SwingF P (m.append ⟨l, v, w⟩).1 (m.last + 1) v ∨
      Prov P.toParams (m.append ⟨l, v, w⟩).1 (m.last + 1) v) :
    (form2 P).P v (m.append ⟨l, v, w⟩).1 (m.last + 1) R := by
  intro _
  refine ⟨l, w, Memory.get?_append_last _ _, fun hx => ?_, fun hx => .inl (hh hx), fun hx => (ht hx).imp_right .inl⟩
  rcases hl with rfl | rfl
  · exact absurd hx hL.not_isL_head
  · exact absurd hx hL.not_isL_tail

/-- The own link message, at the anchor's fresh timestamp. -/
theorem LinkS.msg {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} {n : BitVec 64} (h : LinkS P n σ)
    (hanc : AnchorOk tid σ c g) (w : Msg) : LinkMsg P (c.mem.append w).1 (c.mem.last + 1) n := by
  obtain ⟨V', x', v', w', hg, hv, ht⟩ := h
  have hp0 := Treiber2.AnchorOk.prefix hanc
  have hp := hp0.trans (prefix_append c.mem w)
  exact ⟨V', x', v', w', Nat.lt_succ_of_le (c.mem.last_le_of_get?_eq_some (Memory.get?_of_prefix hp0.2 hg)),
    Memory.get?_of_prefix hp.2 hg, hv, ht.mono hp⟩

/-- `Prov` of the value read at `[y + 8]`, `y` read at `head`/`tail`. -/
theorem prov_of_reads {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {x : Loc} (hx : x = P.head ∨ x = P.tail) {a b : Time} {y y' : Val} (h1 : σ.snap.mem.read? x a = some y)
    (h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 y + 8, 8⟩ b = some y') (hnz : BitVec.setWidth 64 y' ≠ 0) (w : Msg) :
    Prov P.toParams (c.mem.append w).1 (c.mem.last + 1) (BitVec.setWidth 128 (BitVec.setWidth 64 y')) := by
  obtain ⟨ha, h1'⟩ := read_at_append hanc h1 w
  obtain ⟨hb, h2'⟩ := read_at_append hanc h2 w
  exact ⟨by simpa using hnz, x, a, y, b, y', hx, ha, h1', hb, h2', by simp⟩

end Rel

/-! ## The enqueuer -/

section Enq

variable {P : Params2} {σ σ' : State isa} {ph : Ph}

theorem EL'.load (hph : PhOk P ph) {k : LoadKind} {l : Loc} {v : Val} (h : EL' P ph σ)
    (hf : LoadFacts Arch.armv8 0 σ σ' k l v) : EL' P ph σ' := by
  refine ⟨h.1.load hf, h.2.1.frame (same_frame hf.2.1) ?_, hph.2.load h.2.2 hf⟩
  obtain ⟨-, -, -, tr, -, hlv, -⟩ := hf
  rw [hlv.vwOld]; exact Nat.le_refl _

theorem EL'.rmw_tail (hL : QLocs2 P) (hph : PhOk P ph) {op : Val → Option Val} {old : Val} (h : EL' P ph σ)
    (hs : (EnvGC isa Arch.armv8 0 (planE2 P)).step (.rmw .acqRel P.tail.addr P.tail.bytes op) σ old σ') :
    EL' P ph σ' :=
  ⟨h.1.rmw hs, h.2.1.frame (wr_rmw_frame hs (hph.δ8 _).symm fun new _ => gives_tail hL _ new) (rmw_vle hs).vwOld,
    hph.2.rmw h.2.2 hs rfl fun new _ => .inl (gives_tail hL _ new)⟩

/-- **VC `str w9, [x2]`** (the phase's data word, a value `v` with `Dp v`):
permitted (pure, the word whole), and `EL'` after it. -/
theorem vc_e_str2 (hph : PhOk P ph) (σ : State isa) (h : Start P ph σ) (v : Val) (hD : ph.Dp v) :
    (EE2 P).ok (.store .plain false ph.δ.addr ph.δ.bytes v) σ ∧
      ∀ b (σ' : State isa), (EE2 P).step (.store .plain false ph.δ.addr ph.δ.bytes v) σ b σ' → EL' P ph σ' := by
  obtain ⟨⟨hW, hpos, htok, hfw⟩, ⟨O, J, hOJ, hOq, hO0⟩, hX⟩ := h
  have e : ({ addr := ph.δ.addr, bytes := ph.δ.bytes } : Loc) = ph.δ := rfl
  have hnw := hph.δW
  have hO : 0 < O.q := by rw [hOq]; decide
  refine ⟨⟨rfl, by rw [e, hOJ]; exact q_op_pos hO, fun _ => by rw [e, hW.rel_ne hnw]; exact Pred.emp_pure _,
    fun hr => by rw [e, planE2_rel] at hr; simp [hnw] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, ⟨_, -, hr⟩, -⟩ := step_storeFacts (pl := planE2 P) hs
  have hafter : ∀ cl, (planE2 P).after ph.δ v tw cl σ.r = σ.r.addW ph.δ (v, tw) := by
    intro cl; unfold Plan.after; rw [planE2_rel]; simp [hnw]
  rw [e, hafter] at hr
  have hwr : ∀ x, x ≠ ph.δ → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨⟨hW.mono hanc.ghost, fun a => by rw [hwr _ (hph.δ8 a)]; exact hpos a,
    by rw [hwr _ (hph.δtok).symm]; exact htok, fun f hf => ?_⟩,
    ⟨O.addW (v, tw), J, ?_, hOq, v, tw, .inr ⟨hO, rfl⟩, ?_, hwv.vwOld (by decide), hD⟩, hph.2.store hX hs⟩
  · rw [hwv.fwdOther P.tail (hph.δ8 P.t)] at hf
    exact Nat.le_trans (hfw f hf) hwv.mono.vwNew
  · rw [hr, Perm.addW_op _ _ hO, ← hOJ]; simp [Res.addW]
  · rintro p (hp | ⟨-, rfl⟩)
    · rw [hO0 p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-- **VC `ldar x3, [x1]`**: `tail` read, at or below `vwNew` (`FwdT` if
forwarded). -/
theorem vc_e_ldar_tail2 (hph : PhOk P ph) (σ : State isa) (h : EL' P ph σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE2 P).step (.load .acq xcl P.tail.addr P.tail.bytes) σ v σ' → EL1' P ph v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE2 P) hs
  refine ⟨h.load hph hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, hlv, -⟩ := hf
  refine ⟨tr, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs P.tail tr
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (h.1.2.2.2 f hf) hlv.mono.vwNew
  · exact (hlv.acq (by decide) hfw).2

/-- **VC `ldar x4, [x8]`** (`x8 = x3 + 8`): the link read. -/
theorem vc_e_ldar_link2 (hph : PhOk P ph) (σ : State isa) {y3 : Val} (h : EL1' P ph y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE2 P).step (.load .acq xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' → EL2' P ph y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE2 P) hs
  obtain ⟨hel, a, ha, hav⟩ := h
  refine ⟨hel.load hph hf, ?_⟩
  obtain ⟨hanc, -, -, tr, hrd, hlv, -⟩ := hf
  exact ⟨a, tr, hanc.read? ha, Nat.le_trans hav hlv.mono.vwNew, hrd.val⟩

/-- **VC `casal x5, x4, [x1]`** (helping: `x5 = x3`, `x4 ≠ 0`): permitted
(`Prov`), `EL'` after it. -/
theorem vc_e_fix2 (hL : QLocs2 P) (hph : PhOk P ph) (σ : State isa) {y3 y4 : Val} (h : EL2' P ph y3 y4 σ)
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

/-- **VC `casal x5, x2, [x8]`** (the link: `x8 = x3 + 8`, `x5 = 0`, `x2` the
phase's node): permitted (`LinkF` at a link, `TailLoc` at `head`/`tail`,
pure elsewhere); it fails (`EL'`) or succeeds (`Linked`: its own message). -/
theorem vc_e_link2 (hL : QLocs2 P) (hph : PhOk P ph) (σ : State isa) {y3 y4 : Val} (h : EL2' P ph y3 y4 σ) :
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
        NodeFrozenAt ph.δ Dp (Res.only ((planE2 P).gives ⟨BitVec.setWidth 64 y3 + 8, 8⟩ (BitVec.setWidth 128 ph.n)) σ.r) (c.mem.last + 1) := by
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
    exact .inr ⟨hz, hcom', hX', tw, _, _, 0, Treiber.WriteSnap.get?_new hws, by simp, a, y3,
      Nat.lt_of_le_of_lt hav hwb.vwNew, read?_mono (rmw_snap_prefix hs') h1, rfl⟩

/-- **VC `casal x5, x2, [x1]`** (the swing to the phase's node): permitted
(`SwingF`), `Linked` after it. -/
theorem vc_e_swing2 (hL : QLocs2 P) (hph : PhOk P ph) (σ : State isa) (h : Linked P ph σ) (x5 : BitVec 64) :
    (EE2 P).ok (.rmw .acqRel P.tail.addr P.tail.bytes (casOp64 x5 ph.n)) σ ∧
      ∀ old (σ' : State isa), (EE2 P).step (.rmw .acqRel P.tail.addr P.tail.bytes (casOp64 x5 ph.n)) σ old σ' →
        Linked P ph σ' := by
  obtain ⟨hcom, hXph, hls⟩ := h
  have hW := hcom.1
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_,
    gives_tail hL _ _, fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planE2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_w hq]
    have hn : ph.n = P.n1 ∨ ph.n = P.n2 := hph.1.imp (fun h => h.1) (fun h => h.1)
    exact form2_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.q1.head_tail)
      fun _ => .inl ⟨ph.n, hn, by simp, hls.msg hanc _⟩
  · have hs' := envGCAdj_step_iff.mp hs
    exact ⟨hcom.rmw hs', hph.2.rmw hXph hs' rfl fun new _ => .inl (gives_tail hL _ new),
      hls.mono (rmw_snap_prefix hs')⟩

end Enq

/-! ## The dequeuer's predicates -/

/-- **The dequeuer's common facts**. -/
def ComD2 (P : Params2) (σ : State isa) : Prop :=
  GW2 P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ 0 < (σ.r.wr P.tail).q ∧ (∀ x, P.IsW x → 1 ≤ σ.r.acq x 0) ∧
    InitV2 σ.snap.mem P ∧ FwdAll σ

/-- The first dequeue's record: its `Deq` at a swing at or below `vwOld`. -/
def First (P : Params2) (x : BitVec 64) (σ : State isa) : Prop := ∃ V1, Deq σ.snap.mem P V1 x ∧ V1 ≤ σ.vs.vwOld

/-- **A frame fact `Y` of a dequeue** survives the dequeuer's fences, loads
and acquire-release RMWs. -/
structure YOk (P : Params2) (Y : State isa → Prop) : Prop where
  fence : ∀ {σ σ' : State isa}, Y σ → FenceLe σ σ' → Y σ'
  load : ∀ {σ σ' : State isa} {k : LoadKind} {l : Loc} {v : Val}, Y σ → LoadFacts Arch.armv8 1 σ σ' k l v → Y σ'
  rmw : ∀ {σ σ' : State isa} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}, Y σ →
    (EnvGC isa Arch.armv8 1 (planD2 P)).step (.rmw .acqRel addr n op) σ old σ' → Y σ'

/-- **After `ldar x3, [x0]`** of `y3`. -/
def DQ1 (P : Params2) (Y : State isa → Prop) (y3 : Val) (σ : State isa) : Prop :=
  ComD2 P σ ∧ Y σ ∧ ∃ a, σ.snap.mem.read? P.head a = some y3

/-- **After `ldar x5, [x8]`** of `y5`. -/
def DQ3 (P : Params2) (Y : State isa → Prop) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD2 P σ ∧ Y σ ∧ ∃ a tr0, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ tr0 ≤ σ.vs.vrNew

/-- **After `ldr w7, [x5]`**. -/
def DQ4 (P : Params2) (Y : State isa → Prop) (y3 y5 : Val) (x : BitVec 64) (σ : State isa) : Prop :=
  ComD2 P σ ∧ Y σ ∧ DoneAt σ.snap.mem P.toParams y3 y5 x

/-- **`ddone1`** with `X10 = x10`, `X11 = x11`. -/
def Dn2 (P : Params2) (x10 x11 : BitVec 64) (σ : State isa) : Prop := ComD2 P σ ∧ DoneD2 σ.snap.mem P x10 x11

section DeqKeep

variable {P : Params2} {σ σ' : State isa}

theorem afterD2_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) :
    (((planD2 P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planD2_keep]; simp [Res.drop]
  · rw [Res.addW_q]

theorem afterD2_acq (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) (ι : PredId) :
    ((planD2 P).after l v tw cl r).acq x ι = r.acq x ι := by
  unfold Plan.after
  split
  · rw [Res.addW_acq, planD2_keep]; simp [Res.drop]
  · rw [Res.addW_acq]

theorem ComD2.fence (h : ComD2 P σ) (hf : FenceLe σ σ') : ComD2 P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.r ▸ h4, hf.snap ▸ h5, fun l f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hf.vrNew

theorem ComD2.load {k : LoadKind} {l : Loc} {v : Val} (h : ComD2 P σ)
    (hf : LoadFacts Arch.armv8 1 σ σ' k l v) : ComD2 P σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, hr ▸ h4, h5.of_init hanc.snap.init, fun l f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hlv.mono.vrNew

theorem ComD2.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComD2 P σ)
    (hs : (EnvGC isa Arch.armv8 1 (planD2 P)).step (.rmw .acqRel addr n op) σ old σ') : ComD2 P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, ?_, h5.of_init (rmw_snap_init hs), ?_⟩
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h2
    · apply q_op_pos; rw [afterD2_q]; exact h2
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h3
    · apply q_op_pos; rw [afterD2_q]; exact h3
  · intro x hx
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h4 x hx
    · show 1 ≤ ((planD2 P).after _ new tw Pc σ.r).acq x 0 + C.acq x 0
      rw [afterD2_acq]; have := h4 x hx; omega
  · intro l f hfw
    rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : l = ⟨addr, n⟩
    · subst hl; exact rmw_success_fwd hs hnew f hfw
    · rw [rmw_success_getFwd_ne hs hnew hl] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew

theorem yok_true : YOk P fun _ => True := ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem yok_first (x : BitVec 64) : YOk P (First P x) where
  fence h hf := by unfold First; rw [hf.snap, hf.vwOld]; exact h
  load h hf := by
    obtain ⟨V1, hd, hv⟩ := h
    obtain ⟨hanc, -, -, tr, -, hlv, -⟩ := hf
    exact ⟨V1, hd.mono (Treiber2.AnchorOk.prefix hanc), by rw [hlv.vwOld]; exact hv⟩
  rmw h hs := let ⟨V1, hd, hv⟩ := h; ⟨V1, hd.mono (rmw_snap_prefix hs), Nat.le_trans hv (rmw_vle hs).vwOld⟩

variable {Y : State isa → Prop}

theorem DQ1.fence (hY : YOk P Y) {y3 : Val} (h : DQ1 P Y y3 σ) (hf : FenceLe σ σ') : DQ1 P Y y3 σ' :=
  ⟨h.1.fence hf, hY.fence h.2.1 hf, hf.snap ▸ h.2.2⟩

theorem DQ3.fence (hY : YOk P Y) {y3 y5 : Val} (h : DQ3 P Y y3 y5 σ) (hf : FenceLe σ σ') : DQ3 P Y y3 y5 σ' := by
  obtain ⟨h1, hy, a, tr0, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, hY.fence hy hf, a, tr0, hf.snap ▸ h2, hf.snap ▸ h3, Nat.le_trans h4 hf.vrNew⟩

theorem DQ4.fence (hY : YOk P Y) {y3 y5 : Val} {x : BitVec 64} (h : DQ4 P Y y3 y5 x σ) (hf : FenceLe σ σ') :
    DQ4 P Y y3 y5 x σ' :=
  ⟨h.1.fence hf, hY.fence h.2.1 hf, hf.snap ▸ h.2.2⟩

theorem Dn2.fence {x y : BitVec 64} (h : Dn2 P x y σ) (hf : FenceLe σ σ') : Dn2 P x y σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

end DeqKeep

/-! ## The dequeuer -/

section Deq

variable {P : Params2} {Y : State isa → Prop}

/-- **VC `ldar x3, [x0]`**: `head` read. -/
theorem vc_d_ldar_head2 (hY : YOk P Y) (σ : State isa) (h : ComD2 P σ) (hy : Y σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED2 P).step (.load .acq xcl P.head.addr P.head.bytes) σ v σ' → DQ1 P Y v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  refine ⟨h.load hf, hY.load hy hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **A load keeps `DQ1`** (`ldar x4, [x1]`). -/
theorem vc_d_load2 (hY : YOk P Y) (σ : State isa) {y3 : Val} (h : DQ1 P Y y3 σ) {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (ED2 P).step (.load k xcl a n) σ v σ' → DQ1 P Y y3 σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, hy, a, ha⟩ := h
  refine ⟨hc.load hf, hY.load hy hf, a, ?_⟩
  obtain ⟨hanc, -⟩ := hf
  exact hanc.read? ha

/-- **VC `ldar x5, [x8]`** (`x8 = x3 + 8`): the link read at `tr0 ≤ vrNew`. -/
theorem vc_d_ldar_link2 (hY : YOk P Y) (σ : State isa) {y3 : Val} (h : DQ1 P Y y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED2 P).step (.load .acq xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' → DQ3 P Y y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, hy, a, ha⟩ := h
  refine ⟨hc.load hf, hY.load hy hf, a, ?_⟩
  obtain ⟨hanc, -, -, tr0, hrd, hlv, -⟩ := hf
  refine ⟨tr0, hanc.read? ha, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (hc.2.2.2.2.2 _ f hf) hlv.mono.vrNew
  · exact (hlv.acq (by decide) hfw).1

/-- **VC `casal x6, x5, [x1]`** (helping: `x6 = x3`, `x5 ≠ 0`): permitted
(`Prov` from `head`), `ComD2` and `Y` after it. -/
theorem vc_d_help2 (hL : QLocs2 P) (hY : YOk P Y) (σ : State isa) {y3 y5 : Val} (h : DQ3 P Y y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) :
    (ED2 P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED2 P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' → ComD2 P σ' ∧ Y σ' := by
  obtain ⟨hc, hy, a, tr0, h1, h2, -⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hc.2.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ⟨hc.rmw (envGCAdj_step_iff.mp hs),
      hY.rmw hy (envGCAdj_step_iff.mp hs)⟩⟩
  · rw [e, planD2_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.impure hq new
  · rw [e, planD2_gives]; simp
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hc.1.rel_w hq]
    exact form2_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.q1.head_tail)
      fun _ => .inr (prov_of_reads hanc (.inl rfl) h1 h2 hnz _)

/-- **VC `ldr w7, [x5]`** (`x5 ≠ 0`): its window covers the link read
(`DQ4`). -/
theorem vc_d_ldr2 (hY : YOk P Y) (σ : State isa) {y3 y5 : Val} (h : DQ3 P Y y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) {xcl : Bool} :
    ∀ u (σ' : State isa), (ED2 P).step (.load .plain xcl (BitVec.setWidth 64 y5) 4) σ u σ' →
      DQ4 P Y y3 y5 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planD2 P) hs
  obtain ⟨hc, hy, a, tr0, h1, h2, h3⟩ := h
  refine ⟨hc.load hf, hY.load hy hf, ?_⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨a, tr0, tl, u, hanc.read? h1, hanc.read? h2, hnz, hrd.val, fun p wm ha hb hg hl => ?_, rfl⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, ha, Nat.le_trans hb (Nat.le_trans h3
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y5, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **VC `casal x6, x5, [x0]`** (`x6 = x3`): permitted (`HeadF`: the
overwritten message is adjacent); after it `ComD2` and `Y`, and on success
its own swing records the dequeue (`First`, and `DoneD2` after a `First`). -/
theorem vc_d_cas2 (hL : QLocs2 P) (hY : YOk P Y) (σ : State isa) {y3 y5 : Val} {x : BitVec 64}
    (h : DQ4 P Y y3 y5 x σ) :
    (ED2 P).ok (.rmw .acqRel P.head.addr P.head.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED2 P).step (.rmw .acqRel P.head.addr P.head.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' →
        ComD2 P σ' ∧ Y σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 →
          First P x σ' ∧ ∀ x0, First P x0 σ → DoneD2 σ'.snap.mem P x0 x) := by
  obtain ⟨hc, hy, hd⟩ := h
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
    obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 y5), 1⟩
    exact ⟨by simpa using hnz, tr, old, tr0, y5, htr, read?_mono (prefix_append _ _) hrd.val,
      noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _, hb, by rw [ho]; exact h2', by simp⟩
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', hY.rmw hy hs', fun heq => ?_⟩
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, hvw, -, -, -⟩
  · exact absurd heq (casOp64_none hon)
  obtain ⟨-, rfl⟩ := casOp64_some hon
  have hdq : Deq σ'.snap.mem P tw x :=
    ⟨y3, y5, _, 1, hd.mono (rmw_snap_prefix hs'), Treiber.WriteSnap.get?_new hws, by simp⟩
  have hV : σ.vs.vwOld < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel (by decide))
  exact ⟨⟨tw, hdq, hvw (by decide)⟩, fun x0 ⟨V1, hd1, hv1⟩ =>
    ⟨V1, tw, Nat.lt_of_le_of_lt hv1 hV, hd1.mono (rmw_snap_prefix hs'), hdq⟩⟩

end Deq

end Kraken.Promising.SLR.EnvG.MsQueue
