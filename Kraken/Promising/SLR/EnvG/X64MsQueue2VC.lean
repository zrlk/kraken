/-
**Part 3: the per-access verification
conditions of the x64 `msqueue2.kl`** on `EnvGCAdj`, x64 (`Arch.tso`): the
enqueuer is thread `0` on `planE P`, the dequeuer thread `1` on `planD P`
(`EnvG/X64MsQueue2Ghost.lean`).

A copy of the MS queue proof's `EnvG/MsQueue2VC.lean` (same shape) for the x64 program
and layout, with the x64 adjacency proofs' x64 helpers (`cmpxOp64`, `rmw_success_fwd_tso`).

**The enqueuer** runs one loop with its node `n` in `rsi`: phase `n1` holds
both tokens, phase `n2` holds `n2`'s token and has its own `n1` link message
(`PhE`). Per iteration: `E0` (`enq`), `E1` (after `movq (tail),%rbx`), `E2`
(after `movq (%rbx),%rcx`; kept by the re-check `cmpq %rbx,(tail)`), and
after a successful link `Linked` (its own link message). The link `lock
cmpxchgq` releases `LinkF` at a link word (the slot holds the node's token;
the address is a `TailLoc`; the overwritten `0` is adjacent), and `TailLoc`
at `head`/`tail`. Both swings of `tail` release `TailF` (the helping one with
the read of `[rbx]`, the own one with the own link message).

**The dequeuer** reads `head` (`D1`), `tail` (`D2`, with the `tail` read's
window up to the `head` read) and `[rbx]` (`D3`, with its window up to the
`tail` read; kept by the re-check `cmpq %rbx,(head)`). Its helping swing
releases `TailF`; its swing of `head` releases `HeadF` (the overwritten
message adjacent) and records its own message (`Deq`, `First`, `DoneD2`).

The VCs are stated at the unrestricted `EnvGCAdj`; the program runs in
`EnvGCAdjX … sAll` (`within`: `ok` gains `AccessIn sAll`, always true).
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2Final
import Kraken.Promising.SLR.EnvG.X64Treiber2VC

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read? initVal_eq read?_mono read?_le_last
  prefix_append get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 cmpxOp64_casMatch)
open Kraken.Promising.X64.EnvG.Treiber2X (rmw_success_fwd_tso)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The enqueuer's environment (thread `0`). -/
noncomputable abbrev EE (P : Params) : SharedEnv := EnvGCAdj isa Arch.tso 0 (planE P)

/-- The dequeuer's environment (thread `1`). -/
noncomputable abbrev ED (P : Params) : SharedEnv := EnvGCAdj isa Arch.tso 1 (planD P)

/-! ## Step helpers (the MS queue proof's, at any architecture) -/

section StepHelpers

variable {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : EStateX} {k : RmwKind} {addr : BitVec 64} {n : Nat}
  {op : Val → Option Val} {old : Val}

/-- An RMW's snapshot memory extends the previous one
(`TreiberCommon.rmw_snap_prefix`). -/
theorem rmw_snap_prefix (hs : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') :
    σ.snap.mem.Prefix σ'.snap.mem :=
  TreiberCommon.rmw_snap_prefix hs

/-- An RMW's ghost grows (`TreiberCommon.rmw_ghost`). -/
theorem rmw_ghost (hs : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') : σ.g.Le σ'.g :=
  TreiberCommon.rmw_ghost hs

/-- An RMW's views grow (`TreiberCommon.rmw_vle`). -/
theorem rmw_vle (hs : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') : VLe σ.vs σ'.vs :=
  TreiberCommon.rmw_vle hs

/-- The resource after an RMW: unchanged (failure) or `after ⋅ C` (success)
(`TreiberCommon.rmw_res`). -/
theorem rmw_res (hs : (EnvGC isa A tid pl).step (.rmw k addr n op) σ old σ') :
    σ'.r = σ.r ∨ ∃ new tw Pc C, op old = some new ∧ σ'.r = (pl.after ⟨addr, n⟩ new tw Pc σ.r).op C :=
  TreiberCommon.rmw_res hs

end StepHelpers

/-- **A successful TSO RMW** leaves the other forwarding items alone (the TSO
counterpart of the MS queue proof's armv8 `rmw_success_getFwd_ne`). -/
theorem rmw_success_getFwd_ne_tso {tid : Nat} {pl : Plan} {σ σ' : EStateX} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.tso tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) {l : Loc} (hne : l ≠ ⟨addr, n⟩) : σ'.vs.getFwd l = σ.vs.getFwd l := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.tso tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  obtain ⟨-, hwv⟩ := writeSuccs_at Arch.tso tid hc hev
  rw [hvs]
  simp only [rmwAfter, rmwPost, show Arch.tso.rmwFence = true from rfl,
    show (Arch.tso.rmwKind .acqRel == .acqRel) = true from rfl, Bool.not_false, Bool.and_self, ↓reduceIte,
    fenceStep]
  change cx'.views.getFwd l = _
  rw [hwv.fwdOther _ hne]
  have h5 := SpinCommon.readSuccs_fwdb Arch.tso _ hx
  have e : x.2.2.views.getFwd l = (fenceOptCtx Arch.tso (envCtx tid σ.vs c)).views.getFwd l := by
    simp only [Views.getFwd, h5]
  rw [e, SpinCommon.fenceOptCtx_getFwd]
  rfl

/-- A read in the snapshot memory, at the message appended at the anchor:
in the new memory, below the new timestamp. -/
theorem read_at_append {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {x : Loc} {a : Time} {y : Val} (h : σ.snap.mem.read? x a = some y) (w : Msg) :
    a < c.mem.last + 1 ∧ (c.mem.append w).1.read? x a = some y := by
  have h' := read?_mono (TreiberCommon.AnchorOk.prefix hanc) h
  exact ⟨Nat.lt_succ_of_le (read?_le_last h'), read?_mono (prefix_append _ _) h'⟩

/-- A message of the snapshot memory, at the message appended at the
anchor. -/
theorem get_at_append {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {V : Time} {wm : Msg} (h : σ.snap.mem.get? V = some wm) (w : Msg) :
    V < c.mem.last + 1 ∧ (c.mem.append w).1.get? V = some wm := by
  have h' := get?_of_anchor hanc h
  exact ⟨Nat.lt_succ_of_le (c.mem.last_le_of_get?_eq_some h'),
    Memory.get?_of_prefix (prefix_append c.mem w).2 h'⟩

/-- `NoMsgIn` of the snapshot memory, at the message appended at the anchor. -/
theorem noMsgIn_at_append {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {x : Loc} {a b : Time} (hb : b ≤ σ.snap.mem.last + 1) (h : NoMsgIn σ.snap.mem x a b) (w : Msg) :
    NoMsgIn (c.mem.append w).1 x a b :=
  h.mono ((TreiberCommon.AnchorOk.prefix hanc).trans (prefix_append _ _)) hb

/-- `NoMsgIn` of an RMW's message from adjacency at the anchor (as
`noTopIn_of_adj`). -/
theorem noMsgIn_of_adj {P : Params} {tid : Nat} {c : Config isa} {g : Ghost} {tr : Time} (hW : GW P g)
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

theorem drop_wr {L : List Loc} {x : Loc} (h : x ∉ L) (r : Res) : (Res.drop L r).wr x = r.wr x := by
  simp [Res.drop, h]

theorem q_op_pos {a b : Perm} (h : 0 < a.q) : 0 < (a.op b).q := by
  have := b.nonneg
  change 0 < a.q + b.q
  grind

theorem q_op_ge_one {a b : Perm} (h : 1 ≤ a.q) : 1 ≤ (a.op b).q := by
  have := b.nonneg
  change 1 ≤ a.q + b.q
  grind

/-- `NoMsgIn` read off a load's window. -/
theorem noMsgIn_of_window {m : Memory} {x : Loc} {tr B : Time} (hw : m.writeIn x tr B = false) :
    NoMsgIn m x tr (B + 1) := by
  intro p wm h1 h2 hg hl
  have := (Memory.writeIn_iff m x tr B).mpr ⟨p, wm, h1, by omega_t, hg, hl⟩
  rw [hw] at this; cases this

/-! ## Plan facts -/

section PlanFacts

variable {P : Params}

/-- The enqueuer's gives, at every location. -/
theorem planE_gives_eq (hL : QLocs P) (l : Loc) (v : Val) : (planE P).gives l v = gE P l v := by
  by_cases hw : P.IsW l
  · exact planE_gives hL hw v
  · have hn : (planE P).find? l v = none := by
      cases h : (planE P).find? l v with
      | none => rfl
      | some e => obtain ⟨rfl, -, hw', -⟩ := planE_find_mem h; exact absurd hw' hw
    have hnl : ¬ P.IsL l := fun h => hw (isW_of_isL P h)
    simp [Plan.gives, hn, gE, hnl]

theorem tok_not_gives_8 (l : Loc) (v : Val) (a : BitVec 64) : (⟨a, 8⟩ : Loc) ∉ (planE P).gives l v :=
  planE_gives_sub P l v (tok1_ne_of_8 P) (tok2_ne_of_8 P)

theorem afterE_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (h : x ∉ (planE P).gives l v)
    (hx : x ≠ l) : (((planE P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_wr_ne _ _ hx, planE_keep, drop_wr h]
  · rw [Res.addW_wr_ne _ _ hx]

/-- **The enqueuer's own token** `⟨h, 2⟩`: never written, never given (no
`Plan` entry gives a 2-byte location), held whole by the enqueuer alone; the
final assembly's exclusive half of the shared postcondition. -/
def Params.tokH (P : Params) : Loc := ⟨P.h, 2⟩

theorem afterE_qH (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (((planE P).after l v tw cl r).wr P.tokH).q = (r.wr P.tokH).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planE_keep, drop_wr (planE_gives_sub P l v (by simp [Params.tokH, Params.tok1])
      (by simp [Params.tokH, Params.tok2]))]
  · rw [Res.addW_q]

theorem afterE_q8 (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (a : BitVec 64) :
    (((planE P).after l v tw cl r).wr ⟨a, 8⟩).q = (r.wr ⟨a, 8⟩).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planE_keep, drop_wr (tok_not_gives_8 l v a)]
  · rw [Res.addW_q]

/-- `n2`'s token is not given by a write of `n1`. -/
theorem tok2_not_gives_n1 (hL : QLocs P) (l : Loc) : P.tok2 ∉ (planE P).gives l (BitVec.setWidth 128 P.n1) := by
  rw [planE_gives_eq hL]
  unfold gE
  split <;> simp [Ne.symm hL.tok1_tok2]

/-- At a link, the write of `n1` gives `n1`'s token, of `n2` `n2`'s. -/
theorem gives_link_n1 (hL : QLocs P) {l : Loc} (hl : P.IsL l) :
    (planE P).gives l (BitVec.setWidth 128 P.n1) = [P.tok1] := by
  rw [planE_gives_eq hL]; simp [gE, hl]

theorem gives_link_n2 (hL : QLocs P) {l : Loc} (hl : P.IsL l) :
    (planE P).gives l (BitVec.setWidth 128 P.n2) = [P.tok2] := by
  rw [planE_gives_eq hL]; simp [gE, hl, hL.n1v_ne_n2v.symm]

theorem gives_ht (hL : QLocs P) {l : Loc} (hl : l = P.head ∨ l = P.tail) (v : Val) : (planE P).gives l v = [] := by
  rw [planE_gives_eq hL]
  have : ¬ P.IsL l := by rcases hl with rfl | rfl; exact hL.not_isL_head; exact hL.not_isL_tail
  simp [gE, this]

end PlanFacts

/-! ## The release facts -/

section Rel

variable {P : Params}

/-- **`form` of a message to `head`/`tail`**. -/
theorem form_ht (hL : QLocs P) {m : Memory} {l : Loc} {v : Val} {w : Nat} (R : Res) (hl : l = P.head ∨ l = P.tail)
    (hh : l = P.head → HeadF P (m.append ⟨l, v, w⟩).1 (m.last + 1) v)
    (ht : l = P.tail → TailF P (m.append ⟨l, v, w⟩).1 (m.last + 1) v)
    (hp : l = P.head → P.HW w R) :
    (form P).P v (m.append ⟨l, v, w⟩).1 (m.last + 1) R := by
  intro _
  refine ⟨l, w, Memory.get?_append_last _ _, fun hx => ?_, fun hx => .inl (hh hx), fun hx => .inl (ht hx),
    fun hx => .inr (hp hx)⟩
  rcases hl with rfl | rfl
  · exact absurd hx hL.not_isL_head
  · exact absurd hx hL.not_isL_tail

/-- **`TailF` of a swing** (`rax = sw z` read from `tail`): the CAS overwrote
the adjacent `old` (`sw old = sw z`) and writes `y'`, read from `[z]`. -/
theorem tailF_of {tid : Nat} {σ : EStateX} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {rF : Nat → Res} {T : Nat → Prop} (E : Erase rF g T c) (hW : GW P g) {tr : Time} {old z y' : Val}
    (htr : tr < c.mem.last + 1) (hrd : c.mem.read? P.tail tr = some old)
    (hadj : AdjAt tid c g P.tail tr (c.mem.last + 1)) (hx : BitVec.setWidth 64 old = BitVec.setWidth 64 z) {b : Time}
    (h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 z, 8⟩ b = some y') (hnz : BitVec.setWidth 64 y' ≠ 0) (w : Nat) :
    TailF P (c.mem.append ⟨P.tail, BitVec.setWidth 128 (BitVec.setWidth 64 y'), w⟩).1 (c.mem.last + 1)
      (BitVec.setWidth 128 (BitVec.setWidth 64 y')) := by
  obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨P.tail, BitVec.setWidth 128 (BitVec.setWidth 64 y'), w⟩
  exact ⟨by simpa using hnz, tr, old, b, y', htr, read?_mono (prefix_append _ _) hrd,
    noMsgIn_of_adj hW E (.inr (.inl rfl)) hadj _, hb, by rw [hx]; exact h2', by simp⟩

end Rel

/-! ## The enqueuer's predicates -/

/-- **The enqueuer's common facts**: the ghost facts, a positive share of
every 8-byte location, and its own token whole. -/
def ComE (P : Params) (σ : EStateX) : Prop :=
  GW P σ.g ∧ (∀ a, 0 < (σ.r.wr ⟨a, 8⟩).q) ∧ TokFrozen P.tokH σ.r

/-- The enqueuer's own link message of `n` (at `[y]`, `y` read from
`tail`). -/
def LinkS (P : Params) (n : BitVec 64) (σ : EStateX) : Prop :=
  ∃ V' a y v' w', σ.snap.mem.get? V' = some ⟨⟨BitVec.setWidth 64 y, 8⟩, v', w'⟩ ∧ BitVec.setWidth 64 v' = n ∧
    σ.snap.mem.read? P.tail a = some y

/-- **The enqueuer's phase** with node `n`: `n1` with both tokens, or `n2`
with `n2`'s token and its own `n1` link message. -/
def PhE (P : Params) (n : BitVec 64) (σ : EStateX) : Prop :=
  (n = P.n1 ∧ TokFrozen P.tok1 σ.r ∧ TokFrozen P.tok2 σ.r) ∨ (n = P.n2 ∧ TokFrozen P.tok2 σ.r ∧ LinkS P P.n1 σ)

/-- **`enq`**. -/
def E0 (P : Params) (n : BitVec 64) (σ : EStateX) : Prop := ComE P σ ∧ PhE P n σ
/-- **After `movq (tail),%rbx`** of `y3`. -/
def E1 (P : Params) (n : BitVec 64) (y3 : Val) (σ : EStateX) : Prop :=
  E0 P n σ ∧ ∃ a, σ.snap.mem.read? P.tail a = some y3
/-- **After `movq (%rbx),%rcx`** of `y4`. -/
def E2 (P : Params) (n : BitVec 64) (y3 y4 : Val) (σ : EStateX) : Prop :=
  E1 P n y3 σ ∧ ∃ b, σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ b = some y4
/-- **After the link** of `n` at `[y3]`. -/
def Linked (P : Params) (n : BitVec 64) (y3 : Val) (σ : EStateX) : Prop :=
  ComE P σ ∧ ((n = P.n1 ∧ TokFrozen P.tok2 σ.r) ∨ n = P.n2) ∧
    (∃ L w, σ.snap.mem.get? L = some ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 n, w⟩) ∧
    ∃ a, σ.snap.mem.read? P.tail a = some y3

section EnqKeep

variable {P : Params} {σ σ' : EStateX}

theorem ComE.fence (h : ComE P σ) (hf : FenceLe σ σ') : ComE P σ' := by
  unfold ComE; rw [hf.g, hf.r]; exact h

theorem LinkS.mono {n : BitVec 64} (h : LinkS P n σ) (hp : σ.snap.mem.Prefix σ'.snap.mem) : LinkS P n σ' :=
  let ⟨V', a, y, v', w', hg, hv, hr⟩ := h
  ⟨V', a, y, v', w', Memory.get?_of_prefix hp.2 hg, hv, read?_mono hp hr⟩

theorem PhE.fence {n : BitVec 64} (h : PhE P n σ) (hf : FenceLe σ σ') : PhE P n σ' := by
  unfold PhE TokFrozen LinkS; rw [hf.r, hf.snap]; exact h

theorem E0.fence {n : BitVec 64} (h : E0 P n σ) (hf : FenceLe σ σ') : E0 P n σ' := ⟨h.1.fence hf, h.2.fence hf⟩

theorem E1.fence {n : BitVec 64} {y3 : Val} (h : E1 P n y3 σ) (hf : FenceLe σ σ') : E1 P n y3 σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

theorem E2.fence {n : BitVec 64} {y3 y4 : Val} (h : E2 P n y3 y4 σ) (hf : FenceLe σ σ') : E2 P n y3 y4 σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

theorem Linked.fence {n : BitVec 64} {y3 : Val} (h : Linked P n y3 σ) (hf : FenceLe σ σ') : Linked P n y3 σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, by unfold TokFrozen; rw [hf.r]; exact h2, hf.snap ▸ h3, hf.snap ▸ h4⟩

theorem ComE.load {k : LoadKind} {l : Loc} {v : Val} (h : ComE P σ) (hf : LoadFacts Arch.tso 0 σ σ' k l v) :
    ComE P σ' := by
  obtain ⟨hanc, hr, -⟩ := hf
  exact ⟨h.1.mono hanc.ghost, hr ▸ h.2⟩

theorem PhE.load {n : BitVec 64} {k : LoadKind} {l : Loc} {v : Val} (h : PhE P n σ)
    (hf : LoadFacts Arch.tso 0 σ σ' k l v) : PhE P n σ' := by
  obtain ⟨hanc, hr, -⟩ := hf
  unfold PhE TokFrozen at *
  rw [hr]
  exact h.imp id fun h => ⟨h.1, h.2.1, h.2.2.mono (TreiberCommon.AnchorOk.prefix hanc)⟩

theorem E0.load {n : BitVec 64} {k : LoadKind} {l : Loc} {v : Val} (h : E0 P n σ)
    (hf : LoadFacts Arch.tso 0 σ σ' k l v) : E0 P n σ' :=
  ⟨h.1.load hf, h.2.load hf⟩

theorem ComE.rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComE P σ)
    (hs : (EnvGC isa Arch.tso 0 (planE P)).step (.rmw k addr n op) σ old σ') : ComE P σ' := by
  refine ⟨h.1.mono (rmw_ghost hs), fun a => ?_, ?_⟩
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h.2.1 a
    · apply q_op_pos; rw [afterE_q8]; exact h.2.1 a
  · unfold TokFrozen
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h.2.2
    · apply q_op_ge_one; rw [afterE_qH]; exact h.2.2

/-- A token not given by an RMW stays whole. -/
theorem tok_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} {tok : Loc}
    (htok : tok.bytes = 1) (h : TokFrozen tok σ.r)
    (hs : (EnvGC isa Arch.tso 0 (planE P)).step (.rmw k addr n op) σ old σ')
    (hg : ∀ new, op old = some new → tok ∉ (planE P).gives ⟨addr, n⟩ new) (hn : n = 8) : TokFrozen tok σ'.r := by
  unfold TokFrozen at *
  have hne : tok ≠ ⟨addr, n⟩ := fun he => by rw [he] at htok; simp only at htok; omega
  rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hon, hr⟩ <;> rw [hr]
  · exact h
  · apply q_op_ge_one; rw [afterE_q _ _ _ _ _ (hg new hon) hne]; exact h

end EnqKeep

/-! ## The enqueuer -/

section Enq

variable {P : Params} {σ σ' : EStateX} {n : BitVec 64}

theorem tok1_bytes : P.tok1.bytes = 1 := rfl
theorem tok2_bytes : P.tok2.bytes = 1 := rfl

/-- A load keeps `E0`. -/
theorem vc_e_load (σ : EStateX) (h : E0 P n σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {m : Nat} :
    ∀ v (σ' : EStateX), (EE P).step (.load k xcl a m) σ v σ' → E0 P n σ' := fun _ _ hs =>
  h.load (step_loadFacts (pl := planE P) hs)

/-- **VC `movq (tail),%rbx`**: the `tail` read. -/
theorem vc_e_load_tail (σ : EStateX) (h : E0 P n σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (EE P).step (.load .plain xcl P.tail.addr P.tail.bytes) σ v σ' → E1 P n v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  refine ⟨h.load hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **VC `movq (%rbx),%rcx`**: the link read. -/
theorem vc_e_load_link (σ : EStateX) {y3 : Val} (h : E1 P n y3 σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (EE P).step (.load .plain xcl (BitVec.setWidth 64 y3) 8) σ v σ' → E2 P n y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨h0, a, ha⟩ := h
  refine ⟨⟨h0.load hf, a, ?_⟩, ?_⟩
  · obtain ⟨hanc, -⟩ := hf
    exact hanc.read? ha
  · obtain ⟨-, -, -, tr, hrd, -⟩ := hf
    exact ⟨tr, hrd.val⟩

/-- **A load keeps `E2`** (the re-check `cmpq %rbx,(tail)`). -/
theorem vc_e_load2 (σ : EStateX) {y3 y4 : Val} (h : E2 P n y3 y4 σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64}
    {m : Nat} : ∀ v (σ' : EStateX), (EE P).step (.load k xcl a m) σ v σ' → E2 P n y3 y4 σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨⟨h0, a, ha⟩, b, hb⟩ := h
  obtain ⟨hanc, -⟩ := id hf
  exact ⟨⟨h0.load hf, a, hanc.read? ha⟩, b, hanc.read? hb⟩

theorem E2.e0 {y3 y4 : Val} (h : E2 P n y3 y4 σ) : E0 P n σ := h.1.1

/-- **VC `lock cmpxchgq %rcx,(tail)`** (the helping swing: `rax = rbx`,
`rcx ≠ 0`): permitted (`TailF`), `E0` after it. -/
theorem vc_e_help (hL : QLocs P) (σ : EStateX) {y3 y4 : Val} (h : E2 P n y3 y4 σ) (hnz : BitVec.setWidth 64 y4 ≠ 0) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ old σ' → E0 P n σ' := by
  obtain ⟨⟨⟨hcom, hph⟩, a, h1⟩, b, h2⟩ := h
  have hW := hcom.1
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_,
    by rw [e, gives_ht hL (.inr rfl)]; simp, fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planE_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    exact form_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.head_tail)
      (fun _ => tailF_of hanc E (hW.mono hanc.ghost) htr hrd.val hadj (by rw [hx]) h2 hnz _)
      fun hx => absurd hx.symm hL.head_tail
  · have hs' := envGCAdj_step_iff.mp hs
    refine ⟨hcom.rmw hs', ?_⟩
    have hg : ∀ tok new, cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4) old = some new →
        tok ∉ (planE P).gives P.tail new := fun tok new _ => by rw [gives_ht hL (.inr rfl)]; simp
    rcases hph with ⟨hn, h1, h2⟩ | ⟨hn, h2, hl⟩
    · exact .inl ⟨hn, tok_rmw tok1_bytes h1 hs' (hg _) rfl, tok_rmw tok2_bytes h2 hs' (hg _) rfl⟩
    · exact .inr ⟨hn, tok_rmw tok2_bytes h2 hs' (hg _) rfl, hl.mono (rmw_snap_prefix hs')⟩

/-- **VC `lock cmpxchgq %rsi,(%rbx)`** (the link: `rax = 0`, `rsi = n`):
permitted (`LinkF` at a link, `TailLoc` at `head`/`tail`, pure elsewhere);
it fails (`E0`) or succeeds (`Linked`: its own message). -/
theorem vc_e_link (hL : QLocs P) (σ : EStateX) {y3 y4 : Val} (h : E2 P n y3 y4 σ) :
    (EE P).ok (.rmw .acqRel (BitVec.setWidth 64 y3) 8 (cmpxOp64 0 n)) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel (BitVec.setWidth 64 y3) 8 (cmpxOp64 0 n)) σ old σ' →
        (BitVec.setWidth 64 old ≠ 0 ∧ E0 P n σ') ∨ (BitVec.setWidth 64 old = 0 ∧ Linked P n y3 σ') := by
  obtain ⟨⟨⟨hcom, hph⟩, a, h1⟩, -⟩ := h
  have hW := hcom.1
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun hr => ?_⟩⟩, ?_⟩
  · by_cases hq : P.IsW ⟨BitVec.setWidth 64 y3, 8⟩
    · rw [planE_rel, decide_eq_false_iff_not] at hr; exact absurd hq hr
    · rw [hW.rel_ne hq]; exact Pred.emp_pure _
  · have hq : P.IsW ⟨BitVec.setWidth 64 y3, 8⟩ := by rw [planE_rel] at hr; simpa using hr
    obtain ⟨hz, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    refine ⟨by decide, hW.impure hq _, tok_not_gives_8 _ _ _, fun htr hwb hadj => ?_⟩
    rw [hW.rel_w hq, planE_give]
    obtain ⟨rF, E⟩ := hanc.erase
    obtain ⟨ha, h1'⟩ := read_at_append hanc h1 ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 n, 0⟩
    have hTL : TailLoc P _ _ ⟨BitVec.setWidth 64 y3, 8⟩ := ⟨a, y3, ha, h1', rfl⟩
    intro _
    refine ⟨_, 0, Memory.get?_append_last _ _, fun hl => ⟨?_, hTL, tr, old, htr,
      read?_mono (prefix_append _ _) hrd.val, hz, noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _⟩,
      fun _ => .inr hTL, fun _ => .inr hTL, fun _ => .inl hTL⟩
    rcases hph with ⟨rfl, ht1, -⟩ | ⟨rfl, ht2, hls⟩
    · refine .inl ⟨by simp, ?_⟩
      unfold TokFrozen at ht1 ⊢
      rw [gives_link_n1 hL hl]; simpa [Res.only] using ht1
    · refine .inr ⟨by simp, ?_, ?_⟩
      · unfold TokFrozen at ht2 ⊢
        rw [gives_link_n2 hL hl]; simpa [Res.only] using ht2
      · obtain ⟨V', a', y', v', w', hg', hv', hr'⟩ := hls
        obtain ⟨hV', hg''⟩ := get_at_append hanc hg' ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 P.n2, 0⟩
        obtain ⟨ha', hr''⟩ := read_at_append hanc hr' ⟨⟨BitVec.setWidth 64 y3, 8⟩, BitVec.setWidth 128 P.n2, 0⟩
        exact ⟨V', _, v', w', hV', hg'', hv', a', y', ha', hr'', rfl⟩
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  have hcom' := hcom.rmw hs'
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, -, -, -, -⟩
  · refine .inl ⟨(cmpxOp64_casMatch _ _).none _ hon, hcom', ?_⟩
    have hpre := rmw_snap_prefix hs'
    unfold PhE TokFrozen
    rw [hr]
    exact hph.imp id fun h => ⟨h.1, h.2.1, h.2.2.mono hpre⟩
  · obtain ⟨hz, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    have hpre := rmw_snap_prefix hs'
    refine .inr ⟨hz, hcom', ?_, ⟨tw, 0, TreiberCommon.WriteSnap.get?_new hws⟩, a, read?_mono hpre h1⟩
    rcases hph with ⟨rfl, -, ht2⟩ | ⟨rfl, -⟩
    · exact .inl ⟨rfl, tok_rmw tok2_bytes ht2 hs' (fun new hn => by
        obtain ⟨-, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hn; exact tok2_not_gives_n1 hL _) rfl⟩
    · exact .inr rfl

/-- **VC `lock cmpxchgq %rsi,(tail)`** (the own swing: `rax = rbx`, `rsi =
n`): permitted (`TailF` with the own link message), `Linked` after it. -/
theorem vc_e_swing (hL : QLocs P) (σ : EStateX) {y3 : Val} (h : Linked P n y3 σ) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes (cmpxOp64 (BitVec.setWidth 64 y3) n)) σ ∧
      ∀ old (σ' : EStateX), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) n)) σ old σ' → Linked P n y3 σ' := by
  obtain ⟨hcom, htok, ⟨L, wL, hgL⟩, a, h1⟩ := h
  have hW := hcom.1
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  have hnz : n ≠ 0 := by rcases htok with ⟨rfl, -⟩ | rfl; exact hL.n1z; exact hL.n2z
  refine ⟨⟨hcom.2.1 _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_,
    by rw [e, gives_ht hL (.inr rfl)]; simp, fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planE_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    have h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ L = some (BitVec.setWidth 128 n) := by
      rw [read?_of_get? hgL]
    have := tailF_of hanc E (hW.mono hanc.ghost) htr hrd.val hadj (by rw [hx]) h2 (by simpa using hnz) 0
    have hv : BitVec.setWidth 128 (BitVec.setWidth 64 (BitVec.setWidth 128 n)) = BitVec.setWidth 128 n := by simp
    rw [hv] at this
    exact form_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.head_tail) (fun _ => this)
      fun hx => absurd hx.symm hL.head_tail
  · have hs' := envGCAdj_step_iff.mp hs
    have hpre := rmw_snap_prefix hs'
    refine ⟨hcom.rmw hs', ?_, ⟨L, wL, Memory.get?_of_prefix hpre.2 hgL⟩, a, read?_mono hpre h1⟩
    rcases htok with ⟨hn, ht2⟩ | hn
    · exact .inl ⟨hn, tok_rmw tok2_bytes ht2 hs' (fun new _ => by rw [gives_ht hL (.inr rfl)]; simp) rfl⟩
    · exact .inr hn

/-- `Linked` of `n1` is `E0` of `n2`. -/
theorem Linked.next (hL : QLocs P) {y3 : Val} (h : Linked P P.n1 y3 σ) : E0 P P.n2 σ := by
  obtain ⟨hcom, htok, ⟨L, wL, hgL⟩, a, h1⟩ := h
  rcases htok with ⟨-, ht2⟩ | hn
  · exact ⟨hcom, .inr ⟨rfl, ht2, L, a, y3, _, wL, hgL, by simp, h1⟩⟩
  · exact absurd hn hL.n12

end Enq

/-! ## The dequeuer's predicates -/

/-- Every forwarding item at or below `vrNew`. -/
def FwdAll (σ : EStateX) : Prop := ∀ l f, σ.vs.getFwd l = some f → f.time ≤ σ.vs.vrNew

/-- **The dequeuer's common facts**. -/
def ComD (P : Params) (σ : EStateX) : Prop :=
  GW P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ 0 < (σ.r.wr P.tail).q ∧ (∀ x, P.IsW x → 1 ≤ σ.r.acq x 0) ∧
    InitV σ.snap.mem P ∧ FwdAll σ

/-- The first dequeue's record: its `Deq` at a swing at or below `vwOld`. -/
def First (P : Params) (x : BitVec 64) (σ : EStateX) : Prop := ∃ V1, Deq σ.snap.mem P V1 x ∧ V1 ≤ σ.vs.vwOld

/-- **A frame fact `Y` of a dequeue** survives the dequeuer's fences, loads
and RMWs. -/
structure YOk (P : Params) (Y : EStateX → Prop) : Prop where
  fence : ∀ {σ σ' : EStateX}, Y σ → FenceLe σ σ' → Y σ'
  load : ∀ {σ σ' : EStateX} {k : LoadKind} {l : Loc} {v : Val}, Y σ → LoadFacts Arch.tso 1 σ σ' k l v → Y σ'
  rmw : ∀ {σ σ' : EStateX} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}, Y σ →
    (EnvGC isa Arch.tso 1 (planD P)).step (.rmw .acqRel addr n op) σ old σ' → Y σ'

/-- **After `movq (head),%rbx`** of `y3`, read at `tA ≤ vrNew`. -/
def D1 (P : Params) (Y : EStateX → Prop) (y3 : Val) (σ : EStateX) : Prop :=
  ComD P σ ∧ Y σ ∧ ∃ tA, σ.snap.mem.read? P.head tA = some y3 ∧ tA ≤ σ.vs.vrNew

/-- **After `movq (tail),%rdx`** of `yt`, read at `tB ≤ vrNew`, its window
up to `tA`. -/
def D2 (P : Params) (Y : EStateX → Prop) (y3 yt : Val) (σ : EStateX) : Prop :=
  ComD P σ ∧ Y σ ∧ ∃ tA tB, σ.snap.mem.read? P.head tA = some y3 ∧ σ.snap.mem.read? P.tail tB = some yt ∧
    tB ≤ σ.vs.vrNew ∧ (tB < tA → NoMsgIn σ.snap.mem P.tail tB (tA + 1))

/-- **After `movq (%rbx),%rcx`** of `u`, its window up to `tB`. -/
def D3 (P : Params) (Y : EStateX → Prop) (y3 yt u : Val) (σ : EStateX) : Prop :=
  ComD P σ ∧ Y σ ∧ ∃ tA tB tl, σ.snap.mem.read? P.head tA = some y3 ∧ σ.snap.mem.read? P.tail tB = some yt ∧
    (tB < tA → NoMsgIn σ.snap.mem P.tail tB (tA + 1)) ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3, 8⟩ tl = some u ∧
    NoMsgIn σ.snap.mem ⟨BitVec.setWidth 64 y3, 8⟩ tl (tB + 1)

/-- **`ddone`** with `r12 = x12`, `r13 = x13`. -/
def Dn (P : Params) (x12 x13 : BitVec 64) (σ : EStateX) : Prop := ComD P σ ∧ DoneD2 σ.snap.mem P x12 x13

section DeqKeep

variable {P : Params} {σ σ' : EStateX}

theorem afterD_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) :
    (((planD P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planD_keep]; simp [Res.drop]
  · rw [Res.addW_q]

theorem afterD_acq (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) (ι : PredId) :
    ((planD P).after l v tw cl r).acq x ι = r.acq x ι := by
  unfold Plan.after
  split
  · rw [Res.addW_acq, planD_keep]; simp [Res.drop]
  · rw [Res.addW_acq]

theorem ComD.fence (h : ComD P σ) (hf : FenceLe σ σ') : ComD P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.r ▸ h4, hf.snap ▸ h5, fun l f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hf.vrNew

theorem ComD.load {k : LoadKind} {l : Loc} {v : Val} (h : ComD P σ) (hf : LoadFacts Arch.tso 1 σ σ' k l v) :
    ComD P σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, hr ▸ h4, h5.of_init hanc.snap.init, fun l f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hlv.mono.vrNew

theorem ComD.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComD P σ)
    (hs : (EnvGC isa Arch.tso 1 (planD P)).step (.rmw .acqRel addr n op) σ old σ') : ComD P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, ?_, h5.of_init (rmw_snap_prefix hs).1, ?_⟩
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h2
    · apply q_op_pos; rw [afterD_q]; exact h2
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h3
    · apply q_op_pos; rw [afterD_q]; exact h3
  · intro x hx
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, -, hr⟩ <;> rw [hr]
    · exact h4 x hx
    · show 1 ≤ ((planD P).after _ new tw Pc σ.r).acq x 0 + C.acq x 0
      rw [afterD_acq]; have := h4 x hx; omega
  · intro l f hfw
    rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : l = ⟨addr, n⟩
    · subst hl; exact rmw_success_fwd_tso hs hnew f hfw
    · rw [rmw_success_getFwd_ne_tso hs hnew hl] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew

theorem yok_true : YOk P fun _ => True := ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

theorem yok_first (x : BitVec 64) : YOk P (First P x) where
  fence h hf := by unfold First; rw [hf.snap, hf.vwOld]; exact h
  load h hf := by
    obtain ⟨V1, hd, hv⟩ := h
    obtain ⟨hanc, -, -, tr, -, hlv, -⟩ := hf
    exact ⟨V1, hd.mono (TreiberCommon.AnchorOk.prefix hanc), by rw [hlv.vwOld]; exact hv⟩
  rmw h hs := let ⟨V1, hd, hv⟩ := h; ⟨V1, hd.mono (rmw_snap_prefix hs), Nat.le_trans hv (rmw_vle hs).vwOld⟩

variable {Y : EStateX → Prop}

theorem D1.fence (hY : YOk P Y) {y3 : Val} (h : D1 P Y y3 σ) (hf : FenceLe σ σ') : D1 P Y y3 σ' := by
  obtain ⟨h1, hy, tA, h2, h3⟩ := h
  exact ⟨h1.fence hf, hY.fence hy hf, tA, hf.snap ▸ h2, Nat.le_trans h3 hf.vrNew⟩

theorem D2.fence (hY : YOk P Y) {y3 yt : Val} (h : D2 P Y y3 yt σ) (hf : FenceLe σ σ') : D2 P Y y3 yt σ' := by
  obtain ⟨h1, hy, tA, tB, h2, h3, h4, h5⟩ := h
  exact ⟨h1.fence hf, hY.fence hy hf, tA, tB, hf.snap ▸ h2, hf.snap ▸ h3, Nat.le_trans h4 hf.vrNew,
    hf.snap ▸ h5⟩

theorem D3.fence (hY : YOk P Y) {y3 yt u : Val} (h : D3 P Y y3 yt u σ) (hf : FenceLe σ σ') :
    D3 P Y y3 yt u σ' := by
  obtain ⟨h1, hy, h⟩ := h
  exact ⟨h1.fence hf, hY.fence hy hf, hf.snap ▸ h⟩

theorem D3.back {y3 yt u : Val} (h : D3 P Y y3 yt u σ) : ComD P σ ∧ Y σ := ⟨h.1, h.2.1⟩

theorem Dn.fence {x y : BitVec 64} (h : Dn P x y σ) (hf : FenceLe σ σ') : Dn P x y σ' :=
  ⟨h.1.fence hf, hf.snap ▸ h.2⟩

end DeqKeep

/-! ## The dequeuer -/

section Deq

variable {P : Params} {Y : EStateX → Prop}

/-- The read time of an acquire load is at or below `vrNew` (`FwdAll` if
forwarded). -/
theorem deq_read_le {σ σ' : EStateX} {l : Loc} {v : Val} (h : ComD P σ) {xcl : Bool}
    (hs : (ED P).step (.load .plain xcl l.addr l.bytes) σ v σ') :
    ∃ tr, σ'.snap.mem.read? l tr = some v ∧ tr ≤ σ'.vs.vrNew ∧
      σ'.snap.mem.writeIn l tr (readBound Arch.tso σ.vs .plain l) = false ∧ σ.vs.vrNew ≤ σ'.vs.vrNew := by
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨-, -, -, tr, hrd, hlv, -⟩ := hf
  refine ⟨tr, hrd.val, ?_, hrd.window, hlv.mono.vrNew⟩
  by_cases hfw : Fwded σ.vs l tr
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (h.2.2.2.2.2 _ f hf) hlv.mono.vrNew
  · exact (hlv.acq (by decide) hfw).1

/-- **VC `movq (head),%rbx`**: `head` read. -/
theorem vc_d_load_head (hY : YOk P Y) (σ : EStateX) (h : ComD P σ) (hy : Y σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED P).step (.load .plain xcl P.head.addr P.head.bytes) σ v σ' → D1 P Y v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨tA, hr, hle, -⟩ := deq_read_le h hs
  exact ⟨h.load hf, hY.load hy hf, tA, hr, hle⟩

/-- **VC `movq (tail),%rdx`**: `tail` read, its window covering `tA`. -/
theorem vc_d_load_tail (hY : YOk P Y) (σ : EStateX) {y3 : Val} (h : D1 P Y y3 σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED P).step (.load .plain xcl P.tail.addr P.tail.bytes) σ v σ' → D2 P Y y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, hy, tA, hA, hAle⟩ := h
  obtain ⟨tB, hr, hle, hwin, -⟩ := deq_read_le hc hs
  obtain ⟨hanc, -⟩ := id hf
  refine ⟨hc.load hf, hY.load hy hf, tA, tB, hanc.read? hA, hr, hle, fun hlt => ?_⟩
  have := noMsgIn_of_window hwin
  intro p wm h1 h2 hg
  exact this p wm h1 (by have := le_readBound_vrNew Arch.tso σ.vs .plain P.tail; omega_t) hg

/-- **VC `movq (%rbx),%rcx`**: the link read, its window covering `tB`. -/
theorem vc_d_load_link (hY : YOk P Y) (σ : EStateX) {y3 yt : Val} (h : D2 P Y y3 yt σ) {xcl : Bool} :
    ∀ v (σ' : EStateX), (ED P).step (.load .plain xcl (BitVec.setWidth 64 y3) 8) σ v σ' → D3 P Y y3 yt v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, hy, tA, tB, hA, hB, hBle, hwinB⟩ := h
  obtain ⟨hanc, -, -, tl, hrd, -⟩ := id hf
  have hpre := TreiberCommon.AnchorOk.prefix hanc
  refine ⟨hc.load hf, hY.load hy hf, tA, tB, tl, hanc.read? hA, hanc.read? hB, fun hlt => ?_, hrd.val, ?_⟩
  · exact (hwinB hlt).mono hpre (by have := read?_le_last hA; omega_t)
  · have := noMsgIn_of_window hrd.window
    intro p wm h1 h2 hg
    exact this p wm h1 (by
      have := le_readBound_vrNew Arch.tso σ.vs .plain ⟨BitVec.setWidth 64 y3, 8⟩; omega_t) hg

/-- **A load keeps `D3`** (the re-check `cmpq %rbx,(head)`). -/
theorem vc_d_load3 (hY : YOk P Y) (σ : EStateX) {y3 yt u : Val} (h : D3 P Y y3 yt u σ) {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {m : Nat} : ∀ v (σ' : EStateX), (ED P).step (.load k xcl a m) σ v σ' → D3 P Y y3 yt u σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, hy, tA, tB, tl, hA, hB, hw1, hl, hw2⟩ := h
  obtain ⟨hanc, -⟩ := id hf
  have hpre := TreiberCommon.AnchorOk.prefix hanc
  refine ⟨hc.load hf, hY.load hy hf, tA, tB, tl, hanc.read? hA, hanc.read? hB,
    fun hlt => (hw1 hlt).mono hpre (by have := read?_le_last hA; omega_t), hanc.read? hl,
    hw2.mono hpre (by have := read?_le_last hB; omega_t)⟩

/-- **VC `lock cmpxchgq %rcx,(tail)`** (helping: `rax = rbx`, `rcx ≠ 0`):
permitted (`TailF`), `ComD` and `Y` after it. -/
theorem vc_d_help (hL : QLocs P) (hY : YOk P Y) (σ : EStateX) {y3 yt u : Val} (h : D3 P Y y3 yt u σ)
    (hnz : BitVec.setWidth 64 u ≠ 0) :
    (ED P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (ED P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ old σ' → ComD P σ' ∧ Y σ' := by
  obtain ⟨hc, hy, tA, tB, tl, -, -, -, hl, -⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsW P.tail := .inr (.inl rfl)
  refine ⟨⟨hc.2.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ⟨hc.rmw (envGCAdj_step_iff.mp hs),
      hY.rmw hy (envGCAdj_step_iff.mp hs)⟩⟩
  · rw [e, planD_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.impure hq new
  · rw [e, planD_gives]; simp
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hc.1.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    exact form_ht hL _ (.inr rfl) (fun hx => absurd hx.symm hL.head_tail)
      (fun _ => tailF_of hanc E (hc.1.mono hanc.ghost) htr hrd.val hadj (by rw [hx]) hl hnz _)
      fun hx => absurd hx.symm hL.head_tail

/-- **VC `lock cmpxchgq %rcx,(head)`** (the swing: `rax = rbx ≠ rdx`):
permitted (`HeadF`: the overwritten message is adjacent, the three reads);
after it `ComD` and `Y`, and on success its own swing records the dequeue
(`First`, and `DoneD2` after a `First`). -/
theorem vc_d_pop (hL : QLocs P) (hpt : P.trk = false) (hY : YOk P Y) (σ : EStateX) {y3 yt u : Val}
    (h : D3 P Y y3 yt u σ) (hne : BitVec.setWidth 64 yt ≠ BitVec.setWidth 64 y3) :
    (ED P).ok (.rmw .acqRel P.head.addr P.head.bytes
        (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ ∧
      ∀ old (σ' : EStateX), (ED P).step (.rmw .acqRel P.head.addr P.head.bytes
          (cmpxOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 u))) σ old σ' →
        ComD P σ' ∧ Y σ' ∧ (BitVec.setWidth 64 old = BitVec.setWidth 64 y3 →
          First P (BitVec.setWidth 64 u) σ' ∧ ∀ x0, First P x0 σ → DoneD2 σ'.snap.mem P x0 (BitVec.setWidth 64 u)) := by
  obtain ⟨hc, hy, tA, tB, tl, hA, hB, hw1, hl, hw2⟩ := h
  have hW := hc.1
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsW P.head := .inl rfl
  refine ⟨⟨hc.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planD_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planD_gives]; simp
  · obtain ⟨hx, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
    rw [e, hW.rel_w hq]
    obtain ⟨rF, E⟩ := hanc.erase
    refine form_ht hL _ (.inl rfl) (fun _ => ?_) (fun hx => absurd hx hL.head_tail)
      fun _ => .inl hpt
    have w : Msg := ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
    obtain ⟨hAl, hA'⟩ := read_at_append hanc hA ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
    obtain ⟨hBl, hB'⟩ := read_at_append hanc hB ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
    obtain ⟨hll, hl'⟩ := read_at_append hanc hl ⟨P.head, BitVec.setWidth 128 (BitVec.setWidth 64 u), 1⟩
    have hz : (⟨BitVec.setWidth 64 old, 8⟩ : Loc) = ⟨BitVec.setWidth 64 y3, 8⟩ := by rw [hx]
    refine ⟨tr, old, htr, read?_mono (prefix_append _ _) hrd.val, noMsgIn_of_adj (hW.mono hanc.ghost) E hq hadj _,
      tA, y3, tB, yt, tl, u, hAl, hA', hx.symm, hBl, hB', by rw [hx]; exact hne, fun hlt => ?_, hll,
      by rw [hz]; exact hl', by simp, ?_⟩
    · exact noMsgIn_at_append hanc (by have := read?_le_last hA; omega_t) (hw1 hlt) _
    · rw [hz]; exact noMsgIn_at_append hanc (by have := read?_le_last hB; omega_t) hw2 _
  have hs' := envGCAdj_step_iff.mp hs
  refine ⟨hc.rmw hs', hY.rmw hy hs', fun heq => ?_⟩
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
  rcases hbr with ⟨hon, -⟩ | ⟨new, tw, hon, -, -, hws, hwb, -, hvw, -, -, -⟩
  · exact absurd heq ((cmpxOp64_casMatch _ _).none _ hon)
  obtain ⟨-, rfl⟩ := (cmpxOp64_casMatch _ _).some _ _ hon
  have hdq : Deq σ'.snap.mem P tw (BitVec.setWidth 64 u) :=
    ⟨_, 1, TreiberCommon.WriteSnap.get?_new hws, by simp⟩
  have hV : σ.vs.vwOld < tw := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel (by decide))
  exact ⟨⟨tw, hdq, hvw (by decide)⟩, fun x0 ⟨V1, hd1, hv1⟩ =>
    ⟨V1, tw, Nat.lt_of_le_of_lt hv1 hV, hd1.mono (rmw_snap_prefix hs'), hdq⟩⟩

end Deq

end Kraken.Promising.X64.EnvG.MsQueueX
