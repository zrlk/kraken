/-
Part 4: **the per-access verification conditions of
`msqueue1.kl`** on the adjacency environment `EnvGCAdj`, AArch64
(`Arch.armv8`): the enqueuer is thread `0` on `planE P`, the dequeuer thread
`1` on `planD P` (`EnvG/MsQueueGhost.lean`).

**The enqueuer's table predicates** (all with `ComE`: the ghost facts, a
positive share of every 8-byte location, the identity token `tokE`):
- `E0` (start): the data word whole, its writes at or below `coh`;
- `EL` (`enq1_loop`): the data word `O ⋅ J`, `O` whole with its maximal
  write `(d, td)`, `td ≤ vwOld`, `D d` (`DatOK`);
- `EL1 y3` (after `ldar x3, [x1]`): `tail` read `y3`;
- `EL2 y3 y4` (after `ldar x4, [x8]`): and `[y3 + 8]` read `y4`;
- after the link `casal` succeeded: `ComE` only.

**The dequeuer's table predicates** (all with `ComD`: the ghost facts,
positive shares of `head`/`tail`, the acquire id `0` of every queue word,
the initial values, every forwarding item at or below `vrNew`):
- `D1 y3` (after `ldar x3, [x0]`): `head` read `y3`;
- `D3 y3 y5` (after `ldar x5, [x8]`): and `[y3 + 8]` read `y5` at
  `tr0 ≤ vrNew`;
- `D4 y3 y5 x10` (after `ldr w7, [x5]`): `DoneAt` (the reads, the data
  read's window up to `tr0`), kept by the `head` `casal`;
- `Dn x10` (`ddone1`): `DoneD` (`EnvG/MsQueueFinal.lean`).

**VCs**: `vc_e_str`, `vc_e_ldar_tail`, `vc_e_ldar_link`, `vc_e_fix`,
`vc_e_link`, `vc_e_swing`; `vc_d_ldar_head`, `vc_d_load`, `vc_d_ldar_link`,
`vc_d_help`, `vc_d_ldr`, `vc_d_cas`. The link `casal` writes a loaded
address `[y3 + 8]`: a pure message off the queue words, `form` with `n1`
at `head`/`tail`, and `form` with the node frozen (`NodeFrozen`) at a link
word. The helping `casal`s and the dequeuer's `head` `casal` release
`form` by provenance (`Prov`) from the thread's two reads.
-/
import Kraken.Promising.SLR.EnvG.MsQueueFinal
import Kraken.Promising.SLR.EnvG.Treiber2VC

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (casOp64 casOp64_some casOp64_none read?_of_get? get?_of_read? initVal_eq
  get?_of_anchor envGC_rmw_fail_getFwd)
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_le_last read?_mono rmw_success_fwd prefix_append)

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- The enqueuer's environment (thread `0`). -/
noncomputable abbrev EE (P : Params) : SharedEnv := EnvGCAdj isa Arch.armv8 0 (planE P)

/-- The dequeuer's environment (thread `1`). -/
noncomputable abbrev ED (P : Params) : SharedEnv := EnvGCAdj isa Arch.armv8 1 (planD P)

/-! ## Step helpers -/

/-- **A successful armv8 acquire-release RMW** leaves the other forwarding
items alone. -/
theorem rmw_success_getFwd_ne {tid : Nat} {pl : Plan} {σ σ' : State isa} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC isa Arch.armv8 tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) {l : Loc} (hne : l ≠ ⟨addr, n⟩) : σ'.vs.getFwd l = σ.vs.getFwd l := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := (h : RmwOutC Arch.armv8 tid pl σ σ' .acqRel ⟨addr, n⟩ op old)
  rcases hbr with ⟨hon, -⟩ | ⟨new', cx', tw, -, hc, hev, -, -, -, hvs, -⟩
  · rw [hop] at hon; cases hon
  obtain ⟨-, hwv⟩ := writeSuccs_at Arch.armv8 tid hc hev
  rw [hvs]
  simp only [rmwAfter, rmwPost, show Arch.armv8.rmwFence = false from rfl,
    show (Arch.armv8.rmwKind .acqRel == .acqRel) = true from rfl, Bool.not_false, Bool.and_self, ↓reduceIte,
    Bool.false_eq_true]
  change cx'.views.getFwd l = _
  rw [hwv.fwdOther _ hne]
  have h5 := SpinCommon.readSuccs_fwdb Arch.armv8 _ hx
  have e : x.2.2.views.getFwd l = (fenceOptCtx Arch.armv8 (envCtx tid σ.vs c)).views.getFwd l := by
    simp only [Views.getFwd, h5]
  rw [e, SpinCommon.fenceOptCtx_getFwd]
  rfl

/-- An RMW's snapshot memory extends the previous one
(`TreiberCommon.rmw_snap_prefix`). -/
theorem rmw_snap_prefix {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ') :
    σ.snap.mem.Prefix σ'.snap.mem :=
  TreiberCommon.rmw_snap_prefix hs

/-- An RMW keeps the initial memory. -/
theorem rmw_snap_init {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ') :
    σ'.snap.mem.init = σ.snap.mem.init :=
  (rmw_snap_prefix hs).1

/-- The resource after an RMW: unchanged (failure) or `after ⋅ C` (success)
(`TreiberCommon.rmw_res`). -/
theorem rmw_res {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ') :
    σ'.r = σ.r ∨ ∃ new tw Pc C, σ'.r = (pl.after ⟨addr, n⟩ new tw Pc σ.r).op C :=
  (TreiberCommon.rmw_res hs).imp_right fun ⟨new, tw, Pc, C, _, hr⟩ => ⟨new, tw, Pc, C, hr⟩

/-- An RMW's ghost grows (`TreiberCommon.rmw_ghost`). -/
theorem rmw_ghost {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ') :
    σ.g.Le σ'.g :=
  TreiberCommon.rmw_ghost hs

/-- An RMW's views grow (`TreiberCommon.rmw_vle`). -/
theorem rmw_vle {tid : Nat} {pl : Plan} {σ σ' : State isa} {k : RmwKind} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old : Val} (hs : (EnvGC isa Arch.armv8 tid pl).step (.rmw k addr n op) σ old σ') :
    VLe σ.vs σ'.vs :=
  TreiberCommon.rmw_vle hs

/-! ## The plans' resources -/

section PlanRes

variable {P : Params}

theorem planE_keep_wr (l : Loc) (v : Val) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.dat) :
    ((planE P).keep l v cl r).wr x = r.wr x := by
  unfold Plan.keep
  cases h : (planE P).find? l v with
  | none => simp [Res.drop]
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    simp only [planE, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [Plan.Entry.keep, Res.drop, hx]

theorem planE_keep_acq (l : Loc) (v : Val) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.dat) (ι : PredId) :
    ((planE P).keep l v cl r).acq x ι = r.acq x ι := by
  unfold Plan.keep
  cases h : (planE P).find? l v with
  | none => simp [Res.drop]
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    simp only [planE, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [Plan.Entry.keep, Res.drop, hx]

theorem planD_keep_wr (l : Loc) (v : Val) (cl : Prop) (r : Res) (x : Loc) :
    ((planD P).keep l v cl r).wr x = r.wr x := by
  unfold Plan.keep
  cases h : (planD P).find? l v with
  | none => simp [Res.drop]
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    simp only [planD, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [Plan.Entry.keep, Res.drop]

theorem planD_keep_acq (l : Loc) (v : Val) (cl : Prop) (r : Res) (x : Loc) (ι : PredId) :
    ((planD P).keep l v cl r).acq x ι = r.acq x ι := by
  unfold Plan.keep
  cases h : (planD P).find? l v with
  | none => simp [Res.drop]
  | some e =>
    have hm := List.mem_of_find?_eq_some h
    simp only [planD, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> simp [Plan.Entry.keep, Res.drop]

theorem afterE_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.dat) :
    (((planE P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planE_keep_wr _ _ _ _ hx]
  · rw [Res.addW_q]

theorem afterE_wr (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) {x : Loc} (hx : x ≠ P.dat) (hxl : x ≠ l) :
    ((planE P).after l v tw cl r).wr x = r.wr x := by
  unfold Plan.after
  split
  · rw [Res.addW_wr_ne _ _ hxl, planE_keep_wr _ _ _ _ hx]
  · rw [Res.addW_wr_ne _ _ hxl]

/-- The data word after a write to `tail` (the entry gives nothing). -/
theorem afterE_tail_dat (hL : QLocs P) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    ((planE P).after P.tail v tw cl r).wr P.dat = r.wr P.dat := by
  have hq : P.IsQ P.tail := .inr (.inl rfl)
  unfold Plan.after
  rw [planE_rel]
  simp only [hq, decide_true, ↓reduceIte]
  rw [Res.addW_wr_ne _ _ (Ne.symm (tail_dat P)), planE_keep hL hq]
  simp [Res.drop, hL.not_isN_tail]

theorem afterD_q (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) :
    (((planD P).after l v tw cl r).wr x).q = (r.wr x).q := by
  unfold Plan.after
  split
  · rw [Res.addW_q, planD_keep_wr]
  · rw [Res.addW_q]

theorem afterD_acq (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) (x : Loc) (ι : PredId) :
    ((planD P).after l v tw cl r).acq x ι = r.acq x ι := by
  unfold Plan.after
  split
  · rw [Res.addW_acq, planD_keep_acq]
  · rw [Res.addW_acq]

end PlanRes

theorem q_op_pos {a b : Perm} (h : 0 < a.q) : 0 < (a.op b).q := by
  have := b.nonneg
  change 0 < a.q + b.q
  grind

theorem q_op_ge_one {a b : Perm} (h : 1 ≤ a.q) : 1 ≤ (a.op b).q := by
  have := b.nonneg
  change 1 ≤ a.q + b.q
  grind

/-! ## The table predicates -/

/-- **The enqueuer's common facts**: the ghost facts, a positive share of
every 8-byte location, the identity token. -/
def ComE (P : Params) (σ : State isa) : Prop :=
  GW P σ.g ∧ (∀ a, 0 < (σ.r.wr ⟨a, 8⟩).q) ∧ 1 ≤ (σ.r.wr P.tokE).q

/-- The data word `O ⋅ J`, `O` whole with its maximal write `(d, td)`,
`td ≤ vwOld`, `D d`. -/
def DatOK (P : Params) (σ : State isa) : Prop :=
  ∃ O J : Perm, σ.r.wr P.dat = O.op J ∧ O.q = 1 ∧
    ∃ d td, O.X (d, td) ∧ (∀ p, O.X p → p.2 ≤ td) ∧ td ≤ σ.vs.vwOld ∧ D d

/-- **The enqueuer's start**: the data word whole, its writes at or below
`coh`. -/
def E0 (P : Params) (σ : State isa) : Prop :=
  ComE P σ ∧ (σ.r.wr P.dat).q = 1 ∧ ∀ p, (σ.r.wr P.dat).X p → p.2 ≤ σ.vs.getCoh P.dat

/-- **`enq1_loop`**. -/
def EL (P : Params) (σ : State isa) : Prop := ComE P σ ∧ DatOK P σ

/-- **After `ldar x3, [x1]`** of `y3`. -/
def EL1 (P : Params) (y3 : Val) (σ : State isa) : Prop :=
  EL P σ ∧ ∃ a, σ.snap.mem.read? P.tail a = some y3

/-- **After `ldar x4, [x8]`** of `y4`. -/
def EL2 (P : Params) (y3 y4 : Val) (σ : State isa) : Prop :=
  EL P σ ∧ ∃ a b, σ.snap.mem.read? P.tail a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ b = some y4

/-- Every forwarding item at or below `vrNew`. -/
def FwdAll (σ : State isa) : Prop := ∀ l f, σ.vs.getFwd l = some f → f.time ≤ σ.vs.vrNew

/-- **The dequeuer's common facts**. -/
def ComD (P : Params) (σ : State isa) : Prop :=
  GW P σ.g ∧ 0 < (σ.r.wr P.head).q ∧ 0 < (σ.r.wr P.tail).q ∧ (∀ x, P.IsQ x → 1 ≤ σ.r.acq x 0) ∧
    InitV σ.snap.mem P ∧ FwdAll σ

/-- **After `ldar x3, [x0]`** of `y3`. -/
def D1 (P : Params) (y3 : Val) (σ : State isa) : Prop :=
  ComD P σ ∧ ∃ a, σ.snap.mem.read? P.head a = some y3

/-- **After `ldar x5, [x8]`** of `y5`. -/
def D3 (P : Params) (y3 y5 : Val) (σ : State isa) : Prop :=
  ComD P σ ∧ ∃ a tr0, σ.snap.mem.read? P.head a = some y3 ∧
    σ.snap.mem.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ tr0 ≤ σ.vs.vrNew

/-- The dequeuer's last iteration with its two values exposed. -/
def DoneAt (m : Memory) (P : Params) (y3 y5 : Val) (x10 : BitVec 64) : Prop :=
  ∃ (a tr0 tl : Time) (u : Val), m.read? P.head a = some y3 ∧
    m.read? ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0 = some y5 ∧ BitVec.setWidth 64 y5 ≠ 0 ∧
    m.read? ⟨BitVec.setWidth 64 y5, 4⟩ tl = some u ∧
    (∀ p wm, tl < p → p ≤ tr0 → m.get? p = some wm → wm.loc ≠ ⟨BitVec.setWidth 64 y5, 4⟩) ∧
    x10 = BitVec.setWidth 64 (BitVec.setWidth 32 u)

theorem DoneAt.mono {m m' : Memory} (h : m.Prefix m') {P : Params} {y3 y5 : Val} {x : BitVec 64}
    (hd : DoneAt m P y3 y5 x) : DoneAt m' P y3 y5 x := by
  obtain ⟨a, tr0, tl, u, h1, h2, h3, h4, h5, h6⟩ := hd
  have hle := read?_le_last h2
  refine ⟨a, tr0, tl, u, read?_mono h h1, read?_mono h h2, h3, read?_mono h h4,
    fun p wm a b hg => h5 p wm a b (Memory.get?_of_prefix_le h.2 (by omega_t) hg), h6⟩

theorem DoneAt.doneD {m : Memory} {P : Params} {y3 y5 : Val} {x : BitVec 64} (hd : DoneAt m P y3 y5 x) :
    DoneD m P x :=
  let ⟨a, tr0, tl, u, h1, h2, h3, h4, h5, h6⟩ := hd
  ⟨a, y3, tr0, y5, tl, u, h1, h2, h3, h4, h5, h6⟩

/-- **After `ldr w7, [x5]`** (`x10` the data's zero-extended low 32 bits). -/
def D4 (P : Params) (y3 y5 : Val) (x10 : BitVec 64) (σ : State isa) : Prop :=
  ComD P σ ∧ DoneAt σ.snap.mem P y3 y5 x10

/-- **`ddone1`** with `X10 = x10`. -/
def Dn (P : Params) (x10 : BitVec 64) (σ : State isa) : Prop := ComD P σ ∧ DoneD σ.snap.mem P x10

theorem D4.dn {P : Params} {y3 y5 : Val} {x : BitVec 64} {σ : State isa} (h : D4 P y3 y5 x σ) : Dn P x σ :=
  ⟨h.1, h.2.doneD⟩

/-! ## Fences -/

section Fence

variable {P : Params} {σ σ' : State isa}

theorem ComE.fence (h : ComE P σ) (hf : FenceLe σ σ') : ComE P σ' := by
  unfold ComE; rw [hf.g, hf.r]; exact h

theorem DatOK.fence (h : DatOK P σ) (hf : FenceLe σ σ') : DatOK P σ' := by
  unfold DatOK; rw [hf.r, hf.vwOld]; exact h

theorem E0.fence (h : E0 P σ) (hf : FenceLe σ σ') : E0 P σ' := by
  unfold E0; rw [hf.r, hf.getCoh]; exact ⟨h.1.fence hf, h.2⟩

theorem EL.fence (h : EL P σ) (hf : FenceLe σ σ') : EL P σ' := ⟨h.1.fence hf, h.2.fence hf⟩

theorem EL1.fence {y3 : Val} (h : EL1 P y3 σ) (hf : FenceLe σ σ') : EL1 P y3 σ' := by
  unfold EL1; rw [hf.snap]; exact ⟨h.1.fence hf, h.2⟩

theorem EL2.fence {y3 y4 : Val} (h : EL2 P y3 y4 σ) (hf : FenceLe σ σ') : EL2 P y3 y4 σ' := by
  unfold EL2; rw [hf.snap]; exact ⟨h.1.fence hf, h.2⟩

theorem ComD.fence (h : ComD P σ) (hf : FenceLe σ σ') : ComD P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨hf.g ▸ h1, hf.r ▸ h2, hf.r ▸ h3, hf.r ▸ h4, hf.snap ▸ h5, fun l f hfw => ?_⟩
  rw [hf.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hf.vrNew

theorem D1.fence {y3 : Val} (h : D1 P y3 σ) (hf : FenceLe σ σ') : D1 P y3 σ' := by
  unfold D1; rw [hf.snap]; exact ⟨h.1.fence hf, h.2⟩

theorem D3.fence {y3 y5 : Val} (h : D3 P y3 y5 σ) (hf : FenceLe σ σ') : D3 P y3 y5 σ' := by
  obtain ⟨h1, a, tr0, h2, h3, h4⟩ := h
  exact ⟨h1.fence hf, a, tr0, hf.snap ▸ h2, hf.snap ▸ h3, Nat.le_trans h4 hf.vrNew⟩

theorem D4.fence {y3 y5 : Val} {x : BitVec 64} (h : D4 P y3 y5 x σ) (hf : FenceLe σ σ') : D4 P y3 y5 x σ' := by
  unfold D4; rw [hf.snap]; exact ⟨h.1.fence hf, h.2⟩

theorem Dn.fence {x : BitVec 64} (h : Dn P x σ) (hf : FenceLe σ σ') : Dn P x σ' := by
  unfold Dn; rw [hf.snap]; exact ⟨h.1.fence hf, h.2⟩

end Fence

/-! ## Loads and RMWs that keep the facts -/

section Keep

variable {P : Params} {σ σ' : State isa}

theorem ComE.load {tid : Nat} {k : LoadKind} {l : Loc} {v : Val} (h : ComE P σ)
    (hf : LoadFacts Arch.armv8 tid σ σ' k l v) : ComE P σ' := by
  obtain ⟨hanc, hr, -⟩ := hf
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3⟩

theorem DatOK.load {tid : Nat} {k : LoadKind} {l : Loc} {v : Val} (h : DatOK P σ)
    (hf : LoadFacts Arch.armv8 tid σ σ' k l v) : DatOK P σ' := by
  obtain ⟨-, hr, -, tr, -, hlv, -⟩ := hf
  unfold DatOK; rw [hr, hlv.vwOld]; exact h

theorem EL.load {tid : Nat} {k : LoadKind} {l : Loc} {v : Val} (h : EL P σ)
    (hf : LoadFacts Arch.armv8 tid σ σ' k l v) : EL P σ' := ⟨h.1.load hf, h.2.load hf⟩

/-- `ComE` after any RMW of the enqueuer. -/
theorem ComE.rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComE P σ)
    (hs : (EnvGC isa Arch.armv8 0 (planE P)).step (.rmw k addr n op) σ old σ') : ComE P σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_⟩ <;> rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
  · exact h2
  · intro a
    apply q_op_pos
    rw [afterE_q _ _ _ _ _ (dat_ne_of_8 P)]; exact h2 a
  · exact h3
  · apply q_op_ge_one
    rw [afterE_q _ _ _ _ _ (Ne.symm (dat_tokE P))]; exact h3

/-- `DatOK` after an RMW of `tail`. -/
theorem DatOK.rmw_tail (hL : QLocs P) {k : RmwKind} {op : Val → Option Val} {old : Val} (h : DatOK P σ)
    (hs : (EnvGC isa Arch.armv8 0 (planE P)).step (.rmw k P.tail.addr P.tail.bytes op) σ old σ') : DatOK P σ' := by
  obtain ⟨O, J, hOJ, hq, d, td, hX, hm, htd, hD⟩ := h
  have hvw := (rmw_vle hs).vwOld
  rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩
  · exact ⟨O, J, by rw [hr]; exact hOJ, hq, d, td, hX, hm, Nat.le_trans htd hvw, hD⟩
  · refine ⟨O, J.op (C.wr P.dat), ?_, hq, d, td, hX, hm, Nat.le_trans htd hvw, hD⟩
    rw [hr]
    show (((planE P).after P.tail new tw Pc σ.r).wr P.dat).op (C.wr P.dat) = _
    rw [afterE_tail_dat hL, hOJ, Perm.op_assoc]

/-- `EL` after an RMW of `tail`. -/
theorem EL.rmw_tail (hL : QLocs P) {k : RmwKind} {op : Val → Option Val} {old : Val} (h : EL P σ)
    (hs : (EnvGC isa Arch.armv8 0 (planE P)).step (.rmw k P.tail.addr P.tail.bytes op) σ old σ') : EL P σ' :=
  ⟨h.1.rmw hs, h.2.rmw_tail hL hs⟩

theorem ComD.load {k : LoadKind} {l : Loc} {v : Val} (h : ComD P σ)
    (hf : LoadFacts Arch.armv8 1 σ σ' k l v) : ComD P σ' := by
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := hf
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono hanc.ghost, hr ▸ h2, hr ▸ h3, hr ▸ h4, h5.of_init hanc.snap.init, fun l f hfw => ?_⟩
  rw [hlv.getFwd] at hfw
  exact Nat.le_trans (h6 l f hfw) hlv.mono.vrNew

/-- `ComD` after an acquire-release RMW of the dequeuer. -/
theorem ComD.rmw {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} (h : ComD P σ)
    (hs : (EnvGC isa Arch.armv8 1 (planD P)).step (.rmw .acqRel addr n op) σ old σ') : ComD P σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1.mono (rmw_ghost hs), ?_, ?_, ?_, h5.of_init (rmw_snap_init hs), ?_⟩
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h2
    · apply q_op_pos; rw [afterD_q]; exact h2
  · rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h3
    · apply q_op_pos; rw [afterD_q]; exact h3
  · intro x hx
    rcases rmw_res hs with hr | ⟨new, tw, Pc, C, hr⟩ <;> rw [hr]
    · exact h4 x hx
    · show 1 ≤ ((planD P).after _ new tw Pc σ.r).acq x 0 + C.acq x 0
      rw [afterD_acq]; have := h4 x hx; omega
  · intro l f hfw
    rcases Classical.em (op old = none) with hon | hon
    · rw [envGC_rmw_fail_getFwd hs hon] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew
    obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    by_cases hl : l = ⟨addr, n⟩
    · subst hl; exact rmw_success_fwd hs hnew f hfw
    · rw [rmw_success_getFwd_ne hs hnew hl] at hfw
      exact Nat.le_trans (h6 l f hfw) (rmw_vle hs).vrNew

end Keep

/-! ## The release obligations -/

section Rel

variable {P : Params}

/-- A read in the snapshot memory, at the message appended at the anchor:
in the new memory, below the new timestamp. -/
theorem read_at_append {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost} (hanc : AnchorOk tid σ c g)
    {x : Loc} {a : Time} {y : Val} (h : σ.snap.mem.read? x a = some y) (w : Msg) :
    a < c.mem.last + 1 ∧ (c.mem.append w).1.read? x a = some y := by
  have h' := read?_mono (Treiber2.AnchorOk.prefix hanc) h
  exact ⟨Nat.lt_succ_of_le (read?_le_last h'), read?_mono (prefix_append _ _) h'⟩

/-- **`form` by provenance** at `head`/`tail`: the thread read `y` from `head`
or `tail` and `y'` from `[y + 8]`, `y'` non-zero, and writes `y'`. -/
theorem form_prov (hL : QLocs P) {tid : Nat} {σ : State isa} {c : Config isa} {g : Ghost}
    (hanc : AnchorOk tid σ c g) {l x : Loc} (hl : l = P.head ∨ l = P.tail) (hx : x = P.head ∨ x = P.tail)
    {a b : Time} {y y' : Val} (h1 : σ.snap.mem.read? x a = some y)
    (h2 : σ.snap.mem.read? ⟨BitVec.setWidth 64 y + 8, 8⟩ b = some y') (hnz : BitVec.setWidth 64 y' ≠ 0) (R : Res) :
    (form P).P (BitVec.setWidth 128 (BitVec.setWidth 64 y')) (c.mem.append ⟨l, BitVec.setWidth 128 (BitVec.setWidth 64 y'), tid⟩).1
      (c.mem.last + 1) R := by
  intro _
  have hn : ¬ P.IsN l := by
    rcases hl with rfl | rfl
    · exact hL.not_isN_head
    · exact hL.not_isN_tail
  obtain ⟨ha, h1'⟩ := read_at_append hanc h1 ⟨l, BitVec.setWidth 128 (BitVec.setWidth 64 y'), tid⟩
  obtain ⟨hb, h2'⟩ := read_at_append hanc h2 ⟨l, BitVec.setWidth 128 (BitVec.setWidth 64 y'), tid⟩
  refine ⟨l, tid, Memory.get?_append_last _ _, fun h => absurd h hn, fun _ => .inr ⟨?_, x, a, y, b, y', hx, ha, h1',
    hb, h2', ?_⟩⟩
  · simpa using hnz
  · simp

/-- **`form` of `n1`** at `head`/`tail`. -/
theorem form_n1 {tid : Nat} (m : Memory) {l : Loc} (hl : ¬ P.IsN l) (R : Res) :
    (form P).P (BitVec.setWidth 128 P.n1) (m.append ⟨l, BitVec.setWidth 128 P.n1, tid⟩).1 (m.last + 1) R := by
  intro _
  exact ⟨l, tid, Memory.get?_append_last _ _, fun h => absurd h hl, fun _ => .inl (by simp)⟩

end Rel

/-! ## The enqueuer -/

section Enq

variable {P : Params}

/-- **VC `str w9, [x2]`** (the data word, a value `v` with `D v`): permitted
(pure, the word whole), and `EL` after it. -/
theorem vc_e_str (σ : State isa) (h : E0 P σ) (v : Val) (hD : D v) :
    (EE P).ok (.store .plain false P.dat.addr P.dat.bytes v) σ ∧
      ∀ b (σ' : State isa), (EE P).step (.store .plain false P.dat.addr P.dat.bytes v) σ b σ' → EL P σ' := by
  obtain ⟨⟨hW, hpos, htok⟩, hq, hX⟩ := h
  have e : ({ addr := P.dat.addr, bytes := P.dat.bytes } : Loc) = P.dat := rfl
  have hnq := not_isQ_dat P
  refine ⟨⟨rfl, by rw [e, hq]; decide, fun _ => by rw [e, hW.rel_ne hnq]; exact Pred.emp_pure _,
    fun hr => by rw [e, planE_rel] at hr; simp [hnq] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := planE P) hs
  have hafter : ∀ cl, (planE P).after P.dat v tw cl σ.r = σ.r.addW P.dat (v, tw) := by
    intro cl; unfold Plan.after; rw [planE_rel]; simp [hnq]
  rw [e, hafter] at hr
  have hwr : ∀ x, x ≠ P.dat → σ'.r.wr x = σ.r.wr x := fun x hx => by rw [hr, Res.addW_wr_ne _ _ hx]
  refine ⟨⟨hW.mono hanc.ghost, fun a => by rw [hwr _ (dat_ne_of_8 P)]; exact hpos a,
    by rw [hwr _ (Ne.symm (dat_tokE P))]; exact htok⟩, σ'.r.wr P.dat, Perm.unit, (Perm.op_unit _).symm,
    by rw [hr, Res.addW_q]; exact hq, v, tw, ?_, ?_, hwv.vwOld (by decide), hD⟩
  · rw [hr, Res.addW_X_self]; exact .inr ⟨by rw [hq]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hX p hp) hwb.coh)
    · exact Nat.le_refl _

/-- **VC `ldar x3, [x1]`**: `tail` read. -/
theorem vc_e_ldar_tail (σ : State isa) (h : EL P σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE P).step (.load .acq xcl P.tail.addr P.tail.bytes) σ v σ' → EL1 P v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  refine ⟨h.load hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **VC `ldar x4, [x8]`** (`x8 = x3 + 8`): the link read. -/
theorem vc_e_ldar_link (σ : State isa) {y3 : Val} (h : EL1 P y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (EE P).step (.load .acq xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' → EL2 P y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planE P) hs
  obtain ⟨hel, a, ha⟩ := h
  refine ⟨hel.load hf, ?_⟩
  obtain ⟨hanc, -, -, tr, hrd, -⟩ := hf
  exact ⟨a, tr, hanc.read? ha, hrd.val⟩

/-- **VC `casal x5, x4, [x1]`** (helping: `x5 = x3`, `x4 ≠ 0`): permitted
(`form` by provenance), `EL` after it. -/
theorem vc_e_fix (hL : QLocs P) (σ : State isa) {y3 y4 : Val} (h : EL2 P y3 y4 σ)
    (hnz : BitVec.setWidth 64 y4 ≠ 0) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ ∧
      ∀ old (σ' : State isa), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y4))) σ old σ' → EL P σ' := by
  obtain ⟨⟨⟨hW, hpos, htok⟩, hdat⟩, a, b, h1, h2⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsQ P.tail := .inr (.inl rfl)
  refine ⟨⟨hpos _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => EL.rmw_tail hL ⟨⟨hW, hpos, htok⟩, hdat⟩ (envGCAdj_step_iff.mp hs)⟩
  · rw [e, planE_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planE_gives hL hq]; simp [hL.not_isN_tail]
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_q hq]
    exact form_prov hL hanc (.inr rfl) (.inr rfl) h1 h2 hnz _

/-- **VC `casal x5, x2, [x8]`** (the link: `x8 = x3 + 8`, `x5 = 0`, `x2 =
n1`): permitted (pure off the queue words, `form` of `n1` at `head`/`tail`,
`form` with the node frozen at a link word), and every outcome fails (`EL`)
or succeeds (`ComE`). -/
theorem vc_e_link (hL : QLocs P) (σ : State isa) {y3 y4 : Val} (h : EL2 P y3 y4 σ) :
    (EE P).ok (.rmw .acqRel (BitVec.setWidth 64 y3 + 8) 8 (casOp64 0 P.n1)) σ ∧
      ∀ old (σ' : State isa), (EE P).step (.rmw .acqRel (BitVec.setWidth 64 y3 + 8) 8 (casOp64 0 P.n1)) σ old σ' →
        (BitVec.setWidth 64 old ≠ 0 ∧ EL P σ') ∨ (BitVec.setWidth 64 old = 0 ∧ ComE P σ') := by
  obtain ⟨⟨⟨hW, hpos, htok⟩, O, J, hOJ, hOq, d, td, hX, hm, htd, hD⟩, -⟩ := h
  refine ⟨⟨hpos _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun hr => ?_⟩⟩, ?_⟩
  · by_cases hq : P.IsQ ⟨BitVec.setWidth 64 y3 + 8, 8⟩
    · rw [planE_rel, decide_eq_false_iff_not] at hr; exact absurd hq hr
    · rw [hW.rel_ne hq]; exact Pred.emp_pure _
  · have hq : P.IsQ ⟨BitVec.setWidth 64 y3 + 8, 8⟩ := by rw [planE_rel] at hr; simpa using hr
    refine ⟨by decide, hW.impure hq new, ?_, fun htr hwb hadj => ?_⟩
    · rw [planE_gives hL hq]; split <;> simp [dat_ne_of_8]
    obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [hW.rel_q hq, planE_give hL hq]
    by_cases hn : P.IsN ⟨BitVec.setWidth 64 y3 + 8, 8⟩
    · intro _
      have hV : σ.vs.vwOld < c.mem.last + 1 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel (by decide))
      refine ⟨_, 0, Memory.get?_append_last _ _, fun _ => ⟨by simp, O, J, ?_, hOq, d, td, hX, hm,
        Nat.lt_of_le_of_lt htd hV, hD⟩, fun h => absurd hn h⟩
      simp only [hn, ↓reduceIte, Res.only, List.mem_singleton]
      exact hOJ
    · exact form_n1 c.mem hn _
  intro old σ' hs
  have hs' := envGCAdj_step_iff.mp hs
  have hcom := ComE.rmw ⟨hW, hpos, htok⟩ hs'
  rcases Classical.em (casOp64 0 P.n1 old = none) with hon | hon
  · refine .inl ⟨casOp64_none hon, hcom, O, J, ?_, hOq, d, td, hX, hm, Nat.le_trans htd (rmw_vle hs').vwOld, hD⟩
    obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs'
    rcases hbr with ⟨-, -, hr⟩ | ⟨new, -, hon', -⟩
    · rw [hr]; exact hOJ
    · rw [hon] at hon'; cases hon'
  · obtain ⟨new, hnew⟩ := Option.ne_none_iff_exists'.mp hon
    exact .inr ⟨(casOp64_some hnew).1, hcom⟩

/-- **VC `casal x5, x2, [x1]`** (the swing: `x2 = n1`): permitted (`form` of
`n1`), `ComE` after it. -/
theorem vc_e_swing (hL : QLocs P) (σ : State isa) (h : ComE P σ) (x5 : BitVec 64) :
    (EE P).ok (.rmw .acqRel P.tail.addr P.tail.bytes (casOp64 x5 P.n1)) σ ∧
      ∀ old (σ' : State isa), (EE P).step (.rmw .acqRel P.tail.addr P.tail.bytes (casOp64 x5 P.n1)) σ old σ' →
        ComE P σ' := by
  obtain ⟨hW, hpos, htok⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsQ P.tail := .inr (.inl rfl)
  refine ⟨⟨hpos _, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ComE.rmw ⟨hW, hpos, htok⟩ (envGCAdj_step_iff.mp hs)⟩
  · rw [e, planE_rel] at hr; simp [hq] at hr
  · rw [e]; exact hW.impure hq new
  · rw [e, planE_gives hL hq]; simp [hL.not_isN_tail]
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hW.rel_q hq]
    exact form_n1 c.mem hL.not_isN_tail _

end Enq

/-! ## The dequeuer -/

section Deq

variable {P : Params}

/-- **VC `ldar x3, [x0]`**: `head` read. -/
theorem vc_d_ldar_head (σ : State isa) (h : ComD P σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED P).step (.load .acq xcl P.head.addr P.head.bytes) σ v σ' → D1 P v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  refine ⟨h.load hf, ?_⟩
  obtain ⟨-, -, -, tr, hrd, -⟩ := hf
  exact ⟨tr, hrd.val⟩

/-- **A load keeps `D1`** (`ldar x4, [x1]`). -/
theorem vc_d_load (σ : State isa) {y3 : Val} (h : D1 P y3 σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State isa), (ED P).step (.load k xcl a n) σ v σ' → D1 P y3 σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, a, ha⟩ := h
  refine ⟨hc.load hf, a, ?_⟩
  obtain ⟨hanc, -⟩ := hf
  exact hanc.read? ha

/-- **VC `ldar x5, [x8]`** (`x8 = x3 + 8`): the link read at `tr0 ≤ vrNew`. -/
theorem vc_d_ldar_link (σ : State isa) {y3 : Val} (h : D1 P y3 σ) {xcl : Bool} :
    ∀ v (σ' : State isa), (ED P).step (.load .acq xcl (BitVec.setWidth 64 y3 + 8) 8) σ v σ' → D3 P y3 v σ' := by
  intro v σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, a, ha⟩ := h
  refine ⟨hc.load hf, a, ?_⟩
  obtain ⟨hanc, -, -, tr0, hrd, hlv, -⟩ := hf
  refine ⟨tr0, hanc.read? ha, hrd.val, ?_⟩
  by_cases hfw : Fwded σ.vs ⟨BitVec.setWidth 64 y3 + 8, 8⟩ tr0
  · obtain ⟨f, hf, rfl⟩ := hfw
    exact Nat.le_trans (hc.2.2.2.2.2 _ f hf) hlv.mono.vrNew
  · exact (hlv.acq (by decide) hfw).1

/-- **VC `casal x6, x5, [x1]`** (helping: `x6 = x3`, `x5 ≠ 0`): permitted
(`form` by provenance from `head`), `ComD` after it. -/
theorem vc_d_help (hL : QLocs P) (σ : State isa) {y3 y5 : Val} (h : D3 P y3 y5 σ)
    (hnz : BitVec.setWidth 64 y5 ≠ 0) :
    (ED P).ok (.rmw .acqRel P.tail.addr P.tail.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED P).step (.rmw .acqRel P.tail.addr P.tail.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' → ComD P σ' := by
  obtain ⟨hc, a, tr0, h1, h2, -⟩ := h
  have e : ({ addr := P.tail.addr, bytes := P.tail.bytes } : Loc) = P.tail := rfl
  have hq : P.IsQ P.tail := .inr (.inl rfl)
  refine ⟨⟨hc.2.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => hc.rmw (envGCAdj_step_iff.mp hs)⟩
  · rw [e, planD_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.impure hq new
  · rw [e, planD_gives hL hq]; simp
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hc.1.rel_q hq]
    exact form_prov hL hanc (.inr rfl) (.inl rfl) h1 h2 hnz _

/-- **VC `ldr w7, [x5]`** (`x5 ≠ 0`): its window covers the link read
(`D4`). -/
theorem vc_d_ldr (σ : State isa) {y3 y5 : Val} (h : D3 P y3 y5 σ) (hnz : BitVec.setWidth 64 y5 ≠ 0) {xcl : Bool} :
    ∀ u (σ' : State isa), (ED P).step (.load .plain xcl (BitVec.setWidth 64 y5) 4) σ u σ' →
      D4 P y3 y5 (BitVec.setWidth 64 (BitVec.setWidth 32 u)) σ' := by
  intro u σ' hs
  have hf := step_loadFacts (pl := planD P) hs
  obtain ⟨hc, a, tr0, h1, h2, h3⟩ := h
  refine ⟨hc.load hf, ?_⟩
  obtain ⟨hanc, -, -, tl, hrd, hlv, -⟩ := hf
  refine ⟨a, tr0, tl, u, hanc.read? h1, hanc.read? h2, hnz, hrd.val, fun p wm ha hb hg hl => ?_, rfl⟩
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, wm, ha, Nat.le_trans hb (Nat.le_trans h3
    (le_readBound_vrNew Arch.armv8 σ.vs .plain ⟨BitVec.setWidth 64 y5, 4⟩)), hg, hl⟩
  rw [hrd.window] at this; cases this

/-- **VC `casal x6, x5, [x0]`** (`x6 = x3`): permitted (`form` by
provenance from `head`), `D4` after it. -/
theorem vc_d_cas (hL : QLocs P) (σ : State isa) {y3 y5 : Val} {x : BitVec 64} (h : D4 P y3 y5 x σ) :
    (ED P).ok (.rmw .acqRel P.head.addr P.head.bytes
        (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ ∧
      ∀ old (σ' : State isa), (ED P).step (.rmw .acqRel P.head.addr P.head.bytes
          (casOp64 (BitVec.setWidth 64 y3) (BitVec.setWidth 64 y5))) σ old σ' → D4 P y3 y5 x σ' := by
  obtain ⟨hc, hd⟩ := h
  obtain ⟨a, tr0, tl, u, h1, h2, hnz, -⟩ := id hd
  have e : ({ addr := P.head.addr, bytes := P.head.bytes } : Loc) = P.head := rfl
  have hq : P.IsQ P.head := .inl rfl
  refine ⟨⟨hc.2.1, fun c g tr old new hanc hrd hon => ⟨fun hr => ?_, fun _ => ⟨by decide, ?_, ?_,
    fun htr hwb hadj => ?_⟩⟩⟩, fun old σ' hs => ?_⟩
  · rw [e, planD_rel] at hr; simp [hq] at hr
  · rw [e]; exact hc.1.impure hq new
  · rw [e, planD_gives hL hq]; simp
  · obtain ⟨-, rfl⟩ := casOp64_some hon
    rw [e, hc.1.rel_q hq]
    exact form_prov hL hanc (.inl rfl) (.inl rfl) h1 h2 hnz _
  have hs' := envGCAdj_step_iff.mp hs
  exact ⟨hc.rmw hs', hd.mono (rmw_snap_prefix hs')⟩

end Deq

end Kraken.Promising.SLR.EnvG.MsQueue
