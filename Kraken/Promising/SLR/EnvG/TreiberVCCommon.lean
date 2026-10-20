/-
**Part 3: the per-access verification
conditions of the one-push/one-pop Treiber stack, ISA-neutral.**

The Treiber proof's `EnvG/TreiberVC.lean` states its table predicates and VCs at the
AArch64 state type and `Arch.armv8` (and imports AArch64 files, so x64 files
cannot use it). Its arguments do not depend on the ISA: here they are restated
for any `I : ISA` and any profile `A` on the claim-conditional environment
`EnvGC I A tid pl`, with

- the compare-and-swap abstracted to any operation `op` with `CasMatch op x y`
  (succeeds exactly on a 64-bit old value `x`, writing `y`): AArch64's
  `casOp64 x y` (`casal`) and x64's `lock cmpxchgq` operation `cmpxOp64 x y`
  (`EnvG/X64TreiberVC.lean`) are instances;
- the RMW kind `.acqRel` (both `casal` and every x64 RMW), whose claim,
  acquire and release facts hold under every profile (`rfl`);
- the one profile-dependent fact as a hypothesis: the data store is not
  non-temporal (`A.storeKind .plain ≠ .nt`; `.plain` on armv8, `.rel` on tso).

The ownership design (`EnvG/TreiberGhost.lean`, reused unchanged) and the
proofs are the Treiber proof's. These are hoist candidates: `TreiberVC`'s definitions
and VCs are the instances at `I := AArch64.isa`, `A := Arch.armv8`,
`op := casOp64`.

Contents: memory/step helpers (`read?_of_get?`, `get?_of_read?`,
`initVal_eq`, `get?_of_anchor`, `WriteSnap.get?_old/get?_new/init`,
`envGC_rmw_fail_getFwd`), `GW`, `total_acq_of_ge`, `other_absurd`, the table
predicates `Pp`, `Pc`, `Pu0`, `Pu`, `Pd` with their `fence` lemmas, and the
VCs `vc_pop_load`, `vc_pop_cas`, `vc_pop_ldr`, `vc_push_str_d`,
`vc_push_load`, `vc_push_str_n`, `vc_push_cas`.
-/
import Kraken.Promising.SLR.EnvG.TreiberGhost
import Kraken.Promising.SLR.EnvG.RmwGhost
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.EnvG.VCGenCommon
import Kraken.Promising.SLR.EnvG.Seen
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinClaim
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.EnvG.SpscCommon

namespace Kraken.Promising.SLR.EnvG.TreiberCommon

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.EnvG.Treiber

variable {I : ISA}

/-! ## Compare-and-swap operations -/

/-- **`op` is a 64-bit compare-and-swap** of expected value `x` and new value
`y`: it succeeds exactly when the old value's low 64 bits are `x`, writing
`y` (zero-extended). -/
structure CasMatch (op : Val → Option Val) (x y : BitVec 64) : Prop where
  some : ∀ o n, op o = some n → BitVec.setWidth 64 o = x ∧ n = BitVec.setWidth 128 y
  none : ∀ o, op o = none → BitVec.setWidth 64 o ≠ x

/-! ## The parameters of `treiber_pp.kl` -/

/-- The parameters of `treiber_pp.kl` (either ISA) at `top = t` (8 bytes)
and the node `n1 = n` (data word `[n]`, 4 bytes; link `[n + 8]`, 8 bytes),
with the ghost token `tok`. The x64 `TreiberX.tParamsX` is an alias;
the Treiber proof's AArch64 `Treiber.tParams` is still its own copy (same body). -/
def tParamsC (t n : BitVec 64) (tok : Loc) : Params :=
  ⟨⟨t, 8⟩, ⟨n, 4⟩, ⟨n + 8, 8⟩, tok, BitVec.setWidth 128 n⟩

/-- **`TLocs` of `tParamsC` at the token `⟨t, 1⟩`** from `t ≠ n + 8`
(`tLocs_tPX`, and the Treiber proof's `tLocs_tP`, have this proof). -/
theorem tLocs_tParamsC {t n : BitVec 64} (htn : t ≠ n + 8) : TLocs (tParamsC t n ⟨t, 1⟩) where
  top_d := by simp [tParamsC]
  top_n := by simp only [tParamsC, ne_eq, Loc.mk.injEq, and_true]; exact htn
  top_t := by simp [tParamsC]
  d_n := by simp [tParamsC]
  d_t := by simp [tParamsC]
  n_t := by simp [tParamsC]

/-! ## Memory and step helpers -/

theorem read?_of_get? {m : Memory} {ts : Time} {w : Msg} (hw : m.get? ts = some w) :
    m.read? w.loc ts = some w.val := by
  have h0 : ts ≠ 0 := by rintro rfl; simp [Memory.get?] at hw
  unfold Memory.read?
  rw [ite_eq_right h0, hw]
  simp

theorem get?_of_read? {m : Memory} {l : Loc} {ts : Time} {v : Val} (h0 : ts ≠ 0) (h : m.read? l ts = some v) :
    ∃ w, m.get? ts = some w ∧ w.loc = l ∧ w.val = v := by
  unfold Memory.read? at h
  rw [ite_eq_right h0] at h
  split at h
  · next w hw =>
    split at h
    · next he => cases h; exact ⟨w, hw, by simpa using he, rfl⟩
    · cases h
  · cases h

theorem initVal_eq {m m' : Memory} (h : m'.init = m.init) (l : Loc) : m'.initVal l = m.initVal l := by
  simp [Memory.initVal, h]

/-- A message of the snapshot is a message of every admissible anchor. -/
theorem get?_of_anchor {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g)
    {ts : Time} {w : Msg} (hw : σ.snap.mem.get? ts = some w) : c.mem.get? ts = some w :=
  Memory.get?_of_prefix h.snap.msgs hw

/-- Where a write lands: the old messages stay, the write is at `tw`. -/
theorem WriteSnap.get?_old {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) {ts : Time} {w : Msg} (hw : c.mem.get? ts = some w) : c'.mem.get? ts = some w := by
  rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hw
  · rw [hm]
    refine Memory.get?_of_prefix ?_ hw
    simp [Memory.append, Array.toList_push]

theorem WriteSnap.get?_new {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c'.mem.get? tw = some ⟨l, v, tid⟩ := by
  rcases h.mem with ⟨hm, hg, -⟩ | ⟨hm, rfl⟩
  · rw [hm]; exact hg
  · rw [hm]; exact Memory.get?_append_last _ _

theorem WriteSnap.init {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c'.mem.init = c.mem.init := by
  rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩ <;> rw [hm]; rfl

/-- A failed RMW of `EnvGC` leaves the forwarding items alone. -/
theorem envGC_rmw_fail_getFwd {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind}
    {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') (hop : op old = none)
    (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := (h : RmwOutC A tid pl σ σ' k ⟨addr, n⟩ op old)
  rcases hbr with ⟨-, -, hvs, -⟩ | ⟨new, -, -, hop', -⟩
  · have h5 := readSuccs_fwdb A _ hx
    have e : x.2.2.views.getFwd l = (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l := by
      simp only [Views.getFwd, h5]
    rw [hvs, fenceOptCtx_getFwd, e, fenceOptCtx_getFwd]
    rfl
  · rw [hop] at hop'; cases hop'

/-! ## Shared memory and step facts

Generic versions of the Treiber node proof helpers (`Treiber2.prefix_append`,
`WriteSnap.prefix`/`tw_le`, `AnchorOk.prefix`, `read?_le_last`, `read?_mono`,
`rmw_success_fwd`, `acq_pair_false`) and of the `bv_omega` workaround
`bv64_eq_of_sub_eq_zero` (private in three vcgen files); the Treiber2 names
are aliases or instances at `isa`. -/

theorem prefix_append (m : Memory) (w : Msg) : m.Prefix (m.append w).1 :=
  ⟨rfl, by simp [Memory.append, Array.toList_push]⟩

theorem WriteSnap.prefix {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c.mem.Prefix c'.mem := by
  rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact Memory.Prefix.refl _
  · rw [hm]; exact prefix_append _ _

theorem WriteSnap.tw_le {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : tw ≤ c.mem.last + 1 := by
  rcases h.mem with ⟨-, hg, -⟩ | ⟨-, rfl⟩
  · have := c.mem.last_le_of_get?_eq_some hg; simp only [Time] at *; omega
  · exact Nat.le_refl _

theorem AnchorOk.prefix {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (h : AnchorOk tid σ c g) :
    σ.snap.mem.Prefix c.mem := ⟨h.snap.init, h.snap.msgs⟩

theorem read?_le_last {m : Memory} {l : Loc} {ts : Time} {v : Val} (h : m.read? l ts = some v) : ts ≤ m.last :=
  SpscCommon.read?_le_last h

/-- A read is stable under memory growth. -/
theorem read?_mono {m m' : Memory} (h : m.Prefix m') {l : Loc} {ts : Time} {v : Val}
    (hr : m.read? l ts = some v) : m'.read? l ts = some v := by
  by_cases h0 : ts = 0
  · subst h0
    simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at hr ⊢
    rw [initVal_eq h.1, hr]
  · obtain ⟨w, hw, hl, hv⟩ := get?_of_read? h0 hr
    rw [← hl, ← hv]
    exact read?_of_get? (Memory.get?_of_prefix h.2 hw)

/-! ## RMW step facts on `EnvGC`, at any architecture (the MS queue proof's
`MsQueue.rmw_snap_prefix`/`rmw_ghost`/`rmw_vle`/`rmw_res` and the x64 MS queue proof's
`MsQueueX` copies are their instances). -/

section RmwStep

variable {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64} {n : Nat}
  {op : Val → Option Val} {old : Val}

/-- An RMW's snapshot memory extends the previous one. -/
theorem rmw_snap_prefix (hs : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') :
    σ.snap.mem.Prefix σ'.snap.mem := by
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, hsnap, -⟩ | ⟨new, tw, -, -, -, hws, -⟩
  · rw [hsnap]; exact AnchorOk.prefix hanc
  · exact (AnchorOk.prefix hanc).trans (WriteSnap.prefix hws)

/-- An RMW's ghost grows. -/
theorem rmw_ghost (hs : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') : σ.g.Le σ'.g := by
  obtain ⟨c, tr, hanc, -⟩ := step_rmwFactsC hs
  exact hanc.ghost

/-- An RMW's views grow. -/
theorem rmw_vle (hs : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') : VLe σ.vs σ'.vs := by
  obtain ⟨c, tr, hanc, -, hvle, -⟩ := step_rmwFactsC hs
  exact hvle

/-- The resource after an RMW: unchanged (failure) or `after ⋅ C` (success,
with the operation's result `new`). -/
theorem rmw_res (hs : (EnvGC I A tid pl).step (.rmw k addr n op) σ old σ') :
    σ'.r = σ.r ∨ ∃ new tw Pc C, op old = some new ∧ σ'.r = (pl.after ⟨addr, n⟩ new tw Pc σ.r).op C := by
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨-, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨Pc, -, hr⟩, -⟩
  · exact .inl hr
  · exact .inr ⟨new, tw, Pc, _, hon, hr⟩

end RmwStep

/-- **A successful armv8 acquire-release RMW** leaves its forwarding item at
or below `vrNew`. -/
theorem rmw_success_fwd {tid : Nat} {pl : Plan} {σ σ' : State I} {addr : BitVec 64} {n : Nat}
    {op : Val → Option Val} {old new : Val} (h : (EnvGC I Arch.armv8 tid pl).step (.rmw .acqRel addr n op) σ old σ')
    (hop : op old = some new) : ∀ f, σ'.vs.getFwd ⟨addr, n⟩ = some f → f.time ≤ σ'.vs.vrNew := by
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

/-- **Two threads cannot both hold an acquire id** of a location under a
valid erasure. -/
theorem acq_pair_false {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j) {x : Loc} {ι : PredId}
    (h1 : 1 ≤ (rF i).acq x ι) (h2 : 1 ≤ (rF j).acq x ι) : False := by
  have h3 := sub_acq_le (sub_total_pair (rF := rF) (g := g) (c := c) hi hj hij) x ι
  have h4 := E.valid.2 x ι
  have h5 : ((rF i).op (rF j)).acq x ι = (rF i).acq x ι + (rF j).acq x ι := rfl
  omega

/-- `a - b = 0 → a = b` on 64 bits (by `bv_omega`; a named lemma, since
`bv_omega` inside `vcgen` goals hit a kernel mismatch). -/
theorem bv64_eq_of_sub_eq_zero {a b : BitVec 64} (h : a - b = 0#64) : a = b := by bv_omega

/-! ## The ghost facts -/

/-- **The ghost facts** both threads rely on. -/
def GW (P : Params) (g : Ghost) : Prop :=
  g.rel = (ghost₀ P).rel ∧ (ghost₀ P).acqTab <+: g.acqTab ∧ 1 ∈ g.upd P.top

namespace GW

variable {P : Params} {g g' : Ghost}

theorem mono (h : GW P g) (hle : g.Le g') : GW P g' :=
  ⟨hle.rel.trans h.1, h.2.1.trans hle.acqTab, (hle.upd P.top).subset h.2.2⟩

theorem rel_top (h : GW P g) : g.rel P.top = relTop P := by rw [h.1]; exact ghost₀_rel_top P

theorem rel_ne (h : GW P g) {x : Loc} (hx : x ≠ P.top) : g.rel x = Pred.emp := by rw [h.1]; exact ghost₀_rel_ne hx

theorem acqPred_zero (h : GW P g) : g.acqPred 0 = predP P :=
  Ghost.acqPred_of_prefix h.2.1 (by simp [ghost₀])

theorem acqPred_one (h : GW P g) : g.acqPred 1 = predU P :=
  Ghost.acqPred_of_prefix h.2.1 (by simp [ghost₀])

end GW

theorem ghost₀_gw (P : Params) : GW P (ghost₀ P) := ⟨rfl, List.prefix_refl _, by simp [ghost₀]⟩

/-! ## The popper's refutation of an other message -/

/-- An acquire id held at least once by a thread is held once in the total. -/
theorem total_acq_of_ge {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c) {i : Nat}
    (hi : i < c.threads.size) {x : Loc} {ι : PredId} (h : 1 ≤ (rF i).acq x ι) : (total rF g c).acq x ι = 1 := by
  have h1 := sub_acq_le (sub_total_thread (rF := rF) (g := g) (c := c) hi) x ι
  have h2 := E.valid.2 x ι
  omega

/-- **Two other messages refute an erasure in which the popper (thread `1`)
holds the acquire id `0` of `top`**: each has a slot of id `0` holding the
token whole. -/
theorem other_absurd {P : Params} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {r : Res}
    (E : Erase (setRes rF 1 r) g T c) (hn : 1 < c.threads.size) (hW : GW P g) (hacq : 1 ≤ r.acq P.top 0)
    {tr tw : Time} {w : Msg} {new : Val} (hne : tr ≠ tw) (hw : c.mem.get? tr = some w) (hl : w.loc = P.top)
    (ht : w.tid ≠ 0) (hw' : c.mem.get? tw = some ⟨P.top, new, 1⟩) : False := by
  have htot : (total (setRes rF 1 r) g c).acq P.top 0 = 1 :=
    total_acq_of_ge E hn (by rw [setRes_self]; exact hacq)
  have himp : ∀ v, ¬ Pred.Pure (g.rel P.top) v := fun v => by rw [hW.rel_top]; exact relTop_not_pure P v
  have h0 : ∀ {ts : Time} {w : Msg}, c.mem.get? ts = some w → ts ≠ 0 := fun hw => by
    rintro rfl; simp [Memory.get?] at hw
  have hr1 : c.mem.read? (P.top, tr).1 (P.top, tr).2 = some w.val := by
    show c.mem.read? P.top tr = _; rw [← hl]; exact read?_of_get? hw
  have hr2 : c.mem.read? (P.top, tw).1 (P.top, tw).2 = some new := read?_of_get? hw'
  obtain ⟨s, hs, hk, hid, hP⟩ := slot_of_held E htot hr1 (himp _)
  obtain ⟨s', hs', hk', hid', hP'⟩ := slot_of_held E htot hr2 (himp _)
  rw [hW.acqPred_zero] at hP hP'
  have hq := hP.1 (otherMsg_of_get (h0 hw) hw ht)
  have hq' := hP'.1 (otherMsg_of_get (h0 hw') hw' (by simp))
  have hss : s' ≠ s := by
    rintro rfl
    rw [hk] at hk'
    exact hne (congrArg Prod.snd hk')
  have := E.q_add_le_one_slots hs hs' hss P.tok
  rw [hq, hq'] at this
  grind

/-! ## The table predicates -/

/-- **The popper in its loop**: the token whole, a share of `top`, acquire id
`0` of `top`, no forwarding item of `top`, `top`'s initial value `0`. -/
def Pp (P : Params) (σ : State I) : Prop :=
  GW P σ.g ∧ (σ.r.wr P.tok).q = 1 ∧ 0 < (σ.r.wr P.top).q ∧ σ.r.acq P.top 0 = 1 ∧ σ.vs.getFwd P.top = none ∧
    σ.snap.mem.initVal P.top = 0

/-- **The popper after a successful compare-and-swap** that compared `x2`: a
pusher message was read (`x2 = n1`, the claimed node `S`) or an other message
(refuted by the next clean erasure). -/
def Pc (P : Params) (x2 : BitVec 64) (σ : State I) : Prop :=
  GW P σ.g ∧ 1 ≤ σ.r.acq P.top 0 ∧
    ((BitVec.setWidth 64 P.n1 = x2 ∧ ∃ A S : Res, ∃ t : Time, σ.r = A.op S ∧ (S.wr P.n1d).q = 1 ∧
        (S.wr P.n1d).X (1#128, t) ∧ (∀ p, (S.wr P.n1d).X p → p.2 ≤ t) ∧ t ≤ σ.vs.vrNew) ∨
      (∃ tr tw : Time, ∃ w : Msg, ∃ new : Val, tr ≠ tw ∧ σ.snap.mem.get? tr = some w ∧ w.loc = P.top ∧
        w.tid ≠ 0 ∧ σ.snap.mem.get? tw = some ⟨P.top, new, 1⟩))

/-- **The pusher at its start**: the node whole at its initial messages, more
than half of `top`. -/
def Pu0 (P : Params) (σ : State I) : Prop :=
  GW P σ.g ∧ (σ.r.wr P.n1d).q = 1 ∧ (σ.r.wr P.n1n).q = 1 ∧ 1 / 2 < (σ.r.wr P.top).q ∧
    ∀ p, (σ.r.wr P.n1d).X p → p.2 = 0

/-- **The pusher in its loop**: the node whole, `n1d`'s maximal write `(1, t)`
at or below `vwOld`, more than half of `top`. -/
def Pu (P : Params) (σ : State I) : Prop :=
  GW P σ.g ∧ (σ.r.wr P.n1d).q = 1 ∧ (σ.r.wr P.n1n).q = 1 ∧ 1 / 2 < (σ.r.wr P.top).q ∧
    ∃ t, (σ.r.wr P.n1d).X (1#128, t) ∧ (∀ p, (σ.r.wr P.n1d).X p → p.2 ≤ t) ∧ t ≤ σ.vs.vwOld

/-- **The pusher done**: more than half of `top`. -/
def Pd (P : Params) (σ : State I) : Prop := GW P σ.g ∧ 1 / 2 < (σ.r.wr P.top).q

theorem Pu.fence {P : Params} {σ σ' : State I} (h : Pu P σ) (hf : FenceLe σ σ') : Pu P σ' := by
  unfold Pu; rw [hf.g, hf.r, hf.vwOld]; exact h

theorem Pu0.fence {P : Params} {σ σ' : State I} (h : Pu0 P σ) (hf : FenceLe σ σ') : Pu0 P σ' := by
  unfold Pu0; rw [hf.g, hf.r]; exact h

theorem Pd.fence {P : Params} {σ σ' : State I} (h : Pd P σ) (hf : FenceLe σ σ') : Pd P σ' := by
  unfold Pd; rw [hf.g, hf.r]; exact h

theorem Pp.fence {P : Params} {σ σ' : State I} (h : Pp P σ) (hf : FenceLe σ σ') : Pp P σ' := by
  unfold Pp; rw [hf.g, hf.r, hf.snap, hf.getFwd]; exact h

theorem Pc.fence {P : Params} {x2 : BitVec 64} {σ σ' : State I} (h : Pc P x2 σ) (hf : FenceLe σ σ') :
    Pc P x2 σ' := by
  obtain ⟨hW, hacq, hb⟩ := h
  refine ⟨by rw [hf.g]; exact hW, by rw [hf.r]; exact hacq, ?_⟩
  rw [hf.r, hf.snap]
  exact hb.imp (fun ⟨hx, A, S, t, a, b, c, d, e⟩ => ⟨hx, A, S, t, a, b, c, d, Nat.le_trans e hf.vrNew⟩) id

/-! ## Plan lemmas -/

theorem popPlan_after_acq (P : Params) (hL : TLocs P) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    ((popPlan P).after P.top v tw cl r).acq P.top 0 = r.acq P.top 0 := by
  simp [Plan.after, Plan.keep, popPlan, Plan.find?, Plan.Entry.keep, Res.drop, hL.top_t]

theorem pushPlan_after_ne (P : Params) {x : Loc} (hx : x ≠ P.top) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (pushPlan P).after x v tw cl r = r.addW x (v, tw) := by
  unfold Plan.after
  rw [pushPlan_rel]
  simp [hx]

theorem pushPlan_after_q_top (P : Params) (hL : TLocs P) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (((pushPlan P).after P.top v tw cl r).wr P.top).q = (r.wr P.top).q := by
  unfold Plan.after
  rw [pushPlan_rel]
  by_cases hv : v = P.n1
  · subst hv
    simp only [decide_true, Bool.and_self, ↓reduceIte, Res.addW_q]
    simp [Plan.keep, pushPlan, Plan.find?, Plan.Entry.keep, Res.drop, hL.top_d, hL.top_n]
  · simp [hv]

theorem lt_op_left {a b : Perm} {x : Rat} (h : x < a.q) : x < (a.op b).q := by
  have := b.nonneg; show x < a.q + b.q; grind

/-! ## The popper's VCs -/

section Popper

variable {A : Arch}

/-- **VC of a popper load** (of `top`, of `next` at any address): `Pp` is
kept. -/
theorem vc_pop_load {P : Params} (σ : State I) (h : Pp P σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State I), (EnvGC I A 1 (popPlan P)).step (.load k xcl a n) σ v σ' → Pp P σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFacts (pl := popPlan P) hs
  obtain ⟨hW, hq, hpos, hacq, hfw, hi⟩ := h
  exact ⟨hW.mono hanc.ghost, hr ▸ hq, hr ▸ hpos, hr ▸ hacq, by rw [hlv.getFwd]; exact hfw,
    by rw [initVal_eq hanc.snap.init]; exact hi⟩

/-- **VC of the popper's compare-and-swap** on `top` (expected `x2 ≠ 0`, new
`x4`): permitted (a share of `top`, its plan's release of the token, `relTop`
at the popper's own message), and every outcome fails (`Pp` kept) or
succeeds (`Pc`). -/
theorem vc_pop_cas {P : Params} (hL : TLocs P) (σ : State I) (h : Pp P σ) (x2 x4 : BitVec 64) (hx2 : x2 ≠ 0)
    {op : Val → Option Val} (hop : CasMatch op x2 x4) :
    (EnvGC I A 1 (popPlan P)).ok (.rmw .acqRel P.top.addr P.top.bytes op) σ ∧
      ∀ old (σ' : State I), (EnvGC I A 1 (popPlan P)).step (.rmw .acqRel P.top.addr P.top.bytes op) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pp P σ') ∨ (BitVec.setWidth 64 old = x2 ∧ Pc P x2 σ') := by
  obtain ⟨hW, hq, hpos, hacq, hfw, hi⟩ := h
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  refine ⟨⟨hpos, fun c g tr old new hanc _ hon => ⟨fun hr => ?_, fun _ => ⟨rfl, ?_, ?_, fun _ _ => ?_⟩⟩⟩, ?_⟩
  · rw [e, popPlan_rel] at hr; simp at hr
  · rw [e, hW.rel_top]; exact relTop_not_pure P new
  · rw [e, popPlan_gives]; simp [hL.top_t]
  · rw [e, hW.rel_top, popPlan_give]
    refine ⟨Res.only [P.tok] σ.r, Res.unit, (Res.op_unit _).symm, ⟨fun _ => by simpa [Res.only] using hq, fun hp => ?_⟩,
      fun hp => ?_⟩
    · exact absurd (hp.2 _ (Memory.get?_append_last _ _)) (by simp)
    · exact absurd (hp.2 _ (Memory.get?_append_last _ _)) (by simp)
  intro old σ' hs
  obtain ⟨c, tr, hanc, hrd, hvle, -, -, -, -, hacqv, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨hon, hsnap, hr⟩ | ⟨new, tw, hon, htrw, -, hws, -, -, -, -, ⟨Pc', -, hr⟩, hun⟩
  · refine .inl ⟨hop.none _ hon, hW.mono hanc.ghost, hr ▸ hq, hr ▸ hpos, hr ▸ hacq,
      by rw [envGC_rmw_fail_getFwd hs hon]; exact hfw, ?_⟩
    rw [hsnap, initVal_eq hanc.snap.init]; exact hi
  obtain ⟨hx, rfl⟩ := hop.some _ _ hon
  refine .inr ⟨hx, hW.mono hanc.ghost, ?_, ?_⟩
  · rw [hr]
    show 1 ≤ ((popPlan P).after P.top _ tw Pc' σ.r).acq P.top 0 + _
    rw [popPlan_after_acq P hL]; omega
  have hW' := hW.mono hanc.ghost
  -- the message read is not the initial one
  have htr0 : tr ≠ 0 := by
    rintro rfl
    have h1 := hrd.val
    simp only [Memory.read?, ↓reduceIte, Option.some.injEq] at h1
    rw [initVal_eq hanc.snap.init, e, hi] at h1
    subst h1
    exact hx2 (by rw [← hx]; rfl)
  obtain ⟨w, hw, hwl, hwv⟩ := get?_of_read? htr0 hrd.val
  by_cases h0 : w.tid = 0
  · -- a pusher message: the claimed update slot carries the node
    left
    have hpm : PusherMsg c.mem tr := pusherMsg_of_get htr0 hw h0
    obtain ⟨rF, E'⟩ := hanc.erase
    have himp : ¬ Pred.Pure (σ'.g.rel P.top) old := by rw [hW'.rel_top]; exact relTop_not_pure P old
    have hrel : (P.top, tr) ∈ σ'.g.relMsgs :=
      Classical.byContradiction fun hn => himp (E'.pure P.top tr old (by rw [← e]; exact hrd.val) hn)
    obtain ⟨s, R, hid, hP, hprod⟩ := E'.claimedSlot hrel hun hW'.2.2 (by rw [← e]; exact hrd.val)
    rw [hW'.acqPred_one] at hP
    obtain ⟨hv, hnode⟩ := hP hpm
    obtain ⟨hq1, -, t, ht, hX, hmax⟩ := hnode
    have hle := (hacqv rfl (not_fwded_of_none hfw)).1
    refine ⟨by rw [← hx, hv], ((popPlan P).after P.top (BitVec.setWidth 128 x4) tw Pc' σ.r).op R, s.res, t, ?_,
      hq1, hX, hmax, Nat.le_trans ht hle⟩
    rw [hr, claimSlotsC_of_ok (.inl rfl), hprod, Res.op_comm s.res R, Res.op_assoc]
  · -- an other message: recorded for the next clean erasure
    right
    refine ⟨tr, tw, w, _, Nat.ne_of_lt htrw, WriteSnap.get?_old hws hw, by rw [hwl], h0, WriteSnap.get?_new hws⟩

/-- **VC of the popper's data load** (4 bytes at the node's address `x2`)
after a successful compare-and-swap: under the clean flag of the load,
`x2 = n1` and the value read is the node's data `1` (an other message is
refuted by `other_absurd`; a pusher message's node gives `n1d`'s maximal
write `(1, t)`, `t ≤ vrNew`, and `read_max` reads it). Any load kind. -/
theorem vc_pop_ldr {P : Params} (hd : P.n1d = ⟨BitVec.setWidth 64 P.n1, 4⟩) (σ : State I) (x2 : BitVec 64)
    (h : Pc P x2 σ) {k : LoadKind} :
    ∀ v (σ' : State I), (EnvGC I A 1 (popPlan P)).step (.load k false x2 4) σ v σ' →
      (σ'.cl → BitVec.setWidth 64 P.n1 = x2 ∧ BitVec.setWidth 32 v = 1) := by
  intro v σ' hs hc
  obtain ⟨hanc, -, hcl, tr, hrd, hlv, -⟩ := step_loadFacts (pl := popPlan P) hs
  rw [hcl] at hc
  obtain ⟨-, rF, E⟩ := hc
  obtain ⟨hW, hacq, hb⟩ := h
  rcases hb with ⟨hx, A, S, t, hrS, hq, hX, hmax, ht⟩ | ⟨tr', tw', w, new, hne, hw, hl, htid, hw'⟩
  · refine ⟨hx, ?_⟩
    subst hx
    have hl : ({ addr := BitVec.setWidth 64 P.n1, bytes := 4 } : Loc) = P.n1d := hd.symm
    rw [hl] at hrd
    have hv : σ.r.valid := Res.valid_op_left (Erase.valid_claim E hanc.lt P.n1d 0)
    have h1 := hv.1 P.n1d
    rw [hrS] at h1
    change (A.wr P.n1d).q + (S.wr P.n1d).q ≤ 1 at h1
    have hA0 : (A.wr P.n1d).q = 0 := by have := (A.wr P.n1d).nonneg; rw [hq] at h1; grind
    have hq' : (σ.r.wr P.n1d).q = 1 := by
      rw [hrS]; change (A.wr P.n1d).q + (S.wr P.n1d).q = 1; rw [hA0, hq]; grind
    have hX' : (σ.r.wr P.n1d).X (1#128, t) := by rw [hrS]; exact .inr hX
    have hmax' : ∀ p, (σ.r.wr P.n1d).X p → p.2 ≤ t := by
      rw [hrS]
      rintro p (hp | hp)
      · exact absurd hp ((A.wr P.n1d).zero hA0 p)
      · exact hmax p hp
    obtain ⟨th, hth⟩ : ∃ th, σ'.snap.threads[1]? = some th :=
      ⟨σ'.snap.threads[1]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
    have hp : th.prom.contains tr = false := by
      have := hrd.notOwn
      simp only [ownProm, hth, Option.map_some, Option.getD_some] at this
      exact this
    obtain ⟨-, rfl⟩ := read_max E hth hq' hX' hmax' hrd.val hp hrd.window
      (Nat.le_trans ht (le_readBound_vrNew _ _ _ _))
    decide
  · exact (other_absurd E hanc.lt (hW.mono hanc.ghost) hacq hne (get?_of_anchor hanc hw) hl htid
      (get?_of_anchor hanc hw')).elim

end Popper

/-! ## The pusher's VCs -/

section Pusher

variable {A : Arch}

/-- **VC of the pusher's data store** (`n1d := 1`, a plain store; its
effective kind is not non-temporal): permitted (pure, the node whole), and
the write `(1, tw)` is `n1d`'s maximal, `tw ≤ vwOld`. -/
theorem vc_push_str_d {P : Params} (hL : TLocs P) (hnt : A.storeKind .plain ≠ .nt) (σ : State I) (h : Pu0 P σ)
    (v : Val) (hv : v = 1#128) :
    (EnvGC I A 0 (pushPlan P)).ok (.store .plain false P.n1d.addr P.n1d.bytes v) σ ∧
      ∀ b (σ' : State I), (EnvGC I A 0 (pushPlan P)).step (.store .plain false P.n1d.addr P.n1d.bytes v) σ b σ' →
        Pu P σ' := by
  obtain ⟨hW, hqd, hqn, hqt, hX0⟩ := h
  have e : ({ addr := P.n1d.addr, bytes := P.n1d.bytes } : Loc) = P.n1d := rfl
  have hne : P.n1d ≠ P.top := Ne.symm hL.top_d
  refine ⟨⟨rfl, by rw [e, hqd]; decide, fun _ => by rw [e, hW.rel_ne hne]; exact Pred.emp_pure _,
    fun hr => by rw [e, pushPlan_rel] at hr; simp [hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := pushPlan P) hs
  rw [e, pushPlan_after_ne P hne] at hr
  refine ⟨hW.mono hanc.ghost, by rw [hr, Res.addW_q]; exact hqd,
    by rw [hr, Res.addW_wr_ne _ _ (Ne.symm hL.d_n)]; exact hqn,
    by rw [hr, Res.addW_wr_ne _ _ hL.top_d]; exact hqt, tw, ?_, ?_, hwv.vwOld hnt⟩
  · rw [hr, Res.addW_X_self, hv]; exact .inr ⟨by rw [hqd]; decide, rfl⟩
  · intro p hp
    rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rw [hX0 p hp]; exact Nat.zero_le _
    · exact Nat.le_refl _

/-- **VC of a pusher load** (of `top`): `Pu` is kept. -/
theorem vc_push_load {P : Params} (σ : State I) (h : Pu P σ) {k : LoadKind} {xcl : Bool} {a : BitVec 64} {n : Nat} :
    ∀ v (σ' : State I), (EnvGC I A 0 (pushPlan P)).step (.load k xcl a n) σ v σ' → Pu P σ' := by
  intro v σ' hs
  obtain ⟨hanc, hr, -, tr, -, hlv, -⟩ := step_loadFacts (pl := pushPlan P) hs
  obtain ⟨hW, hqd, hqn, hqt, t, hX, hmax, ht⟩ := h
  exact ⟨hW.mono hanc.ghost, hr ▸ hqd, hr ▸ hqn, hr ▸ hqt, t, hr ▸ hX, hr ▸ hmax,
    Nat.le_trans ht hlv.mono.vwOld⟩

/-- **VC of the pusher's link store** (`n1n :=` any value, a plain store):
permitted (pure, the node whole), `Pu` kept. -/
theorem vc_push_str_n {P : Params} (hL : TLocs P) (σ : State I) (h : Pu P σ) (v : Val) :
    (EnvGC I A 0 (pushPlan P)).ok (.store .plain false P.n1n.addr P.n1n.bytes v) σ ∧
      ∀ b (σ' : State I), (EnvGC I A 0 (pushPlan P)).step (.store .plain false P.n1n.addr P.n1n.bytes v) σ b σ' →
        Pu P σ' := by
  obtain ⟨hW, hqd, hqn, hqt, t, hX, hmax, ht⟩ := h
  have e : ({ addr := P.n1n.addr, bytes := P.n1n.bytes } : Loc) = P.n1n := rfl
  have hne : P.n1n ≠ P.top := Ne.symm hL.top_n
  refine ⟨⟨rfl, by rw [e, hqn]; decide, fun _ => by rw [e, hW.rel_ne hne]; exact Pred.emp_pure _,
    fun hr => by rw [e, pushPlan_rel] at hr; simp [hne] at hr⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, -, -, hwv, -, ⟨_, -, hr⟩, -, -⟩ := step_storeFacts (pl := pushPlan P) hs
  rw [e, pushPlan_after_ne P hne] at hr
  have hd : σ'.r.wr P.n1d = σ.r.wr P.n1d := by rw [hr, Res.addW_wr_ne _ _ hL.d_n]
  refine ⟨hW.mono hanc.ghost, by rw [hd]; exact hqd, by rw [hr, Res.addW_q]; exact hqn,
    by rw [hr, Res.addW_wr_ne _ _ hL.top_n]; exact hqt, t, by rw [hd]; exact hX, by rw [hd]; exact hmax,
    Nat.le_trans ht hwv.mono.vwOld⟩

/-- **VC of the pusher's compare-and-swap** on `top` (expected `x2`, new `x1`
the node's address `n1`): permitted (a share of `top`; the plan's release of
the node, whose `relTop` holds at the pusher's message: `predP` by the value
`n1`, `predU` by the node and `t ≤ vwOld < tw`), and every outcome fails (`Pu`
kept) or succeeds (`Pd`). -/
theorem vc_push_cas {P : Params} (hL : TLocs P) (σ : State I) (h : Pu P σ) (x2 x1 : BitVec 64)
    (hx1 : BitVec.setWidth 128 x1 = P.n1) {op : Val → Option Val} (hop : CasMatch op x2 x1) :
    (EnvGC I A 0 (pushPlan P)).ok (.rmw .acqRel P.top.addr P.top.bytes op) σ ∧
      ∀ old (σ' : State I), (EnvGC I A 0 (pushPlan P)).step (.rmw .acqRel P.top.addr P.top.bytes op) σ old σ' →
        (BitVec.setWidth 64 old ≠ x2 ∧ Pu P σ') ∨ (BitVec.setWidth 64 old = x2 ∧ Pd P σ') := by
  obtain ⟨hW, hqd, hqn, hqt, t, hX, hmax, ht⟩ := h
  have e : ({ addr := P.top.addr, bytes := P.top.bytes } : Loc) = P.top := rfl
  have hpos : 0 < (σ.r.wr P.top).q := by grind
  refine ⟨⟨hpos, fun c g tr old new hanc _ hon => ⟨fun hr => ?_, fun _ => ⟨rfl, ?_, ?_, fun _ hwb => ?_⟩⟩⟩, ?_⟩
  · obtain ⟨-, rfl⟩ := hop.some _ _ hon
    rw [e, pushPlan_rel] at hr; simp [hx1] at hr
  · rw [e, hW.rel_top]; exact relTop_not_pure P new
  · obtain ⟨-, rfl⟩ := hop.some _ _ hon
    rw [e, hx1, pushPlan_gives]; simp [hL.top_d, hL.top_n]
  · obtain ⟨-, rfl⟩ := hop.some _ _ hon
    rw [e, hW.rel_top, hx1, pushPlan_give]
    have hlt : t < c.mem.last + 1 := Nat.lt_of_le_of_lt ht
      (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) (hwb.rel rfl))
    refine ⟨Res.unit, Res.only [P.n1d, P.n1n] σ.r, (Res.unit_op _).symm,
      ⟨fun ho => absurd (ho.2 _ (Memory.get?_append_last _ _)) (by simp), fun _ => rfl⟩, fun _ => ⟨rfl, ?_⟩⟩
    refine ⟨by simpa [Res.only] using hqd, by simpa [Res.only] using hqn, t, Nat.le_of_lt hlt, ?_, ?_⟩
    · simpa [Res.only] using hX
    · simpa [Res.only] using hmax
  intro old σ' hs
  obtain ⟨c, tr, hanc, -, hvle, -, -, -, -, -, hbr⟩ := step_rmwFactsC hs
  rcases hbr with ⟨hon, -, hr⟩ | ⟨new, tw, hon, -, -, -, -, -, -, -, ⟨Pc', -, hr⟩, -⟩
  · exact .inl ⟨hop.none _ hon, hW.mono hanc.ghost, hr ▸ hqd, hr ▸ hqn, hr ▸ hqt, t, hr ▸ hX, hr ▸ hmax,
      Nat.le_trans ht hvle.vwOld⟩
  obtain ⟨hx, rfl⟩ := hop.some _ _ hon
  refine .inr ⟨hx, hW.mono hanc.ghost, ?_⟩
  rw [hr]
  exact lt_op_left (by rw [pushPlan_after_q_top P hL]; exact hqt)

end Pusher

end Kraken.Promising.SLR.EnvG.TreiberCommon
