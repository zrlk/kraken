/-
**Part 2: the ticket lock worker's VCs on the
ticket environment `EnvGTD`** (`EnvG/TicketEnv.lean`), under `Arch.armv8`.
ISA-neutral (the `vcgen` proof is `EnvG/TicketLockVCGen.lean`).

- `tkPlan P`: every write to `owner` is a release that gives all of the
  counter and the share `tkDelta` of `owner` (`CasSmoke.lockDelta`'s three
  cases: clean with a surplus above `1/N`, clean without, unclean half),
  `Plan.Split.shareD`.
- Invariants: `Start` (before `ldadda`), `Spin t` (the loop invariant, ticket
  `t`: an acquire id of `owner` whose predicate is usable at `t`, `OkT`, as
  `TakeMp.OkPred`), `Got t` (after the take: all of `C`, writes below
  `vrNew`/`vwNew`, `Good` or a surplus of `owner`), `Read t v` (after `ldr`:
  under the clean flag a surplus or `v = t`), `Stored t` (after `str`: the
  maximal counter write below `vwOld`, of value `t + 1` under the clean flag
  without a surplus), `QEnd` (under the clean flag: at least `1/N` of
  `owner`, `kLoc tid`, and the own `next` message matched by an `owner`
  message).
- VCs: `vc_ldadda` (the hand-out: ticket `t = old < N + 1`, its token, the
  own `next` message of value `t + 1`), `vc_ldar` (`TakeMp.vc_k1` with the
  surplus case), `vc_ldr`, `vc_str`, `vc_stlr` (the release obligation, as
  `CasSmoke.storeOk_lockRelease`, and what is kept, as `lockRelease_post`);
  `*.fence`.
- `EnvGTD`'s `FenceMono` instance and `simp` set (as `EnvG/TakeVCGenCommon.lean`
  for `EnvGT`; moved to `EnvG/TicketEnv.lean`); `rmwOut_getFwd_ne` (a
  successful RMW leaves the other locations' forwarding items alone; alias of
  the neutral `EnvG.rmwOut_getFwd_ne`).
-/
import Kraken.Promising.SLR.EnvG.TicketLockGhost
import Kraken.Promising.SLR.EnvG.TicketEnv
import Kraken.Promising.SLR.EnvG.TicketREnv
import Kraken.Promising.SLR.EnvG.TakeAllWr
import Kraken.Promising.SLR.EnvG.TakeVCGenCommon
import Kraken.Promising.SLR.EnvG.Seen
import Kraken.Promising.SLR.EnvG.SplitD
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.ReleaseStore
import Kraken.Promising.SLR.EnvG.LockVC
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.SpinCommon

variable {I : ISA}

/-- `omega` on `Time`/`View`/`PredId` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View, PredId] at *); omega))

/-! ## `EnvGTD`: fences and `simp`

`EnvGTD`'s `FenceMono` instance, `fenceMono_le_envGTD` and the
`envGTD_step_*'` simp lemmas are in `EnvG/TicketEnv.lean` (same
names, namespace `TicketLock`). -/

/- `rmwOut_getFwd_ne`: a successful or failed RMW leaves the other locations'
forwarding items alone (alias of the neutral
`EnvG.rmwOut_getFwd_ne`, `EnvG/LockVC.lean`). -/
hoist_alias [Kraken.Promising.SLR.EnvG.rmwOut_getFwd_ne ↦ Kraken.Promising.SLR.EnvG.TicketLock.rmwOut_getFwd_ne]

/-! ## The plan -/

open Classical in
/-- The share of `owner` a release gives. -/
noncomputable def tkDelta (P : Sys) (cl : Prop) (r : Res) : Rat :=
  if cl then (if 1 / (P.N : Rat) < (r.wr P.O).q ∧ 0 < 1 / (P.N : Rat) then (r.wr P.O).q - 1 / (P.N : Rat) else 0)
  else (r.wr P.O).q / 2

theorem tkDelta_lt (P : Sys) (cl : Prop) (r : Res) (hq : 0 < (r.wr P.O).q) : tkDelta P cl r < (r.wr P.O).q := by
  unfold tkDelta
  split
  · split
    · grind
    · exact hq
  · grind

theorem tkDelta_nonneg (P : Sys) (cl : Prop) (r : Res) : 0 ≤ tkDelta P cl r := by
  have := (r.wr P.O).nonneg
  unfold tkDelta; split
  · split <;> grind
  · grind

/-- **The ticket lock's plan**: every write to `owner` is a release giving
the counter and `tkDelta` of `owner`. -/
noncomputable def tkPlan (P : Sys) : Plan :=
  ⟨[{ loc := P.O, gives := [], split := some (Plan.Split.shareD P.O [P.C] (tkDelta P) (tkDelta_lt P)) }]⟩

theorem tkPlan_valid (P : Sys) : (tkPlan P).Valid := by
  intro e he
  simp only [tkPlan, List.mem_singleton] at he
  subst he
  exact List.not_mem_nil

theorem tkPlan_find (P : Sys) (v : Val) :
    (tkPlan P).find? P.O v = some { loc := P.O, gives := [], split := some (Plan.Split.shareD P.O [P.C] (tkDelta P) (tkDelta_lt P)) } := by
  simp [tkPlan, Plan.find?]

theorem tkPlan_rel_O (P : Sys) (v : Val) : (tkPlan P).rel P.O v = true := by
  rw [Plan.rel, tkPlan_find]; rfl

theorem tkPlan_rel_ne {P : Sys} {l : Loc} (h : l ≠ P.O) (v : Val) : (tkPlan P).rel l v = false := by
  simp [tkPlan, Plan.rel, Plan.find?, Ne.symm h]

theorem tkPlan_after_ne {P : Sys} {l : Loc} (h : l ≠ P.O) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (tkPlan P).after l v tw cl r = r.addW l (v, tw) := by
  simp only [Plan.after, tkPlan_rel_ne h, Bool.false_eq_true, ↓reduceIte]

theorem tkPlan_give (P : Sys) (v : Val) (cl : Prop) (r : Res) :
    (tkPlan P).give P.O v cl r = Res.shareGive [P.C] P.O (tkDelta P cl r) r := by
  rw [Plan.give, tkPlan_find]; rfl

theorem tkPlan_after_O (P : Sys) (v : Val) (tw : Time) (cl : Prop) (r : Res) :
    (tkPlan P).after P.O v tw cl r = (Res.shareKeepD [P.C] P.O (tkDelta P cl r) r).addW P.O (v, tw) := by
  simp only [Plan.after, tkPlan_rel_O, ↓reduceIte, Plan.keep, tkPlan_find]; rfl

theorem tkPlan_gives (P : Sys) (v : Val) : (tkPlan P).gives P.O v = [] := by
  rw [Plan.gives, tkPlan_find]; rfl

/-- The ticket lock's environment for thread `tid`. -/
noncomputable abbrev E (I : ISA) (P : Sys) (hL : Locs P) (tid : Nat) : SharedEnv :=
  EnvGTD I Arch.armv8 tid (tkPlan P) (disp P hL.xo)

/-! ## The world -/

/-- The world: above the initial ghost's release predicates and acquire
table. -/
def World (P : Sys) (g : Ghost) : Prop := (tkGhost default P).Le g

variable {P : Sys}

theorem World.of_init {m : Memory} {g : Ghost} (h : (tkGhost m P).Le g) : World P g := ⟨h.rel, h.acqTab, h.upd⟩

theorem World.rel_O {g : Ghost} (h : World P g) : g.rel P.O = relO P := by
  rw [h.rel]; exact tkGhost_rel_O

theorem World.rel_ne {g : Ghost} (h : World P g) {l : Loc} (hl : l ≠ P.O) : g.rel l = Pred.emp := by
  rw [h.rel]; exact tkGhost_rel_ne hl

theorem World.acqPred {g : Ghost} (h : World P g) {n : Nat} (hn : n < P.N + 1) :
    n < g.acqTab.length ∧ g.acqPred n = qPred P n := by
  have hlt : n < (tkGhost default P).acqTab.length := by rw [tkGhost_acqTab_length]; omega_t
  exact ⟨Nat.lt_of_lt_of_le hlt h.acqTab.length_le, by rw [Ghost.acqPred_of_prefix h.acqTab hlt, tkGhost_acqPred_q hn]⟩

theorem World.le {g g' : Ghost} (h : World P g) (h' : g.Le g') : World P g' := Ghost.Le.trans h h'

/-! ## The invariants -/

/-- The thread's own `next` message, of value `t + 1`, in `c`. -/
def NextMsg (P : Sys) (tid t : Nat) (c : Config I) : Prop :=
  ∃ tw w, c.mem.get? tw = some w ∧ w.loc = P.X ∧ w.tid = tid ∧ w.val.toNat = t + 1

theorem NextMsg.snap {tid t : Nat} {c c' : Config I} (h : NextMsg P tid t c) (hs : SnapLe tid c c') :
    NextMsg P tid t c' := by
  obtain ⟨tw, w, hw, h1⟩ := h
  exact ⟨tw, w, Memory.get?_of_prefix hs.msgs hw, h1⟩

theorem NextMsg.write {tid t : Nat} {c c' c'' : Config I} {l : Loc} {v : Val} {tw : Time} (h : NextMsg P tid t c)
    (hs : SnapLe tid c c') (hw : WriteSnap tid c' c'' l v tw) : NextMsg P tid t c'' := by
  obtain ⟨ts, w, hg, h1⟩ := h.snap hs
  exact ⟨ts, w, hw.get?_old' hg, h1⟩

/-- **A usable acquire predicate for ticket `t`**: at value `t` it gives
`CS t`, unless its timestamp is that of an `owner` message of another value
(where a spurious take relaxed it). -/
def OkT (P : Sys) (t : Nat) (c : Config I) (ψ : Pred) : Prop :=
  ∀ v m V R, ψ.P v m V R → lo v = t → CS P t V R ∨ ∃ v0, c.mem.read? P.O V = some v0 ∧ lo v0 ≠ t

theorem OkT.snap {t tid : Nat} {c c' : Config I} {ψ : Pred} (h : OkT P t c ψ) (hs : SnapLe tid c c') :
    OkT P t c' ψ := fun v m V R hP hv =>
  (h v m V R hP hv).imp id fun ⟨v0, hr, h0⟩ => ⟨v0, hs.read? hr, h0⟩

/-- The resources every invariant keeps: the world, at least `1/N` of
`owner`, all of `kLoc tid`. -/
def Keep (P : Sys) (tid : Nat) (σ : State I) : Prop :=
  World P σ.g ∧ 1 / (P.N : Rat) ≤ (σ.r.wr P.O).q ∧ 1 ≤ (σ.r.wr (kLoc tid)).q

/-- Before `ldadda`. -/
def Start (P : Sys) (tid : Nat) (σ : State I) : Prop :=
  Keep P tid σ ∧ 0 < (σ.r.wr P.X).q ∧ σ.vs.getCoh P.X = 0 ∧ σ.vs.getFwd P.X = none ∧ σ.vs.getFwd P.O = none

/-- **The loop invariant** (at `spin`), ticket `t`. -/
def Spin (P : Sys) (tid t : Nat) (σ : State I) : Prop :=
  Keep P tid σ ∧ t < P.N + 1 ∧ NextMsg P tid t σ.snap ∧ σ.vs.getFwd P.O = none ∧
    ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq P.O ι ∧ OkT P t σ.snap (σ.g.acqPred ι)

/-- The counter's maximal write has value `n`. -/
def Good (P : Sys) (n : Nat) (r : Res) : Prop :=
  ∃ val ts, (r.wr P.C).X (val, ts) ∧ val.toNat = n ∧ ∀ p, (r.wr P.C).X p → p.2 ≤ ts

/-- After the take: all of `C`, every write below `vrNew` and `vwNew`, `Good`
or a surplus. -/
def Got (P : Sys) (tid t : Nat) (σ : State I) : Prop :=
  Keep P tid σ ∧ t < P.N + 1 ∧ NextMsg P tid t σ.snap ∧ (σ.r.wr P.C).q = 1 ∧
    (∀ p, (σ.r.wr P.C).X p → p.2 ≤ σ.vs.vrNew ∧ p.2 ≤ σ.vs.vwNew) ∧
    (Good P t σ.r ∨ 1 / (P.N : Rat) < (σ.r.wr P.O).q)

/-- After `ldr` of `v`. -/
def Read (P : Sys) (tid t : Nat) (v : Val) (σ : State I) : Prop :=
  Got P tid t σ ∧ (σ.cl → 1 / (P.N : Rat) < (σ.r.wr P.O).q ∨ v.toNat = t)

/-- After `str`. -/
def Stored (P : Sys) (tid t : Nat) (σ : State I) : Prop :=
  Keep P tid σ ∧ t < P.N + 1 ∧ NextMsg P tid t σ.snap ∧ (σ.r.wr P.C).q = 1 ∧
    ∃ u tw, (σ.r.wr P.C).X (u, tw) ∧ (∀ p, (σ.r.wr P.C).X p → p.2 ≤ tw) ∧ tw ≤ σ.vs.vwOld ∧
      (σ.cl → ¬ 1 / (P.N : Rat) < (σ.r.wr P.O).q → u.toNat = t + 1)

/-- **At the end**: under the clean flag, at least `1/N` of `owner`, all of
`kLoc tid`, and the own `next` message matched by an `owner` message. -/
def QEnd (P : Sys) (tid : Nat) (σ : State I) : Prop :=
  World P σ.g ∧ (σ.cl → 1 / (P.N : Rat) ≤ (σ.r.wr P.O).q ∧ 1 ≤ (σ.r.wr (kLoc tid)).q ∧
    ∃ tw w, σ.snap.mem.get? tw = some w ∧ w.loc = P.X ∧ w.tid = tid ∧
      ∃ ts v, σ.snap.mem.read? P.O ts = some v ∧ lo v = w.val.toNat)

/-! ## Fences -/

section Fence

variable {tid t : Nat} {σ σ' : State I}

theorem Keep.fence (h : Keep P tid σ) (hf : FenceLe σ σ') : Keep P tid σ' := by
  unfold Keep; rw [hf.g, hf.r]; exact h

theorem Start.fence (h : Start P tid σ) (hf : FenceLe σ σ') : Start P tid σ' := by
  unfold Start; rw [hf.getCoh, hf.getFwd, hf.getFwd, hf.r]; exact ⟨h.1.fence hf, h.2⟩

theorem Spin.fence (h : Spin P tid t σ) (hf : FenceLe σ σ') : Spin P tid t σ' := by
  unfold Spin; rw [hf.getFwd, hf.snap, hf.g, hf.r]; exact ⟨h.1.fence hf, h.2⟩

theorem Got.fence (h : Got P tid t σ) (hf : FenceLe σ σ') : Got P tid t σ' := by
  obtain ⟨hk, h1, h2, h3, h4, h5⟩ := h
  refine ⟨hk.fence hf, h1, by rw [hf.snap]; exact h2, by rw [hf.r]; exact h3, fun p hp => ?_, by rw [hf.r]; exact h5⟩
  rw [hf.r] at hp
  exact ⟨Nat.le_trans (h4 p hp).1 hf.vrNew, Nat.le_trans (h4 p hp).2 hf.vwNew⟩

theorem Read.fence {v : Val} (h : Read P tid t v σ) (hf : FenceLe σ σ') : Read P tid t v σ' :=
  ⟨h.1.fence hf, by rw [hf.cl, hf.r]; exact h.2⟩

theorem Stored.fence (h : Stored P tid t σ) (hf : FenceLe σ σ') : Stored P tid t σ' := by
  unfold Stored; rw [hf.snap, hf.r, hf.cl, hf.vwOld]; exact ⟨h.1.fence hf, h.2⟩

theorem QEnd.fence (h : QEnd P tid σ) (hf : FenceLe σ σ') : QEnd P tid σ' := by
  unfold QEnd; rw [hf.g, hf.r, hf.cl, hf.snap]; exact h

end Fence

/-! ## Resource lemmas -/

theorem q_op_le (r s : Res) (x : Loc) : (r.wr x).q ≤ ((r.op s).wr x).q := Perm.le_op_left _ _

/- `takeAll_q_ge`, `takeAll_q_slot`: the take only adds to the resource
(aliases of the neutral `EnvG.takeAll_q_ge` / `EnvG.takeAll_q_slot`,
`EnvG/TakeAllWr.lean`). -/
hoist_alias [Kraken.Promising.SLR.EnvG.takeAll_q_ge ↦ Kraken.Promising.SLR.EnvG.TicketLock.takeAll_q_ge,
  Kraken.Promising.SLR.EnvG.takeAll_q_slot ↦ Kraken.Promising.SLR.EnvG.TicketLock.takeAll_q_slot]

/-! ## The start -/

/-- **`Start` at the initial environment state** (ISA-neutral form
of `TicketLock.start_init` and `TicketX.start_initX`): `1/N` of `next` and
`owner`, all of `kLoc tid`, the initial ghost, and the initial (zero)
views. -/
theorem start_initG {P' : Sys} (hL' : Locs P') (m : Memory) (tid : Nat) (snap : Config I) :
    Start P' tid ({ snap, vs := {}, r := thRes m P' tid, g := tkGhost m P', cl := True } : State I) := by
  have hXO := hL'.xo
  have hKX := kLoc_ne hL'.xb tid
  have hKO := kLoc_ne hL'.ob tid
  have hN : (0 : Rat) < 1 / (P'.N : Rat) := by
    have : (0 : Rat) < P'.N := by exact_mod_cast hL'.n0
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr this
  refine ⟨⟨World.of_init (Ghost.Le.refl _), ?_, ?_⟩, ?_, by simp [Views.getCoh], by simp [Views.getFwd],
    by simp [Views.getFwd]⟩ <;>
    simp only [thRes, Res.initOf, Perm.init, thFrac, hXO, Ne.symm hXO, hKX, hKO, Ne.symm hKX, Ne.symm hKO,
      ite_true, ite_false] <;> grind

/-! ## The VCs -/

variable (hL : Locs P) {tid : Nat}

include hL in
/-- **VC of the ticket RMW, of any acquiring kind, any architecture**
(generic form of `vc_ldaddK` and `TicketX.vcX_xadd`), in `EnvGTDR`
(`tkPlan` never releases at `next`): permitted at `Start`, and every outcome
is in `Spin` at the ticket read, below `N + 1`. -/
theorem vc_ldaddKA (A : Arch) {k : RmwKind} (hk : (A.loadKind (A.rmwKind k).loadKind).isAcquire = true)
    (σ : State I) (h : Start P tid σ) {op : Val → Option Val}
    (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).ok (.rmw k P.X.addr P.X.bytes op) σ ∧
      ∀ old (σ' : State I), (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).step (.rmw k P.X.addr P.X.bytes op)
        σ old σ' → Spin P tid old.toNat σ' := by
  obtain ⟨⟨hW, hO, hK⟩, hX, hcoh, hfx, hfo⟩ := h
  have hXO := hL.xo
  have hnew : ∀ x : Val, x.toNat < P.N + 1 → ((x.setWidth 32 + 1#32).setWidth 128 : Val).toNat = x.toNat + 1 := by
    intro x hx
    have := hL.n32
    simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := x.toNat) (by omega), Nat.mod_eq_of_lt (a := 1) (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨⟨hX, fun c g tr old new _ _ hon => ⟨fun _ => .inr ⟨hk, not_fwded_of_none hfx⟩,
      fun _ => by rw [hW.rel_ne hXO]; exact Pred.emp_pure _, fun hr => absurd hr (by rw [tkPlan_rel_ne hXO]; decide)⟩⟩,
    rfl, ⟨fun x => by rw [hop]; simp, fun x y hx hy => by rw [hop] at hy; cases hy; exact hnew x hx⟩,
    fun v => tkPlan_rel_ne hXO v, hcoh⟩, ?_⟩
  intro old σ' hs
  obtain ⟨σ₁, hout, hlt, rfl⟩ := hs
  have hfo' := rmwOut_getFwd_ne hout (Ne.symm hXO)
  obtain ⟨c, tr, hanc, -, -, -, -, -, -, -, hbr⟩ := rmwOut_facts hout
  rcases hbr with ⟨hn, -⟩ | ⟨new, tw, hon, -, -, hws, -, -, -, -, ⟨P', -, hr⟩, -⟩
  · rw [hop] at hn; cases hn
  simp only [disp] at hlt
  rw [hop] at hon; cases hon
  have hr' : σ₁.r = (σ.r.op (Res.prod ((claimedSlots σ₁.g P.X tr).map (·.res)))).addW P.X
      (((old.setWidth 32 + 1#32).setWidth 128 : Val), tw) := by
    rw [hr, Plan.afterRmw, tkPlan_after_ne hXO]
  have hq : ∀ x, (σ.r.wr x).q ≤ ((σ₁.r.op (tok P.O old.toNat)).wr x).q := fun x => by
    refine Rat.le_trans ?_ (q_op_le _ _ x)
    rw [hr', Res.addW_q]; exact q_op_le _ _ x
  have hW' := hW.le hanc.ghost
  obtain ⟨hlen, hpred⟩ := hW'.acqPred hlt
  refine ⟨⟨hW', Rat.le_trans hO (hq _), Rat.le_trans hK (hq _)⟩, hlt,
    ⟨tw, _, hws.get?_new', rfl, rfl, hnew old hlt⟩, by rw [hfo']; exact hfo, old.toNat, hlen, ?_, ?_⟩
  · show 1 ≤ σ₁.r.acq P.O old.toNat + (tok P.O (id old.toNat)).acq P.O old.toNat
    simp [tok]
  · rw [hpred]; exact fun v m V R hP hv => .inl (hP.1 hv)

include hL in
/-- **VC of the ticket RMW, of any acquiring kind** (generic form of
`vc_ldadda` and `TicketLock.vc_ldaddal`), in `EnvGTDR` (`tkPlan` never
releases at `next`): permitted at `Start`, and every outcome is in `Spin` at
the ticket read, below `N + 1`. `vc_ldaddKA` at `Arch.armv8`. -/
theorem vc_ldaddK {k : RmwKind} (hk : (Arch.armv8.loadKind (Arch.armv8.rmwKind k).loadKind).isAcquire = true)
    (σ : State I) (h : Start P tid σ) {op : Val → Option Val}
    (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (EnvGTDR I Arch.armv8 tid (tkPlan P) (disp P hL.xo)).ok (.rmw k P.X.addr P.X.bytes op) σ ∧
      ∀ old (σ' : State I), (EnvGTDR I Arch.armv8 tid (tkPlan P) (disp P hL.xo)).step (.rmw k P.X.addr P.X.bytes op)
        σ old σ' → Spin P tid old.toNat σ' :=
  vc_ldaddKA hL Arch.armv8 hk σ h hop

include hL in
/-- **VC `ldadda w6, w3, [x0]`** (the hand-out): permitted at `Start`, and
every outcome is in `Spin` at the ticket read, below `N + 1`. -/
theorem vc_ldadda (σ : State I) (h : Start P tid σ) {op : Val → Option Val}
    (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (E I P hL tid).ok (.rmw .acq P.X.addr P.X.bytes op) σ ∧
      ∀ old (σ' : State I), (E I P hL tid).step (.rmw .acq P.X.addr P.X.bytes op) σ old σ' →
        Spin P tid old.toNat σ' :=
  have h' := vc_ldaddK hL (k := .acq) (by decide) σ h hop
  ⟨⟨h'.1.1, h'.1.2.1, h'.1.2.2.1, by decide, h'.1.2.2.2.2⟩, h'.2⟩

include hL in
/-- **VC of the spin's acquiring load, any architecture** (generic
form of `vc_ldar` and `TicketX.vcX_spin`), in `EnvGTDR`: a value of another
low word keeps `Spin`, the ticket's value gives `Got`. -/
theorem vc_ldarA (A : Arch) {k : LoadKind} (hk : (A.loadKind k).isAcquire = true) {t : Nat} (σ : State I)
    (h : Spin P tid t σ) :
    ∀ v (σ' : State I), (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).step (.load k false P.O.addr P.O.bytes) σ v σ' →
      (lo v ≠ t → Spin P tid t σ') ∧ (lo v = t → Got P tid t σ') := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsTDR hs
  obtain ⟨⟨hW, hO, hK⟩, htl, hnx, hfw, ι, hlt, hacq1, hok⟩ := h
  have hn := hanc.lt
  have hacq : σ.r.acq P.O ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hc : TakeCond A k σ.vs P.O tr := ⟨hk, not_fwded_of_none hfw⟩
  have ha' : a = takeAll P.O tr σ.r ga := ha.1 hc
  have hW' : World P σ'.g := by rw [hg]; exact (hW.le hanc.ghost).le ha.ghost_le
  have hok' : OkT P t σ'.snap (ga.acqPred ι) := by rw [hanc.acqPred hlt]; exact hok.snap hanc.snap
  have hq : ∀ x, (σ.r.wr x).q ≤ (σ'.r.wr x).q := fun x => by rw [hr, ha']; exact takeAll_q_ge _ _ _ _ x
  have hkeep : Keep P tid σ' := ⟨hW', Rat.le_trans hO (hq _), Rat.le_trans hK (hq _)⟩
  have hnx' := hnx.snap hanc.snap
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · obtain ⟨ι', h1, h2, hp⟩ := takeAll_held (l := P.O) (tr := tr) (r := σ.r) (g := ga) hacq1 (hanc.acqLen hlt)
    refine ⟨hkeep, htl, hnx', by rw [hlv.getFwd]; exact hfw, ι', by rw [hg, ha']; exact h2, by rw [hr, ha']; exact h1, ?_⟩
    rw [hg, ha']
    rcases hp with hp | hp
    · rw [hp]; exact hok'
    · rw [hp]
      intro v' m V R hP hv'
      rcases hP with ⟨rfl, -⟩ | hP
      · exact .inr ⟨v, hrd.val, hv⟩
      · exact hok' v' m V R hP hv'
  · obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (P.O, tr)) E hn hacq hrd.val
      (by rw [hanc.rel, hW.rel_O]; exact relO_impure P v)
    obtain ⟨hq1, hle, hgb⟩ : CS P t tr s.res := by
      rcases hok' v _ tr s.res hP hv with hG | ⟨v0, hr0, h0⟩
      · exact hG
      · rw [hrd.val] at hr0; cases hr0; exact absurd hv h0
    obtain ⟨hq', hX'⟩ := takeAll_wr_full hn E hs hkey (by rw [hid]; exact hacq) hq1
    have hvw := hlv.acq hk (not_fwded_of_none hfw)
    refine ⟨hkeep, htl, hnx', by rw [hr, ha']; exact hq', fun p hp => ?_, ?_⟩
    · rw [hr, ha'] at hp
      have := hle p ((hX' p).mp hp)
      exact ⟨Nat.le_trans this hvw.1, Nat.le_trans this hvw.2⟩
    · rcases hgb with ⟨val, ts, hX, hval, hmax⟩ | hpos
      · refine .inl ⟨val, ts, ?_, hval, fun p hp => ?_⟩
        · rw [hr, ha']; exact (hX' _).mpr hX
        · rw [hr, ha'] at hp; exact hmax p ((hX' p).mp hp)
      · right
        have := takeAll_q_slot E hs hkey (by rw [hid]; exact hacq) P.O
        rw [hr, ha']; grind

include hL in
/-- **VC `ldar w4, [x1]`** (the spin's acquire load): a value of another low
word keeps `Spin`, the ticket's value gives `Got`. `vc_ldarA` at `Arch.armv8`, `.acq`. -/
theorem vc_ldar {t : Nat} (σ : State I) (h : Spin P tid t σ) :
    ∀ v (σ' : State I), (E I P hL tid).step (.load .acq false P.O.addr P.O.bytes) σ v σ' →
      (lo v ≠ t → Spin P tid t σ') ∧ (lo v = t → Got P tid t σ') :=
  vc_ldarA hL Arch.armv8 (k := .acq) (by decide) σ h

include hL in
/-- **VC of the plain counter load, any architecture** (generic
form of `vc_ldr` and `TicketX.vcX_ldc`), in `EnvGTDR`: the load may take
(`Arch.tso`) or not (`Arch.armv8`); the full counter is kept
(`takeEff_wr_fullG`); under the clean flag the value read is the ticket, or
there is a surplus. -/
theorem vc_ldrA (A : Arch) {t : Nat} (σ : State I) (h : Got P tid t σ) :
    ∀ v (σ' : State I), (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).step (.load .plain false P.C.addr P.C.bytes) σ v σ' →
      Read P tid t v σ' := by
  intro v σ' hs
  obtain ⟨ga, hanc, ⟨rF₀, E₀⟩, hcl, tr, hrd, hlv, a, ha, hr, hg, -⟩ := step_loadFactsTDR hs
  obtain ⟨⟨hW, hO, hK⟩, htl, hnx, hq, hle, hgb⟩ := h
  obtain ⟨hq', hX'⟩ := takeEff_wr_fullG hanc.lt E₀ ha hq
  have hqa : ∀ x, (σ.r.wr x).q ≤ (σ'.r.wr x).q := fun x => by rw [hr]; exact takeEff_q_ge ha x
  have hgb' : Good P t σ'.r ∨ 1 / (P.N : Rat) < (σ'.r.wr P.O).q := by
    rcases hgb with ⟨val, ts, hX, hval, hmax⟩ | hs
    · exact .inl ⟨val, ts, by rw [hr, hX']; exact hX, hval, fun p hp => hmax p (by rw [hr, hX'] at hp; exact hp)⟩
    · exact .inr (Std.lt_of_lt_of_le hs (hqa _))
  refine ⟨⟨⟨by rw [hg]; exact (hW.le hanc.ghost).le ha.ghost_le, Rat.le_trans hO (hqa _), Rat.le_trans hK (hqa _)⟩,
    htl, hnx.snap hanc.snap, by rw [hr]; exact hq', fun p hp => ?_, hgb'⟩, fun hc => ?_⟩
  · rw [hr, hX'] at hp
    exact ⟨Nat.le_trans (hle p hp).1 hlv.mono.vrNew, Nat.le_trans (hle p hp).2 hlv.mono.vwNew⟩
  rcases hgb with ⟨val, ts, hX, hval, hmax⟩ | hs
  · right
    rw [hcl] at hc
    obtain ⟨-, rF, E'⟩ := hc
    obtain ⟨t', ht⟩ : ∃ t', σ'.snap.threads[tid]? = some t' :=
      ⟨σ'.snap.threads[tid]'hanc.lt, Array.getElem?_eq_getElem hanc.lt⟩
    have hp : t'.prom.contains tr = false := by
      have := hrd.notOwn
      simp only [ownProm, ht, Option.map_some, Option.getD_some] at this
      exact this
    have hts : ts ≤ readBound A σ.vs .plain P.C :=
      Nat.le_trans (hle _ hX).1 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    rw [(read_max E' ht hq hX hmax hrd.val hp hrd.window hts).2, hval]
  · exact .inl (Std.lt_of_lt_of_le hs (hqa _))

include hL in
/-- **VC `ldr w5, [x2]`** (the counter, plain): nothing is taken; under the
clean flag the value read is the ticket, or there is a surplus. `vc_ldrA` at `Arch.armv8`. -/
theorem vc_ldr {t : Nat} (σ : State I) (h : Got P tid t σ) :
    ∀ v (σ' : State I), (E I P hL tid).step (.load .plain false P.C.addr P.C.bytes) σ v σ' → Read P tid t v σ' :=
  vc_ldrA hL Arch.armv8 σ h

include hL in
/-- **VC of the plain counter store, any architecture** (generic
form of `vc_str` and `TicketX.vcX_stc`), in `EnvGTDR`, for a plain store
that is not non-temporal (`hnt`): permitted, and afterwards `Stored`. -/
theorem vc_strA (A : Arch) (hnt : A.storeKind .plain ≠ .nt) {t : Nat} {v u : Val} (σ : State I)
    (h : Read P tid t v σ) (hu : v.toNat = t → u.toNat = t + 1) :
    (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).ok (.store .plain false P.C.addr P.C.bytes u) σ ∧
      ∀ b (σ' : State I), (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).step (.store .plain false P.C.addr P.C.bytes u) σ b σ' →
        Stored P tid t σ' := by
  have hOC := hL.oc
  obtain ⟨⟨⟨hW, hO, hK⟩, htl, hnx, hq, hle, -⟩, hrd⟩ := h
  refine ⟨⟨⟨rfl, by rw [hq]; decide, fun _ => by rw [hW.rel_ne (Ne.symm hOC)]; exact Pred.emp_pure _,
    fun hr => absurd hr (by rw [tkPlan_rel_ne (Ne.symm hOC)]; decide)⟩, fun h => hL.xc h.symm⟩, ?_⟩
  intro b σ' hs
  obtain ⟨c, tw, hanc, hws, hwb, hwv, -, ⟨P', -, hr⟩, hcl, -⟩ := step_storeFactsTDR hs
  rw [tkPlan_after_ne (Ne.symm hOC)] at hr
  refine ⟨⟨hW.le hanc.ghost, by rw [hr, Res.addW_q]; exact hO, by rw [hr, Res.addW_q]; exact hK⟩, htl,
    hnx.write hanc.snap hws, by rw [hr, Res.addW_q]; exact hq, u, tw, ?_, fun p hp => ?_, hwv.vwOld hnt,
    fun hc hs' => ?_⟩
  · rw [hr, Res.addW_X_self, hq]; exact .inr ⟨by decide, rfl⟩
  · rw [hr, Res.addW_X_self] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hle p hp).2 hwb.vwNew)
    · exact Nat.le_refl _
  · rw [hcl] at hc
    rw [hr, Res.addW_q] at hs'
    exact hu ((hrd hc).resolve_left hs')

include hL in
/-- **VC `str w5, [x2]`** (the counter, plain): permitted, and afterwards the
maximal write is the stored `u`, at or below `vwOld`, of value `t + 1` under
the clean flag without a surplus (`hu`: the stored value is the loaded one
plus one). `vc_strA` at `Arch.armv8`. -/
theorem vc_str {t : Nat} {v u : Val} (σ : State I) (h : Read P tid t v σ) (hu : v.toNat = t → u.toNat = t + 1) :
    (E I P hL tid).ok (.store .plain false P.C.addr P.C.bytes u) σ ∧
      ∀ b (σ' : State I), (E I P hL tid).step (.store .plain false P.C.addr P.C.bytes u) σ b σ' →
        Stored P tid t σ' :=
  vc_strA hL Arch.armv8 (by decide) σ h hu

include hL in
/-- **VC of the release of `owner`, any architecture** (generic
form of `vc_stlr` and `TicketX.vcX_rel`), in `EnvGTDR`, for a store of a
release kind (`hk`): permitted (`CS (t + 1)`), and afterwards `QEnd`. -/
theorem vc_stlrA (A : Arch) {k : StoreKind} (hk : A.storeKind k = .rel) {t : Nat} {u4 : Val} (σ : State I)
    (h : Stored P tid t σ) (hu4 : lo u4 = t + 1) :
    (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).ok (.store k false P.O.addr P.O.bytes u4) σ ∧
      ∀ b (σ' : State I), (EnvGTDR I A tid (tkPlan P) (disp P hL.xo)).step (.store k false P.O.addr P.O.bytes u4) σ b σ' →
        QEnd P tid σ' := by
  have hOC := hL.oc
  have hN0 := hL.n0
  have hN : (0 : Rat) < 1 / (P.N : Rat) := by
    have : (0 : Rat) < P.N := by exact_mod_cast hN0
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr this
  obtain ⟨⟨hW, hO, hK⟩, -, hnx, hq, u, tw, hX, hmax, htw, hgood⟩ := h
  have hpos : 0 < (σ.r.wr P.O).q := Std.lt_of_lt_of_le hN hO
  refine ⟨⟨⟨rfl, hpos, fun h => absurd (tkPlan_rel_O P u4) (by rw [h]; decide),
    fun _ => ⟨.inl hk, by rw [hW.rel_O]; exact relO_impure P u4, by rw [tkPlan_gives]; exact List.not_mem_nil, ?_⟩⟩,
    fun h => hL.xo h.symm⟩, ?_⟩
  · intro c g _ hwb
    rw [hW.rel_O, tkPlan_give]
    show CS P (lo u4) _ _
    have hCw : (Res.shareGive [P.C] P.O (tkDelta P σ.cl σ.r) σ.r).wr P.C = σ.r.wr P.C :=
      Res.shareGive_wr_ne (Ne.symm hOC) (List.mem_singleton_self _)
    have hrel := hwb.rel hk
    have htw' : tw < c.mem.last + 1 := by simp only [Time, View] at *; omega
    refine ⟨by rw [hCw]; exact hq, fun p hp => ?_, ?_⟩
    · rw [hCw] at hp; exact Nat.le_of_lt (Nat.lt_of_le_of_lt (hmax p hp) htw')
    have hbad : 0 < tkDelta P σ.cl σ.r →
        0 < ((Res.shareGive [P.C] P.O (tkDelta P σ.cl σ.r) σ.r).wr P.O).q := fun h0 => by
      rw [Res.shareGive_wr_self, Perm.take_q_of _ (tkDelta_nonneg _ _ _) (Rat.le_of_lt (tkDelta_lt P _ _ hpos))]
      exact h0
    by_cases hcl : σ.cl
    · by_cases hs : 1 / (P.N : Rat) < (σ.r.wr P.O).q
      · right; apply hbad
        simp only [tkDelta, hcl, hs, hN, and_self, ↓reduceIte]; grind
      · left
        rw [hCw, hu4]
        exact ⟨u, tw, hX, hgood hcl hs, hmax⟩
    · right; apply hbad
      simp only [tkDelta, hcl, ↓reduceIte]; grind
  · intro b σ' hs
    obtain ⟨c, tw', hanc, hws, -, -, -, ⟨P', hP', hr⟩, hcl, -⟩ := step_storeFactsTDR hs
    rw [tkPlan_after_O] at hr
    refine ⟨hW.le hanc.ghost, fun hc => ?_⟩
    rw [hcl] at hc
    have hPc := hP' hc
    have hKO : kLoc tid ≠ P.O := kLoc_ne hL.ob tid
    have hKC : kLoc tid ∉ [P.C] := by simp [kLoc_ne hL.cb tid]
    have hδ : tkDelta P P' σ.r = if 1 / (P.N : Rat) < (σ.r.wr P.O).q then (σ.r.wr P.O).q - 1 / (P.N : Rat) else 0 := by
      simp only [tkDelta, hPc, hN, and_true, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩
    · rw [hr, Res.addW_q]
      simp only [Res.shareKeepD, ↓reduceIte, Perm.leaveD, Perm.clampQ]
      rw [hδ]; split <;> grind
    · rw [hr, Res.addW_wr_ne _ _ hKO]
      simp only [Res.shareKeepD, hKO, hKC, ↓reduceIte]
      exact hK
    · obtain ⟨ts, w, hg, hl, ht, hv⟩ := hnx.write hanc.snap hws
      refine ⟨ts, w, hg, hl, ht, tw', u4, ?_, by rw [hu4, hv]⟩
      exact read?_of_get?' hws.get?_new'

include hL in
/-- **VC `stlr w4, [x1]`** (the release of `u4`, low word `t + 1`):
permitted (`CS (t + 1)`: the counter, `Good` in clean mode without a surplus,
a share of `owner` otherwise), and afterwards `QEnd`. `vc_stlrA` at `Arch.armv8`, `.rel`. -/
theorem vc_stlr {t : Nat} {u4 : Val} (σ : State I) (h : Stored P tid t σ) (hu4 : lo u4 = t + 1) :
    (E I P hL tid).ok (.store .rel false P.O.addr P.O.bytes u4) σ ∧
      ∀ b (σ' : State I), (E I P hL tid).step (.store .rel false P.O.addr P.O.bytes u4) σ b σ' → QEnd P tid σ' :=
  vc_stlrA hL Arch.armv8 rfl σ h hu4

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_ldadda
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_ldar
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_ldr
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_str
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_stlr
