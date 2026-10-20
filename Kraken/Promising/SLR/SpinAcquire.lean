/-
The ISA-neutral facts behind an acquiring RMW on the spinlock's lock word
(the AArch64 `swpa` and the x64 `xchgl` cells), over `SpinCommon.Sys`.
Originally restated from `SLR/SwpAcquire.lean` and `SLR/SwpCells.lean`
(stated there over the AArch64 `SwpInv.Params`, in files importing the
AArch64 syntax, which cannot be imported next to the x64 syntax); those
copies are gone: the AArch64 files use these at `SwpInv.Params.sys`.

- views: a fence-optional RMW and a write keep the forwarding items of other
  locations and `vrNew`; an exclusive write leaves an exclusive forwarding
  item; an acquire read not forwarded from a non-exclusive write raises
  `vrNew` and `vwNew` to the timestamp read (`readSuccs_acq_le`);
- claims: claiming keeps `mayWrite` (`mayWrite_claim`); reading a zero low
  word from the lock claims `Good` or `Bad` (`World.lock_claim'`);
- holding: a `Fresh` thread claiming the pool is `Holding`
  (`holding_of_pool`), with the counter relation under `Good`
  (`counterGood_of_good`).
-/
import Kraken.Promising.SLR.SpinClaim
import Kraken.Promising.SLR.RmwPendClaim
import Kraken.Promising.SLR.RuleShapes

namespace Kraken.Promising.SLR.SpinCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.Spinlock

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))
/-! ## Views of an acquire swap -/

section Views

variable {A : Arch} {tid : Nat} {iv : InstrViews}

theorem fenceOptCtx_getFwd (cx : Ctx) (l : Loc) : (fenceOptCtx A cx).views.getFwd l = cx.views.getFwd l := by
  unfold fenceOptCtx; split
  · rfl
  · rfl

theorem fenceOptCtx_vrNew (cx : Ctx) : cx.views.vrNew ≤ (fenceOptCtx A cx).views.vrNew := by
  unfold fenceOptCtx; split
  · simp only [fenceStep]; exact Nat.le_max_left _ _
  · exact Nat.le_refl _

theorem rmwAfter_getFwd (k : RmwKind) (noRet : Bool) (l l' : Loc) (cx : Ctx) :
    (rmwAfter A k noRet l cx).views.getFwd l' = cx.views.getFwd l' := by
  unfold rmwAfter rmwPost
  split <;> split <;> rfl

theorem rmwAfter_getCoh (k : RmwKind) (noRet : Bool) (l l' : Loc) (cx : Ctx) :
    (rmwAfter A k noRet l cx).views.getCoh l' = cx.views.getCoh l' := by
  unfold rmwAfter rmwPost
  split <;> split <;> rfl

theorem rmwAfter_vrNew (k : RmwKind) (noRet : Bool) (l : Loc) (cx : Ctx) :
    cx.views.vrNew ≤ (rmwAfter A k noRet l cx).views.vrNew := by
  unfold rmwAfter rmwPost
  split <;> split <;> simp only [fenceStep] <;> omega_t

/-- A write leaves `vrNew` alone. -/
theorem writeSuccs_vrNew {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra) : cx'.views.vrNew = cx.views.vrNew := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;> rfl

/-- An exclusive write to `l` leaves an exclusive forwarding item for `l`. -/
theorem writeSuccs_getFwd_xcl {xr : View} {cx cx' : Ctx} {k : StoreKind} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (hc : cx' ∈ writeSuccs A tid iv cx k true l v tr extra xr) :
    ∀ f, cx'.views.getFwd l = some f → f.xcl = true := by
  rcases (mem_writeSuccs A tid).mp hc with ⟨-, -, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
  · intro f hf
    rw [afterWrite_getFwd] at hf
    simp only [↓reduceIte, Option.some.injEq] at hf
    rw [← hf]

/-- A write of `l := v` leaves its forwarding item at the write's message, at or
below `coh l`. -/
theorem writeSuccs_getFwd_msg {xr : View} {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (hc : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra xr) :
    ∀ f, cx'.views.getFwd l = some f → cx'.mem.get? f.time = some ⟨l, v, tid⟩ ∧ f.time ≤ cx'.views.getCoh l := by
  intro f hf
  rcases (mem_writeSuccs A tid).mp hc with ⟨t, -, w, hw, hl, hv, ht, -, rfl⟩ | ⟨-, rfl⟩ <;>
    rw [afterWrite_getFwd] at hf <;> simp only [↓reduceIte, Option.some.injEq] at hf <;> subst hf <;>
    refine ⟨?_, by rw [afterWrite_getCoh]; simp only [↓reduceIte]; omega_t⟩
  · show cx.mem.get? t = _
    rw [hw]; cases w; simp_all
  · exact Memory.get?_append_last _ _

/-- **An acquire read not forwarded from a non-exclusive write** raises
`vrNew` and `vwNew` to the timestamp read, when every forwarding item of `l`
is exclusive and the architecture forwards exclusive writes to plain loads
only (`Arch.fwdXclOnlyPlain`; on `Arch.armv8` an acquire read may forward
from the thread's own exclusive write and is then ordered only after that
write's read). -/
theorem readSuccs_acq_le {cx : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet) (hk : (A.loadKind k).isAcquire = true)
    (hpl : (A.loadKind k == .plain) = false)
    (hfw : ∀ f, cx.views.getFwd l = some f → f.time = x.1 → f.xcl = true ∧ A.fwdXclOnlyPlain = true) :
    x.1 ≤ x.2.2.views.vrNew ∧ x.1 ≤ x.2.2.views.vwNew := by
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  have hrv : t ≤ readView A (A.loadKind k) (cx.views.getFwd l) t := by
    unfold readView
    split
    · rename_i f hf
      by_cases ht : f.time = t
      · simp only [(hfw f hf ht).1, (hfw f hf ht).2, hpl, Bool.not_true, Bool.or_false, Bool.and_false,
          Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_refl _
      · simp only [ht, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact Nat.le_refl _
    · exact Nat.le_refl _
  simp only [readNext, hk, ↓reduceIte]
  constructor <;> omega_t

/-- `fenceOptCtx` keeps `coh`. -/
theorem fenceOptCtx_getCoh (cx : Ctx) (l : Loc) : (fenceOptCtx A cx).views.getCoh l = cx.views.getCoh l := by
  unfold fenceOptCtx; split
  · rfl
  · rfl

/-- A read of `l` does not read at `lo` when a write of `l` is in `(lo, coh l]`
(so neither does it take the forwarding view of an item at `lo`). -/
theorem readSuccs_ne_of_writeIn {cx : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet) {lo : Time}
    (hw : cx.mem.writeIn l lo (cx.views.getCoh l) = true) : x.1 ≠ lo := by
  obtain ⟨t, v, rfl, -, -, hwin, -⟩ := (mem_readSuccs A).mp hx
  intro h
  obtain rfl : t = lo := h
  obtain ⟨p, w, h1, h2, h3, h4⟩ := (Memory.writeIn_iff _ _ _ _).mp hw
  have := (Memory.writeIn_iff _ _ _ _).mpr ⟨p, w, h1, Nat.le_trans h2 (Nat.le_max_right (readPre A iv cx k) _), h3, h4⟩
  rw [hwin] at this; cases this

/-- **A read of `l` of a value other than that of the write `w` of `l` at
`lo ≤ coh l`**, with every forwarding item of `l` at `lo`: it reads above `lo`
(the window `(t, coh l]` holds no write of `l`), not forwarded, so afterwards
a write of `l` is in `(lo, coh l]`. -/
theorem readSuccs_writeIn_of_ne {cx : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv cx k xcl l noRet) {lo : Time} {w : Msg}
    (hlo : lo ≤ cx.views.getCoh l) (hw : cx.mem.get? lo = some w) (hwl : w.loc = l) (hv : x.2.1 ≠ w.val)
    (hfw : ∀ f, cx.views.getFwd l = some f → f.time = lo) :
    cx.mem.writeIn l lo (x.2.2.views.getCoh l) = true := by
  obtain ⟨t, v, rfl, -, hrd, hwin, -⟩ := (mem_readSuccs A).mp hx
  have h0 : lo ≠ 0 := by rintro rfl; simp [Memory.get?] at hw
  have hne : t ≠ lo := by
    rintro rfl
    simp only [Memory.read?, h0, ↓reduceIte, hw, hwl, beq_self_eq_true, Option.some.injEq] at hrd
    exact hv hrd.symm
  have hlt : lo < t := by
    refine Nat.lt_of_le_of_ne (Nat.le_of_not_lt fun h => ?_) (Ne.symm hne)
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨lo, w, h, Nat.le_trans hlo (Nat.le_max_right (readPre A iv cx k) _), hw, hwl⟩
    rw [hwin] at this; cases this
  obtain ⟨w', hw', hwl'⟩ : ∃ w', cx.mem.get? t = some w' ∧ w'.loc = l := by
    simp only [Memory.read?, Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le lo) hlt), ↓reduceIte] at hrd
    split at hrd
    · rename_i w' hw'
      refine ⟨w', hw', ?_⟩
      split at hrd
      · simpa using ‹(w'.loc == l) = true›
      · cases hrd
    · cases hrd
  have hrv : t ≤ readView A (A.loadKind k) (cx.views.getFwd l) t := by
    unfold readView
    split
    · rename_i f hf
      simp only [show f.time ≠ t from (hfw f hf).symm ▸ Ne.symm hne, decide_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte]
      exact Nat.le_refl _
    · exact Nat.le_refl _
  refine (Memory.writeIn_iff _ _ _ _).mpr ⟨t, w', hlt, ?_, hw', hwl'⟩
  show t ≤ (cx.views.setCoh l (max (readPre A iv cx k) (readView A (A.loadKind k) (cx.views.getFwd l) t))).getCoh l
  simp only [Views.getCoh_setCoh, ↓reduceIte]
  omega_t

/-- A read only raises `coh`. -/
theorem readSuccs_getCoh_le (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) {l' : Loc} :
    c.views.getCoh l' ≤ x.2.2.views.getCoh l' := by
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  exact Views.getCoh_le_setCoh _ _ _ _

/-- A read leaves the forwarding items alone. -/
theorem readSuccs_fwdb (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    x.2.2.views.fwdb = c.views.fwdb := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · by_cases hp : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
        (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
        c.prom.contains t) = true
    · rw [ite_eq_left hp] at ht; cases ht
    · rw [ite_eq_right hp] at ht
      simp only [Option.some.injEq] at ht
      subst ht
      rfl


end Views

/-! ## What a claim gives and keeps -/

section Claim

/-- A positive fraction of a product comes from a component. -/
theorem pos_prod_exists {rs : List Res} {x : Loc} (h : 0 < ((Res.prod rs).wr x).q) :
    ∃ r ∈ rs, 0 < (r.wr x).q := by
  induction rs with
  | nil => simp [Res.unit, Perm.unit] at h
  | cons s rs ih =>
    rw [Res.prod_cons, Res.pos_op] at h
    rcases h with h | h
    · exact ⟨s, List.mem_cons_self .., h⟩
    · obtain ⟨r, hr, h⟩ := ih h
      exact ⟨r, List.mem_cons_of_mem _ hr, h⟩

/-- An acquire id of a product comes from a component. -/
theorem acq_prod_exists {rs : List Res} {x : Loc} {ι : PredId} (h : 1 ≤ (Res.prod rs).acq x ι) :
    ∃ r ∈ rs, 1 ≤ r.acq x ι := by
  induction rs with
  | nil => simp [Res.unit] at h
  | cons s rs ih =>
    rw [Res.prod_cons] at h
    change 1 ≤ s.acq x ι + (Res.prod rs).acq x ι at h
    by_cases hs : 1 ≤ s.acq x ι
    · exact ⟨s, List.mem_cons_self .., hs⟩
    · obtain ⟨r, hr, h⟩ := ih (by omega)
      exact ⟨r, List.mem_cons_of_mem _ hr, h⟩

theorem mem_claimedSlots {g : Ghost} {x : Loc} {tr : Time} {s : Slot} (h : s ∈ claimedSlots g x tr) :
    s ∈ g.u ∧ s.id ∈ g.upd s.key.1 := by
  unfold claimedSlots at h
  obtain ⟨hs, hu⟩ := List.mem_filter.mp h
  simp only [updSlot, decide_eq_true_eq] at hu
  exact ⟨hs, by rw [hu.1]; exact hu.2⟩

/-- **Claiming keeps `mayWrite` within the old one**: the claimed slots are
update slots, acquirable by everyone (`CanAcq.upd`), so what the thread
gains from them it could already acquire. -/
theorem mayWrite_claim {r : Res} {g : Ghost} {x : Loc} {tr tw : Time} {p : Val × Time} {y : Loc}
    (h : mayWrite ((r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p)
      (rmwGhost g x tr tw false []) y) :
    mayWrite r g y := by
  have hu : ∀ s ∈ (rmwGhost g x tr tw false []).u, s ∈ g.u := by
    intro s hs
    rcases mem_rmw_u.mp hs with ⟨hs, -⟩ | hs
    · exact hs
    · cases hs
  have hacq : ∀ {k : Key} {ι : PredId}, CanAcq (rmwGhost g x tr tw false []).u g.upd
      ((r.op (Res.prod ((claimedSlots g x tr).map (·.res)))).addW x p).acq k ι → CanAcq g.u g.upd r.acq k ι := by
    intro k ι hc
    induction hc with
    | base hs ha =>
      rename_i s
      change 1 ≤ r.acq s.key.1 s.id + (Res.prod ((claimedSlots g x tr).map (·.res))).acq s.key.1 s.id at ha
      by_cases hr : 1 ≤ r.acq s.key.1 s.id
      · exact .base (hu _ hs) hr
      · obtain ⟨_, hm, h1⟩ := acq_prod_exists
          (show 1 ≤ (Res.prod ((claimedSlots g x tr).map (·.res))).acq s.key.1 s.id by omega)
        obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hm
        obtain ⟨hs0u, hs0i⟩ := mem_claimedSlots hs0
        exact .step (.upd hs0u hs0i) hs0u (hu _ hs) h1
    | upd hs hi => exact .upd (hu _ hs) hi
    | step _ hs hs' ha ih => exact .step ih (hu _ hs) (hu _ hs') ha
  rcases h with h | ⟨s, hs, hc, hq⟩
  · rw [Res.addW_q, Res.pos_op] at h
    rcases h with h | h
    · exact .inl h
    · obtain ⟨_, hm, h1⟩ := pos_prod_exists h
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hm
      obtain ⟨hs0u, hs0i⟩ := mem_claimedSlots hs0
      exact .inr ⟨s0, hs0u, .upd hs0u hs0i, h1⟩
  · exact .inr ⟨s, hu s hs, hacq hc, hq⟩

/-- `lockPred` is not pure at a zero low word: the empty resource holds no
part of the counter. -/
theorem lockPred_not_pure_low {P : Sys} {v : Val} (hv : BitVec.setWidth 32 v = 0) : ¬ Pred.Pure P.φ v := by
  intro h
  have := h ({ init := [], msgs := #[] } : Memory) 0 hv
  rcases this with ⟨_, _, _, ⟨hC, _⟩, _⟩ | ⟨_, _, hC, _⟩ <;>
    simp [Res.unit, Perm.unit] at hC

/-- **What an RMW reading a zero low word from the lock acquires**
(`SpinCommon.World.lock_claim` at `lockPred`'s unlocked test): the claimed
slots of the (unclaimed) message read contain a part `R` satisfying `Good`
at the message's timestamp or `Bad`. -/
theorem World.lock_claim' {I : ISA} {P : Sys} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}
    (hW : World P g) (E : Erase rF g T c) {tr : Time} {v : Val} (hrd : c.mem.read? P.Lk tr = some v)
    (hv : BitVec.setWidth 32 v = 0) (hun : ¬ g.Claimed (P.Lk, tr)) :
    ∃ R R' : Res, Res.prod ((claimedSlots g P.Lk tr).map (·.res)) = R.op R' ∧
      (Good P.N P.C P.K P.F tr R ∨ Bad P.N P.Lk P.C P.K P.F R) := by
  obtain ⟨hL, -, ι, hι, -, hφ⟩ := hW
  by_cases hrel : (P.Lk, tr) ∈ g.relMsgs
  · obtain ⟨s, R', -, hP, hprod⟩ := E.claimedSlot hrel hun hι hrd
    rw [hφ] at hP
    exact ⟨s.res, R', hprod, hP hv⟩
  · have := E.pure P.Lk tr v hrd hrel
    rw [hL] at this
    exact absurd this (lockPred_not_pure_low hv)

/-- The only message a write event writes is its own (from any start
context against `c`'s memory and `t`'s promises, to any later context with
the same memory and promises). -/
theorem writtenCx_writeEv' {I : ISA} {c : Config I} {t : Thread I} {tid : Nat} {cx₀ cx' cx'' : Ctx} {l : Loc}
    {v : Val} {tr : Option Time} {tw : Time} {w : Msg} (hm₀ : cx₀.mem = c.mem) (hp₀ : cx₀.prom = t.prom)
    (hev : WriteEv tid cx₀ cx' l v tr tw) (hm : cx''.mem = cx'.mem) (hp : cx''.prom = cx'.prom)
    (hw : WrittenCx c t cx'' w) : w = ⟨l, v, tid⟩ := by
  obtain ⟨ts, hget, hnp, hnew⟩ := hw
  rw [hm] at hget
  rw [hp] at hnp
  have hts : ts = tw := by
    rcases hnew with hlt | hpr
    · rcases hev.cases with ⟨hm', -, -⟩ | ⟨hm', rfl⟩
      · rw [hm', hm₀] at hget
        exact absurd (Memory.last_le_of_get?_eq_some _ hget) (Nat.not_le.mpr hlt)
      · have := Memory.last_le_of_get?_eq_some _ hget
        rw [hm', Memory.last_append, hm₀] at this
        rw [hm₀]
        exact Nat.le_antisymm this hlt
    · refine Classical.byContradiction fun hne => hnp ?_
      rw [hev.prom, hp₀]
      exact (List.mem_erase_of_ne hne).mpr hpr
  subst hts
  rcases hev.cases with ⟨hm', -, hg⟩ | ⟨hm', rfl⟩
  · rw [hm'] at hget
    exact Option.some.inj (hget.symm.trans hg)
  · rw [hm', Memory.get?_append_last] at hget
    exact (Option.some.inj hget).symm

end Claim

theorem setWidth_32_128 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 128 y) = y := by
  apply BitVec.eq_of_toNat_eq; simp

theorem one_div_pos {N : Nat} (h : 0 < N) : (0 : Rat) < 1 / (N : Rat) := by
  have : (0 : Rat) < N := by exact_mod_cast h
  rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr this

/-- **Holding after acquiring the pool**: a `Fresh` thread that claims a
resource containing the pool for `S` (the composition valid) holds all of
`C` and of `K tid` (`S tid = false`: it holds `F tid` itself). -/
theorem holding_of_pool {P : Sys} {tid : Nat} {r R R' : Res} {S : Nat → Bool} {p : Val × Time}
    (htid : tid < P.N) (hN0 : 0 < P.N) (hfr : Fresh P tid r) (hval : (r.op (R.op R')).valid)
    (hpool : Pool P.N P.C P.K P.F S R) : Holding P tid S ((r.op (R.op R')).addW P.Lk p) := by
  have hq : ∀ y, (((r.op (R.op R')).addW P.Lk p).wr y).q = (r.wr y).q + ((R.wr y).q + (R'.wr y).q) :=
    fun y => by rw [Res.addW_q]; rfl
  have hv : ∀ y, (r.wr y).q + ((R.wr y).q + (R'.wr y).q) ≤ 1 := hval.1
  obtain ⟨hC, hS⟩ := hpool
  have hSt : S tid = false := by
    cases h : S tid
    · rfl
    · have h1 := (hS tid htid).2 h
      have := hv (P.F tid); have := (R'.wr (P.F tid)).nonneg; have := hfr.2.1
      exfalso; grind
  refine ⟨?_, hSt, htid, ?_, ?_, ?_, fun j hj hjt => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> simp only [hq]
  · have := hv P.C; have := (r.wr P.C).nonneg; have := (R'.wr P.C).nonneg; grind
  · have := (hS tid htid).1 hSt; have := hfr.1; have := (R'.wr (P.K tid)).nonneg; grind
  · have := hfr.2.1; have := (R.wr (P.F tid)).nonneg; have := (R'.wr (P.F tid)).nonneg; grind
  · have := one_div_pos hN0; have := hfr.2.2; have := (R.wr P.Lk).nonneg; have := (R'.wr P.Lk).nonneg; grind
  · have := (hS j hj).1 h; have := (r.wr (P.K j)).nonneg; have := (R'.wr (P.K j)).nonneg; grind
  · have := (hS j hj).2 h; have := (r.wr (P.F j)).nonneg; have := (R'.wr (P.F j)).nonneg; grind

/-- **The counter relation after acquiring `Good`**: the pool holds all of
`C`, so neither the thread nor the rest holds any, and the counter's write
set is the pool's. -/
theorem counterGood_of_good {P : Sys} {r R R' : Res} {S : Nat → Bool} {k : Nat} {ts : Time} {p : Val × Time}
    (hLC : P.Lk ≠ P.C) (hval : (r.op (R.op R')).valid) (hC : (R.wr P.C).q = 1)
    (hX : (R.wr P.C).X (BitVec.ofNat 128 k, ts)) (hmax : ∀ p, (R.wr P.C).X p → p.2 ≤ ts)
    (hk : k = ((List.range P.N).filter S).length) : CounterGood P S k ts ((r.op (R.op R')).addW P.Lk p) := by
  have hv : (r.wr P.C).q + ((R.wr P.C).q + (R'.wr P.C).q) ≤ 1 := hval.1 P.C
  have n1 := (r.wr P.C).nonneg
  have n3 := (R'.wr P.C).nonneg
  have h1 : (r.wr P.C).q = 0 := by grind
  have h3 : (R'.wr P.C).q = 0 := by grind
  unfold CounterGood CounterMax
  rw [Res.addW_wr_ne _ _ (Ne.symm hLC)]
  refine ⟨⟨.inr (.inl hX), fun p hp => ?_⟩, hk⟩
  rcases hp with hp | hp | hp
  · exact absurd hp ((r.wr P.C).zero h1 p)
  · exact hmax p hp
  · exact absurd hp ((R'.wr P.C).zero h3 p)

end Kraken.Promising.SLR.SpinCommon
