/-
Whole-thread environment (`EnvG`): **the generic prepay
theorem**, proved for stores. ISA-neutral.

`EnvG/Env.lean` states `PrepayGeneric`: a thread at a store that `EnvG`
permits (`StoreOk`) may promise the message with its effect accounted at
promise time. Both kinds of store go through `Erase.prepay_exempt`
(`NPSafe`'s erasure exempts the promising thread):

- a planned release (`pl.rel l v = true`): the slots `ss` of `Plan.give`
  (`Erase.slotsFor` on `RelOb`), the thread keeping `Plan.keep`
  (`Plan.keep_op_give`);
- a pure message (`pl.rel l v = false`): the slots of the unit resource
  (`Erase.slotsFor` on `Pred.Pure`), the thread keeping the whole resource.

K2/K1 are `prepay_K2`/`prepay_K1`, `acqLe` is `mayWrite_store_le`.

**Phase 1: releases are stores.** A release RMW (AArch64 `swpal`/`casal`/
`ldaddl`, every x64 RMW) would need the RMW variant `PrepayGenericRmw`
(stated here as a `Prop`, not proved; `KNOWN_GAPS.md`): the RMW's claimed
update slots of the read message enter the thread before the promise, which
needs the RMW fulfilment of a pending promise (`prepayRmwGhost`, retired
`Erase.prepayRmw`) and the claim floor at promise time.

(this `Prop` is not provable as stated; the corrected statement
`PrepayGenericRmw'`, proved as `prepayGenericRmw'`, is in
`EnvG/PrepayRmw.lean`, whose module docstring explains the difference.)
-/
import Kraken.Promising.SLR.EnvG.LinkS

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **The generic prepay theorem at a store node, exposing the ghost**:
`PrepayGeneric`'s conclusion, with the ghost after the promise
`prepayGhost g l (c.mem.last + 1) ss` for some slots `ss`. Extensions of the
erasure that are kept by `prepayGhost` (e.g. the ticket dispenser's `TX`,
`prepayGenericTD`) are transported from it. -/
theorem prepayGenericG {A : Arch} (tid : Nat) (pl : Plan) (σ : State I) (k : StoreKind) (l : Loc) (v : Val)
    (c : Config I) (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (_ : pl.Valid)
    (hok : StoreOk A tid pl σ k false l v) (hanc : AnchorOk tid σ c g) (ht : c.threads[tid]? = some t₁)
    (E : Erase (setRes rF tid σ.r) g (fun _ => True) c) (hwb : WriteBound A σ.vs k l (c.mem.last + 1)) :
    ∃ (r' : Res) (ss : List Slot),
      Erase (setRes rF tid r') (prepayGhost g l (c.mem.last + 1) ss) (fun _ => True) (PromisedBy c tid t₁ ⟨l, v, tid⟩) ∧
      g.Le (prepayGhost g l (c.mem.last + 1) ss) ∧
      (c.mem.append ⟨l, v, tid⟩).2 ∈ (prepayGhost g l (c.mem.last + 1) ss).pend ∧
      (∀ ts, ts ∈ g.pend → ts ∈ (prepayGhost g l (c.mem.last + 1) ss).pend) ∧
      (∀ ts, ts ∈ (prepayGhost g l (c.mem.last + 1) ss).pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, v, tid⟩).2) ∧
      r' = pl.after l v (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' (prepayGhost g l (c.mem.last + 1) ss) x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ (prepayGhost g l (c.mem.last + 1) ss) x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' (prepayGhost g l (c.mem.last + 1) ss) x b → reachB σ.r g x b) := by
  obtain ⟨-, hpos, hpure, hrel⟩ := hok
  have hgr : g.rel = σ.g.rel := hanc.ghost.rel
  -- the given-away resource `R` and the slots carrying it
  obtain ⟨R, hP, hkeep⟩ : ∃ R, (g.rel l).P v (c.mem.append ⟨l, v, tid⟩).1 (c.mem.last + 1) R ∧
      (pl.after l v (c.mem.last + 1) σ.cl σ.r).op R = σ.r.addW l (v, c.mem.last + 1) := by
    cases hrl : pl.rel l v with
    | false =>
      refine ⟨Res.unit, hgr ▸ hpure hrl _ _, ?_⟩
      simp [Plan.after, hrl, Res.op_unit]
    | true =>
      obtain ⟨-, -, hgl, hob⟩ := hrel hrl
      refine ⟨pl.give l v σ.cl σ.r, hgr ▸ hob c g hanc hwb, ?_⟩
      simp only [Plan.after, hrl, ↓reduceIte]
      exact pl.keep_op_give hgl σ.cl σ.r _
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP
  have hres : (pl.after l v (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      (setRes rF tid σ.r tid).addW l (v, c.mem.last + 1) := by
    rw [hprod, setRes_self]; exact hkeep
  have hpos' : 0 < ((setRes rF tid σ.r tid).wr l).q := by rw [setRes_self]; exact hpos
  have E' := Erase.prepay_exempt (w := ⟨l, v, tid⟩) E ht trivial hpos' hss hres
  rw [setRes_setRes] at E'
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
    have h1 := E.slot_key_le hs
    rw [he, hss.key s' hs'] at h1
    simp only at h1
    omega_t
  have hres0 : (pl.after l v (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      σ.r.addW l (v, c.mem.last + 1) := by rw [hprod]; exact hkeep
  refine ⟨_, ss, E', ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩, List.mem_cons_self, fun ts h => List.mem_cons_of_mem _ h,
    fun ts h => ?_, rfl, fun x hx => mayWrite_store_le (tw := c.mem.last + 1) (rel := true) hres0 rfl hdisj hx, prepay_K2 hss, prepay_K1 hss hres0⟩
  rcases List.mem_cons.mp h with h | h
  · exact .inr h
  · exact .inl h

/-- **The generic prepay theorem at a store node** (`PrepayGeneric`; from
`prepayGenericG`, forgetting the ghost's form). -/
theorem prepayGeneric {A : Arch} : PrepayGeneric I A := by
  intro tid pl σ k l v c g rF t₁ hv hok hanc ht E hwb
  obtain ⟨r', ss, h⟩ := prepayGenericG (A := A) tid pl σ k l v c g rF t₁ hv hok hanc ht E hwb
  exact ⟨r', _, h⟩

/-- **The generic prepay theorem at an RMW node** (statement only; **not
proved — phase 1: releases are stores**, `KNOWN_GAPS.md`): thread `tid` at
a successful release-kind RMW reading `(l, tr)` and writing `new` may
promise the message with the RMW's effect accounted (`prepayRmwGhost`: the
claimed update slots of `(l, tr)` into the thread, the release slots out,
the message pending). The claim needs `tr` at most the thread's floor after
the RMW (`ClaimOk`) at promise time, and the later fulfilment must be an
RMW fulfilling a pending promise, which `ErAt.fulfilPend` does not cover
(the claim is made at promise time). -/
def PrepayGenericRmw (I : ISA) (A : Arch) : Prop :=
  ∀ (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) (c : Config I)
    (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (tr : Time) (old new : Val),
    pl.Valid → RmwOk A tid pl σ k l op → effRelRmw A k → AnchorOk tid σ c g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid σ.r) g (fun _ => True) c → (∃ w, c.mem.get? tr = some w ∧ w.loc = l ∧ w.val = old) →
    op old = some new → pl.rel l new = true →
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.afterRmw l new tr (c.mem.last + 1) g σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b)

end Kraken.Promising.SLR.EnvG
