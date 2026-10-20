/-
Whole-thread environment (`EnvG`), release-kind RMWs, part 1: **the generic prepay
theorem at an RMW node**, additively beside
`EnvG/Prepay.lean`. ISA-neutral.

## Why `PrepayGenericRmw` (Prepay.lean) is not proved

The original statement `PrepayGenericRmw` is kept unchanged but is **not provable
as stated**:

- it asks for `r' = pl.afterRmw l new tr ts g σ.r`, i.e. the claimed update
  slots of the message read, `claimedSlots g l tr`, join the thread **at
  promise time**. Erasure forbids claiming at promise time: a claimer is never
  an outstanding promise (`Erase.claimFulf`, T1c option (B), which retired
  `Erase.prepayRmw`), and while `(l, tr)` is unclaimed its update slots stay
  in `u` (`Erase.slotsDom`). So whenever `claimedSlots g l tr ≠ []` the
  slots' resources would be counted twice;
- it lacks the hypotheses needed to use the RMW's permission `RmwOk` at all:
  `RmwOk` quantifies over reads the environment offers (`ReadAt`, with the
  read window), and its release obligation needs the write bound
  (`WriteBound`) of the fresh timestamp; the statement only has
  `∃ w, c.mem.get? tr = some w ∧ …`;
- its `r'` does not match the frozen in-flight relation `Inflight`
  (`EnvG/NodeRel.lean`), which records the actual resource after a prepay as
  `pl.after l v ts σ.r` (no claimed slots).

## The corrected statement `PrepayGenericRmw'`

The RMW's write is prepaid like a store (`prepayGhost`: no claim; the RMW
claims when its write really fulfils the pending promise,
`Erase.claimPend`/`EvTree.eraseWPR_rmw_pendClaim`, as the x64 spinlock's
prepaid `xchg` already does, `X64SpinPrepay` case (5)):

- hypotheses: an environment read `ReadAt` of `(l, tr)` with value `old` at
  the anchor `c`, `op old = some new`, the write bound of the fresh timestamp,
  and, for a planned release, that the slots the RMW will claim carry nothing
  at the locations the release gives away (`give l new C = unit`, see
  `RelRmwGiveOk`);
- conclusion: as `PrepayGeneric`, with `r' = pl.after l new ts σ.cl σ.r`.

F1: the side condition is stated on the whole-location give,
`Res.only (pl.gives l new) C = Res.unit`; `RmwOk` makes every release RMW's
entry whole (`Plan.Whole`), so `pl.give l new cl` is `Res.only (pl.gives l
new)` for every `cl` (`Plan.give_of_whole`). A general `(cl, r)` split does
not satisfy `Plan.give_op_of_unit`'s homomorphism law, which is why release
RMWs may not split (phase-1 limit).

A pure value gives away the unit resource (purity from `RmwOk`); a planned
release gives away `pl.give l new σ.r`: `RmwOk`'s obligation is for
`pl.give l new (σ.r ⋅ C)`, which is `pl.give l new σ.r` when
`pl.give l new C = unit` (`Res.only_op`).

`RelRmwGiveOk I pl rel`: the per-program form of the side condition, at every
erasure ghost with release predicates `rel`. It is trivial when the plan's
releases give nothing away, and in general a program obligation (e.g. an
unlock RMW that reads the thread's own lock message, which is not in release
mode, claims nothing: `Erase.claimedSlots_nil`).

Caveat (`KNOWN_GAPS.md` release-RMW limit 2): the statement quantifies
over every erasure ghost, location and read time, not over the message the
RMW actually reads. An erasure ghost may hold a release-mode message at `l`
whose unclaimed update slot carries a given-away location. So with
`pl.gives l new ≠ []` the condition is not provable as stated, and the example
above does not discharge it. Every use so far is `RelRmwGiveOk.of_gives_nil`.
-/
import Kraken.Promising.SLR.EnvG.Prepay

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.Sim

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-! ## The resource algebra -/

/-- `Res.only` distributes over composition. -/
theorem Res.only_op (L : List Loc) (a b : Res) : Res.only L (a.op b) = (Res.only L a).op (Res.only L b) := by
  apply Res.ext
  · funext x
    simp only [Res.op, Res.only]
    split
    · rfl
    · exact (Perm.op_unit _).symm
  · funext x ι
    simp only [Res.op, Res.only]
    split <;> omega

/-- What a planned whole release (no split, `Plan.Whole`) gives away of
`r ⋅ C`, when `C` has nothing at the given-away locations. -/
theorem Plan.give_op_of_unit (pl : Plan) {l : Loc} {v : Val} {r C : Res} (hs : pl.Whole l v) (cl : Prop)
    (h : Res.only (pl.gives l v) C = Res.unit) : pl.give l v cl (r.op C) = pl.give l v cl r := by
  rw [pl.give_of_whole hs, pl.give_of_whole hs, Res.only_op, h, Res.op_unit]

/-! ## The statement and the side condition -/

/-- **The generic prepay theorem at an RMW node**, corrected (see the module
docstring for why `PrepayGenericRmw` is not provable): thread `tid` at a
live RMW of kind `k` on `l` that `σ` permits (`RmwOk`), whose read of
`(l, tr)` with value `old` the environment offers at the admissible anchor
`(c, g)` and whose operation succeeds with `new`, may promise `⟨l, new⟩` with
the RMW's *write* accounted (no claim at promise time). For a planned release,
the slots the RMW claims carry nothing at the given-away locations. The
conclusion is `PrepayGeneric`'s, with `r' = pl.after l new ts σ.r` (the
frozen `Inflight`'s shape). -/
def PrepayGenericRmw' (I : ISA) (A : Arch) : Prop :=
  ∀ (tid : Nat) (pl : Plan) (σ : State I) (k : RmwKind) (l : Loc) (op : Val → Option Val) (c : Config I)
    (g : Ghost) (rF : Nat → Res) (t₁ : Thread I) (tr : Time) (old new : Val),
    pl.Valid → RmwOk A tid pl σ k l op → AnchorOk tid σ c g → c.threads[tid]? = some t₁ →
    Erase (setRes rF tid σ.r) g (fun _ => True) c →
    ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old → op old = some new →
    WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1) →
    (pl.rel l new = true → Res.only (pl.gives l new) (Res.prod ((claimedSlots g l tr).map (·.res))) = Res.unit) →
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.after l new (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b)

/-- **The give-away side condition of planned-release RMWs** for a program
whose release predicates are `rel`: at every erasure ghost, the update slots
an RMW claims carry nothing at the locations a planned release of its written
value gives away. -/
def RelRmwGiveOk (I : ISA) (pl : Plan) (rel : Loc → Pred) : Prop :=
  ∀ (rF : Nat → Res) (g : Ghost) (c : Config I) (l : Loc) (tr : Time) (new : Val), g.rel = rel →
    Erase rF g (fun _ => True) c → pl.rel l new = true →
    Res.only (pl.gives l new) (Res.prod ((claimedSlots g l tr).map (·.res))) = Res.unit

/-- A plan whose releases give nothing away satisfies `RelRmwGiveOk`. -/
theorem RelRmwGiveOk.of_gives_nil {pl : Plan} {rel : Loc → Pred} (h : ∀ l v, pl.gives l v = []) :
    RelRmwGiveOk I pl rel := by
  intro _ _ _ l _ new _ _ _
  apply Res.ext
  · funext x; simp [Res.only, h, Res.unit]
  · funext x ι; simp [Res.only, h, Res.unit]

/-! ## The proof -/

/-- **The generic prepay theorem at an RMW node** (`PrepayGenericRmw'`). -/
theorem prepayGenericRmw' {A : Arch} : PrepayGenericRmw' I A := by
  intro tid pl σ k l op c g rF t₁ tr old new hv hok hanc ht E hrd hop hwb hgive
  obtain ⟨-, hpure, hrel⟩ := hok.2 c g tr old new hanc hrd hop
  have hgr : g.rel = σ.g.rel := hanc.ghost.rel
  have htr : tr < c.mem.last + 1 := Nat.lt_succ_of_le (read?_le_last' hrd.val)
  -- the given-away resource `R` and the slots carrying it
  obtain ⟨R, hP, hkeep⟩ : ∃ R, (g.rel l).P new (c.mem.append ⟨l, new, tid⟩).1 (c.mem.last + 1) R ∧
      (pl.after l new (c.mem.last + 1) σ.cl σ.r).op R = σ.r.addW l (new, c.mem.last + 1) := by
    cases hrl : pl.rel l new with
    | false =>
      refine ⟨Res.unit, hgr ▸ hpure hrl _ _, ?_⟩
      simp [Plan.after, hrl, Res.op_unit]
    | true =>
      obtain ⟨-, -, hgl, hwh, hob⟩ := hrel hrl
      have h1 := hob htr hwb
      rw [pl.give_op_of_unit hwh σ.cl (hgive hrl)] at h1
      refine ⟨pl.give l new σ.cl σ.r, hgr ▸ h1, ?_⟩
      simp only [Plan.after, hrl, ↓reduceIte]
      exact pl.keep_op_give hgl σ.cl σ.r _
  have hpos : 0 < (σ.r.wr l).q := hok.1
  obtain ⟨ss, hss, hprod⟩ := Erase.slotsFor E hP
  have hres : (pl.after l new (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      (setRes rF tid σ.r tid).addW l (new, c.mem.last + 1) := by
    rw [hprod, setRes_self]; exact hkeep
  have hpos' : 0 < ((setRes rF tid σ.r tid).wr l).q := by rw [setRes_self]; exact hpos
  have E' := Erase.prepay_exempt (w := ⟨l, new, tid⟩) E ht trivial hpos' hss hres
  rw [setRes_setRes] at E'
  have hdisj : ∀ s ∈ g.u, ∀ s' ∈ ss, s.key ≠ s'.key := fun s hs s' hs' he => by
    have h1 := E.slot_key_le hs
    rw [he, hss.key s' hs'] at h1
    simp only at h1
    omega_t
  have hres0 : (pl.after l new (c.mem.last + 1) σ.cl σ.r).op (Res.prod (ss.map (·.res))) =
      σ.r.addW l (new, c.mem.last + 1) := by rw [hprod]; exact hkeep
  refine ⟨_, prepayGhost g l (c.mem.last + 1) ss, E', ⟨rfl, List.prefix_refl _, fun _ => List.prefix_refl _⟩,
    List.mem_cons_self, fun ts h => List.mem_cons_of_mem _ h, fun ts h => ?_, rfl,
    fun x hx => mayWrite_store_le (tw := c.mem.last + 1) (rel := true) hres0 rfl hdisj hx, prepay_K2 hss,
    prepay_K1 hss hres0⟩
  rcases List.mem_cons.mp h with h | h
  · exact .inr h
  · exact .inl h

/-- `PrepayGenericRmw'` with the side condition from `RelRmwGiveOk` (the
program's release predicates are the env's, `Ghost.Le` fixes them). -/
theorem prepayGenericRmw'_of_giveOk {A : Arch} {tid : Nat} {pl : Plan} {σ : State I} {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {c : Config I} {g : Ghost} {rF : Nat → Res} {t₁ : Thread I} {tr : Time}
    {old new : Val} (hG : RelRmwGiveOk I pl σ.g.rel) (hv : pl.Valid) (hok : RmwOk A tid pl σ k l op)
    (hanc : AnchorOk tid σ c g) (ht : c.threads[tid]? = some t₁) (E : Erase (setRes rF tid σ.r) g (fun _ => True) c)
    (hrd : ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old) (hop : op old = some new)
    (hwb : WriteBound A σ.vs (A.rmwKind k).storeKind l (c.mem.last + 1)) :
    ∃ (r' : Res) (g' : Ghost),
      Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ ⟨l, new, tid⟩) ∧ g.Le g' ∧
      (c.mem.append ⟨l, new, tid⟩).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append ⟨l, new, tid⟩).2) ∧
      r' = pl.after l new (c.mem.last + 1) σ.cl σ.r ∧
      (∀ x, mayWrite r' g' x → mayWrite σ.r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB σ.r g x b) :=
  prepayGenericRmw' tid pl σ k l op c g rF t₁ tr old new hv hok hanc ht E hrd hop hwb
    (fun hrl => hG (setRes rF tid σ.r) g c l tr new hanc.ghost.rel E hrl)

end Kraken.Promising.SLR.EnvG
