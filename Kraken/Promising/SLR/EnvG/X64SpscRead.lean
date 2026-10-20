/-
**Part 4: the read lemmas of the SPSC
proof** (ISA-neutral where possible; hoist candidates).

- `read_own`: a thread holding all of `x` (maximal write `(v0, ts)`) reads
  either its own maximal write or a later message that is pure under `x`'s
  release predicate. **Any erasure** (`T` arbitrary): a later release message
  would be settled, hence in the holder's write set, hence `≤ ts`. With an
  impure predicate (`psiT`) the read is exact without the clean flag; this
  is how the producer knows its `tail` and the consumer its initial `head`.
- `takeFold_acq_ne`, `takeEff_acq_ne`: a take at `l` keeps the acquire ids of
  every other location.
- `LoadKeep` (`loadKeep`): what every `EnvGTX` load keeps (ghost order, full
  permissions, ids of other locations, views, forwarding, snapshot, `cl`).
- `OkPred`, `SpinAt`, `spin_read`: an acquire spin on a location the thread
  does not write. The thread holds an acquire id of `l` whose predicate is
  usable relative to the last message read `K`; a read at `tr` is `K` itself
  (value `vK`), or a later message that is pure, or a later release message
  whose slot (taken whole) satisfies `l`'s release predicate.
- `writeSnap_read?`, `SpinAt.load_other`, `SpinAt.store_other`,
  `SpinAt.fence`: the spin facts survive accesses to other locations.
-/
import Kraken.Promising.SLR.EnvG.X64SpscSpec
import Kraken.Promising.SLR.EnvG.TakeX64Link
import Kraken.Promising.SLR.EnvG.TakeX64VCGen
import Kraken.Promising.SLR.EnvG.Alias
import Kraken.Promising.SLR.EnvG.SpscCommon

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

/-! ## Reading an own location -/

section ReadOwn

variable {I : ISA}

/-- A non-initial message read is a message of the location. -/
theorem msg_of_read? {M : Memory} {l : Loc} {ts : Time} {v : Val} (hrd : M.read? l ts = some v) (h0 : ts ≠ 0) :
    ∃ w, M.get? ts = some w ∧ w.loc = l ∧ w.val = v := by
  simp only [Memory.read?, h0, ↓reduceIte] at hrd
  split at hrd
  · next w hw =>
    by_cases hl : w.loc = l
    · simp only [hl, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hrd
      exact ⟨w, hw, hl, hrd⟩
    · simp [hl] at hrd
  · cases hrd

/-- **A read of a location the thread holds all of** (any erasure): with
maximal write `(v0, ts)`, `ts ≤ B` and no write to `x` in `(tr, B]`, the
read is `(v0, ts)` or a later message, pure under `x`'s release predicate. -/
theorem read_own {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} {tid : Nat} {r : Res} {x : Loc}
    {v0 val : Val} {ts tr B : Time} (E : Erase (setRes rF tid r) g T c) (hn : tid < c.threads.size)
    (hq : (r.wr x).q = 1) (hX : (r.wr x).X (v0, ts)) (hmax : ∀ p, (r.wr x).X p → p.2 ≤ ts)
    (hrd : c.mem.read? x tr = some val) (hwi : c.mem.writeIn x tr B = false) (hB : ts ≤ B) :
    (tr = ts ∧ val = v0) ∨ (ts < tr ∧ Pred.Pure (g.rel x) val) := by
  have hq' : ((setRes rF tid r tid).wr x).q = 1 := by rw [setRes_self]; exact hq
  obtain ⟨hth, hsl⟩ := E.unique_holder hn hq'
  obtain ⟨d, hd⟩ := sub_total_thread (rF := setRes rF tid r) (g := g) hn
  have hpos : 0 < ((total (setRes rF tid r) g c).wr x).q := by
    rw [hd]; show 0 < ((setRes rF tid r tid).wr x).q + (d.wr x).q
    rw [hq']; have := (d.wr x).nonneg; grind
  have hXT : ((total (setRes rF tid r) g c).wr x).X (v0, ts) := by
    rw [hd]; exact Or.inl (by rw [setRes_self]; exact hX)
  have hmaxT : ∀ p, ((total (setRes rF tid r) g c).wr x).X p → p.2 ≤ ts := by
    intro p hp
    rcases X_total_cases hp with ⟨j, hj, hXj⟩ | ⟨s, hs', hXs⟩
    · by_cases hjt : j = tid
      · subst hjt; rw [setRes_self] at hXj; exact hmax _ hXj
      · exact (((setRes rF tid r j).wr x).zero (hth j hj hjt) _ hXj).elim
    · exact ((s.res.wr x).zero (hsl s hs') _ hXs).elim
  have htr : Tracked c g (total (setRes rF tid r) g c) x := .inl hpos
  have hF0 := (E.writes x htr _).mp hXT
  have hr0 := fulf_read? hF0
  have hle : ts ≤ tr := by
    refine Nat.le_of_not_lt fun hlt => ?_
    rcases hF0 with ⟨h0, -⟩ | ⟨w, hw, hl, -, -⟩
    · simp only at h0; rw [h0] at hlt; exact Nat.not_lt_zero _ hlt
    · have := (Memory.writeIn_iff _ _ _ _).mpr ⟨ts, w, hlt, hB, hw, hl⟩
      rw [hwi] at this; cases this
  rcases Nat.lt_or_ge ts tr with hlt | hge
  · refine .inr ⟨hlt, ?_⟩
    by_cases hrm : (x, tr) ∈ g.relMsgs
    · exfalso
      have hs : Settled c g tr := E.relSettled _ hrm
      obtain ⟨w, hw, hl, hv⟩ := msg_of_read? hrd (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le ts) hlt))
      have hXr := (E.writes x htr (val, tr)).mpr (.inr ⟨w, hw, hl, hv, hs⟩)
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (hmaxT _ hXr))
    · exact E.pure x tr val hrd hrm
  · obtain rfl := Nat.le_antisymm hge hle
    exact .inl ⟨rfl, Option.some.inj (hrd.symm.trans hr0)⟩

end ReadOwn

/-! ## Takes keep the ids of other locations -/

theorem takeFold_acq_ne (l : Loc) (tr : Time) {x : Loc} (hx : x ≠ l) {ι : PredId} :
    ∀ (ids : List PredId) (a : TakeAcc), 1 ≤ a.r.acq x ι → 1 ≤ (ids.foldl (takeStep l tr) a).r.acq x ι
  | [], _, h => h
  | j :: ids, a, h => by
    rw [List.foldl_cons]
    refine takeFold_acq_ne l tr hx ids _ ?_
    unfold takeStep
    split
    · simp only [takeRes, Res.op, swapAcq, hx, false_and, ↓reduceIte]
      omega
    · exact h

theorem takeEff_acq_ne {A : Arch} {k : LoadKind} {vs : Views} {l : Loc} {tr : Time} {r : Res} {ga : Ghost}
    {a : TakeAcc} (ha : TakeEff A k vs l tr r ga a) {x : Loc} (hx : x ≠ l) {ι : PredId} (h : 1 ≤ r.acq x ι) :
    1 ≤ a.r.acq x ι := by
  by_cases hc : TakeCond A k vs l tr
  · rw [ha.1 hc]; exact takeFold_acq_ne l tr hx _ _ h
  · rw [ha.2 hc]; exact h

/-! ## What a load keeps -/

/-- **What an `EnvGTX` load of `l` keeps.** -/
structure LoadKeep (tid : Nat) (l : Loc) (σ σ' : EStateX) : Prop where
  ghost : σ.g.Le σ'.g
  full : ∀ x, (σ.r.wr x).q = 1 → (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (σ.r.wr x).X p
  acq : ∀ x, x ≠ l → ∀ ι, 1 ≤ σ.r.acq x ι → 1 ≤ σ'.r.acq x ι
  vs : VLe σ.vs σ'.vs
  fwd : ∀ x, σ'.vs.getFwd x = σ.vs.getFwd x
  snap : SnapLe tid σ.snap σ'.snap
  cl : σ'.cl → σ.cl

theorem loadKeep {A : Arch} {pl : Plan} {S : SharedEnv.Layout} {tid : Nat} {σ σ' : EStateX} {k : LoadKind}
    {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val}
    (hs : (EnvGTX A tid pl S).step (.load k xcl a n) σ v σ') : LoadKeep tid ⟨a, n⟩ σ σ' := by
  obtain ⟨ga, hanc, ⟨rF, E⟩, hcl, tr, -, hlv, a', ha, hr, hg, -⟩ := step_loadFactsT (pl := pl) hs
  refine ⟨by rw [hg]; exact hanc.ghost.trans ha.ghost_le, fun x hq => ?_, fun x hx ι h => ?_, hlv.mono,
    hlv.getFwd, hanc.snap, fun h => (hcl ▸ h).1⟩
  · rw [hr]; exact takeEff_wr_full hanc.lt E ha hq
  · rw [hr]; exact takeEff_acq_ne ha hx h

theorem LoadKeep.rel {tid : Nat} {l : Loc} {σ σ' : EStateX} (h : LoadKeep tid l σ σ') : σ'.g.rel = σ.g.rel :=
  h.ghost.rel

theorem LoadKeep.pred {tid : Nat} {l : Loc} {σ σ' : EStateX} (h : LoadKeep tid l σ σ') {ι : PredId}
    (hι : ι < σ.g.acqTab.length) : σ'.g.acqPred ι = σ.g.acqPred ι :=
  Ghost.acqPred_of_prefix h.ghost.acqTab hι

theorem LoadKeep.len {tid : Nat} {l : Loc} {σ σ' : EStateX} (h : LoadKeep tid l σ σ') {ι : PredId}
    (hι : ι < σ.g.acqTab.length) : ι < σ'.g.acqTab.length :=
  Nat.lt_of_lt_of_le hι h.ghost.acqTab.length_le

/-! ## Spinning -/

-- **A usable acquire predicate** `φ` for the release predicate `ψ`, relative
-- to the last message read `K`: `ψ`, or the empty resource at a view at or
-- below `K` (where an earlier take relaxed it). Neutral (`SpscCommon`).
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.OkPred ↦ Kraken.Promising.X64.EnvG.SpscX.OkPred,
  Kraken.Promising.SLR.EnvG.SpscCommon.OkPred.refl ↦ Kraken.Promising.X64.EnvG.SpscX.OkPred.refl,
  Kraken.Promising.SLR.EnvG.SpscCommon.OkPred.mono ↦ Kraken.Promising.X64.EnvG.SpscX.OkPred.mono]

theorem OkPred.takeAt {ψ φ : Pred} {K tr : Time} (h : OkPred ψ φ K) (hK : K ≤ tr) : OkPred ψ (φ.takeAt tr) tr :=
  fun v m V R hP => by
    rcases hP with ⟨rfl, rfl⟩ | hP
    · exact .inr ⟨Nat.le_refl _, rfl⟩
    · exact (h v m V R hP).imp id fun ⟨h1, h2⟩ => ⟨Nat.le_trans h1 hK, h2⟩

/-- **Spin facts** at `l` (release predicate `ψ`): no own forwarding item, the
last message read `K` (value `vK`) at or below the coherence view, and a held
acquire id with a usable predicate. -/
structure SpinAt (l : Loc) (ψ : Pred) (K : Time) (vK : Val) (σ : EStateX) : Prop where
  fwd : σ.vs.getFwd l = none
  coh : K ≤ σ.vs.getCoh l
  msg : σ.snap.mem.read? l K = some vK
  id : ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq l ι ∧ OkPred ψ (σ.g.acqPred ι) K

theorem SpinAt.load_other {tid : Nat} {l l' : Loc} {ψ : Pred} {K : Time} {vK : Val} {σ σ' : EStateX}
    (h : SpinAt l ψ K vK σ) (hk : LoadKeep tid l' σ σ') (hne : l ≠ l') : SpinAt l ψ K vK σ' := by
  obtain ⟨hf, hc, hm, ι, hlt, ha, hok⟩ := h
  exact ⟨by rw [hk.fwd]; exact hf, Nat.le_trans hc (hk.vs.coh l), hk.snap.read? hm, ι, hk.len hlt,
    hk.acq l hne ι ha, by rw [hk.pred hlt]; exact hok⟩

theorem SpinAt.fence {l : Loc} {ψ : Pred} {K : Time} {vK : Val} {σ σ' : EStateX} (h : SpinAt l ψ K vK σ)
    (hf : FenceLe σ σ') : SpinAt l ψ K vK σ' := by
  obtain ⟨hfw, hc, hm, ι, hlt, ha, hok⟩ := h
  exact ⟨by rw [hf.getFwd]; exact hfw, by rw [hf.getCoh]; exact hc, by rw [hf.snap]; exact hm, ι,
    by rw [hf.g]; exact hlt, by rw [hf.r]; exact ha, by rw [hf.g]; exact hok⟩

/-- A message read before a write is read after it. -/
theorem writeSnap_read? {tid : Nat} {c c' : Config isa} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) {x : Loc} {ts : Time} {u : Val} (hr : c.mem.read? x ts = some u) :
    c'.mem.read? x ts = some u :=
  SpscCommon.writeSnap_read? h hr

/-- **The spin facts survive a store to another location** whose planned
release, if any, does not give `l` away (whole-location plans). -/
theorem SpinAt.store_other {A : Arch} {pl : Plan} {S : SharedEnv.Layout} {tid : Nat} {l : Loc} {ψ : Pred}
    {K : Time} {vK : Val} {σ σ' : EStateX} {k : StoreKind} {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val}
    {b : Bool} (h : SpinAt l ψ K vK σ) (hs : (EnvGTX A tid pl S).step (.store k xcl a n v) σ b σ')
    (hne : l ≠ ⟨a, n⟩) (hwh : pl.Whole ⟨a, n⟩ v) (hng : l ∉ pl.gives ⟨a, n⟩ v) : SpinAt l ψ K vK σ' := by
  obtain ⟨c, tw, hanc, hws, -, hwv, -, ⟨P, -, hr⟩, -⟩ := step_storeFactsT hs
  obtain ⟨hf, hc, hm, ι, hlt, ha, hok⟩ := h
  have hghost : σ.g.Le σ'.g := hanc.ghost
  refine ⟨by rw [hwv.fwdOther l hne]; exact hf, Nat.le_trans hc (hwv.mono.coh l), writeSnap_read? hws (hanc.snap.read? hm),
    ι, Nat.lt_of_lt_of_le hlt hghost.acqTab.length_le, ?_, by rw [Ghost.acqPred_of_prefix hghost.acqTab hlt]; exact hok⟩
  rw [hr]
  unfold Plan.after
  split
  · rw [Res.addW_acq, pl.keep_of_whole hwh]
    simp only [Res.drop, hng, ↓reduceIte]
    exact ha
  · rw [Res.addW_acq]; exact ha

/-- **An acquire spin read** (`Arch.tso` plain load, not forwarded) of `l`
with spin facts at `K`: the spin facts move to the message read `tr ≥ K`,
and the read is `K` itself, or a later pure message, or a later release
message whose slot `R` satisfies `ψ`; the thread held none of what `R` holds
fully, and now holds it with `R`'s write set; `tr` is below the new views. -/
theorem spin_read {pl : Plan} {S : SharedEnv.Layout} {tid : Nat} {a : BitVec 64} {ψ : Pred} {K : Time}
    {vK : Val} {σ σ' : EStateX} {v : Val} (hrel : σ.g.rel ⟨a, 4⟩ = ψ) (hsp : SpinAt ⟨a, 4⟩ ψ K vK σ)
    (hs : (EnvGTX Arch.tso tid pl S).step (.load .plain false a 4) σ v σ') :
    ∃ tr, SpinAt ⟨a, 4⟩ ψ tr v σ' ∧ K ≤ tr ∧
      ((tr = K ∧ v = vK) ∨ (K < tr ∧ Pred.Pure ψ v) ∨
        (K < tr ∧ ∃ R, ψ.P v σ'.snap.mem tr R ∧
          (∀ x, (R.wr x).q = 1 → (σ.r.wr x).q = 0 ∧ (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (R.wr x).X p) ∧
          tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew)) := by
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a', ha, hr, hg, -⟩ := step_loadFactsT (pl := pl) hs
  obtain ⟨hfw, hcoh, hmsg, ι, hlt, hacq1, hok⟩ := hsp
  have hn := hanc.lt
  have hacq : σ.r.acq ⟨a, 4⟩ ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hnf := not_fwded_of_none (tr := tr) hfw
  have hc : TakeCond Arch.tso .plain σ.vs ⟨a, 4⟩ tr := ⟨by decide, hnf⟩
  have ha' : a' = takeAll ⟨a, 4⟩ tr σ.r ga := ha.1 hc
  have hok' : OkPred ψ (ga.acqPred ι) K := by rw [hanc.acqPred hlt]; exact hok
  have hK' : σ'.snap.mem.read? ⟨a, 4⟩ K = some vK := hanc.snap.read? hmsg
  have hKtr : K ≤ tr := by
    refine Nat.le_of_not_lt fun hlt' => ?_
    obtain ⟨w, hw, hl, -⟩ := msg_of_read? hK' (Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt'))
    have hB : K ≤ readBound Arch.tso σ.vs .plain ⟨a, 4⟩ := Nat.le_trans hcoh (Nat.le_max_right _ _)
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨K, w, hlt', hB, hw, hl⟩
    rw [hrd.window] at this; cases this
  obtain ⟨ι', h1, h2, hp⟩ := takeAll_held (l := ⟨a, 4⟩) (tr := tr) (r := σ.r) (g := ga) hacq1 (hanc.acqLen hlt)
  have hsp' : SpinAt ⟨a, 4⟩ ψ tr v σ' := by
    refine ⟨by rw [hlv.getFwd]; exact hfw, hlv.coh hnf, hrd.val, ι', by rw [hg, ha']; exact h2,
      by rw [hr, ha']; exact h1, ?_⟩
    rw [hg, ha']
    rcases hp with hp | hp
    · rw [hp]; exact hok'.mono hKtr
    · rw [hp]; exact hok'.takeAt hKtr
  refine ⟨tr, hsp', hKtr, ?_⟩
  rcases Nat.lt_or_ge K tr with hlt' | hge
  · by_cases hpure : Pred.Pure ψ v
    · exact .inr (.inl ⟨hlt', hpure⟩)
    · refine .inr (.inr ⟨hlt', ?_⟩)
      obtain ⟨s, hs, hkey, hid, hP⟩ := SLR.EnvG.slot_of_seen (k := (⟨a, 4⟩, tr)) E hn hacq hrd.val
        (by rw [hanc.rel, hrel]; exact hpure)
      have hPs : ψ.P v σ'.snap.mem tr s.res := by
        rcases hok' v _ tr s.res hP with h | ⟨h, -⟩
        · exact h
        · exact absurd h (Nat.not_le.mpr hlt')
      have hvw := hlv.acq (by decide) hnf
      refine ⟨s.res, hPs, fun x hq => ?_, hvw.1, hvw.2⟩
      have hsum := E.q_add_le_one_slot hn hs x
      rw [setRes_self, hq] at hsum
      have h0 := (σ.r.wr x).nonneg
      obtain ⟨hq', hX'⟩ := takeAll_wr_full hn E hs hkey (by rw [hid]; exact hacq) hq
      exact ⟨by grind, by rw [hr, ha']; exact hq', fun p => by rw [hr, ha']; exact hX' p⟩
  · obtain rfl := Nat.le_antisymm hKtr hge
    exact .inl ⟨rfl, Option.some.inj (hrd.val.symm.trans hK')⟩

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.read_own
#print axioms Kraken.Promising.X64.EnvG.SpscX.spin_read
#print axioms Kraken.Promising.X64.EnvG.SpscX.loadKeep
