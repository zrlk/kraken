/-
ISA-neutral facts for the **unlock** of the spinlock-counter workers and its
prepayment, over `SpinCommon.Sys`: the `Sys` twins of the
AArch64-only `release_split` (`SLR/SwpRelease.lean`) and of the machine facts
of `SLR/SwpRelease.lean`/`SLR/SwpPrepay.lean`, which live in files importing
the AArch64 syntax and so cannot be used by the x64 worker
(`SLR/X64SpinInv.lean`).

## The release split

Holding the lock (`Holding S`), the unlock message `(Lk, 0, tw)` carries the
pool for `S' = S[tid := true]` (`relFrac`: all of `C`, all of `F tid`, half of
`K j` for `j ∉ S'`, all of `F j` for `j ∈ S'`, `j ≠ tid`) and, for the `Bad`
disjunct, a share `δ` of `Lk`. The thread keeps the rest (`Res.leave`,
`SLR/ResSplit.lean`): `K tid` whole and, clean, at least `1/N` of `Lk`, and
its write set of `Lk` gains `(0, tw)` above every earlier own write, i.e.
`Post`.

- clean, counter relation (`CounterMax (k+1) ts`, `ts ≤ vw < tw`): `Good`
  with `δ = 0`;
- clean, surplus (`1/N < q`): `Bad` with `δ = q - 1/N`;
- unclean: `Bad` with `δ = q/2` (no `Post` is asked).

## Machine facts

- `writeSuccs_fresh_vwOld`: a fresh release append lies above `vwOld`;
- `writeSuccs_fulfil_writeOk`, `writeOk_rel_vwOld`, `writeSuccs_fulfil_coh`:
  a write that removes the outstanding promise `ts` writes at `ts` (allowed
  there, above `vwOld` for a release; `coh l` raised to `ts`);
- `writeSuccs_fulfil_live`: the store step of `EvTree.RelFulfilsLive`: the
  fulfilled message, and every other outstanding promise at the same
  location above `ts`.
-/
import Kraken.Promising.SLR.SpinCommon
import Kraken.Promising.SLR.ResSplit
import Kraken.Promising.SLR.ReleaseStore
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.PromiseFulfil

namespace Kraken.Promising.SLR.SpinCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.Spinlock

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Machine facts -/

section Machine

variable {A : Arch} {tid : Nat} {iv : InstrViews}

/-- A release store that appends a fresh message lies above `vwOld`. -/
theorem writeSuccs_fresh_vwOld {c : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) (hk : A.storeKind k = .rel)
    (hm : c'.mem = (c.mem.append ⟨l, v, tid⟩).1) : c.views.vwOld < c.mem.last + 1 := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · exfalso
    split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      have hm' : c.mem = (c.mem.append ⟨l, v, tid⟩).1 := hm
      have h2 := Memory.get?_append_last c.mem ⟨l, v, tid⟩
      rw [← hm'] at h2
      have := c.mem.last_le_of_get?_eq_some h2
      omega_t
    · cases h
  · split at h
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hok', rfl⟩ := h
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    subst ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok'
    obtain ⟨hb, -⟩ := hok'
    simp only [hk, show (StoreKind.rel == StoreKind.rel) = true from rfl, ↓reduceIte] at hb
    simp only [Memory.last] at hb ⊢
    omega_t

/-- A write that removes the outstanding promise `ts` is allowed at `ts`. -/
theorem writeSuccs_fulfil_writeOk {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last) {ts : Time} (hin : ts ∈ cx.prom) (hout : ts ∉ cx'.prom) :
    WriteOk A tid iv cx k l tr extra ts := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, hok, rfl⟩ | ⟨-, rfl⟩
  · by_cases hne : ts = t
    · subst hne; exact hok
    · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
  · exfalso
    apply hout
    simp only [afterWrite]
    have hne : ts ≠ cx.mem.last + 1 := fun he => Nat.not_succ_le_self _ (he ▸ hb ts hin)
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

/-- A release write lies above `vwOld`. -/
theorem writeOk_rel_vwOld {cx : Ctx} {k : StoreKind} {l : Loc} {tr : Option Time} {extra : View} {ts : Time}
    (hk : A.storeKind k = .rel) (h : WriteOk A tid iv cx k l tr extra ts) : cx.views.vwOld < ts := by
  have h1 := h.1
  simp only [writePre, hk, show (StoreKind.rel == StoreKind.rel) = true from rfl, ↓reduceIte] at h1
  simp only [View] at *
  omega

/-- A write that removes the outstanding promise `ts` writes at `ts`: it
erases `ts` from the promises, keeps the memory and raises `coh l` to `ts`. -/
theorem writeSuccs_fulfil_coh {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last) {ts : Time} (hin : ts ∈ cx.prom) (hout : ts ∉ cx'.prom) :
    cx'.prom = cx.prom.erase ts ∧ cx'.mem = cx.mem ∧ ts ≤ cx'.views.getCoh l := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · by_cases hne : ts = t
    · subst hne
      refine ⟨rfl, rfl, ?_⟩
      rw [afterWrite_getCoh]
      simp only [↓reduceIte]
      exact Nat.le_max_right _ _
    · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
  · exfalso
    apply hout
    simp only [afterWrite]
    have hne : ts ≠ cx.mem.last + 1 := fun he => Nat.not_succ_le_self _ (he ▸ hb ts hin)
    exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

/-- **A live fulfilment** (the store step of `EvTree.RelFulfilsLive`): a write
that removes the outstanding promise `ts` and leaves no promise dead
(`Ctx.NoDead`) fulfils the message `(l, v)` at `ts`, is allowed at `ts`, and
every other outstanding promise at `l` lies above `ts` (else the raised
`coh l ≥ ts` would make it dead). -/
theorem writeSuccs_fulfil_live {cx cx' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : cx' ∈ writeSuccs A tid iv cx k xcl l v tr extra)
    (hb : ∀ p ∈ cx.prom, p ≤ cx.mem.last) {ts : Time} (hin : ts ∈ cx.prom) (hout : ts ∉ cx'.prom)
    (hnd : cx'.NoDead) :
    (∃ w, cx.mem.get? ts = some w ∧ w.loc = l ∧ w.val = v) ∧ WriteOk A tid iv cx k l tr extra ts ∧
      ∀ p ∈ cx.prom, p ≠ ts → ∀ w, cx.mem.get? p = some w → w.loc = l → ts < p := by
  refine ⟨writeSuccs_unpromise h hin hout, writeSuccs_fulfil_writeOk h hb hin hout, fun p hpt hne w hw hwl => ?_⟩
  obtain ⟨hpr, hmem, hcoh⟩ := writeSuccs_fulfil_coh h hb hin hout
  have h1 := hnd p (by rw [hpr]; exact (List.mem_erase_of_ne hne).mpr hpt) w (by rw [hmem]; exact hw)
  rw [hwl] at h1
  exact Nat.lt_of_le_of_lt hcoh (Nat.lt_of_le_of_lt (Nat.le_max_left _ _) h1)

end Machine

/-! ## The lock's predicate -/

/-- The lock's release predicate is impure at `0`. -/
theorem lock_impure {P : Sys} {g : Ghost} (hW : World P g) : ¬ Pred.Pure (g.rel P.Lk) 0#128 := fun h => by
  rw [hW.1] at h
  rcases h default 0 (by first | rfl | decide) with ⟨_, _, _, ⟨hq, _⟩, _⟩ | ⟨hq, _⟩
  · simp [Res.unit, Perm.unit] at hq
  · simp [Res.unit, Perm.unit] at hq

/-! ## Counting -/

/-- `S[tid := true]`. -/
def setTrue (S : Nat → Bool) (tid : Nat) : Nat → Bool := fun j => if j = tid then true else S j

theorem filter_setTrue_length {S : Nat → Bool} {tid : Nat} (hS : S tid = false) :
    ∀ n, tid < n → ((List.range n).filter (setTrue S tid)).length = ((List.range n).filter S).length + 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rw [List.range_succ, List.filter_append, List.filter_append, List.length_append, List.length_append]
    by_cases hn : tid < n
    · rw [ih hn]
      have : setTrue S tid n = S n := by simp [setTrue, show n ≠ tid by omega]
      simp only [List.filter_cons, List.filter_nil, this]
      omega
    · have htn : tid = n := by omega
      subst htn
      have heq : (List.range tid).filter (setTrue S tid) = (List.range tid).filter S := by
        apply List.filter_congr
        intro j hj
        have : j ≠ tid := by have := List.mem_range.mp hj; omega
        simp [setTrue, this]
      rw [heq]
      simp [setTrue, hS]

/-! ## The release split -/

section Split

variable {P : Sys} {tid : Nat} {S : Nat → Bool}

open Classical in
/-- The fractions the unlock message carries: the pool for `S[tid := true]`
and a share `δ` of the lock. -/
noncomputable def relFrac (P : Sys) (tid : Nat) (S : Nat → Bool) (δ : Rat) (x : Loc) : Rat :=
  if x = P.C then 1 else if x = P.Lk then δ else if x = P.F tid then 1
  else if ∃ j < P.N, j ≠ tid ∧ S j = false ∧ x = P.K j then 1 / 2
  else if ∃ j < P.N, j ≠ tid ∧ S j = true ∧ x = P.F j then 1 else 0

theorem relFrac_nonneg {δ : Rat} (hδ : 0 ≤ δ) (x : Loc) : 0 ≤ relFrac P tid S δ x := by
  unfold relFrac
  repeat' split
  all_goals first | exact hδ | grind

theorem relFrac_le {r : Res} (hH : Holding P tid S r) {δ : Rat}
    (hδ : δ ≤ (r.wr P.Lk).q) (x : Loc) : relFrac P tid S δ x ≤ (r.wr x).q := by
  obtain ⟨hC, -, htid, -, hF, -, hj⟩ := hH
  unfold relFrac
  split
  · next h => subst h; rw [hC]; exact Rat.le_refl
  split
  · next h => subst h; exact hδ
  split
  · next h => subst h; exact hF
  split
  · next h =>
    obtain ⟨j, hjN, hne, hS, rfl⟩ := h
    exact (hj j hjN hne).1 hS
  split
  · next h =>
    obtain ⟨j, hjN, hne, hS, rfl⟩ := h
    exact (hj j hjN hne).2 hS
  · exact (r.wr x).nonneg

theorem relFrac_C {δ : Rat} : relFrac P tid S δ P.C = 1 := by simp [relFrac]

theorem relFrac_Lk (hL : SpinLocs P.N P.Lk P.C P.K P.F) {δ : Rat} : relFrac P tid S δ P.Lk = δ := by
  simp [relFrac, hL.lk_c]

theorem relFrac_Ktid (hL : SpinLocs P.N P.Lk P.C P.K P.F) (htid : tid < P.N) {δ : Rat} :
    relFrac P tid S δ (P.K tid) = 0 := by
  have h1 := hL.k_c tid htid
  have h2 := hL.k_lk tid htid
  have h3 := hL.k_f tid htid tid htid
  have h4 : ¬ ∃ j < P.N, j ≠ tid ∧ S j = false ∧ P.K tid = P.K j :=
    fun ⟨j, hj, hne, _, he⟩ => hne (hL.k_inj tid htid j hj he).symm
  have h5 : ¬ ∃ j < P.N, j ≠ tid ∧ S j = true ∧ P.K tid = P.F j :=
    fun ⟨j, hj, _, _, he⟩ => hL.k_f tid htid j hj he
  simp [relFrac, h1, h2, h3, h4, h5]

/-- The message's part is the pool for `S[tid := true]`. -/
theorem relFrac_pool (hL : SpinLocs P.N P.Lk P.C P.K P.F) (htid : tid < P.N) {r : Res} {δ : Rat} (hδ : 0 ≤ δ)
    (hfle : ∀ x, relFrac P tid S δ x ≤ (r.wr x).q) :
    Pool P.N P.C P.K P.F (setTrue S tid) (r.take (relFrac P tid S δ) (relFrac_nonneg hδ)) := by
  refine ⟨by rw [Res.take_q, relFrac_C], fun j hj => ⟨fun hS => ?_, fun hS => ?_⟩⟩
  · have hne : j ≠ tid := by intro h; subst h; simp [setTrue] at hS
    have hSj : S j = false := by simpa [setTrue, hne] using hS
    rw [Res.take_q]
    have h4 : ∃ i < P.N, i ≠ tid ∧ S i = false ∧ P.K j = P.K i := ⟨j, hj, hne, hSj, rfl⟩
    simp [relFrac, hL.k_c j hj, hL.k_lk j hj, hL.k_f j hj tid htid, h4]
  · rw [Res.take_q]
    by_cases hne : j = tid
    · subst hne
      simp [relFrac, hL.f_c j hj, hL.f_lk j hj]
    · have hSj : S j = true := by simpa [setTrue, hne] using hS
      have hFF : P.F j ≠ P.F tid := fun h => hne (hL.f_inj j hj tid htid h)
      have h4 : ¬ ∃ i < P.N, i ≠ tid ∧ S i = false ∧ P.F j = P.K i :=
        fun ⟨i, hi, _, _, he⟩ => hL.k_f i hi j hj he.symm
      have h5 : ∃ i < P.N, i ≠ tid ∧ S i = true ∧ P.F j = P.F i := ⟨j, hj, hne, hSj, rfl⟩
      simp [relFrac, hL.f_c j hj, hL.f_lk j hj, hFF, h4, h5]

/-- **The release split** (see the module doc): `r ⊎ {(0, tw)}` is `r' ⋅ R`
with `R` (no acquire ids) satisfying `Good` at `tw` or `Bad`, and `r'` keeping
`K tid` whole, the write set of `Lk` (plus `(0, tw)`) and, clean, `Post`.
`hlt`: every own write of `Lk` is below `tw`; `hvw`: the counter's maximal
write of the `Good` case is below `tw`. -/
theorem release_split (hL : SpinLocs P.N P.Lk P.C P.K P.F) {r : Res} {k : Nat} (hH : Holding P tid S r)
    {cl : Prop} {vw : View}
    (hm : cl → 1 / P.N ≤ (r.wr P.Lk).q ∧
      ((∃ ts, CounterMax P (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ vw) ∨ 1 / P.N < (r.wr P.Lk).q))
    {tw : Time} (hlt : ∀ p, (r.wr P.Lk).X p → p.2 < tw) (hvw : vw < tw) :
    ∃ R r', r'.op R = r.addW P.Lk (0#128, tw) ∧ (∀ y ι, R.acq y ι = 0) ∧
      (Good P.N P.C P.K P.F tw R ∨ Bad P.N P.Lk P.C P.K P.F R) ∧ 1 ≤ (r'.wr (P.K tid)).q ∧
      (∀ p, (r'.wr P.Lk).X p → (r.wr P.Lk).X p ∨ p = (0#128, tw)) ∧ (cl → Post P.N P.Lk P.K r') ∧
      (r'.wr P.C).q = 0 ∧ 0 < (r'.wr P.Lk).q := by
  have hH' := hH
  obtain ⟨hC, hSt, htid, hK, -, hpos, -⟩ := hH'
  have hlc : P.Lk ≠ P.C := hL.lk_c
  have hN : (0 : Rat) < 1 / P.N := by
    have : (0 : Rat) < P.N := by exact_mod_cast (Nat.lt_of_le_of_lt (Nat.zero_le _) htid)
    rw [Rat.div_def, Rat.one_mul]; exact Rat.inv_pos.mpr this
  -- the share of the lock the message takes, and its mode
  obtain ⟨δ, hδ0, hδq, hmode, hpost, hδlt⟩ : ∃ δ : Rat, 0 ≤ δ ∧ δ ≤ (r.wr P.Lk).q ∧
      ((δ = 0 ∧ ∃ ts, CounterMax P (BitVec.ofNat 128 (k + 1)) ts r ∧ k = ((List.range P.N).filter S).length ∧
        ts ≤ vw) ∨ 0 < δ) ∧ (cl → 1 / P.N ≤ (r.wr P.Lk).q - δ) ∧ δ < (r.wr P.Lk).q := by
    by_cases hcl : cl
    · obtain ⟨h1, h2 | h2⟩ := hm hcl
      · exact ⟨0, Rat.le_refl, by grind, .inl ⟨rfl, h2⟩, fun _ => by grind, hpos⟩
      · exact ⟨(r.wr P.Lk).q - 1 / P.N, by grind, by grind, .inr (by grind), fun _ => by grind, by grind⟩
    · exact ⟨(r.wr P.Lk).q / 2, by grind, by grind, .inr (by grind), fun h => absurd h hcl, by grind⟩
  let rp := r.addW P.Lk (0#128, tw)
  have hqp : ∀ x, (rp.wr x).q = (r.wr x).q := fun x => Res.addW_q _ _ _ _
  have hfle : ∀ x, relFrac P tid S δ x ≤ (rp.wr x).q := fun x => by
    rw [hqp]; exact relFrac_le hH hδq x
  have hf0 := relFrac_nonneg (P := P) (tid := tid) (S := S) hδ0
  refine ⟨rp.take _ hf0, rp.leave _ hfle, Res.leave_op_take _ _ hf0 hfle, fun _ _ => rfl, ?_, ?_, ?_, ?_,
    by rw [Res.leave_q, hqp, relFrac_C, hC]; grind, by rw [Res.leave_q, hqp, relFrac_Lk hL]; grind⟩
  · -- the message's part
    have hpool := relFrac_pool hL htid hδ0 hfle
    rcases hmode with ⟨rfl, ts, ⟨hX, hmax⟩, hk, hts⟩ | hδ
    · refine .inl ⟨k + 1, setTrue S tid, ts, hpool, ?_, fun p hp => ?_, ?_, ?_⟩
      · rw [Res.take_X_pos _ _ _ (by rw [relFrac_C]; decide), Res.addW_wr_ne _ _ (Ne.symm hlc)]
        exact hX
      · rw [Res.take_X_pos _ _ _ (by rw [relFrac_C]; decide), Res.addW_wr_ne _ _ (Ne.symm hlc)] at hp
        exact hmax p hp
      · rw [filter_setTrue_length hSt _ htid, hk]
      · omega_t
    · refine .inr ⟨?_, _, hpool⟩
      rw [Res.take_q, relFrac_Lk hL]; exact hδ
  · rw [Res.leave_q, hqp, relFrac_Ktid hL htid]; grind
  · intro p hp
    rw [Res.leave_X, Res.addW_X_self] at hp
    rcases hp.2 with h | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  · intro hcl
    have h1 := hpost hcl
    refine ⟨⟨tid, htid, by rw [Res.leave_q, hqp, relFrac_Ktid hL htid]; grind⟩, by
      rw [Res.leave_q, hqp, relFrac_Lk hL]; exact h1, fun p hp hp0 => ?_⟩
    have hne : (r.wr P.Lk).q - δ ≠ 0 := by grind
    refine ⟨(0#128, tw), ?_, rfl, ?_⟩
    · rw [Res.leave_X, hqp, relFrac_Lk hL, Res.addW_X_self]
      exact ⟨hne, .inr ⟨hpos, rfl⟩⟩
    · rw [Res.leave_X, Res.addW_X_self] at hp
      rcases hp.2 with h | ⟨-, rfl⟩
      · exact hlt p h
      · exact absurd rfl hp0

end Split

end Kraken.Promising.SLR.SpinCommon
