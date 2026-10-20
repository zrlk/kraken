/-
**A generic `PromiseFresh'` discharge for single-RMW
dispenser programs** (ticket lock, layer F). ISA-neutral.

`theorem1IIPureX_G₀_S (tx_promiseLaw D)` (`SLR/TicketRule.lean`,
`SLR/TicketX.lean`) needs `PromiseFresh' G₀ A fuel states initMem D.XFresh`:
on every real path from `Config.init states initMem` to a final
configuration, a promise to the counter `x = D.x` writes the next rank
(`xCount + 1`) and its thread has no message to `x` yet. This file proves it
for every program of the following shape, at every prepay guard `G` (the
conclusion holds of every promise, `RelFulfilled'` or not):

- `SingleRmwDispenser A fuel x N states initMem Bef Aft`: each thread `tid`
  runs in two phases, `Bef tid` / `Aft tid` (predicates on its states; the
  initial state is `Bef`). At every reachable state in `Bef`, the next
  instruction's tree is `EvTree.BefX x N` (no store to `x`; an RMW on `x`
  that writes writes `old + 1` when `old < N`, and continues in `Aft`); at
  every reachable state in `Aft`, it is `EvTree.AftX x` (no message to `x`).
  So a thread writes `x` only by its hand-out RMW, at most once.
- the initial value of `x` is `0`, and there are at most `N` threads.

`promiseFresh_of_singleRmwDispenser` is the result;
`theorem1IIPureX_G₀_S_singleRmw` plugs it into `theorem1IIPureX_G₀_S`.

The proof, on a path `π` to a final configuration:
1. `phaseInv_path`: every thread is `Aft`, or `Bef` with all its messages to
   `x` outstanding promises (`PhaseInv`); `aft_persist`: `Aft` persists.
2. `removal_handOut`: the step that removes a thread's promise to `x` is its
   hand-out RMW (`stepOne_befX`), from a state not in `Aft`, into `Aft`.
   Hence (`aft_noXProm`) an `Aft` thread holds no promise to `x`.
3. `promise_xFresh`: a promise to `x` at step `J` is removed later by the
   thread's hand-out, so the thread was in `Bef` at `J`; any other message to
   `x` of the thread would be a promise removed by a second hand-out (or by
   the same one, which removes one promise to `x` only): none. The hand-out
   reads `(x, tr)` atomically up to the promise, so it reads the rank
   `xCount (π.cfg J).mem |M_J|`, below `N` by pigeonhole
   (`CountInv.old_lt`), and writes it plus one.
4. `countInv_path`: `CountInv` (`SLR/TicketX.lean`) on every configuration,
   by induction, with step 3 at promise steps and
   `CountInv.xFresh_of_atomic` at an appending hand-out.
-/
import Kraken.Promising.SLR.DispenserRun

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`). -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **A single-RMW dispenser program** on `x` with bound `N` (see the module
docstring): phases `Bef tid` / `Aft tid` of each thread `tid`; every initial
state is `Bef`; at every reachable state, a `Bef` state's next instruction
is `EvTree.BefX x N` and an `Aft` state's is `EvTree.AftX x`. -/
structure SingleRmwDispenser (A : Arch) (fuel : Nat) (x : Loc) (N : Nat) (states : List I.State)
    (initMem : List (Loc × Val)) (Bef Aft : Nat → I.State → Prop) : Prop where
  init : ∀ tid st, states[tid]? = some st → Bef tid st
  bef : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I) tree,
    c.threads[tid]? = some t → Bef tid t.st → I.exec t.st = some tree → tree.BefX x N (Bef tid) (Aft tid)
  aft : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I) tree,
    c.threads[tid]? = some t → Aft tid t.st → I.exec t.st = some tree → tree.AftX x (Aft tid)

/-- **`SingleRmwDispenser` from per-cell facts** under a thread-local
invariant `Jinv` of the reachable states (as `promisePure_of_relWritesT`). -/
theorem SingleRmwDispenser.ofCells {A : Arch} {fuel : Nat} {x : Loc} {N : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {Bef Aft : Nat → I.State → Prop} (Jinv : Nat → I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t.st)
    (hinit : ∀ tid st, states[tid]? = some st → Bef tid st)
    (hbef : ∀ tid st tree, Jinv tid st → Bef tid st → I.exec st = some tree → tree.BefX x N (Bef tid) (Aft tid))
    (haft : ∀ tid st tree, Jinv tid st → Aft tid st → I.exec st = some tree → tree.AftX x (Aft tid)) :
    SingleRmwDispenser A fuel x N states initMem Bef Aft where
  init := hinit
  bef c hc tid t tree ht hb hex := hbef tid t.st tree (hJ c hc tid t ht) hb hex
  aft c hc tid t tree ht ha hex := haft tid t.st tree (hJ c hc tid t ht) ha hex

namespace SingleRmw

/-! ## Machine steps -/

/- `succ_cases'`: a machine step is an instruction step or a promise step
(alias of the neutral `SLR.succ_cases'`, `SLR/StepRunCommon.lean`). -/
hoist_alias [Kraken.Promising.SLR.succ_cases' ↦ Kraken.Promising.SLR.SingleRmw.succ_cases']

theorem init_thread {states : List I.State} {initMem : List (Loc × Val)} {tid : Nat} {t : Thread I}
    (ht : (Config.init states initMem : Config I).threads[tid]? = some t) : states[tid]? = some t.st ∧ t.prom = [] := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map] at ht
  cases h : states[tid]? with
  | none => rw [h] at ht; cases ht
  | some st =>
    rw [h] at ht
    cases ht
    exact ⟨rfl, rfl⟩

theorem init_get? {states : List I.State} {initMem : List (Loc × Val)} {ts : Time} :
    (Config.init states initMem : Config I).mem.get? ts = none := by
  simp [Config.init, Memory.get?]

/-! ## The phase invariant -/

/-- **The phase invariant**: every thread is `Aft`, or `Bef` with all its
messages to `x` outstanding promises. -/
def PhaseInv (x : Loc) (Bef Aft : Nat → I.State → Prop) (c : Config I) : Prop :=
  ∀ tid t, c.threads[tid]? = some t → Aft tid t.st ∨
    (Bef tid t.st ∧ ∀ ts w, c.mem.get? ts = some w → w.loc = x → w.tid = tid → ts ∈ t.prom)

variable {A : Arch} {fuel : Nat} {x : Loc} {N : Nat} {states : List I.State} {initMem : List (Loc × Val)}
  {Bef Aft : Nat → I.State → Prop}

theorem phaseInv_init (hS : SingleRmwDispenser A fuel x N states initMem Bef Aft) :
    PhaseInv x Bef Aft (Config.init states initMem : Config I) := by
  intro tid t ht
  exact .inr ⟨hS.init tid t.st (init_thread ht).1, fun ts w hw => by rw [init_get?] at hw; cases hw⟩

/-- **The phase invariant is preserved by every machine step** from a
reachable configuration. -/
theorem phaseInv_step [I.LawfulState] (hS : SingleRmwDispenser A fuel x N states initMem Bef Aft)
    {c c' : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hs : c' ∈ (succs A c fuel).1)
    (hP : PhaseInv x Bef Aft c) : PhaseInv x Bef Aft c' := by
  rcases succ_cases' hs with ⟨j, tj, outs, o, hj, hstep, ho, rfl⟩ | ⟨j, tj, pw, hj, -, rfl⟩
  · -- the messages to `x` after the step: old ones, or by `j`
    have hnew : ∀ ts w, o.mem.get? ts = some w → w.loc = x → c.mem.get? ts = some w ∨ w.tid = j := by
      intro ts w hw hl
      rcases hP j tj hj with ha | ⟨hb, -⟩
      · exact .inl ((stepOne_aftX A hstep ho (hS.aft c hc j tj · hj ha)).1.1.2 ts w hw hl)
      · rcases stepOne_befX A hstep ho (hS.bef c hc j tj · hj hb) with ⟨hk, -⟩ | ⟨⟨t', hh⟩, -⟩
        · exact .inl (hk.1.2 ts w hw hl)
        · exact hh.xmsg hw hl
    intro i ti hi
    rw [Config.withThread_get? _ _ _ (lt_size_of_get? hj)] at hi
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte, Option.some.injEq] at hi
      subst hi
      rcases hP j tj hj with ha | ⟨hb, hown⟩
      · exact .inl (stepOne_aftX A hstep ho (hS.aft c hc j tj · hj ha)).2
      · rcases stepOne_befX A hstep ho (hS.bef c hc j tj · hj hb) with ⟨hk, hb' | ha'⟩ | ⟨-, ha'⟩
        · exact .inr ⟨hb', fun ts w hw hl ht =>
            hk.2 ts w (hown ts w (hk.1.2 ts w hw hl) hl ht) (hk.1.2 ts w hw hl) hl⟩
        · exact .inl ha'
        · exact .inl ha'
    · simp only [hij, ↓reduceIte] at hi
      rcases hP i ti hi with ha | ⟨hb, hown⟩
      · exact .inl ha
      · refine .inr ⟨hb, fun ts w hw hl ht => ?_⟩
        rcases hnew ts w hw hl with h | h
        · exact hown ts w h hl ht
        · exact absurd (h.symm.trans ht) hij
  · intro i ti hi
    rw [Config.withThread_get? _ _ _ (lt_size_of_get? hj)] at hi
    by_cases hij : j = i
    · subst hij
      simp only [↓reduceIte, Option.some.injEq] at hi
      subst hi
      rcases hP j tj hj with ha | ⟨hb, hown⟩
      · exact .inl ha
      · refine .inr ⟨hb, fun ts w hw hl ht => ?_⟩
        rcases Dispenser.get?_append_cases hw with ⟨-, hg⟩ | ⟨rfl, -⟩
        · exact List.mem_append_left _ (hown ts w hg hl ht)
        · exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [hij, ↓reduceIte] at hi
      rcases hP i ti hi with ha | ⟨hb, hown⟩
      · exact .inl ha
      · refine .inr ⟨hb, fun ts w hw hl ht => ?_⟩
        rcases Dispenser.get?_append_cases hw with ⟨-, hg⟩ | ⟨-, rfl⟩
        · exact hown ts w hg hl ht
        · exact absurd ht hij

/-- **`Aft` persists** across a machine step from a reachable
configuration. -/
theorem aft_step [I.LawfulState] (hS : SingleRmwDispenser A fuel x N states initMem Bef Aft)
    {c c' : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hs : c' ∈ (succs A c fuel).1)
    {j : Nat} {t : Thread I} (ht : c.threads[j]? = some t) (ha : Aft j t.st) :
    ∃ t', c'.threads[j]? = some t' ∧ Aft j t'.st := by
  rcases succ_cases' hs with ⟨i, ti, outs, o, hi, hstep, ho, rfl⟩ | ⟨i, ti, pw, hi, -, rfl⟩
  · rw [Config.withThread_get? _ _ _ (lt_size_of_get? hi)]
    by_cases hij : i = j
    · subst hij
      rw [hi] at ht; cases ht
      exact ⟨o.thread, by simp, (stepOne_aftX A hstep ho (hS.aft c hc i _ · hi ha)).2⟩
    · simp only [hij, ↓reduceIte]
      exact ⟨t, ht, ha⟩
  · rw [Config.withThread_get? _ _ _ (lt_size_of_get? hi)]
    by_cases hij : i = j
    · subst hij
      rw [hi] at ht; cases ht
      simp only [↓reduceIte]
      exact ⟨_, rfl, ha⟩
    · simp only [hij, ↓reduceIte]
      exact ⟨t, ht, ha⟩

/-! ## Along a path -/

section PathLemmas

variable [I.LawfulState] (hS : SingleRmwDispenser A fuel x N states initMem Bef Aft) {π : Path A fuel I}
  (h0 : π.cfg 0 = Config.init states initMem)
include hS h0

omit [I.LawfulState] hS in
theorem reach_init {q : Nat} (hq : q ≤ π.len) : Reachable A fuel (Config.init states initMem) (π.cfg q) := by
  rw [← h0]; exact π.reachable q hq

/-- `PhaseInv` on every configuration of the path. -/
theorem phaseInv_path : ∀ q, q ≤ π.len → PhaseInv x Bef Aft (π.cfg q)
  | 0, _ => by rw [h0]; exact phaseInv_init hS
  | q + 1, hq => phaseInv_step hS (reach_init h0 (by omega)) (π.step q (by omega))
      (phaseInv_path q (by omega))

/-- `Aft` persists along the path. -/
theorem aft_persist {q q' j : Nat} {t : Thread I} (hqq : q ≤ q') (hq' : q' ≤ π.len)
    (ht : (π.cfg q).threads[j]? = some t) (ha : Aft j t.st) : ∃ t', (π.cfg q').threads[j]? = some t' ∧ Aft j t'.st := by
  obtain ⟨d, rfl⟩ : ∃ d, q' = q + d := ⟨q' - q, by omega⟩
  induction d with
  | zero => exact ⟨t, ht, ha⟩
  | succ d ih =>
    obtain ⟨t1, h1, h2⟩ := ih (by omega) (by omega)
    exact aft_step hS (reach_init h0 (by omega)) (π.step (q + d) (by omega)) h1 h2

/-- **The removal of a promise to `x` is the hand-out**: the step `f` that
removes thread `j`'s outstanding promise `ts` to `x` runs `j`'s hand-out RMW,
writing at `ts`, from a state not in `Aft`, into `Aft`. -/
theorem removal_handOut (hP : ∀ q, q ≤ π.len → PhaseInv x Bef Aft (π.cfg q)) {f j : Nat} {ts : Time} {w : Msg}
    (hf : f < π.len) (hh : HoldsProm (π.cfg f) j ts) (hn : ¬ HoldsProm (π.cfg (f + 1)) j ts)
    (hw : (π.cfg f).mem.get? ts = some w) (hl : w.loc = x) :
    ∃ tf tf', (π.cfg f).threads[j]? = some tf ∧ ¬ Aft j tf.st ∧ (π.cfg (f + 1)).threads[j]? = some tf' ∧
      Aft j tf'.st ∧ HandOut x N j tf.prom (π.cfg f).mem tf'.prom (π.cfg (f + 1)).mem ts := by
  obtain ⟨tf, outs, o, htf, hstep, ho, htf', hmf, hin, hout⟩ := removal_is_instr (succs_cases (π.step f hf)) hh hn
  have hc := reach_init h0 (Nat.le_of_lt hf)
  have hnA : ¬ Aft j tf.st := fun ha =>
    hout ((stepOne_aftX A hstep ho (hS.aft _ hc j tf · htf ha)).1.2 ts w hin hw hl)
  rcases hP f (Nat.le_of_lt hf) j tf htf with ha | ⟨hb, -⟩
  · exact absurd ha hnA
  rcases stepOne_befX A hstep ho (hS.bef _ hc j tf · htf hb) with ⟨hk, -⟩ | ⟨⟨t', hh'⟩, ha'⟩
  · exact absurd (hk.2 ts w hin hw hl) hout
  · have hts : ts = t' := by
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpr⟩ := hh'
      exact hout (hpr ts w hin hw hl hne)
    subst hts
    exact ⟨tf, o.thread, htf, hnA, htf', ha', by rw [hmf]; exact hh'⟩

/-- **An `Aft` thread holds no promise to `x`** on a path to a final
configuration (it would have to be removed by a hand-out, from a state not
in `Aft`). -/
theorem aft_noXProm (hfin : (π.cfg π.len).final = true) (hP : ∀ q, q ≤ π.len → PhaseInv x Bef Aft (π.cfg q))
    {q j : Nat} {t : Thread I} {ts : Time} {w : Msg} (hq : q ≤ π.len) (ht : (π.cfg q).threads[j]? = some t)
    (ha : Aft j t.st) (hts : ts ∈ t.prom) (hw : (π.cfg q).mem.get? ts = some w) (hl : w.loc = x) : False := by
  rcases Nat.lt_or_ge q π.len with hlt | hge
  · cases q with
    | zero =>
      rw [h0] at ht
      rw [(init_thread ht).2] at hts
      cases hts
    | succ J =>
      obtain ⟨f, hJf, hf, hheld, hgone⟩ := π.first_removal hfin (J := J) (by omega) ⟨t, ht, hts⟩
      have hwf : (π.cfg f).mem.get? ts = some w := by
        rw [(π.mem_prefix (j := J + 1) (by omega) (Nat.le_of_lt hf)).get? ((π.cfg (J + 1)).mem.last_le_of_get?_eq_some hw)]
        exact hw
      obtain ⟨tf, _, htf, hnA, -⟩ := removal_handOut hS h0 hP hf (hheld f hJf (Nat.le_refl f)) hgone hwf hl
      obtain ⟨t', h1, h2⟩ := aft_persist hS h0 (q := J + 1) (q' := f) (by omega) (Nat.le_of_lt hf) ht ha
      rw [htf] at h1
      cases h1
      exact hnA h2
  · obtain rfl : q = π.len := by omega
    rw [Config.final_prom hfin ht] at hts
    cases hts

end PathLemmas

/-! ## Freshness of promises and the counting invariant -/

/- `Dispenser.CountInv.xsame` (`CountInv` transfers to a memory with no new
message to `x`) is in `SLR/TicketX.lean` (same name). -/

/-- **A promise to `x` is fresh** (the core of `PromiseFresh'`): on a path to
a final configuration, with `CountInv` at the promise step `J`, a promise of
thread `j` to `x` writes `xCount |M_J| + 1`, and `j` has no message to `x` in
`M_J`. -/
theorem promise_xFresh [I.LawfulState] {π : Path A fuel I} (D : Dispenser) (hS : SingleRmwDispenser A fuel D.x D.N states initMem Bef Aft)
    (h0 : π.cfg 0 = Config.init states initMem) (hfin : (π.cfg π.len).final = true)
    (hP : ∀ q, q ≤ π.len → PhaseInv D.x Bef Aft (π.cfg q)) {J : Nat} (hJ : J < π.len) (hC : D.CountInv (π.cfg J))
    {j : Nat} {t : Thread I} {pw : Msg × View} (ht : (π.cfg J).threads[j]? = some t)
    (hstep : π.cfg (J + 1) = (π.cfg J).withThread j
      { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1) :
    D.XFresh (π.cfg J).mem { pw.1 with tid := j } := by
  refine (Classical.em (pw.1.loc = D.x)).elim (fun hx => ?_) (fun hx h => absurd h hx)
  have hsz := lt_size_of_get? ht
  have hJ1 : (π.cfg (J + 1)).threads[j]? =
      some { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] } := by
    rw [hstep, Config.withThread_get? _ _ _ hsz]; simp
  have hm1 : (π.cfg (J + 1)).mem = ((π.cfg J).mem.append { pw.1 with tid := j }).1 := by rw [hstep]; rfl
  have hh : HoldsProm (π.cfg (J + 1)) j ((π.cfg J).mem.last + 1) :=
    ⟨_, hJ1, List.mem_append_right _ (List.mem_singleton_self _)⟩
  obtain ⟨f, hJf, hf, hheld, hgone⟩ := π.first_removal hfin hJ hh
  have hwf : (π.cfg f).mem.get? ((π.cfg J).mem.last + 1) = some { pw.1 with tid := j } := by
    rw [(π.mem_prefix (j := J + 1) (by omega) (Nat.le_of_lt hf)).get? (by rw [hm1, Memory.last_append]; exact Nat.le_refl _),
      hm1]
    exact Memory.get?_append_last _ _
  obtain ⟨tf, tf', htf, hnA, htf', haf', H⟩ := removal_handOut hS h0 hP hf (hheld f hJf (Nat.le_refl f)) hgone hwf hx
  -- `j` is not `Aft` at `J`, so `Bef` with its messages to `x` outstanding
  have hnAJ : ¬ Aft j t.st := fun ha => by
    obtain ⟨t'', h1, h2⟩ := aft_persist hS h0 (q := J) (q' := f) (by omega) (Nat.le_of_lt hf) ht ha
    rw [htf] at h1
    cases h1
    exact hnA h2
  obtain ⟨-, hownJ⟩ := (hP J (Nat.le_of_lt hJ) j t ht).resolve_left hnAJ
  -- `j` has no message to `x` at `J`
  have hown : ∀ ts w', (π.cfg J).mem.get? ts = some w' → w'.loc = D.x → w'.tid ≠ j := by
    intro ts w' hw' hl' htid
    have hh' : HoldsProm (π.cfg (J + 1)) j ts := ⟨_, hJ1, List.mem_append_left _ (hownJ ts w' hw' hl' htid)⟩
    have hle := (π.cfg J).mem.last_le_of_get?_eq_some hw'
    obtain ⟨f', hJf', hf', hheld', hgone'⟩ := π.first_removal hfin hJ hh'
    have hwf' : (π.cfg f').mem.get? ts = some w' := by
      rw [(π.mem_prefix (j := J) (by omega) (Nat.le_of_lt hf')).get? hle]; exact hw'
    obtain ⟨_, _, htf2, hnA2, htf2', haf2', -⟩ :=
      removal_handOut hS h0 hP hf' (hheld' f' hJf' (Nat.le_refl f')) hgone' hwf' hl'
    rcases Nat.lt_trichotomy f f' with hlt | heq | hgt
    · obtain ⟨t3, h1, h2⟩ := aft_persist hS h0 (q := f + 1) (q' := f') hlt (Nat.le_of_lt hf') htf' haf'
      rw [htf2] at h1
      cases h1
      exact hnA2 h2
    · subst heq
      obtain ⟨tq, htq, htsq⟩ := hheld' f hJf' (Nat.le_refl f)
      rw [htf] at htq
      cases htq
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hpr⟩ := H
      exact hgone' ⟨tf', htf', hpr ts w' htsq hwf' hl' (by omega_t)⟩
    · obtain ⟨t3, h1, h2⟩ := aft_persist hS h0 (q := f' + 1) (q' := f) hgt (Nat.le_of_lt hf) htf2' haf2'
      rw [htf] at h1
      cases h1
      exact hnA h2
  -- the hand-out reads the rank and writes it plus one
  obtain ⟨m1, m2, tr, old, new, hX1, hrd, htr, hat, hop, hwr, -, -⟩ := H
  have hwnew : ({ pw.1 with tid := j } : Msg) = ⟨D.x, new, j⟩ := by
    rcases hwr with ⟨hg, -⟩ | ⟨he, -⟩
    · rw [hwf] at hg; exact Option.some.inj hg
    · exfalso
      have := (π.cfg f).mem.last_le_of_get?_eq_some hwf
      have := hX1.1.last_le
      omega_t
  have hpJ : (π.cfg J).mem.Prefix m1 := (π.mem_prefix (j := J) (j' := f) (by omega) (Nat.le_of_lt hf)).trans hX1.1
  have htr' : tr ≤ (π.cfg J).mem.last := by omega_t
  have hrdJ : (π.cfg J).mem.read? D.x tr = some old := by rw [← hpJ.read? htr']; exact hrd
  have hatJ : (π.cfg J).mem.atomic D.x j tr ((π.cfg J).mem.last + 1) = true := by
    rw [← Dispenser.atomic_prefix hpJ htr (Nat.le_refl _)]; exact hat
  have hlt : old.toNat < D.N := (hC.old_lt hrdJ hsz fun ts w' _ hw' hl' => hown ts w' hw' hl').1
  rw [hwnew]
  exact (hC.xFresh_of_atomic hrdJ hatJ hown hsz (hop hlt)).2

theorem countInv_init {D : Dispenser} (hx0 : ({ init := initMem, msgs := #[] } : Memory).initVal D.x = 0)
    (hN : states.length ≤ D.N) : D.CountInv (Config.init states initMem : Config I) where
  init := hx0
  rank _ _ hw := by rw [init_get?] at hw; cases hw
  wlt _ _ hw := by rw [init_get?] at hw; cases hw
  wdist _ _ _ _ hw := by rw [init_get?] at hw; cases hw
  sz := by simpa [Config.init] using hN

/-- **`CountInv` on every configuration of a path to a final
configuration.** -/
theorem countInv_path [I.LawfulState] {π : Path A fuel I} (D : Dispenser) (hS : SingleRmwDispenser A fuel D.x D.N states initMem Bef Aft)
    (h0 : π.cfg 0 = Config.init states initMem) (hfin : (π.cfg π.len).final = true)
    (hP : ∀ q, q ≤ π.len → PhaseInv D.x Bef Aft (π.cfg q))
    (hx0 : ({ init := initMem, msgs := #[] } : Memory).initVal D.x = 0) (hN : states.length ≤ D.N) :
    ∀ q, q ≤ π.len → D.CountInv (π.cfg q)
  | 0, _ => by rw [h0]; exact countInv_init hx0 hN
  | q + 1, hq => by
    have hC := countInv_path D hS h0 hfin hP hx0 hN q (by omega)
    have hqlen : q < π.len := by omega
    rcases succ_cases' (π.step q hqlen) with ⟨j, tj, outs, o, hj, hstep, ho, he⟩ | ⟨j, tj, pw, hj, -, he⟩
    · have hsz : (π.cfg (q + 1)).threads.size = (π.cfg q).threads.size := by
        rw [he]; exact Config.withThread_size ..
      have hm : (π.cfg (q + 1)).mem = o.mem := by rw [he]; rfl
      have hc := reach_init h0 (Nat.le_of_lt hqlen)
      rcases hP q (Nat.le_of_lt hqlen) j tj hj with ha | ⟨hb, hownq⟩
      · exact hC.xsame (by rw [hm]; exact (stepOne_aftX A hstep ho (hS.aft _ hc j tj · hj ha)).1.1) hsz
      · rcases stepOne_befX A hstep ho (hS.bef _ hc j tj · hj hb) with ⟨hk, -⟩ | ⟨⟨ts, H⟩, ha'⟩
        · exact hC.xsame (by rw [hm]; exact hk.1) hsz
        · have Hp := H.prefix
          obtain ⟨m1, m2, tr, old, new, hX1, hrd, htr, hat, hop, hwr, hX2, hpr⟩ := H
          rcases hwr with ⟨-, rfl⟩ | ⟨rfl, rfl⟩
          · exact hC.xsame (by rw [hm]; exact hX1.trans hX2) hsz
          · have hj1 : (π.cfg (q + 1)).threads[j]? = some o.thread := by
              rw [he, Config.withThread_get? _ _ _ (lt_size_of_get? hj)]; simp
            -- `j` has no message to `x` (it would stay a promise of the `Aft` thread `j`)
            have hown : ∀ ts w, (π.cfg q).mem.get? ts = some w → w.loc = D.x → w.tid ≠ j := by
              intro ts w hw hl htid
              have hle := (π.cfg q).mem.last_le_of_get?_eq_some hw
              have := hX1.1.last_le
              exact aft_noXProm hS h0 hfin hP (q := q + 1) hq hj1 ha'
                (hpr ts w (hownq ts w hw hl htid) hw hl (by omega_t))
                (by rw [hm, Hp.get? hle]; exact hw) hl
            let c1 : Config I := ⟨(π.cfg q).threads, m1⟩
            have hC1 : D.CountInv c1 := hC.xsame hX1 rfl
            have hown1 : ∀ ts w, m1.get? ts = some w → w.loc = D.x → w.tid ≠ j :=
              fun ts w hw hl => hown ts w (hX1.2 ts w hw hl) hl
            have hlt := (hC1.old_lt (c := c1) hrd (lt_size_of_get? hj) fun ts w _ => hown1 ts w).1
            have hfr := (hC1.xFresh_of_atomic (c := c1) hrd hat hown1 (lt_size_of_get? hj) (hop hlt)).2
            have hC2 : D.CountInv (⟨(π.cfg q).threads, (m1.append ⟨D.x, new, j⟩).1⟩ : Config I) :=
              hC1.append (c := c1) rfl hfr rfl fun _ => lt_size_of_get? hj
            exact hC2.xsame (by rw [hm]; exact hX2) hsz
    · have hfr := promise_xFresh D hS h0 hfin hP hqlen hC hj he
      exact hC.append (by rw [he]; rfl) hfr (by rw [he]; exact Config.withThread_size ..)
        fun _ => lt_size_of_get? hj

end SingleRmw

open SingleRmw in
/-- **`PromiseFresh'` for single-RMW dispenser programs** (the main result;
see the module docstring): a `SingleRmwDispenser` program on `D.x` with bound
`D.N`, with `x` initially `0` and at most `D.N` threads, satisfies
`PromiseFresh' G … D.XFresh` for every prepay guard `G`. -/
theorem promiseFresh_of_singleRmwDispenser [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} (D : Dispenser) {Bef Aft : Nat → I.State → Prop}
    (hS : SingleRmwDispenser A fuel D.x D.N states initMem Bef Aft)
    (hx0 : ({ init := initMem, msgs := #[] } : Memory).initVal D.x = 0) (hN : states.length ≤ D.N)
    (G : PrepayGuard I) : PromiseFresh' G A fuel states initMem D.XFresh := by
  intro π h0 hfin J hJ j t pw ht _ hstep _
  have hP := phaseInv_path hS h0
  exact promise_xFresh D hS h0 hfin hP hJ (countInv_path D hS h0 hfin hP hx0 hN J (Nat.le_of_lt hJ)) ht hstep

/-- **Theorem 1′ over `Erase ∧ TX D` for single-RMW dispenser programs**:
`theorem1IIPureX_G₀_S (tx_promiseLaw D)` with `PromiseFresh'` discharged by
`promiseFresh_of_singleRmwDispenser`. -/
theorem theorem1IIPureX_G₀_S_singleRmw [I.LawfulState] (A : Arch) (fuel : Nat) (D : Dispenser)
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost) {Bef Aft : Nat → I.State → Prop}
    (hNT : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : Erase rF g (fun _ => False) (Config.init states initMem)) (hX : D.TX g (Config.init states initMem))
    (hpend : ∀ ts, ts ∉ g.pend) (hpure : PromisePure' G₀ A fuel states initMem g.rel)
    (hS : SingleRmwDispenser A fuel D.x D.N states initMem Bef Aft)
    (hx0 : ({ init := initMem, msgs := #[] } : Memory).initVal D.x = 0) (hN : states.length ≤ D.N)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeP (modelX I D.TX) A B tid G₀ (K2Scope (model I) AllocIds) n m True (Config.init states initMem)
        (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hlive : c.Live A fuel) :
    ∃ v rF' g', c.VirtualOfG G₀ A v ∧ Erase rF' g' (fun _ => False) v ∧ D.TX g' v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' :=
  theorem1IIPureX_G₀_S (Dispenser.tx_promiseLaw D) A fuel B states initMem rF g hNT E hX hpend hpure
    (promiseFresh_of_singleRmwDispenser D hS hx0 hN G₀) hsafe c hc hlive

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.SingleRmw.phaseInv_path
#print axioms Kraken.Promising.SLR.SingleRmw.promise_xFresh
#print axioms Kraken.Promising.SLR.SingleRmw.countInv_path
#print axioms Kraken.Promising.SLR.promiseFresh_of_singleRmwDispenser
#print axioms Kraken.Promising.SLR.theorem1IIPureX_G₀_S_singleRmw
