import WeakCore.TermExtStep
/-! # TermPermit — (D4) what certification reads of the permits

Bundle obligation O6 (`certified_wake`), restated for the view-carrying permit (T4(A)).  A certificate of thread `q`
(`Solo … q`) reads no other thread's permit, and of its own only `permit.getD 0`: a permit-less `park` in a certificate
and a `park` on a permit carrying view 0 acquire the same view (`parkVs_norm`).  So a `wake` by thread `i` neither
creates nor destroys a certificate of `i` itself (its own `unpark` gives it view 0, `wake`'s `j = i` branch) nor of any
thread other than the one woken.  It CAN destroy the woken thread's certificate (the `park` in it then acquires the
larger view).  The proof normalises the permits (`erasePermits q`) and shows that each
`Solo … q` step commutes with the normalisation. -/

namespace TermPermit
open CoreLang CoreTerm TermRun TermExtStep
open WeakMem (Memory Ts Arch)

/-- (D4) A thread step neither reads nor changes the permit. -/
theorem tstep_permit (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (b : Option Ts) :
    tstep g mem pairs { th with permit := b } =
      (tstep g mem pairs th).map (fun r => (r.1, r.2.1, { r.2.2 with permit := b })) := by
  obtain ⟨term, env, σs, stack, vs, promises, nalloc, undefs, tidLbl, permit⟩ := th
  simp only [tstep]
  repeat' split
  all_goals (try simp [stOf, withS])
  all_goals (try simp only [ol, callFrame, enter])
  all_goals (try (generalize List.find? (fun x => x.name == _) g.p = o; cases o <;> simp <;>
    (generalize evalAt env _ = o2; cases o2 <;> simp)))
  all_goals (try simp [List.map_flatMap, List.map_map, Function.comp_def])
  all_goals (try (intro _ _ _; split <;> simp))

theorem tstep_permit_mem {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (h : r ∈ tstep g mem pairs th) : r.2.2.permit = th.permit := by
  have e := tstep_permit g mem pairs th th.permit
  rw [show ({ th with permit := th.permit } : TTh) = th from rfl] at e
  rw [e] at h
  obtain ⟨r0, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- The certified thread's permit, normalised: only `getD 0` is kept. -/
def normTh (th : TTh) : TTh := { th with permit := some (th.permit.getD 0) }

/-- Thread `m`'s permit, normalised for a certificate of thread `q`: `q`'s by `normTh`, every other one cleared. -/
def eraseTh (q m : Nat) (th : TTh) : TTh := if m = q then normTh th else { th with permit := none }

/-- A configuration with its permits normalised for a certificate of thread `q`. -/
def erasePermits (q : Nat) (c : Cfg) : Cfg := { c with ths := c.ths.mapIdx (eraseTh q) }

theorem eraseTh_self (q : Nat) (th : TTh) : eraseTh q q th = normTh th := by simp [eraseTh]

theorem eraseTh_idem (q m : Nat) (th : TTh) : eraseTh q m (eraseTh q m th) = eraseTh q m th := by
  by_cases h : m = q
  · subst h; simp only [eraseTh_self]; rfl
  · simp [eraseTh, h]

theorem eraseTh_promises (q m : Nat) (th : TTh) : (eraseTh q m th).promises = th.promises := by
  unfold eraseTh; split <;> rfl

/-- (D4) A `park` on a permit carrying view 0 acquires nothing: as a permit-less `park`. -/
theorem parkVs_norm (sz : Nat) (th : TTh) : parkVs sz (normTh th) = parkVs sz th := by
  simp only [parkVs, normTh]
  rcases hp : th.permit with _ | v
  · simp only [Option.getD_none, Nat.zero_min, Nat.max_zero]
  · rfl

theorem erase_get (q : Nat) (c : Cfg) (j : Nat) : (erasePermits q c).ths[j]? = (c.ths[j]?).map (eraseTh q j) := by
  simp [erasePermits, Array.getElem?_mapIdx]

theorem erase_size (q : Nat) (c : Cfg) : (erasePermits q c).ths.size = c.ths.size := by simp [erasePermits]

theorem erase_n (q : Nat) (c : Cfg) : (erasePermits q c).n = c.n := by
  unfold Cfg.n; rw [erase_size]; rfl

theorem mapIdx_set (q i : Nat) (A : Array TTh) (t : TTh) :
    (A.set! i t).mapIdx (eraseTh q) = (A.mapIdx (eraseTh q)).set! i (eraseTh q i t) := by
  simp only [Array.set!_eq_setIfInBounds, Array.mapIdx_setIfInBounds]

theorem mapIdx_idem (q : Nat) (A : Array TTh) : (A.mapIdx (eraseTh q)).mapIdx (eraseTh q) = A.mapIdx (eraseTh q) := by
  rw [Array.mapIdx_mapIdx]; congr 1; funext m t; exact eraseTh_idem q m t

theorem erase_erase (q : Nat) (c : Cfg) : erasePermits q (erasePermits q c) = erasePermits q c := by
  simp only [erasePermits, mapIdx_idem]

/-- Replacing thread `i` commutes with the normalisation, given the same normalised thread. -/
theorem erase_upd (q i : Nat) (c : Cfg) (mem : Memory) (pairs : List Ts) (tr : List Event) {t t' : TTh}
    (h : eraseTh q i t = eraseTh q i t') :
    erasePermits q { c with mem := mem, pairs := pairs, ths := c.ths.set! i t, trace := tr } =
      erasePermits q { c with mem := mem, pairs := pairs, ths := (erasePermits q c).ths.set! i t', trace := tr } := by
  simp only [erasePermits, mapIdx_set, mapIdx_idem, h]

theorem noPromises_erase (q : Nat) (c : Cfg) (i : Nat) : noPromises (erasePermits q c) i = noPromises c i := by
  unfold noPromises; rw [erase_get]; cases c.ths[i]? <;> simp [eraseTh_promises]

theorem eraseTh_tys (q m : Nat) (th : TTh) : (eraseTh q m th).tys = th.tys := by
  unfold eraseTh; by_cases h : m = q <;> simp [h, normTh]

theorem tysOf_erase (q : Nat) (c : Cfg) : tysOf (erasePermits q c) = tysOf c := by
  have h : (erasePermits q c).ths.toList.map TTh.tys = c.ths.toList.map TTh.tys := by
    apply List.ext_getElem
    · simp [erasePermits]
    · intro n h1 h2; simp [erasePermits, eraseTh_tys]
  funext l
  have e : ∀ d : Cfg, tysOf d l = (d.ths.toList.map TTh.tys).findSome? (fun ts => (ts.find? (·.1 == l)).map (·.2)) := by
    intro d; simp only [tysOf, List.findSome?_map]; rfl
  rw [e, e, h]

theorem gOf_erase (p : Prog) (k : Promises.Knobs) (arch : Arch) (q : Nat) (c : Cfg) (i : Nat) :
    gOf p k arch (erasePermits q c) i = gOf p k arch c i := by
  simp only [gOf, erase_n, tysOf_erase]; rfl

/-- Thread `q`'s steps commute with the normalisation. -/
theorem threadSteps_erase (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (q : Nat) :
    (threadSteps p k arch c q).map (erasePermits q) =
      (threadSteps p k arch (erasePermits q c) q).map (erasePermits q) := by
  unfold threadSteps
  rw [erase_get, gOf_erase]
  cases h : c.ths[q]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some, eraseTh_self]
    have hm : (erasePermits q c).mem = c.mem := rfl
    have hpr : (erasePermits q c).pairs = c.pairs := rfl
    rw [show normTh th = { th with permit := some (th.permit.getD 0) } from rfl, hm, hpr,
      tstep_permit (gOf p k arch c q) c.mem c.pairs th (some (th.permit.getD 0)), List.map_map, List.map_map,
      List.map_map]
    apply List.map_congr_left
    rintro ⟨m, pr, t⟩ hr
    have hp := tstep_permit_mem hr
    exact erase_upd q q c m pr c.trace (by simp only at hp; simp only [eraseTh_self, normTh, hp, Option.getD_some])

theorem promise_erase (c : Cfg) (q : Nat) (a : WeakMem.Address) (v : WeakMem.Val) (w : Ts) :
    erasePermits q (promise c q a v w) = erasePermits q (promise (erasePermits q c) q a v w) := by
  unfold promise
  rw [erase_get]
  cases h : c.ths[q]? with
  | none => exact (erase_erase q c).symm
  | some th =>
    simp only [Option.map_some]
    exact erase_upd q q c _ c.pairs c.trace (by simp only [eraseTh_self]; rfl)

theorem extCfg_erase (c : Cfg) (q : Nat) (th : TTh) (x : String) (n : ExtName) (e : Expr) (ws rs : List Word) :
    erasePermits q (extCfg c q th x n e ws rs) = erasePermits q (extCfg (erasePermits q c) q (normTh th) x n e ws rs) := by
  have he : (normTh th).tidLbl = th.tidLbl := rfl
  cases n
  case current =>
    simp only [extCfg, curCfg, he]
    cases hl : th.tidLbl with
    | some l => exact erase_upd q q c c.mem c.pairs c.trace (by simp only [eraseTh_self]; rfl)
    | none =>
      simp only [erase_n]
      exact erase_upd q q c c.mem c.pairs c.trace (by simp only [eraseTh_self]; rfl)
  all_goals
    simp only [extCfg]
    refine erase_upd q q c c.mem c.pairs _ ?_
    simp only [eraseTh_self, show (erasePermits q c).mem = c.mem from rfl, parkVs_norm]
    rfl

theorem extSteps_erase (c : Cfg) (q : Nat) :
    (extSteps c q).map (erasePermits q) = (extSteps (erasePermits q c) q).map (erasePermits q) := by
  unfold extSteps
  rw [erase_get]
  cases h : c.ths[q]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some, eraseTh_self]
    have ht : (normTh th).term = th.term := rfl
    have hv : (normTh th).env = th.env := rfl
    rw [ht, hv]
    generalize th.term = t
    split
    · rename_i x n a e
      try dsimp only
      have hn : ExtNeedsNoProm n (normTh th) ↔ ExtNeedsNoProm n th := Iff.rfl
      by_cases hn0 : ExtNeedsNoProm n th
      · simp only [hn0, hn.2 hn0, ite_true]
      · have hn1 : ¬ ExtNeedsNoProm n (normTh th) := fun h => hn0 (hn.1 h); simp only [hn0, hn1, ite_false]
        split
        · rw [List.map_map, List.map_map]
          exact List.map_congr_left (fun rs _ => extCfg_erase c q th x n e _ rs)
        · rfl
    · rename_i hne
      first
        | rfl
        | (split
           · rename_i x n a e
             exact absurd rfl (hne x n a e)
           · rfl)

/-- Two configurations that agree up to the permits a certificate of thread `q` does not read. -/
def PermEq (q : Nat) (c d : Cfg) : Prop := erasePermits q c = erasePermits q d

theorem solo_perm {p : Prog} {k : Promises.Knobs} {arch : Arch} {q : Nat} {c c' : Cfg}
    (h : Solo p k arch q c c') : ∀ d, PermEq q c d → ∃ d', Solo p k arch q d d' ∧ PermEq q c' d' := by
  induction h with
  | refl c => exact fun d hd => ⟨d, .refl _, hd⟩
  | thread hin _ ih =>
    intro d hd
    rename_i c0 c1 c2
    have h1 := List.mem_map_of_mem (f := erasePermits q) hin
    rw [threadSteps_erase, hd, ← threadSteps_erase] at h1
    obtain ⟨d1, hd1, he⟩ := List.mem_map.1 h1
    obtain ⟨d2, hs, hp⟩ := ih d1 he.symm
    exact ⟨d2, .thread hd1 hs, hp⟩
  | prom a v w hw _ ih =>
    intro d hd
    unfold PermEq at hd
    obtain ⟨d2, hs, hp⟩ := ih (promise d _ a v w) (by
      unfold PermEq; rw [promise_erase, hd, ← promise_erase])
    exact ⟨d2, .prom a v w (by have h2 := congrArg (fun x : Cfg => x.mem.size) hd; exact Nat.lt_of_lt_of_eq hw h2) hs, hp⟩
  | ext hin _ ih =>
    intro d hd
    have h1 := List.mem_map_of_mem (f := erasePermits q) hin
    rw [extSteps_erase, hd, ← extSteps_erase] at h1
    obtain ⟨d1, hd1, he⟩ := List.mem_map.1 h1
    obtain ⟨d2, hs, hp⟩ := ih d1 he.symm
    exact ⟨d2, .ext hd1 hs, hp⟩

/-- Certification of thread `q` agrees on configurations equal up to the permits it does not read. -/
theorem certified_perm {p : Prog} {k : Promises.Knobs} {arch : Arch} {c d : Cfg} {q : Nat} (h : PermEq q c d)
    (hc : Certified p k arch c q) : Certified p k arch d q := by
  obtain ⟨c', hs, hn⟩ := hc
  obtain ⟨d', hs', hp⟩ := solo_perm hs d h
  exact ⟨d', hs', by rw [← noPromises_erase, ← hp, noPromises_erase]; exact hn⟩

theorem eraseTh_setPermit {q m : Nat} {u : Ts} (th : TTh) (h : m ≠ q ∨ u = 0) :
    eraseTh q m { th with permit := some (max (th.permit.getD 0) u) } = eraseTh q m th := by
  by_cases hm : m = q
  · subst hm
    rcases h with h | rfl
    · exact absurd rfl h
    · simp only [eraseTh_self, normTh, Option.getD_some, Nat.max_zero]
  · simp [eraseTh, hm]

theorem setPermit_perm (c : Cfg) (q j : Nat) (u : Ts) (h : j ≠ q ∨ u = 0) : PermEq q (setPermit c j u) c := by
  unfold PermEq setPermit
  cases hc : c.ths[j]? with
  | none => rfl
  | some th =>
    simp only [erasePermits, mapIdx_set, eraseTh_setPermit th h]
    congr 1
    apply Array.ext_getElem?
    intro m
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases hm : j = m
    · subst hm
      obtain ⟨hj, hg⟩ := Array.getElem?_eq_some_iff.mp hc
      simp [hj, hg]
    · simp only [hm, ite_false]

/-- (D4) The thread a `wake` gives a permit, if any. -/
def woken (c : Cfg) (n : ExtName) (ws : List Word) : Option Nat :=
  match n, ws with
  | .unpark, [t] => thrOfTid c t
  | _, _ => none

theorem wake_perm (c : Cfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) (q : Nat)
    (hq : q = i ∨ woken c n ws ≠ some q) : PermEq q (wake c i v n ws) c := by
  unfold wake
  split
  · rename_i t
    split
    · rename_i j hj
      apply setPermit_perm
      by_cases hji : j = i
      · exact .inr (by simp [hji])
      · refine .inl fun hjq => ?_
        rcases hq with rfl | hq
        · exact hji hjq
        · exact hq (hjq ▸ hj)
    · rfl
  · rfl

/-- **O6 `certified_wake`.** A `wake` by thread `i` neither creates nor destroys a certificate of `i` itself (the mover)
or of any thread other than the one woken.  (The woken thread's certificate may be lost: the `park` in it then
acquires the permit's view.) -/
theorem certified_wake (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) (v : Ts) (n : ExtName)
    (ws : List Word) (q : Nat) (hq : q = i ∨ woken c n ws ≠ some q) :
    Certified p k arch (wake c i v n ws) q ↔ Certified p k arch c q :=
  ⟨certified_perm (wake_perm c i v n ws q hq), certified_perm (wake_perm c i v n ws q hq).symm⟩

/-- **O5 `park_site_step`.** At a `park` site the old `ret ()` behaviour is always an `Ext` step, whatever the permit
and the promises: certification is the only premise, as for the old prelude call. -/
theorem park_site_step (p : Prog) (k : Promises.Knobs) (arch : Arch) {c : Cfg} {i : Nat} {th : TTh} {x : String}
    {a : At} {e : Expr} {rt : Ty} {ws : List Word} (hth : c.ths[i]? = some th)
    (hterm : th.term = .let_ x (.ext .park a) e) (hev : evalAt th.env a = some (rt, ws))
    (hc : Certified p k arch (extCfg c i th x .park e ws []) i) :
    Ext p k arch c (wake (extCfg c i th x .park e ws []) i (relView th.vs) .park ws) :=
  .mk i x .park a e th rt ws [] hth hterm
    (fun h => by simp [ExtNeedsNoProm, CoreTerm.ExtName.isChoice] at h) hev
    (by simp [CoreTerm.ExtName.Admits]) hc

end TermPermit

#print axioms TermPermit.tstep_permit
#print axioms TermPermit.certified_wake
#print axioms TermPermit.park_site_step
