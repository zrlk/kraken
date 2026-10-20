/-
**Kernel-evaluable promise certification**.

`certify` (`Machine.lean`) keeps its visited set in a `Std.HashSet` and
memoises in a `Std.HashMap` (`CertCache`); the kernel cannot evaluate either
(the bucket index is a `USize`, `mixHash` is opaque). `reachGoL` is
`certify.go` with the visited set a list (`List.any` with the same `==`),
and the ISA's `exec`/`deps` replaced by `ex`/`dp` (as in `reachStepOne`), so
`decide` evaluates it on AArch64 with `reachA64ExecK`/`reachA64Deps`.
-/
import Kraken.Promising.ReachCore
import Kraken.Promising.PromiseSafe

namespace Kraken.Promising

variable {I : ISA}

/-- `certify.go` with a list for the visited set and `ex`/`dp` for the
ISA's `exec`/`deps`. -/
def reachGoL (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (tid : Nat) : Nat → List (Thread I × Memory) × CertResult I →
      Thread I × Memory × List (Msg × View) × Bool → List (Thread I × Memory) × CertResult I
  | n, (visited, acc), (t, mem, ws, done) =>
    if visited.any (· == (t, mem)) then (visited, acc) else
    let visited := (t, mem) :: visited
    if t.hasDeadPromise mem then (visited, acc) else
    let (acc, done) :=
      if !done && t.prom.isEmpty then ({ acc with certified := true, writes := acc.writes ++ ws }, true)
      else (acc, done)
    if (ex t.st).isNone then (visited, acc)
    else
      match n with
      | 0 => (visited, { acc with boundHit := true })
      | n + 1 =>
        match reachStepOne ex dp A t tid mem with
        | none => (visited, acc)
        | some outs =>
          let (next, acc) := outs.foldl (init := ([], acc)) fun (next, acc) o =>
            match o with
            | .error m => (next, { acc with faults := acc.faults ++ [m] })
            | .ok o =>
              if done then ((o.thread, o.mem, [], true) :: next, { acc with writes := acc.writes ++ o.promisedNow })
              else ((o.thread, o.mem, ws ++ o.promisedNow, false) :: next, acc)
          next.foldl (reachGoL ex dp A tid n) (visited, acc)

/-- The certification result `certify` computes on a cache miss, by
`reachGoL`. -/
def reachCert (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) : CertResult I :=
  (reachGoL ex dp A tid fuel ([], {}) (t, mem, [], false)).2

/-! ## `reachGoL` computes what `certify.go` computes -/

/-- The product instances of `PromiseSafe.lean` are private; the same
facts again. -/
theorem reach_prod_beq_iff {α β : Type} [BEq α] [BEq β] (a b : α × β) :
    (a == b) = true ↔ (a.1 == b.1) = true ∧ (a.2 == b.2) = true := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  show (a1 == b1 && a2 == b2) = true ↔ _
  simp only [Bool.and_eq_true]

instance reachEquivBEqProd {α β : Type} [BEq α] [BEq β] [EquivBEq α] [EquivBEq β] : EquivBEq (α × β) where
  rfl := (reach_prod_beq_iff _ _).mpr ⟨BEq.rfl, BEq.rfl⟩
  symm h := (reach_prod_beq_iff _ _).mpr
    ⟨BEq.symm ((reach_prod_beq_iff _ _).mp h).1, BEq.symm ((reach_prod_beq_iff _ _).mp h).2⟩
  trans h h' := (reach_prod_beq_iff _ _).mpr
    ⟨BEq.trans ((reach_prod_beq_iff _ _).mp h).1 ((reach_prod_beq_iff _ _).mp h').1,
     BEq.trans ((reach_prod_beq_iff _ _).mp h).2 ((reach_prod_beq_iff _ _).mp h').2⟩

instance reachLawfulHashableProd {α β : Type} [BEq α] [BEq β] [Hashable α] [Hashable β]
    [LawfulHashable α] [LawfulHashable β] : LawfulHashable (α × β) where
  hash_eq {a b} h := by
    obtain ⟨h1, h2⟩ := (reach_prod_beq_iff a b).mp h
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    show mixHash (hash a1) (hash a2) = mixHash (hash b1) (hash b2)
    rw [show hash a1 = hash b1 from hash_eq h1, show hash a2 = hash b2 from hash_eq h2]

/-- A `certify.go` accumulator and a `reachGoL` one agree: the same result,
and the visited sets contain the same states. -/
def ReachGoRel (p : Std.HashSet (Thread I × Memory) × CertResult I)
    (q : List (Thread I × Memory) × CertResult I) : Prop :=
  p.2 = q.2 ∧ ∀ x, p.1.contains x = q.1.any (· == x)

theorem reachGoL_rel [I.LawfulState] (A : Arch) (tid : Nat) :
    ∀ (n : Nat) (p : Std.HashSet (Thread I × Memory) × CertResult I)
      (q : List (Thread I × Memory) × CertResult I) (st : Thread I × Memory × List (Msg × View) × Bool),
      ReachGoRel p q → ReachGoRel (certify.go A tid n p st) (reachGoL I.exec I.deps A tid n q st) := by
  intro n
  induction n with
  | zero =>
    rintro ⟨V, acc⟩ ⟨L, acc'⟩ ⟨t, mem, ws, done⟩ ⟨h2, h1⟩
    simp only at h2 h1
    subst h2
    have hins : ∀ x, (V.insert (t, mem)).contains x = ((t, mem) :: L).any (· == x) := by
      intro x
      rw [Std.HashSet.contains_insert, List.any_cons, h1]
    unfold certify.go reachGoL
    simp only [Thread.halted, h1 (t, mem)]
    split
    · exact ⟨rfl, h1⟩
    split
    · exact ⟨rfl, hins⟩
    by_cases hh : (I.exec t.st).isNone = true
    · simp only [hh, ite_true]
      exact ⟨rfl, hins⟩
    · simp only [hh, ite_false, Bool.false_eq_true]
      exact ⟨rfl, hins⟩
  | succ n ih =>
    rintro ⟨V, acc⟩ ⟨L, acc'⟩ ⟨t, mem, ws, done⟩ ⟨h2, h1⟩
    simp only at h2 h1
    subst h2
    have hins : ∀ x, (V.insert (t, mem)).contains x = ((t, mem) :: L).any (· == x) := by
      intro x
      rw [Std.HashSet.contains_insert, List.any_cons, h1]
    have hfold : ∀ (l : List (Thread I × Memory × List (Msg × View) × Bool)) p q, ReachGoRel p q →
        ReachGoRel (l.foldl (certify.go A tid n) p) (l.foldl (reachGoL I.exec I.deps A tid n) q) := by
      intro l
      induction l with
      | nil => exact fun _ _ h => h
      | cons s l ihl => exact fun p q h => ihl _ _ (ih p q s h)
    unfold certify.go reachGoL
    simp only [Thread.halted, h1 (t, mem), reachStepOne_eq]
    split
    · exact ⟨rfl, h1⟩
    split
    · exact ⟨rfl, hins⟩
    by_cases hh : (I.exec t.st).isNone = true
    · simp only [hh, ite_true]
      exact ⟨rfl, hins⟩
    simp only [hh, ite_false, Bool.false_eq_true]
    cases stepOne A t tid mem with
    | none => exact ⟨rfl, hins⟩
    | some outs => exact hfold _ _ _ ⟨rfl, hins⟩

/-- **`reachGoL` is `certify.go`'s result**, from an empty visited set. -/
theorem reachCert_eq [I.LawfulState] (A : Arch) (t : Thread I) (tid : Nat) (mem : Memory) (fuel : Nat) :
    (certify.go A tid fuel ({}, {}) (t, mem, [], false)).2 = reachCert I.exec I.deps A t tid mem fuel :=
  (reachGoL_rel A tid fuel ({}, {}) ([], {}) _ ⟨rfl, fun x => by simp⟩).1

/-! ## An exact cache: `certify` returns the fresh result -/

/-- Every entry of the cache on a key satisfying `K` is the fresh
certification result (`certify.go` from nothing visited). -/
def ReachCacheExact (A : Arch) (fuel : Nat) (K : Thread I → Nat → Prop) (cache : CertCache I) : Prop :=
  ∀ (t : Thread I) (tid : Nat) (mem : Memory) (r : CertResult I),
    K t tid → cache[(t, tid, mem)]? = some r → r = (certify.go A tid fuel ({}, {}) (t, mem, [], false)).2

theorem ReachCacheExact.empty (A : Arch) (fuel : Nat) (K : Thread I → Nat → Prop) :
    ReachCacheExact A fuel K ({} : CertCache I) := by
  intro t tid mem r _ h
  simp at h

theorem ReachCacheExact.insert [I.LawfulState] {A : Arch} {fuel : Nat} {K : Thread I → Nat → Prop}
    {cache : CertCache I} (hK : KeyLawful K) (hc : ReachCacheExact A fuel K cache) {t : Thread I} {tid : Nat}
    {mem : Memory} (ht : K t tid) :
    ReachCacheExact A fuel K (cache.insert (t, tid, mem) (certify.go A tid fuel ({}, {}) (t, mem, [], false)).2) := by
  intro t' tid' mem' r' ht' h
  rw [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    obtain ⟨h1, h23⟩ := (reach_prod_beq_iff _ _).mp heq
    obtain ⟨h2, h3⟩ := (reach_prod_beq_iff _ _).mp h23
    simp only [beq_iff_eq] at h2 h3
    subst h2 h3
    cases h
    rw [← hK t t' tid ht ht' h1]
  · exact hc t' tid' mem' r' ht' h

/-- **`certify` with an exact cache returns the fresh result**, and the
cache stays exact. -/
theorem reach_certify_exact [I.LawfulState] {A : Arch} {fuel : Nat} {K : Thread I → Nat → Prop}
    (hK : KeyLawful K) {cache : CertCache I} (hc : ReachCacheExact A fuel K cache) {t : Thread I} {tid : Nat}
    (ht : K t tid) (mem : Memory) :
    (certify A cache t tid mem fuel).1 = (certify.go A tid fuel ({}, {}) (t, mem, [], false)).2 ∧
      ReachCacheExact A fuel K (certify A cache t tid mem fuel).2 := by
  unfold certify
  split
  · rename_i r h
    exact ⟨hc t tid mem r ht h, hc⟩
  · exact ⟨rfl, hc.insert hK ht⟩

/-! ## Membership in `succs` of promise steps and promise-holding steps -/

private theorem reachC_foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h0, _ => h0
  | a :: l, b, h0, hs => reachC_foldl_inv P f l (f b a) (hs b a List.mem_cons_self h0)
      (fun b' a' ha' => hs b' a' (List.mem_cons_of_mem _ ha'))

/-- A fold with an invariant `Inv` reaches `Q` if one element establishes
`Q` and every element keeps it. -/
private theorem reachC_foldl_adds {α β : Type} (Inv Q : β → Prop) (f : β → α → β) (a₀ : α) :
    ∀ (l : List α), (∀ b a, a ∈ l → Inv b → Inv (f b a)) → (∀ b a, a ∈ l → Inv b → Q b → Q (f b a)) →
      (∀ b, Inv b → Q (f b a₀)) → ∀ (b : β), Inv b → a₀ ∈ l → Q (l.foldl f b)
  | [], _, _, _, _, _, h => by cases h
  | a :: l, hinv, hkeep, hadd, b, h0, h => by
    have hinv' : ∀ b a', a' ∈ l → Inv b → Inv (f b a') := fun b a' h => hinv b a' (List.mem_cons_of_mem _ h)
    rcases List.mem_cons.mp h with he | h
    · subst he
      exact (reachC_foldl_inv (fun b => Inv b ∧ Q b) f l _ ⟨hinv b a₀ List.mem_cons_self h0, hadd b h0⟩
        (fun b a ha hb => ⟨hinv' b a ha hb.1, hkeep b a (List.mem_cons_of_mem _ ha) hb.1 hb.2⟩)).2
    · exact reachC_foldl_adds Inv Q f a₀ l hinv'
        (fun b a' h => hkeep b a' (List.mem_cons_of_mem _ h)) hadd (f b a) (hinv b a List.mem_cons_self h0) h

/-- The accumulator of `succsL`'s folds. -/
private abbrev ReachCAcc (I : ISA) := List (Config I × List TraceEv) × Bool × List String × CertCache I

/-- The invariant of `succsL`'s folds: the cache is exact on the keys
`succsL` asks about. -/
private abbrev ReachCInv [I.LawfulState] (A : Arch) (fuel : Nat) (c : Config I) (a : ReachCAcc I) : Prop :=
  ReachCacheExact A fuel c.SameProg a.2.2.2

/-- The inner (per-outcome) fold step of `succsL`. -/
private def reachCInner (A : Arch) (c : Config I) (tid fuel : Nat) (a : ReachCAcc I) (o : Except String (Outcome I)) :
    ReachCAcc I :=
  match o with
  | .error msg => (a.1, a.2.1, a.2.2.1 ++ [msg], a.2.2.2)
  | .ok o =>
    let c' := c.withThread tid o.thread o.mem
    if o.thread.prom.isEmpty then ((c', o.log) :: a.1, a.2.1, a.2.2.1, a.2.2.2)
    else
      let (r, cache) := certify A a.2.2.2 o.thread tid o.mem fuel
      if r.certified then ((c', o.log) :: a.1, a.2.1 || r.boundHit, a.2.2.1, cache)
      else (a.1, a.2.1 || r.boundHit, a.2.2.1, cache)

private theorem reachCInner_keeps (A : Arch) (c : Config I) (tid fuel : Nat) (m : Config I)
    (a : ReachCAcc I) (o : Except String (Outcome I)) (hm : m ∈ a.1.map (·.1)) :
    m ∈ (reachCInner A c tid fuel a o).1.map (·.1) := by
  obtain ⟨next, bound, faults, cache⟩ := a
  unfold reachCInner
  simp only at hm ⊢
  split
  · exact hm
  · split
    · simp [hm]
    · split <;> simp_all

private theorem reachCInner_inv [I.LawfulState] (A : Arch) (c : Config I) (tid fuel : Nat) {t : Thread I}
    (ht : c.threads[tid]? = some t) {outs : List (Except String (Outcome I))} (hs : stepOne A t tid c.mem = some outs)
    (a : ReachCAcc I) (o : Except String (Outcome I)) (ho : o ∈ outs) (ha : ReachCInv A fuel c a) :
    ReachCInv A fuel c (reachCInner A c tid fuel a o) := by
  obtain ⟨next, bound, faults, cache⟩ := a
  unfold reachCInner
  split
  · exact ha
  · rename_i o
    have hc' := (reach_certify_exact (Config.SameProg.keyLawful c) ha ⟨t, ht, stepOne_static A hs ho⟩ o.mem).2
    simp only
    split
    · exact ha
    · split <;> exact hc'

/-- The promise configurations `certifiedPromises` offers, as configurations. -/
private theorem reach_mem_certifiedPromises [I.LawfulState] {A : Arch} {fuel : Nat} {c : Config I} {tid : Nat}
    {t : Thread I} (ht : c.threads[tid]? = some t) {cache : CertCache I}
    (hc : ReachCacheExact A fuel c.SameProg cache) {w : Msg} {ν : View}
    (hw : (w, ν) ∈ (certify.go A tid fuel ({}, {}) (t, c.mem, [], false)).2.writes) (hν : ν ≤ c.mem.last) :
    c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1 ∈
      (certifiedPromises A cache c tid fuel).1.map (·.1) ∧
    ReachCacheExact A fuel c.SameProg (certifiedPromises A cache c tid fuel).2.2 := by
  have he := reach_certify_exact (Config.SameProg.keyLawful c) hc ⟨t, ht, rfl⟩ c.mem (fuel := fuel)
  unfold certifiedPromises
  simp only [ht]
  refine ⟨?_, he.2⟩
  rw [he.1]
  simp only [List.map_map, List.mem_map, Function.comp_def]
  refine ⟨w, ?_, rfl⟩
  rw [List.mem_eraseDups]
  exact List.mem_map.mpr ⟨(w, ν), List.mem_filter.mpr ⟨hw, decide_eq_true hν⟩, rfl⟩

private theorem reach_certifiedPromises_inv [I.LawfulState] {A : Arch} {fuel : Nat} {c : Config I} {tid : Nat}
    {cache : CertCache I} (hc : ReachCacheExact A fuel c.SameProg cache) :
    ReachCacheExact A fuel c.SameProg (certifiedPromises A cache c tid fuel).2.2 := by
  unfold certifiedPromises
  split
  · exact hc
  · rename_i t ht
    exact (reach_certify_exact (Config.SameProg.keyLawful c) hc ⟨t, ht, rfl⟩ c.mem).2

/-- **A promise-holding instruction step is a successor** when the fresh
certification of the resulting thread succeeds. -/
theorem reach_mem_succs_cert [I.LawfulState] (A : Arch) (fuel : Nat) {c : Config I} {tid : Nat}
    {outs : List (Except String (Outcome I))} (hs : stepThread A c tid = some outs)
    {o : Outcome I} (ho : Except.ok o ∈ outs)
    (hcert : (certify.go A tid fuel ({}, {}) (o.thread, o.mem, [], false)).2.certified = true) :
    c.withThread tid o.thread o.mem ∈ (succs A c fuel).1 := by
  obtain ⟨t, ht, hs1⟩ := stepThread_eq_some hs
  have hlt : tid < c.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  let m := c.withThread tid o.thread o.mem
  show m ∈ (succsL A {} c fuel none).1.map (·.1)
  unfold succsL
  refine reachC_foldl_adds (ReachCInv A fuel c) (fun x : ReachCAcc I => m ∈ x.1.map Prod.fst) _ tid _ ?_ ?_ ?_ _
    (ReachCacheExact.empty A fuel _) (List.mem_range.mpr hlt)
  · rintro ⟨next, bound, faults, cache⟩ t' - ha
    simp only
    apply reach_certifiedPromises_inv
    split
    · exact ha
    · rename_i outs' hs'
      obtain ⟨t'', ht'', hs''⟩ := stepThread_eq_some hs'
      exact reachC_foldl_inv (ReachCInv A fuel c) _ outs' _ ha
        (fun b a hmem hb => reachCInner_inv A c t' fuel ht'' hs'' b a hmem hb)
  · rintro ⟨next, bound, faults, cache⟩ t' - - hm
    simp only
    split
    · simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      exact Or.inl hm
    · simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      left
      exact reachC_foldl_inv (fun x : ReachCAcc I => m ∈ x.1.map Prod.fst) _ _ _ hm
        (fun b a _ hb => reachCInner_keeps A c t' fuel m b a hb)
  · rintro ⟨next, bound, faults, cache⟩ ha
    simp only [hs, List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
    left
    refine reachC_foldl_adds (ReachCInv A fuel c) (fun x : ReachCAcc I => m ∈ x.1.map Prod.fst) _ (.ok o) outs
      (fun b a h hb => reachCInner_inv A c tid fuel ht hs1 b a h hb)
      (fun b a _ _ hb => reachCInner_keeps A c tid fuel m b a hb) ?_ _ ha ho
    rintro ⟨next, bound, faults, cache⟩ hb
    have he := reach_certify_exact (Config.SameProg.keyLawful c) hb ⟨t, ht, stepOne_static A hs1 ho⟩ o.mem
      (fuel := fuel)
    unfold reachCInner
    simp only
    split
    · simp [m]
    · rw [he.1, hcert]
      simp [m]

/-- **A certified promise is a successor**: a write of the fresh
certification of thread `tid` whose constraining view is at most `|M|`,
appended and promised. -/
theorem reach_mem_succs_promise [I.LawfulState] (A : Arch) (fuel : Nat) {c : Config I} {tid : Nat}
    {t : Thread I} (ht : c.threads[tid]? = some t) {w : Msg} {ν : View}
    (hw : (w, ν) ∈ (certify.go A tid fuel ({}, {}) (t, c.mem, [], false)).2.writes) (hν : ν ≤ c.mem.last) :
    c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1 ∈
      (succs A c fuel).1 := by
  have hlt : tid < c.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  let m := c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1
  show m ∈ (succsL A {} c fuel none).1.map (·.1)
  unfold succsL
  refine reachC_foldl_adds (ReachCInv A fuel c) (fun x : ReachCAcc I => m ∈ x.1.map Prod.fst) _ tid _ ?_ ?_ ?_ _
    (ReachCacheExact.empty A fuel _) (List.mem_range.mpr hlt)
  · rintro ⟨next, bound, faults, cache⟩ t' - ha
    simp only
    apply reach_certifiedPromises_inv
    split
    · exact ha
    · rename_i outs' hs'
      obtain ⟨t'', ht'', hs''⟩ := stepThread_eq_some hs'
      exact reachC_foldl_inv (ReachCInv A fuel c) _ outs' _ ha
        (fun b a hmem hb => reachCInner_inv A c t' fuel ht'' hs'' b a hmem hb)
  · rintro ⟨next, bound, faults, cache⟩ t' - - hm
    simp only
    split
    · simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      exact Or.inl hm
    · simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      left
      exact reachC_foldl_inv (fun x : ReachCAcc I => m ∈ x.1.map Prod.fst) _ _ _ hm
        (fun b a _ hb => reachCInner_keeps A c t' fuel m b a hb)
  · rintro ⟨next, bound, faults, cache⟩ ha
    have key : ∀ cache', ReachCacheExact A fuel c.SameProg cache' →
        m ∈ ((certifiedPromises A cache' c tid fuel).1.map fun x => (x.1, [x.2])).map Prod.fst := by
      intro cache' hc'
      have := (reach_mem_certifiedPromises ht hc' hw hν).1
      simpa [List.map_map, Function.comp_def] using this
    simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
    right
    split
    · exact key _ ha
    · rename_i outs' hs'
      obtain ⟨t'', ht'', hs''⟩ := stepThread_eq_some hs'
      exact key _ (reachC_foldl_inv (ReachCInv A fuel c) _ outs' _ ha
        (fun b a hmem hb => reachCInner_inv A c tid fuel ht'' hs'' b a hmem hb))

/-! ## The checker with promises -/

/-- A step of a trace with promises: thread `tid`'s next instruction, keeping
the first outcome with read/write timestamps `sel` (as `reachStep`) that
holds no promise or is certified; or a promise by thread `tid` of value
`val` to the location at address `addr` (the first such certified write). -/
inductive ReachPStep where
  | instr (tid : Nat) (sel : List Nat)
  | promise (tid : Nat) (addr : BitVec 64) (val : Val)

/-- The outcome an instruction step accepts: the selected timestamps, and no
promise left or a successful certification of the new thread. -/
def ReachSelP (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (fuel tid : Nat) (sel : List Nat) (o : Except String (Outcome I)) : Option (Outcome I) :=
  match o with
  | .ok o =>
    if reachStamps o.log == sel && (o.thread.prom.isEmpty || (reachCert ex dp A o.thread tid o.mem fuel).certified)
    then some o else none
  | .error _ => none

/-- One step of a trace with promises. -/
def reachPStep (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (fuel : Nat) (c : Config I) : ReachPStep → Option (Config I)
  | .instr tid sel => match c.threads[tid]? with
    | none => none
    | some t => match reachStepOne ex dp A t tid c.mem with
      | none => none
      | some outs => (outs.findSome? (ReachSelP ex dp A fuel tid sel)).map fun o => c.withThread tid o.thread o.mem
  | .promise tid addr val => match c.threads[tid]? with
    | none => none
    | some t =>
      ((reachCert ex dp A t tid c.mem fuel).writes.find? fun (w, ν) =>
          w.loc.addr == addr && w.val == val && decide (ν ≤ c.mem.last)).map fun (w, _) =>
        c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1

/-- Replay a trace with promises. -/
def reachPRun (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (fuel : Nat) : Config I → List ReachPStep → Option (Config I)
  | c, [] => some c
  | c, s :: tr => (reachPStep ex dp A fuel c s).bind fun c' => reachPRun ex dp A fuel c' tr

theorem reachPStep_sound [I.LawfulState] (A : Arch) (fuel : Nat) {c c' : Config I} {s : ReachPStep}
    (h : reachPStep I.exec I.deps A fuel c s = some c') : c' ∈ (succs A c fuel).1 := by
  cases s with
  | instr tid sel =>
    simp only [reachPStep] at h
    split at h
    · cases h
    · rename_i t ht
      rw [reachStepOne_eq] at h
      split at h
      · cases h
      · rename_i outs hs'
        have hs : stepThread A c tid = some outs := by simp [stepThread, ht, hs']
        obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨e, he, hsel⟩ := List.exists_of_findSome?_eq_some ho
        unfold ReachSelP at hsel
        split at hsel
        · split at hsel
          · rename_i hc
            cases hsel
            simp only [Bool.and_eq_true, Bool.or_eq_true] at hc
            rcases hc.2 with hp | hp
            · exact reach_mem_succs A fuel hs he hp
            · rw [← reachCert_eq] at hp
              exact reach_mem_succs_cert A fuel hs he hp
          · cases hsel
        · cases hsel
  | promise tid addr val =>
    simp only [reachPStep] at h
    split at h
    · cases h
    · rename_i t ht
      obtain ⟨⟨w, ν⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
      have hmem := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      rw [← reachCert_eq] at hmem
      exact reach_mem_succs_promise A fuel ht hmem hp.2

/-- **Soundness of the checker with promises**: a replayed trace is a run. -/
theorem reachPRun_sound [I.LawfulState] (A : Arch) (fuel : Nat) :
    ∀ {c c' : Config I} {tr : List ReachPStep}, reachPRun I.exec I.deps A fuel c tr = some c' →
      Reachable A fuel c c'
  | c, c', [], h => by cases h; exact .refl c
  | c, c', s :: tr, h => by
    simp only [reachPRun] at h
    obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp h
    exact .step (reachPStep_sound A fuel hm) (reachPRun_sound A fuel hr)

/-- The Boolean a reachability theorem with promises evaluates. -/
def reachPCheck (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (fuel : Nat) (c0 : Config I) (tr : List ReachPStep) (p : Config I → Bool) : Bool :=
  match reachPRun ex dp A fuel c0 tr with
  | some c => reachFinal ex c && p c
  | none => false

/-- **A witness with promises from one evaluation**, at the given `fuel`
(certification depends on it). -/
theorem reach_witness_promise [I.LawfulState] (A : Arch) (fuel : Nat) {ex : I.State → Option (EvTree I.State)}
    {dp : I.State → InstrDeps I.RegId} (hex : ex = I.exec) (hdp : dp = I.deps) {c0 : Config I}
    {tr : List ReachPStep} {P : Config I → Prop} [DecidablePred P]
    (h : reachPCheck ex dp A fuel c0 tr (fun c => decide (P c)) = true) :
    ∃ c, Reachable A fuel c0 c ∧ c.final = true ∧ P c := by
  subst hex hdp
  unfold reachPCheck at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨c, reachPRun_sound A fuel hc, h.1, h.2⟩
  · cases h

end Kraken.Promising

#print axioms Kraken.Promising.reachCert_eq
#print axioms Kraken.Promising.reachPRun_sound
#print axioms Kraken.Promising.reach_witness_promise
