import WeakCore.TermLiveCertMoves
import WeakCore.TermLiveCertKey
import WeakCore.TermLiveX
/-! # TermLiveCertRun — item 38 v1: the soundness of `check` (G2)

A promise-free `machineE` run from `c0` walks the certificate's nodes (`run_nodes`); past some point it visits only
nodes it visits infinitely often; those are quiet (`FairS.prog`, and finitely many nodes with monotone memory and
coherence views admit only finitely many `Progress` steps); the ranks then stabilise; a spinning thread gives a move
inside the final rank, which refutes `noSpin`, and `unfair j` is refuted by `FairS.weak`. -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveMach TermLiveL3 TermProgress TermLiveProps TermSpawnStep TermExtStep
open TermLiveGrow
open WeakMem (Arch Address Val Msg)
open Promises.Sim (MemExt)

/-! ### Moves: coherence, memory, views -/

theorem extCfg_facts {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) (x : String) (n : ExtName)
    (e : Expr) (ws rs : List Word) :
    (extCfg c i th x n e ws rs).mem = c.mem ∧ (extCfg c i th x n e ws rs).ths.size = c.ths.size ∧
      ∀ j : Nat, ((extCfg c i th x n e ws rs).ths[j]?).map (·.vs.coh) = (c.ths[j]?).map (·.vs.coh) := by
  have hi : i < c.ths.size := lt_of_get hth
  have hg : c.ths[i] = th := by simpa [Array.getElem?_eq_getElem hi] using hth
  unfold extCfg curCfg
  split <;> (try split) <;>
  · refine ⟨rfl, by simp, fun j => ?_⟩
    simp only [getElem?_set!]
    by_cases e1 : i = j
    · subst e1; simp [hi, hg]
      all_goals (try (unfold parkVs; split <;> rfl))
    · simp [e1]

theorem cohOf_of_cohLeX {c c' : Cfg} (h : CohLeX c c') (j : Nat) (b : Address) : cohOf c j b ≤ cohOf c' j b := by
  unfold cohOf
  cases h1 : c.ths[j]? with
  | none => simp
  | some th =>
    have hj : j < c'.ths.size := Nat.lt_of_lt_of_le (lt_of_get h1) h.1
    have h2 : c'.ths[j]? = some c'.ths[j] := Array.getElem?_eq_getElem hj
    simpa [h2] using h.2 j th _ h1 h2 b

/-- (D4) `wake` keeps every thread's views. -/
theorem wake_vs (c : Cfg) (i : Nat) (v : WeakMem.Ts) (n : ExtName) (ws : List Word) (j : Nat) :
    ((wake c i v n ws).ths[j]?).map (·.vs.coh) = (c.ths[j]?).map (·.vs.coh) := by
  rcases wake_get c i v n ws j with h | ⟨th, u, h1, h2⟩
  · rw [h]
  · rw [h1, h2]; rfl

/-- A `machineE` thread move keeps `CfgCoh`, extends memory and raises no existing thread's coherence view. -/
theorem moveE_facts {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} (hc : CfgCoh c)
    (h : mstepE p k arch c (i, .thr) c') : CfgCoh c' ∧ MemExt c.mem c'.mem ∧ CohLeX c c' := by
  rcases h with ⟨h1, -⟩ | ⟨x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, h6⟩ |
      ⟨x, n, a, e, th, rt, ws, rs, h1, h2, h3, h4, h5, -, h6, rfl⟩
  · obtain ⟨hc', hl⟩ := threadSteps_coh h1 hc
    exact ⟨hc', threadSteps_ext h1, CohLeX.ofCohLe hl⟩
  · have hs : TermLiveX.SpawnBy p k arch c.cap c i c' := ⟨x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, h6⟩
    obtain ⟨hm, hcc, -, -⟩ := TermLiveX.spawnBy_sound hs
    exact ⟨(hcc hc).1, hm, (hcc hc).2⟩
  · obtain ⟨hm0, hsz0, hv0⟩ := extCfg_facts h1 x n e ws rs
    have hm : (wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws).mem = c.mem := by rw [wake_mem]; exact hm0
    have hsz : (wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws).ths.size = c.ths.size := by
      rw [wake_size]; exact hsz0
    have hv : ∀ j : Nat, ((wake (extCfg c i th x n e ws rs) i (relView th.vs) n ws).ths[j]?).map (·.vs.coh) =
        (c.ths[j]?).map (·.vs.coh) :=
      fun j => by rw [← hv0 j]; exact wake_vs _ _ _ _ _ j
    refine ⟨fun j t hj => ?_, by rw [hm]; exact Promises.Sim.MemExt.refl _, ⟨Nat.le_of_eq hsz.symm, ?_⟩⟩
    · have := hv j
      rw [hj] at this
      cases h0 : c.ths[j]? with
      | none => rw [h0] at this; cases this
      | some t0 =>
        rw [h0] at this
        simp only [Option.map_some, Option.some.injEq] at this
        rw [hm]
        intro b; rw [this]; exact hc j t0 h0 b
    · intro j t t' h0 h0' b
      have := hv j
      rw [h0, h0'] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [this]
      exact Nat.le_refl _

/-- (D4) A `machineE` environment move (a spurious wake) is `extCfg` at a park site: it keeps `CfgCoh`, memory,
every coherence view and the thread count. -/
theorem envE_facts {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} (hc : CfgCoh c)
    (h : mstepE p k arch c (i, .env) c') :
    CfgCoh c' ∧ MemExt c.mem c'.mem ∧ CohLeX c c' ∧ i < c.ths.size ∧ c'.ths.size = c.ths.size := by
  obtain ⟨x, a, e, th, rt, ws, h1, -, -, -, rfl⟩ := spuriousWake_elim h
  obtain ⟨hm, hsz, hv⟩ := extCfg_facts h1 x .park e ws []
  refine ⟨fun j t hj => ?_, by rw [hm]; exact Promises.Sim.MemExt.refl _, ⟨Nat.le_of_eq hsz.symm, ?_⟩,
    lt_of_get h1, hsz⟩
  · have := hv j
    rw [hj] at this
    cases h0 : c.ths[j]? with
    | none => rw [h0] at this; cases this
    | some t0 =>
      rw [h0] at this
      simp only [Option.map_some, Option.some.injEq] at this
      rw [hm]
      intro b; rw [this]; exact hc j t0 h0 b
  · intro j t t' h0 h0' b
    have := hv j
    rw [h0, h0'] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this]
    exact Nat.le_refl _

/-- (D4) The threads' total term size. -/
noncomputable def termMass (c : Cfg) : Nat := (c.ths.toList.map fun th => sizeOf th.term).sum

theorem sum_set_lt : ∀ (l : List Nat) (i x : Nat), i < l.length → (h : x < l[i]!) → (l.set i x).sum < l.sum
  | [], _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | a :: l, 0, x, _, h => by
    simp only [List.set_cons_zero, List.sum_cons]
    simp only [List.getElem!_cons_zero] at h
    omega
  | a :: l, i + 1, x, hi, h => by
    simp only [List.set_cons_succ, List.sum_cons]
    have := sum_set_lt l i x (by simpa using hi) (by simpa using h)
    omega

/-- (D4) An environment move (a return from `park`) lowers `termMass`: environment moves alone cannot go on forever. -/
theorem envE_mass {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : mstepE p k arch c (i, .env) c') : termMass c' < termMass c := by
  obtain ⟨x, a, e, th, rt, ws, h1, h2, -, -, rfl⟩ := spuriousWake_elim h
  have hi : i < c.ths.size := lt_of_get h1
  have hg : c.ths[i] = th := by simpa [Array.getElem?_eq_getElem hi] using h1
  have e1 : ∀ t : TTh, (c.ths.set! i t).toList = c.ths.toList.set i t := fun t => by simp [Array.set!]
  unfold termMass extCfg
  simp only [e1, List.map_set]
  refine sum_set_lt _ _ _ (by simp [hi]) ?_
  simp [h1, h2]
  omega

/-! ### Reading the checker -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {ct : Cert}

theorem check_spec {c0 : Cfg} (hc : check p k arch X V ct c0 = true) :
    0 < ct.nodes.size ∧ cfgKey c0 = cfgKey (ct.nodes[0]?.getD default) ∧
      ∀ v, v < ct.nodes.size → ct.nodeOK p k arch X V v = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  exact ⟨hc.1.1.1.1, hc.1.2, hc.2⟩

/-- What `nodeOK` says. (By the definition's precedence the justification test sits inside `nodeOK`'s
per-move loop: it is checked at every node with a move, which is all the proof needs.) -/
theorem nodeOK_spec {v : Nat} (h : ct.nodeOK p k arch X V v = true) :
    pfB (ct.nd v) = true ∧
    (∀ i, i < (ct.nd v).ths.size → (movesPF p k arch V (ct.nd v) i).length = (ct.tg v i).length ∧
      ∀ e w, (e, w) ∈ ct.mt p k arch V v i → w < ct.nodes.size ∧ cfgKey e = cfgKey (ct.nodes[w]?.getD default) ∧
        (ct.quiet p k arch X V v = true → ct.quiet p k arch X V w = true → ct.rk w ≤ ct.rk v ∧
          (ct.rk w = ct.rk v → ct.js v ≠ .noSpin ∧ ct.js v ≠ .unfair i)) ∧
        (ct.quiet p k arch X V v = true → ∀ j, ct.js v = .unfair j → j ∉ X ∧ movesPF p k arch V (ct.nd v) j ≠ [])) := by
  unfold Cert.nodeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hpf, -⟩, hi⟩, -⟩, -⟩ := h
  refine ⟨hpf, fun i hlt => ⟨(hi i hlt).1, fun e w hew => ?_⟩⟩
  obtain ⟨h2, hj⟩ := (hi i hlt).2 (e, w) hew
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨hw, hkey⟩, h3⟩ := h2
  refine ⟨hw, hkey, fun hqv hqw => ?_, fun hq j hjs => ?_⟩
  · rcases h3 with h3 | ⟨h4, h5⟩
    · simp [hqv, hqw] at h3
    · refine ⟨h4, fun heq => ?_⟩
      rcases h5 with h5 | h5
      · exact absurd heq (by simpa using h5)
      · simpa using h5
  · rw [hq, hjs] at hj
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at hj
    exact ⟨by simpa using hj.1, hj.2⟩

/-- (D4) What `nodeOK` says of the environment edges. -/
theorem nodeOK_env_spec {v : Nat} (h : ct.nodeOK p k arch X V v = true) :
    (envsPF p k arch (ct.nd v)).length = (ct.te v).length ∧
    ∀ e w, (e, w) ∈ ct.me p k arch v → w < ct.nodes.size ∧ cfgKey e = cfgKey (ct.nodes[w]?.getD default) ∧
      (ct.quiet p k arch X V v = true → ct.quiet p k arch X V w = true → ct.rk w ≤ ct.rk v) ∧
      (ct.quiet p k arch X V v = true → ∀ j, ct.js v = .unfair j → j ∉ X ∧ movesPF p k arch V (ct.nd v) j ≠ []) := by
  unfold Cert.nodeOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨-, hlen⟩, hm⟩ := h
  refine ⟨hlen, fun e w hew => ?_⟩
  obtain ⟨h2, hj⟩ := hm (e, w) hew
  simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at h2
  obtain ⟨⟨hw, hkey⟩, h3⟩ := h2
  refine ⟨hw, hkey, fun hqv hqw => ?_, fun hq j hjs => ?_⟩
  · rcases h3 with h3 | h3
    · simp [hqv, hqw] at h3
    · exact h3
  · rw [hq, hjs] at hj
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true',
      List.isEmpty_eq_false_iff] at hj
    exact ⟨by simpa using hj.1, hj.2⟩

theorem pfB_noPromises {c : Cfg} (h : pfB c = true) (i : Nat) : noPromises c i = true := by
  unfold noPromises
  cases h1 : c.ths[i]? with
  | none => rfl
  | some th =>
    simp only [pfB, Array.all_eq_true] at h
    have hi := lt_of_get h1
    have := h i hi
    simp only [Array.getElem?_eq_getElem hi, Option.some.injEq] at h1
    subst h1
    simpa using this

theorem canon_get (c : Cfg) (i : Nat) : (canon c).ths[i]? = (c.ths[i]?).map (canonTh (locs c)) := by
  simp [canon_eq]

theorem noPromises_canon (c : Cfg) (i : Nat) : noPromises (canon c) i = noPromises c i := by
  unfold noPromises
  rw [canon_get]
  cases c.ths[i]? <;> rfl

theorem canon_size (c : Cfg) : (canon c).ths.size = c.ths.size := by simp [canon_eq]

theorem mem_zip_of_len {α β : Type} : ∀ {l : List α} {l' : List β}, l.length = l'.length → ∀ {x : α}, x ∈ l →
    ∃ y, (x, y) ∈ l.zip l'
  | [], _, _, _, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp at h
  | a :: l, b :: l', h, x, hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨b, by simp⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_len (by simpa using h) hx
      exact ⟨y, by simp [hy]⟩

theorem movesPF_lt {c e : Cfg} {i : Nat} (h : e ∈ movesPF p k arch V c i) : i < c.ths.size := by
  rcases Nat.lt_or_ge i c.ths.size with hi | hi
  · exact hi
  · rw [movesPF_out hi] at h; cases h

/-- (D4) A spurious wake of a present thread is an environment move of the node. -/
theorem envsPF_mem {c e : Cfg} {i : Nat} (hi : i < c.ths.size) (he : e ∈ wakesPF p k arch c i) :
    e ∈ envsPF p k arch c := by
  simp only [envsPF, List.mem_flatMap, List.mem_range]
  exact ⟨i, hi, he⟩

/-- (D4) At a node of an accepted certificate an environment move is matched to a node. -/
theorem env_node {c0 : Cfg} (hc : check p k arch X V ct c0 = true) {v : Nat} (hv : v < ct.nodes.size) {e : Cfg}
    (he : e ∈ envsPF p k arch (ct.nd v)) : ∃ w, (e, w) ∈ ct.me p k arch v := by
  obtain ⟨-, -, hall⟩ := check_spec hc
  exact mem_zip_of_len (nodeOK_env_spec (hall v hv)).1 he

theorem env_target {c0 : Cfg} (hc : check p k arch X V ct c0 = true) {v w : Nat} {e : Cfg} (hv : v < ct.nodes.size)
    (h : (e, w) ∈ ct.me p k arch v) : w < ct.nodes.size ∧ canon e = ct.nd w := by
  obtain ⟨-, -, hall⟩ := check_spec hc
  obtain ⟨hw, hkey, -⟩ := (nodeOK_env_spec (hall v hv)).2 e w h
  exact ⟨hw, cfgKey_canon hkey⟩

/-- **The node of a move.** At a node of an accepted certificate, a move of `movesPF` is matched to a node whose
`canon` form it has; it has no promise out. -/
theorem move_node {c0 : Cfg} (hc : check p k arch X V ct c0 = true) {v : Nat} (hv : v < ct.nodes.size) {i : Nat}
    {e : Cfg} (he : e ∈ movesPF p k arch V (ct.nd v) i) :
    ∃ w, (e, w) ∈ ct.mt p k arch V v i ∧ w < ct.nodes.size ∧ canon e = ct.nd w ∧ noPromises e i = true := by
  obtain ⟨-, -, hall⟩ := check_spec hc
  obtain ⟨-, hi⟩ := nodeOK_spec (hall v hv)
  have hlt := movesPF_lt he
  obtain ⟨hlen, hm⟩ := hi i hlt
  obtain ⟨w, hw⟩ := mem_zip_of_len hlen he
  obtain ⟨hwn, hkey, -⟩ := hm e w hw
  have hcan : canon e = ct.nd w := cfgKey_canon hkey
  refine ⟨w, hw, hwn, hcan, ?_⟩
  obtain ⟨hpfw, -⟩ := nodeOK_spec (hall w hwn)
  rw [← noPromises_canon, hcan]
  exact pfB_noPromises hpfw i

end

/-! ### Combinatorics on `Nat`-indexed sequences -/

theorem not_often {P : Nat → Prop} (h : ¬ Often P) : ∃ n, ∀ m, n ≤ m → ¬ P m := by
  rcases Classical.em (∃ n, ∀ m, n ≤ m → ¬ P m) with h1 | h1
  · exact h1
  · exact absurd (fun n => by
      rcases Classical.em (∃ m, n ≤ m ∧ P m) with h2 | h2
      · exact h2
      · exact absurd ⟨n, fun m hm hp => h2 ⟨m, hm, hp⟩⟩ h1) h

/-- Past some point a bounded sequence takes only values it takes infinitely often. -/
theorem ev_inf {f : Nat → Nat} {N : Nat} (hb : ∀ n, f n < N) :
    ∃ N0, ∀ n, N0 ≤ n → Often (fun m => f m = f n) := by
  have key : ∀ K, ∃ N0, ∀ n, N0 ≤ n → f n < K → Often (fun m => f m = f n) := by
    intro K
    induction K with
    | zero => exact ⟨0, fun n _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ K ih =>
      obtain ⟨N0, hN0⟩ := ih
      rcases Classical.em (Often (fun m => f m = K)) with hK | hK
      · refine ⟨N0, fun n hn hlt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h1 | h1
        · exact hN0 n hn h1
        · rw [h1]; exact hK
      · obtain ⟨m0, hm0⟩ := not_often hK
        refine ⟨max N0 m0, fun n hn hlt => ?_⟩
        have h1 : f n ≠ K := hm0 n (Nat.le_trans (Nat.le_max_right _ _) hn)
        exact hN0 n (Nat.le_trans (Nat.le_max_left _ _) hn) (by omega)
  obtain ⟨N0, h⟩ := key N
  exact ⟨N0, fun n hn => h n hn (hb n)⟩

/-- Infinitely many `P`-points of a bounded sequence share a value. -/
theorem often_pigeon {P : Nat → Prop} {f : Nat → Nat} {N : Nat} (hb : ∀ n, f n < N) (hP : Often P) :
    ∃ v, Often (fun m => P m ∧ f m = v) := by
  have key : ∀ K, Often (fun m => P m ∧ f m < K) → ∃ v, Often (fun m => P m ∧ f m = v) := by
    intro K
    induction K with
    | zero => intro h; obtain ⟨m, -, -, hm⟩ := h 0; exact absurd hm (Nat.not_lt_zero _)
    | succ K ih =>
      intro h
      rcases Classical.em (Often (fun m => P m ∧ f m = K)) with hK | hK
      · exact ⟨K, hK⟩
      · obtain ⟨m0, hm0⟩ := not_often hK
        apply ih
        intro n
        obtain ⟨m, hm, hp, hlt⟩ := h (max n m0)
        have h1 : ¬ (P m ∧ f m = K) := hm0 m (Nat.le_trans (Nat.le_max_right _ _) hm)
        refine ⟨m, Nat.le_trans (Nat.le_max_left _ _) hm, hp, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h2 | h2
        · exact h2
        · exact absurd ⟨hp, h2⟩ h1
  exact key N (fun n => by obtain ⟨m, hm, hp⟩ := hP n; exact ⟨m, hm, hp, hb m⟩)

theorem noninc_le {g : Nat → Nat} {n0 : Nat} (hg : ∀ n, n0 ≤ n → g (n + 1) ≤ g n) :
    ∀ d, g (n0 + d) ≤ g n0
  | 0 => Nat.le_refl _
  | d + 1 => Nat.le_trans (hg (n0 + d) (Nat.le_add_right _ _)) (noninc_le hg d)

/-- A non-increasing sequence of naturals is eventually constant. -/
theorem noninc_stab {g : Nat → Nat} : ∀ (a n0 : Nat), g n0 ≤ a → (∀ n, n0 ≤ n → g (n + 1) ≤ g n) →
    ∃ N1, n0 ≤ N1 ∧ ∀ n, N1 ≤ n → g n = g N1
  | 0, n0, ha, hg => ⟨n0, Nat.le_refl _, fun n hn => by
      have := noninc_le hg (n - n0)
      rw [Nat.add_sub_cancel' hn] at this
      omega⟩
  | a + 1, n0, ha, hg => by
      rcases Classical.em (∀ n, n0 ≤ n → g n = g n0) with h | h
      · exact ⟨n0, Nat.le_refl _, h⟩
      · have h' : ∃ n, n0 ≤ n ∧ g n ≠ g n0 := by
          rcases Classical.em (∃ n, n0 ≤ n ∧ g n ≠ g n0) with h2 | h2
          · exact h2
          · exact absurd (fun n hn => by
              rcases Classical.em (g n = g n0) with h3 | h3
              · exact h3
              · exact absurd ⟨n, hn, h3⟩ h2) h
        obtain ⟨n1, hn1, hne⟩ := h'
        have hle := noninc_le hg (n1 - n0)
        rw [Nat.add_sub_cancel' hn1] at hle
        obtain ⟨N1, hN1, hst⟩ := noninc_stab a n1 (by omega) (fun n hn => hg n (Nat.le_trans hn1 hn))
        exact ⟨N1, Nat.le_trans hn1 hN1, hst⟩

/-! ### The run on the certificate -/

open Classical in
/-- The next node index: the target the certificate names for the move taken, if any. -/
noncomputable def idxNext (p : Prog) (k : Promises.Knobs) (arch : Arch) (V : List Nat) (ct : Cert)
    (r : LRun (machineE p k arch).L) (n v : Nat) : Nat :=
  match (r.lbl n : Option (Nat × Lbl)) with
  | some (i, .thr) => if h : ∃ w, (r.cfg (n + 1), w) ∈ ct.mt p k arch V v i then Classical.choose h else v
  | some (_, .env) => if h : ∃ w, (r.cfg (n + 1), w) ∈ ct.me p k arch v then Classical.choose h else v
  | _ => v

/-- The node index of the run at `n`. -/
noncomputable def idx (p : Prog) (k : Promises.Knobs) (arch : Arch) (V : List Nat) (ct : Cert)
    (r : LRun (machineE p k arch).L) : Nat → Nat
  | 0 => 0
  | n + 1 => idxNext p k arch V ct r n (idx p k arch V ct r n)

section Run
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {ct : Cert} {c0 : Cfg}
  {r : LRun (machineE p k arch).L}

theorem lbl_cases (hpf : PromiseFreeRun r) (n : Nat) :
    r.lbl n = none ∨ (∃ i, r.lbl n = some (i, .thr)) ∨ ∃ i, r.lbl n = some (i, .env) := by
  cases h : r.lbl n with
  | none => exact Or.inl rfl
  | some l =>
    obtain ⟨i, b⟩ := l
    cases b
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact absurd h (hpf n i)
    · exact Or.inr (Or.inr ⟨i, rfl⟩)

theorem step_target (hc : check p k arch X V ct c0 = true) {v i w : Nat} {e : Cfg} (hv : v < ct.nodes.size)
    (h : (e, w) ∈ ct.mt p k arch V v i) : w < ct.nodes.size ∧ canon e = ct.nd w := by
  obtain ⟨-, -, hall⟩ := check_spec hc
  obtain ⟨-, hi⟩ := nodeOK_spec (hall v hv)
  have he : e ∈ movesPF p k arch V (ct.nd v) i := (List.of_mem_zip h).1
  obtain ⟨hw, hkey, -⟩ := (hi i (movesPF_lt he)).2 e w h
  exact ⟨hw, cfgKey_canon hkey⟩

theorem idx_none (n : Nat) (hl : r.lbl n = none) : idx p k arch V ct r (n + 1) = idx p k arch V ct r n := by
  simp [idx, idxNext, hl]

/-- One step of the run on the certificate. -/
theorem run_step (hc : check p k arch X V ct c0 = true) (hr : (machineE p k arch).Run r) (hsr : ScriptedRun V r)
    (n : Nat)
    (hv : idx p k arch V ct r n < ct.nodes.size) (heq : r.cfg n = ct.nd (idx p k arch V ct r n))
    (hcoh : CfgCoh (r.cfg n)) (i : Nat) (hl : r.lbl n = some (i, .thr)) :
    (r.cfg (n + 1), idx p k arch V ct r (n + 1)) ∈ ct.mt p k arch V (idx p k arch V ct r n) i ∧
      idx p k arch V ct r (n + 1) < ct.nodes.size ∧ r.cfg (n + 1) = ct.nd (idx p k arch V ct r (n + 1)) ∧
      CfgCoh (r.cfg (n + 1)) := by
  have hm := hr n
  have hst : mstepE p k arch (r.cfg n) (i, .thr) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
  obtain ⟨hcoh', -, -⟩ := moveE_facts hcoh hst
  rw [heq] at hst
  obtain ⟨-, -, hall⟩ := check_spec hc
  obtain ⟨hpfv, -⟩ := nodeOK_spec (hall _ hv)
  have hin := movesPF_complete (pfB_noPromises hpfv i) hst
    (fun th x w a e' h1 h2 => hsr n i th x w a e' hl (by rw [heq]; exact h1) h2)
  obtain ⟨w, hw, -⟩ := move_node hc hv hin
  have hex : ∃ w, (r.cfg (n + 1), w) ∈ ct.mt p k arch V (idx p k arch V ct r n) i := ⟨w, hw⟩
  have hi : idx p k arch V ct r (n + 1) = Classical.choose hex := by simp [idx, idxNext, hl, hex]
  have hsp := Classical.choose_spec hex
  rw [← hi] at hsp
  obtain ⟨hw', hcan⟩ := step_target hc hv hsp
  exact ⟨hsp, hw', by rw [← hcan, canon_self hcoh'], hcoh'⟩

/-- (D4) An environment step of the run on the certificate. -/
theorem run_step_env (hc : check p k arch X V ct c0 = true) (hr : (machineE p k arch).Run r) (n : Nat)
    (hv : idx p k arch V ct r n < ct.nodes.size) (heq : r.cfg n = ct.nd (idx p k arch V ct r n))
    (hcoh : CfgCoh (r.cfg n)) (i : Nat) (hl : r.lbl n = some (i, .env)) :
    (r.cfg (n + 1), idx p k arch V ct r (n + 1)) ∈ ct.me p k arch (idx p k arch V ct r n) ∧
      idx p k arch V ct r (n + 1) < ct.nodes.size ∧ r.cfg (n + 1) = ct.nd (idx p k arch V ct r (n + 1)) ∧
      CfgCoh (r.cfg (n + 1)) := by
  have hm := hr n
  have hst : mstepE p k arch (r.cfg n) (i, .env) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
  obtain ⟨hcoh', -, -, hi, -⟩ := envE_facts hcoh hst
  rw [heq] at hst hi
  obtain ⟨-, -, hall⟩ := check_spec hc
  obtain ⟨hpfv, -⟩ := nodeOK_spec (hall _ hv)
  have hin := envsPF_mem hi (wakesPF_complete (pfB_noPromises hpfv i) hst)
  have hex : ∃ w, (r.cfg (n + 1), w) ∈ ct.me p k arch (idx p k arch V ct r n) := env_node hc hv hin
  have hi' : idx p k arch V ct r (n + 1) = Classical.choose hex := by simp [idx, idxNext, hl, hex]
  have hsp := Classical.choose_spec hex
  rw [← hi'] at hsp
  obtain ⟨hw', hcan⟩ := env_target hc hv hsp
  exact ⟨hsp, hw', by rw [← hcan, canon_self hcoh'], hcoh'⟩

/-- **The run walks the certificate.** -/
theorem run_nodes (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) :
    ∀ n, idx p k arch V ct r n < ct.nodes.size ∧ r.cfg n = ct.nd (idx p k arch V ct r n) ∧ CfgCoh (r.cfg n)
  | 0 => by
    obtain ⟨hN, hkey, -⟩ := check_spec hc
    have hi0 : idx p k arch V ct r 0 = 0 := rfl
    rw [hi0]
    refine ⟨hN, ?_, hs ▸ h0⟩
    show r.cfg 0 = canon _
    rw [hs, ← cfgKey_canon hkey, canon_self h0]
  | n + 1 => by
    obtain ⟨hv, heq, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr n
    rcases lbl_cases hpf n with hl | ⟨i, hl⟩ | ⟨i, hl⟩
    · have hm := hr n
      have he : r.cfg (n + 1) = r.cfg n := by rw [hl] at hm; exact hm
      rw [idx_none n hl, he]
      exact ⟨hv, heq, hcoh⟩
    · exact (run_step hc hr hsr n hv heq hcoh i hl).2
    · exact (run_step_env hc hr n hv heq hcoh i hl).2

/-- The move taken at `n` is a certificate edge into the next node. -/
theorem idx_step (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n i : Nat) (hl : r.lbl n = some (i, .thr)) :
    (r.cfg (n + 1), idx p k arch V ct r (n + 1)) ∈ ct.mt p k arch V (idx p k arch V ct r n) i := by
  obtain ⟨hv, heq, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr n
  exact (run_step hc hr hsr n hv heq hcoh i hl).1

theorem progB_sound {c c' : Cfg} {i : Nat} (h : progB c c' i = true) : Progress c c' i := by
  simp only [progB, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨b, -, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, hb⟩

theorem run_mono_step (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) :
    (r.cfg n).mem.size ≤ (r.cfg (n + 1)).mem.size ∧ ∀ j b, cohOf (r.cfg n) j b ≤ cohOf (r.cfg (n + 1)) j b := by
  obtain ⟨-, -, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr n
  have hm := hr n
  rcases lbl_cases hpf n with hl | ⟨i, hl⟩ | ⟨i, hl⟩
  · have he : r.cfg (n + 1) = r.cfg n := by rw [hl] at hm; exact hm
    rw [he]; exact ⟨Nat.le_refl _, fun _ _ => Nat.le_refl _⟩
  · have hst : mstepE p k arch (r.cfg n) (i, .thr) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
    obtain ⟨-, hme, hle⟩ := moveE_facts hcoh hst
    exact ⟨hme.size, fun j b => cohOf_of_cohLeX hle j b⟩
  · have hst : mstepE p k arch (r.cfg n) (i, .env) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
    obtain ⟨-, hme, hle, -⟩ := envE_facts hcoh hst
    exact ⟨hme.size, fun j b => cohOf_of_cohLeX hle j b⟩

/-- Memory size and coherence views only grow along the run. -/
theorem run_mono (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) :
    ∀ d, (r.cfg n).mem.size ≤ (r.cfg (n + d)).mem.size ∧ ∀ j b, cohOf (r.cfg n) j b ≤ cohOf (r.cfg (n + d)) j b
  | 0 => ⟨Nat.le_refl _, fun _ _ => Nat.le_refl _⟩
  | d + 1 => by
    obtain ⟨h1, h2⟩ := run_mono hc h0 hr hs hpf hsr n d
    obtain ⟨h3, h4⟩ := run_mono_step hc h0 hr hs hpf hsr (n + d)
    exact ⟨Nat.le_trans h1 h3, fun j b => Nat.le_trans (h2 j b) (h4 j b)⟩

/-- **Finitely many `Progress` steps.** Two progress steps at the same node would undo a strict increase. -/
theorem prog_finite (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) :
    ¬ Often (fun n => ∃ j, Progress (r.cfg n) (r.cfg (n + 1)) j) := by
  intro hP
  have hb : ∀ n, idx p k arch V ct r n < ct.nodes.size := fun n => (run_nodes hc h0 hr hs hpf hsr n).1
  obtain ⟨v, hv⟩ := often_pigeon hb hP
  obtain ⟨n, -, ⟨j, hj⟩, hn⟩ := hv 0
  obtain ⟨m, hm, -, hmv⟩ := hv (n + 1)
  have hcm : r.cfg m = r.cfg n := by
    rw [(run_nodes hc h0 hr hs hpf hsr m).2.1, (run_nodes hc h0 hr hs hpf hsr n).2.1, hmv, hn]
  obtain ⟨h1, h2⟩ := run_mono hc h0 hr hs hpf hsr (n + 1) (m - (n + 1))
  rw [Nat.add_sub_cancel' hm, hcm] at h1 h2
  rcases hj with hj | ⟨b, hb'⟩
  · omega
  · have := h2 j b; omega

theorem live_of {D : Nat → Option Nat} (hD : ∀ i, D i ≠ none → i ∈ X) {j n : Nat} (hj : j ∉ X)
    (hlt : j < (r.cfg n).ths.size) : LiveS r D j := by
  refine ⟨⟨n, hlt⟩, ?_⟩
  rcases Classical.em (D j = none) with h | h
  · exact h
  · exact absurd (hD j h) hj

theorem no_move_lbl (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) {m : Nat}
    (hno : ∀ i, movesPF p k arch V (ct.nd (idx p k arch V ct r m)) i = [])
    (hne : envsPF p k arch (ct.nd (idx p k arch V ct r m)) = []) : r.lbl m = none := by
  rcases lbl_cases hpf m with hl | ⟨i, hl⟩ | ⟨i, hl⟩
  · exact hl
  rotate_left
  · obtain ⟨hv, heq, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr m
    have hm := hr m
    have hst : mstepE p k arch (r.cfg m) (i, .env) (r.cfg (m + 1)) := by rw [hl] at hm; exact hm
    obtain ⟨-, -, -, hi, -⟩ := envE_facts hcoh hst
    rw [heq] at hst hi
    obtain ⟨-, -, hall⟩ := check_spec hc
    obtain ⟨hpfv, -⟩ := nodeOK_spec (hall _ hv)
    have hin := envsPF_mem hi (wakesPF_complete (pfB_noPromises hpfv i) hst)
    rw [hne] at hin
    cases hin
  · obtain ⟨hv, heq, -⟩ := run_nodes hc h0 hr hs hpf hsr m
    have hm := hr m
    have hst : mstepE p k arch (r.cfg m) (i, .thr) (r.cfg (m + 1)) := by rw [hl] at hm; exact hm
    rw [heq] at hst
    obtain ⟨-, -, hall⟩ := check_spec hc
    obtain ⟨hpfv, -⟩ := nodeOK_spec (hall _ hv)
    have hin := movesPF_complete (pfB_noPromises hpfv i) hst
      (fun th x w a e' h1 h2 => hsr m i th x w a e' hl (by rw [heq]; exact h1) h2)
    rw [hno i] at hin
    cases hin

/-- At a node with no move (thread or environment) the run stutters forever. -/
theorem stuck_run (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat)
    (hno : ∀ i, movesPF p k arch V (ct.nd (idx p k arch V ct r n)) i = [])
    (hne : envsPF p k arch (ct.nd (idx p k arch V ct r n)) = []) :
    ∀ d, idx p k arch V ct r (n + d) = idx p k arch V ct r n ∧ r.lbl (n + d) = none
  | 0 => ⟨rfl, no_move_lbl hc h0 hr hs hpf hsr hno hne⟩
  | d + 1 => by
    obtain ⟨h1, h2⟩ := stuck_run hc h0 hr hs hpf hsr n hno hne d
    have h3 : idx p k arch V ct r (n + (d + 1)) = idx p k arch V ct r n := by
      rw [← Nat.add_assoc, idx_none _ h2, h1]
    exact ⟨h3, no_move_lbl hc h0 hr hs hpf hsr (by rw [h3]; exact hno) (by rw [h3]; exact hne)⟩

theorem quiet_of {v : Nat}
    (h : ∀ j, j < (ct.nd v).ths.size → j ∉ X → ∀ e ∈ movesPF p k arch V (ct.nd v) j, progB (ct.nd v) e j = false) :
    ct.quiet p k arch X V v = true := by
  simp only [Cert.quiet, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  intro j hj
  rcases Classical.em (j ∈ X) with hx | hx
  · left; simpa using hx
  · right; intro e he; simpa using h j hj hx e he

end Run

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {c0 : Cfg} {ct : Cert}

/-- **Item 38 v1 (liveness, completeness).** -/
theorem no_livelock_of_check (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0)
    (r : LRun (machineE p k arch).L) (D : Nat → Option Nat) (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hD : ∀ i, D i ≠ none → i ∈ X) (hf : FairS (machineE p k arch) r D) :
    ¬ LivelockS (machineE p k arch) r D := by
  rintro ⟨-, -, i, -, hoft⟩
  have hrn := run_nodes hc h0 hr hs hpf hsr
  have hb : ∀ n, idx p k arch V ct r n < ct.nodes.size := fun n => (hrn n).1
  obtain ⟨-, -, hall⟩ := check_spec hc
  have hpfn := prog_finite hc h0 hr hs hpf hsr
  have hmach : ∀ n j e, e ∈ movesPF p k arch V (ct.nd (idx p k arch V ct r n)) j →
      mstepE p k arch (r.cfg n) (j, .thr) e := by
    intro n j e he
    obtain ⟨w, -, -, -, hnp⟩ := move_node hc (hb n) he
    rw [(hrn n).2.1]; exact movesPF_sound he hnp
  obtain ⟨N0, hN0⟩ := ev_inf hb
  -- the nodes visited from `N0` on are quiet
  have hq : ∀ n, N0 ≤ n → ct.quiet p k arch X V (idx p k arch V ct r n) = true := by
    intro n hn
    apply quiet_of
    intro j hj hjX e he
    cases hpb : progB (ct.nd (idx p k arch V ct r n)) e j with
    | false => rfl
    | true =>
      exfalso
      have hlt : j < (r.cfg n).ths.size := by rw [(hrn n).2.1]; exact hj
      have hp := hf.prog j (live_of hD hjX hlt) (fun m0 => by
        obtain ⟨m, hm, hmv⟩ := hN0 n hn m0
        refine ⟨m, hm, e, hmach m j e (by rw [hmv]; exact he), ?_⟩
        rw [(hrn m).2.1, hmv]; exact progB_sound hpb)
      apply hpfn
      intro m0
      obtain ⟨m, hm, -, hpr⟩ := hp m0
      exact ⟨m, hm, j, hpr⟩
  -- an edge taken from `N0` on stays within quiet nodes
  have hedge : ∀ n i', N0 ≤ n → r.lbl n = some (i', .thr) →
      ct.rk (idx p k arch V ct r (n + 1)) ≤ ct.rk (idx p k arch V ct r n) ∧
      (ct.rk (idx p k arch V ct r (n + 1)) = ct.rk (idx p k arch V ct r n) →
        ct.js (idx p k arch V ct r n) ≠ .noSpin ∧ ct.js (idx p k arch V ct r n) ≠ .unfair i') := by
    intro n i' hn hl
    have hst := idx_step hc h0 hr hs hpf hsr n i' hl
    have he : r.cfg (n + 1) ∈ movesPF p k arch V (ct.nd (idx p k arch V ct r n)) i' := (List.of_mem_zip hst).1
    obtain ⟨-, hi⟩ := nodeOK_spec (hall _ (hb n))
    exact ((hi i' (movesPF_lt he)).2 _ _ hst).2.2.1 (hq n hn) (hq (n + 1) (Nat.le_succ_of_le hn))
  have hmono : ∀ n, N0 ≤ n → ct.rk (idx p k arch V ct r (n + 1)) ≤ ct.rk (idx p k arch V ct r n) := by
    intro n hn
    rcases lbl_cases hpf n with hl | ⟨i', hl⟩ | ⟨i', hl⟩
    · rw [idx_none n hl]; exact Nat.le_refl _
    · exact (hedge n i' hn hl).1
    · obtain ⟨hst, -, -, -⟩ := run_step_env hc hr n (hb n) (hrn n).2.1 (hrn n).2.2 i' hl
      exact ((nodeOK_env_spec (hall _ (hb n))).2 _ _ hst).2.2.1 (hq n hn) (hq (n + 1) (Nat.le_succ_of_le hn))
  obtain ⟨N1, hN01, hN1⟩ :=
    noninc_stab (g := fun n => ct.rk (idx p k arch V ct r n)) _ N0 (Nat.le_refl _) hmono
  have hrk : ∀ n, N1 ≤ n → ct.rk (idx p k arch V ct r n) = ct.rk (idx p k arch V ct r N1) := fun n hn => hN1 n hn
  have hjs : ∀ n, N1 ≤ n → ct.js (idx p k arch V ct r n) = ct.js (idx p k arch V ct r N1) := by
    intro n hn; unfold Cert.js; rw [hrk n hn]
  have hsame : ∀ n i', N1 ≤ n → r.lbl n = some (i', .thr) →
      ct.js (idx p k arch V ct r N1) ≠ .noSpin ∧ ct.js (idx p k arch V ct r N1) ≠ .unfair i' := by
    intro n i' hn hl
    have h1 : ct.rk (idx p k arch V ct r (n + 1)) = ct.rk (idx p k arch V ct r n) := by
      rw [hrk (n + 1) (Nat.le_succ_of_le hn), hrk n hn]
    rw [← hjs n hn]
    exact (hedge n i' (Nat.le_trans hN01 hn) hl).2 h1
  obtain ⟨m1, hm1, hl1⟩ := hoft N1
  have hJ := (hsame m1 i hm1 hl1).1
  cases hJs : ct.js (idx p k arch V ct r N1) with
  | noSpin => exact hJ hJs
  | unfair j =>
    have hjm : ∀ n, N1 ≤ n → j ∉ X ∧ movesPF p k arch V (ct.nd (idx p k arch V ct r n)) j ≠ [] := by
      intro n hn
      rcases Classical.em (∃ i', movesPF p k arch V (ct.nd (idx p k arch V ct r n)) i' ≠ []) with ⟨i', hi'⟩ | hno
      · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hi'
        obtain ⟨w, hw, -⟩ := move_node hc (hb n) he
        obtain ⟨-, hi⟩ := nodeOK_spec (hall _ (hb n))
        exact ((hi i' (movesPF_lt he)).2 e w hw).2.2.2 (hq n (Nat.le_trans hN01 hn)) j
          (by rw [hjs n hn]; exact hJs)
      · rcases Classical.em (envsPF p k arch (ct.nd (idx p k arch V ct r n)) = []) with hne | hne
        · exfalso
          have hno' : ∀ i', movesPF p k arch V (ct.nd (idx p k arch V ct r n)) i' = [] := fun i' => by
            rcases Classical.em (movesPF p k arch V (ct.nd (idx p k arch V ct r n)) i' = []) with h | h
            · exact h
            · exact absurd ⟨i', h⟩ hno
          obtain ⟨m, hm, hlm⟩ := hoft n
          have := (stuck_run hc h0 hr hs hpf hsr n hno' hne (m - n)).2
          rw [Nat.add_sub_cancel' hm, hlm] at this
          cases this
        · obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨w, hw⟩ := env_node hc (hb n) he
          exact ((nodeOK_env_spec (hall _ (hb n))).2 e w hw).2.2.2 (hq n (Nat.le_trans hN01 hn)) j
            (by rw [hjs n hn]; exact hJs)
    obtain ⟨hjX, hne⟩ := hjm N1 (Nat.le_refl _)
    obtain ⟨e1, he1⟩ := List.exists_mem_of_ne_nil _ hne
    have hlt : j < (r.cfg N1).ths.size := by rw [(hrn N1).2.1]; exact movesPF_lt he1
    have hw := hf.weak j (live_of hD hjX hlt) ⟨N1, fun n hn => by
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (hjm n hn).2
      exact ⟨e, hmach n j e he⟩⟩
    obtain ⟨m, hm, hlm⟩ := hw N1
    exact (hsame m j hm hlm).2 hJs

theorem reach_of_check (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0)
    (r : LRun (machineE p k arch).L) (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) :
    ∃ v, v < ct.nodes.size ∧ r.cfg n = canon (ct.nodes[v]?.getD default) := by
  obtain ⟨hv, heq, -⟩ := run_nodes hc h0 hr hs hpf hsr n
  exact ⟨_, hv, heq⟩

theorem final_canon (c : Cfg) : (canon c).final = c.final := by
  simp only [Cfg.final, canon_eq, Array.all_map]
  rfl

theorem outcome_canon (m : Nat) (watch : List (Nat × Nat)) (c : Cfg) :
    outcome m watch (canon c) = outcome m watch c := by
  simp only [outcome, canon_get]
  have h1 : ∀ o : Option TTh, (o.map (canonTh (locs c))).bind TermSmoke.resWs = o.bind TermSmoke.resWs := by
    intro o; cases o <;> rfl
  simp only [h1]
  rfl

theorem outcome_of_check (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0)
    (r : LRun (machineE p k arch).L) (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) (hfin : (r.cfg n).final = true) (m : Nat) (watch : List (Nat × Nat)) :
    ∃ v, v < ct.nodes.size ∧ (ct.nodes[v]?.getD default).final = true ∧
      outcome m watch (r.cfg n) = outcome m watch (ct.nodes[v]?.getD default) := by
  obtain ⟨v, hv, heq⟩ := reach_of_check hc h0 r hr hs hpf hsr n
  refine ⟨v, hv, ?_, ?_⟩
  · rw [← final_canon, ← heq]; exact hfin
  · rw [heq, outcome_canon]

end

/-! ### Without spawns, `Fair` and `Livelock` -/

section Spawn
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {ct : Cert} {c0 : Cfg}
  {r : LRun (machineE p k arch).L}

theorem move_size {c e : Cfg} {i : Nat} (he : e ∈ movesPF p k arch V c i)
    (hsp : TermSpawnSuccs.spawnSuccsAt c i = []) : e.ths.size = c.ths.size := by
  simp only [movesPF, List.mem_append, hsp, List.not_mem_nil, or_false] at he
  rcases he with he | he
  · exact TermLiveMach.threadSteps_size he
  · obtain ⟨x, n, a, e', th, rt, ws, rs, h1, -, -, -, -, -, -, rfl⟩ := extSuccs0_extBy he
    rw [wake_size]
    exact (extCfg_facts h1 x n e' ws rs).2.1

theorem noSpawnB_spec (h : noSpawnB ct = true) {v i : Nat} (hv : v < ct.nodes.size)
    (hi : i < (ct.nd v).ths.size) : TermSpawnSuccs.spawnSuccsAt (ct.nd v) i = [] := by
  simp only [noSpawnB, List.all_eq_true, List.mem_range, List.isEmpty_iff] at h
  exact h v hv i hi

/-- Without spawn moves the thread count is constant along the run. -/
theorem run_size (hc : check p k arch X V ct c0 = true) (hns : noSpawnB ct = true) (h0 : CfgCoh c0)
    (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) :
    ∀ n, (r.cfg n).ths.size = (r.cfg 0).ths.size
  | 0 => rfl
  | n + 1 => by
    rw [← run_size hc hns h0 hr hs hpf hsr n]
    rcases lbl_cases hpf n with hl | ⟨i, hl⟩ | ⟨i, hl⟩
    · have hm := hr n
      have he : r.cfg (n + 1) = r.cfg n := by rw [hl] at hm; exact hm
      rw [he]
    · obtain ⟨hv, heq, -⟩ := run_nodes hc h0 hr hs hpf hsr n
      have he := (List.of_mem_zip (idx_step hc h0 hr hs hpf hsr n i hl)).1
      rw [heq]
      exact move_size he (noSpawnB_spec hns hv (movesPF_lt he))
    · obtain ⟨-, -, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr n
      have hm := hr n
      have hst : mstepE p k arch (r.cfg n) (i, .env) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
      exact (envE_facts hcoh hst).2.2.2.2

end Spawn

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {c0 : Cfg} {ct : Cert}

theorem no_livelock_of_check_fair (hc : check p k arch X V ct c0 = true) (hns : noSpawnB ct = true)
    (h0 : CfgCoh c0)
    (r : LRun (machineE p k arch).L) (D : Nat → Option Nat) (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hD : ∀ i, D i ≠ none → i ∈ X) (hf : Fair (machineE p k arch) r D (fun _ => True)) :
    ¬ Livelock (machineE p k arch) r D := by
  have hsz := run_size hc hns h0 hr hs hpf hsr
  have hlive : ∀ i, LiveS r D i → Live r D i := fun i ⟨⟨n, hn⟩, hd⟩ => ⟨by rw [← hsz n]; exact hn, hd⟩
  have hfs : FairS (machineE p k arch) r D :=
    ⟨fun i hi => hf.weak i (hlive i hi), fun i hi => hf.prog i (hlive i hi)⟩
  rintro ⟨n0, hfz, i, hi, hoft⟩
  exact no_livelock_of_check hc h0 r D hr hs hpf hsr hD hfs ⟨n0, hfz, i, ⟨⟨0, hi.1⟩, hi.2⟩, hoft⟩

end

/-! ### Termination -/

theorem bdd_fin (h : Nat → Nat) : ∀ N, ∃ B, ∀ v, v < N → h v ≤ B
  | 0 => ⟨0, fun v hv => absurd hv (Nat.not_lt_zero _)⟩
  | N + 1 => by
    obtain ⟨B, hB⟩ := bdd_fin h N
    refine ⟨max B (h N), fun v hv => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with h1 | h1
    · exact Nat.le_trans (hB v h1) (Nat.le_max_left _ _)
    · rw [h1]; exact Nat.le_max_right _ _

section Term
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {ct : Cert} {c0 : Cfg}
  {r : LRun (machineE p k arch).L}

theorem run_memext (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (n : Nat) : ∀ d, MemExt (r.cfg n).mem (r.cfg (n + d)).mem
  | 0 => Promises.Sim.MemExt.refl _
  | d + 1 => by
    refine Promises.Sim.MemExt.trans (run_memext hc h0 hr hs hpf hsr n d) ?_
    obtain ⟨-, -, hcoh⟩ := run_nodes hc h0 hr hs hpf hsr (n + d)
    have hm := hr (n + d)
    rcases lbl_cases hpf (n + d) with hl | ⟨i, hl⟩ | ⟨i, hl⟩
    · have he : r.cfg (n + d + 1) = r.cfg (n + d) := by rw [hl] at hm; exact hm
      show MemExt _ (r.cfg (n + d + 1)).mem
      rw [he]; exact Promises.Sim.MemExt.refl _
    · have hst : mstepE p k arch (r.cfg (n + d)) (i, .thr) (r.cfg (n + d + 1)) := by rw [hl] at hm; exact hm
      exact (moveE_facts hcoh hst).2.1
    · have hst : mstepE p k arch (r.cfg (n + d)) (i, .env) (r.cfg (n + d + 1)) := by rw [hl] at hm; exact hm
      exact (envE_facts hcoh hst).2.1

theorem step_lt (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) {n i : Nat} (hl : r.lbl n = some (i, .thr)) :
    i < (r.cfg n).ths.size := by
  obtain ⟨-, heq, -⟩ := run_nodes hc h0 hr hs hpf hsr n
  have he := (List.of_mem_zip (idx_step hc h0 hr hs hpf hsr n i hl)).1
  rw [heq]; exact movesPF_lt he

theorem node_move (hc : check p k arch X V ct c0 = true) (h0 : CfgCoh c0) (hr : (machineE p k arch).Run r)
    (hs : r.cfg 0 = c0) (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) {n j : Nat} {e : Cfg}
    (he : e ∈ movesPF p k arch V (ct.nd (idx p k arch V ct r n)) j) : mstepE p k arch (r.cfg n) (j, .thr) e := by
  obtain ⟨hv, heq, -⟩ := run_nodes hc h0 hr hs hpf hsr n
  obtain ⟨w, -, -, -, hnp⟩ := move_node hc hv he
  rw [heq]; exact movesPF_sound he hnp

theorem noStuckB_spec (h : noStuckB p k arch V ct = true) {v : Nat} (hv : v < ct.nodes.size) :
    (ct.nd v).final = true ∨ ∃ i, i < (ct.nd v).ths.size ∧ movesPF p k arch V (ct.nd v) i ≠ [] := by
  simp only [noStuckB, List.all_eq_true, List.mem_range, Bool.or_eq_true, List.any_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  exact h v hv

end Term

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {X : List Nat} {V : List Nat} {c0 : Cfg} {ct : Cert}

theorem terminates_of_check (hc : check p k arch [] V ct c0 = true) (hst : noStuckB p k arch V ct = true)
    (h0 : CfgCoh c0)
    (r : LRun (machineE p k arch).L) (hr : (machineE p k arch).Run r) (hs : r.cfg 0 = c0)
    (hpf : PromiseFreeRun r) (hsr : ScriptedRun V r) (hf : FairS (machineE p k arch) r (fun _ => none)) :
    ∃ n, (r.cfg n).final = true := by
  have hrn := run_nodes hc h0 hr hs hpf hsr
  have hb : ∀ n, idx p k arch V ct r n < ct.nodes.size := fun n => (hrn n).1
  obtain ⟨Bt, hBt⟩ := bdd_fin (fun v => (ct.nd v).ths.size) ct.nodes.size
  obtain ⟨Bm, hBm⟩ := bdd_fin (fun v => (ct.nd v).mem.size) ct.nodes.size
  have hszt : ∀ n, (r.cfg n).ths.size ≤ Bt := fun n => by rw [(hrn n).2.1]; exact hBt _ (hb n)
  have hszm : ∀ n, (r.cfg n).mem.size ≤ Bm := fun n => by rw [(hrn n).2.1]; exact hBm _ (hb n)
  rcases Classical.em (Often (fun n => ∃ i, r.lbl n = some (i, .thr))) with hA | hB
  · -- some thread steps infinitely often while memory freezes: a `LivelockS`
    exfalso
    have hfb : ∀ n, (r.lbl n).elim 0 Prod.fst < Bt + 1 := by
      intro n
      rcases lbl_cases hpf n with hl | ⟨i, hl⟩ | ⟨i, hl⟩
      · rw [hl]; show 0 < Bt + 1; omega
      · have := step_lt hc h0 hr hs hpf hsr hl
        have := hszt n
        simp only [hl, Option.elim]
        omega
      · have hm := hr n
        have hst : mstepE p k arch (r.cfg n) (i, .env) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
        have := (envE_facts (hrn n).2.2 hst).2.2.2.1
        have := hszt n
        simp only [hl, Option.elim]
        omega
    obtain ⟨v, hv⟩ := often_pigeon hfb hA
    have hov : Often (fun n => r.lbl n = some (v, .thr)) := fun n0 => by
      obtain ⟨m, hm, ⟨i, hl⟩, hfv⟩ := hv n0
      have h1 : (r.lbl m).elim 0 Prod.fst = i := by rw [hl]; rfl
      have h2 : i = v := h1 ▸ hfv
      exact ⟨m, hm, by show r.lbl m = some (v, .thr); rw [hl, h2]⟩
    have hmono : ∀ n, 0 ≤ n → Bm - (r.cfg (n + 1)).mem.size ≤ Bm - (r.cfg n).mem.size := fun n _ => by
      have := (run_mono_step hc h0 hr hs hpf hsr n).1; omega
    obtain ⟨N1, -, hN1⟩ := noninc_stab (g := fun n => Bm - (r.cfg n).mem.size) _ 0 (Nat.le_refl _) hmono
    have hfz : Frozen r N1 := by
      intro n hn
      have h1 : Bm - (r.cfg n).mem.size = Bm - (r.cfg N1).mem.size := hN1 n hn
      have h2 := run_memext hc h0 hr hs hpf hsr N1 (n - N1)
      rw [Nat.add_sub_cancel' hn] at h2
      have h3 := hszm n
      have h4 := hszm N1
      exact TermLiveMach.memExt_eq_of_size h2 (by omega)
    obtain ⟨m, -, hlm⟩ := hov 0
    exact no_livelock_of_check hc h0 r (fun _ => none) hr hs hpf hsr (fun i h => absurd rfl h) hf
      ⟨N1, hfz, v, ⟨⟨m, step_lt hc h0 hr hs hpf hsr hlm⟩, rfl⟩, hov⟩
  · -- eventually the run stutters at one node, which is final by `noStuckB` and `FairS.weak`
    obtain ⟨N0, hN0⟩ := not_often hB
    have hnothr : ∀ m, N0 ≤ m → r.lbl m = none ∨ ∃ i, r.lbl m = some (i, .env) := fun m hm => by
      rcases lbl_cases hpf m with hl | ⟨i, hl⟩ | hl
      · exact Or.inl hl
      · exact absurd ⟨i, hl⟩ (hN0 m hm)
      · exact Or.inr hl
    have hmass : ∀ n, N0 ≤ n → termMass (r.cfg (n + 1)) ≤ termMass (r.cfg n) := fun n hn => by
      have hm := hr n
      rcases hnothr n hn with hl | ⟨i, hl⟩
      · have he : r.cfg (n + 1) = r.cfg n := by rw [hl] at hm; exact hm
        rw [he]; exact Nat.le_refl _
      · have hst : mstepE p k arch (r.cfg n) (i, .env) (r.cfg (n + 1)) := by rw [hl] at hm; exact hm
        exact Nat.le_of_lt (envE_mass hst)
    obtain ⟨N2, hN02, hN2⟩ := noninc_stab (g := fun n => termMass (r.cfg n)) _ N0 (Nat.le_refl _) hmass
    have hnone : ∀ m, N2 ≤ m → r.lbl m = none := fun m hm => by
      rcases hnothr m (Nat.le_trans hN02 hm) with hl | ⟨i, hl⟩
      · exact hl
      · exfalso
        have h := hr m
        have hst : mstepE p k arch (r.cfg m) (i, .env) (r.cfg (m + 1)) := by rw [hl] at h; exact h
        have h1 := envE_mass hst
        have h2 : termMass (r.cfg (m + 1)) = termMass (r.cfg N2) := hN2 (m + 1) (Nat.le_succ_of_le hm)
        have h3 : termMass (r.cfg m) = termMass (r.cfg N2) := hN2 m hm
        omega
    have hconst : ∀ d, r.cfg (N2 + d) = r.cfg N2 := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
        have hm := hr (N2 + d)
        rw [hnone _ (Nat.le_add_right _ _)] at hm
        rw [← Nat.add_assoc, ← ih]
        exact hm
    rcases noStuckB_spec hst (hb N2) with hfin | ⟨i, hi, hne⟩
    · exact ⟨N2, by rw [(hrn N2).2.1]; exact hfin⟩
    · exfalso
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
      have hlt : i < (r.cfg N2).ths.size := by rw [(hrn N2).2.1]; exact hi
      have hmv := node_move hc h0 hr hs hpf hsr he
      have hw := hf.weak i ⟨⟨N2, hlt⟩, rfl⟩ ⟨N2, fun n hn => ⟨e, by
        have := hconst (n - N2)
        rw [Nat.add_sub_cancel' hn] at this
        rw [this]; exact hmv⟩⟩
      obtain ⟨m, hm, hlm⟩ := hw N2
      rw [hnone m hm] at hlm
      cases hlm

end

end TermLiveCert
#print axioms TermLiveCert.no_livelock_of_check
#print axioms TermLiveCert.no_livelock_of_check_fair
#print axioms TermLiveCert.reach_of_check
#print axioms TermLiveCert.outcome_of_check
#print axioms TermLiveCert.terminates_of_check
#print axioms TermLiveCert.envE_mass
