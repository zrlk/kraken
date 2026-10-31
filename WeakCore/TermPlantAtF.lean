import WeakCore.TermCert
import WeakCore.TermLiveProps

/-! # TermPlantAtF: a fulfilled promise ends at or below the new coherence

`tstep_fulCoh`: for `r ∈ tstep g mem pairs th` (from a `CohAt` state), every promise `u` of `th`
no longer outstanding in `r` (message `m`) has `u ≤ r.2.2.vs.coh m.loc`: a fulfil commits
`coh a := u` at `a = m.loc` (`stepStore`, `stepRmw`, `stepRmwPair`), and coherence never goes
down afterwards (`TermLiveProps.Mono`).  The sweep mirrors `TermCert.tstep_appUp`, carrying
`Mono ∧ AppUp ∧ FulC` (`FM`).
-/

namespace TermPlantAtF
open CoreLang CoreTerm TermRun
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermCert (AppUp AppUpM)
open TermLiveProps (Mono CohAt)

/-- Fulfilled promises of `P` (not in `P'`) are at or below `vs'.coh` at their location. -/
def FulM (mem : Memory) (P : List Ts) (vs' : VState) (P' : List Ts) : Prop :=
  ∀ u ∈ P, u ∉ P' → ∀ m, mem[u]? = some m → u ≤ vs'.coh m.loc

def FulC (s s' : St) : Prop := CohAt s.mem s.vs → FulM s.mem s.promises s'.vs s'.promises

def FM (s s' : St) : Prop := Mono s s' ∧ AppUp s s' ∧ FulC s s'

theorem FM.refl (s : St) : FM s s :=
  ⟨Mono.refl' s, AppUpM.refl' _ _ _, fun _ _ hu hu' => absurd hu hu'⟩

theorem FM.trans {s1 s2 s3 : St} (a : FM s1 s2) (b : FM s2 s3) : FM s1 s3 := by
  refine ⟨Mono.trans a.1 b.1, TermCert.AppUp.trans a.2.1 b.2.1, fun hc u hu hu3 m hm => ?_⟩
  obtain ⟨hc2, -⟩ := a.1 hc
  obtain ⟨-, hl3⟩ := b.1 hc2
  have hm2 : s2.mem[u]? = some m := a.2.1.2.1 u m hm
  by_cases h2 : u ∈ s2.promises
  · exact b.2.2 hc2 u h2 hu3 m hm2
  · exact Nat.le_trans (a.2.2 hc u hu h2 m hm) (hl3 _)

theorem FM.keep {s s' : St} (h1 : Mono s s') (h2 : AppUp s s') (h3 : s'.promises = s.promises) : FM s s' :=
  ⟨h1, h2, fun _ _ hu hu' => absurd (h3 ▸ hu) hu'⟩

/-! ## Leaves -/

theorem stepStore_fulM {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    FulM mem th.promises th'.vs th'.promises := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun u hu hu' => absurd hu hu'
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            intro u hu hu' m hmu
            have e := TermFul.not_mem_erase hu hu'
            subst e
            rw [hm] at hmu; cases hmu
            have hl : pm.loc = a := by
              simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1.1
            simp [hl]
          · simp at hf

theorem stepRmw_fulM_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    FulM mem th.promises th'.vs th'.promises := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro u hu hu'
    rw [TermFul.lockFence_prom] at hu'
    exact absurd hu hu'
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro u hu hu'
        rw [TermFul.lockFence_prom] at hu'
        exact absurd hu hu'
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hc, rfl, rfl⟩ := hf
          intro u hu hu' m hmu
          rw [TermFul.lockFence_prom] at hu'
          have e := TermFul.not_mem_erase hu hu'
          subst e
          rw [hm] at hmu; cases hmu
          have hl : pm.loc = a := by
            simp only [Bool.and_eq_true, beq_iff_eq] at hc; exact hc.1.1.1.1
          rw [TermFul.lockFence_coh]
          simp [hl]

theorem stepRmw_fulM {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    FulM mem th.promises th'.vs th'.promises := by
  have hx := stepRmw_fulM_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rwa [TermFul.lockFence_prom] at hx

theorem stepRmwPair_fulM_at {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    FulM mem th.promises th'.vs th'.promises := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    intro u hu hu'
    rw [TermFul.lockFence_prom] at hu'
    exact absurd hu hu'
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      intro u hu hu'
      rw [TermFul.lockFence_prom] at hu'
      exact absurd hu hu'
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨hc, rfl, rfl, rfl⟩ := hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    intro u hu hu' m hmu
    rw [TermFul.lockFence_prom] at hu'
    rw [TermFul.lockFence_coh]
    by_cases e0 : u = tw
    · subst e0
      rw [hm] at hmu; cases hmu
      have hl : pm0.loc = a := by
        first
          | exact hc.1.1.1.1.1.1.1.1.2
          | exact hc.1.1.1.1.1.1.1.1.1.2
          | exact hc.1.1.1.1.1.1.1.2
      simp [hl]
    · have hu1 : u ∈ th.promises.erase tw := (List.mem_erase_of_ne e0).2 hu
      have e1 := TermFul.not_mem_erase hu1 hu'
      subst e1
      rw [hm1] at hmu; cases hmu
      have hl : pm1.loc = a.next := by
        exact hc.1.1.1.1.1.2
      have hne : a.next ≠ a := TermCert.next_ne a
      simp [hl, hne]

theorem stepRmwPair_fulM {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    FulM mem th.promises th'.vs th'.promises := by
  have hx := stepRmwPair_fulM_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rwa [TermFul.lockFence_prom] at hx

/-! ## State-level primitives -/

theorem fm_eq {s s' : St} (h1 : s'.vs = s.vs) (h2 : s'.promises = s.promises) (h3 : s'.mem = s.mem) :
    FM s s' := by
  refine FM.keep (fun hc => ⟨by rw [h1, h3]; exact hc, fun b => by rw [h1]; exact Nat.le_refl _⟩) ?_ h2
  show AppUpM s.mem s.vs s.promises s'.mem s'.vs s'.promises
  rw [h1, h2, h3]; exact AppUpM.refl' _ _ _

theorem rmw_fm {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hp : s'.promises = th'.promises) (hs : s.mem = mem) :
    FM s s' := by
  refine ⟨TermLiveProps.rmw_mono h hm hv hs, ?_, fun _ => ?_⟩
  · show AppUpM s.mem s.vs s.promises s'.mem s'.vs s'.promises
    rw [hm, hv, hp, hs]; exact TermCert.stepRmw_appUp h
  · show FulM s.mem s.promises s'.vs s'.promises
    rw [hv, hp, hs]; exact stepRmw_fulM h

theorem rmwPair_fm {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hp : s'.promises = th'.promises) (hs : s.mem = mem) :
    FM s s' := by
  refine ⟨TermLiveProps.rmwPair_mono h hm hv hs, ?_, fun _ => ?_⟩
  · show AppUpM s.mem s.vs s.promises s'.mem s'.vs s'.promises
    rw [hm, hv, hp, hs]; exact TermCert.stepRmwPair_appUp h
  · show FulM s.mem s.promises s'.vs s'.promises
    rw [hv, hp, hs]; exact stepRmwPair_fulM h

theorem loadUnits_fm {arch' : Arch} {pw : Word} {a : Address} {acq : Bool}
    {us : List Acc} {n : Nat} {s : St} {r : St × List Word} (hr : r ∈ loadUnits arch' pw a acq us n s) :
    FM s r.1 := by
  obtain ⟨-, -, e3⟩ := TermFul.loadUnits_keep us n s r hr
  exact FM.keep (TermLiveProps.loadUnits_mono _ _ _ _ _ _ _ (show (r.1, r.2) ∈ _ from hr))
    (TermCert.loadUnits_appUp hr) e3

theorem fenceS_fm (s : St) (f : WeakMem.Fence) : FM s (fenceS s f) :=
  FM.keep (TermLiveProps.fenceS_mono s f) (TermCert.fenceS_appUp s f) rfl

theorem allocBuf_fm (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    FM s (allocBuf lbl n zero s).1 :=
  FM.keep (TermLiveProps.allocBuf_mono lbl n zero s) (TermCert.allocBuf_appUp lbl n zero s) rfl

theorem storeUnits_fm {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      FM s s'
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact FM.refl _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      refine FM.trans ?_ (storeUnits_fm us ws (i + 1) _ s' hs)
      exact ⟨fun hc => TermLiveProps.stepStore_coh hst hc,
        TermCert.stepStore_appUp (th := mth s pw w w) hst, fun _ => stepStore_fulM hst⟩
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have h2 : AppUpM s.mem s.vs s.promises
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).1
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.vs
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.promises := by
        simp only [Promises.stepStorePair]
        exact TermCert.AppUpM.push2 _ _ (Nat.le_max_left _ _)
          (Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _))
      have hp := TermLiveProps.stepStorePair_coh (mem := s.mem) (pairs := s.pairs) (th := mth s pw w0 w1)
        (a := offs a i) (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel)
      have hq := (TermFul.stepStorePair_shape s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel).1
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs hp hq
      obtain ⟨mem', pairs', th⟩ := R
      refine FM.trans ?_ (storeUnits_fm us ws (i + 2) _ s' hs)
      exact FM.keep (fun hc => hp hc) h2 hq
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem alloc_fm {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : FM s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  refine FM.trans ?_ (storeUnits_fm us ws 0 _ s' hs)
  exact FM.keep (fun hc => TermLiveProps.allocCoh hc lbl (nWords us) (fun _ => .undef))
    (TermCert.fold_appUp s _ _ _ rfl) rfl

theorem injM_fm {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word}
    {r : St × List Word} (h : r ∈ injM g s ty j p) : FM s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_fm hs
      dsimp only
      split
      · exact FM.trans this (fenceS_fm _ _)
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact FM.refl _

theorem projM_fm {g : G} {s : St} {ty : Ty} {ws : List Word}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) : FM s r.1 := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_fm h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact FM.trans d1 (loadUnits_fm h2))
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact FM.refl _

theorem evalOp_fm {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : FM s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact FM.refl _ | exact fenceS_fm _ _ | exact allocBuf_fm _ _ _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_fm hx
         | exact storeUnits_fm _ _ _ _ _ hx
         | exact alloc_fm hx
         | exact rmw_fm hx rfl rfl rfl rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact FM.trans (projM_fm hx) (injM_fm hy)
         | exact FM.trans (loadUnits_fm hx) (storeUnits_fm _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_fm hx
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact FM.trans d1 (storeUnits_fm _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_fm hx
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_fm _ _ _ _)

/-- The sweep: a thread step is `Mono ∧ AppUp ∧ FulC`. -/
theorem tstep_fm {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) :
    FM (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact FM.refl _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, h2⟩ := TermCert.enter_eq he
       exact fm_eq h1 h2 rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, h2⟩ := TermCert.enter_eq he
       exact fm_eq h1 h2 rfl)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_fm hx
         | (split <;> exact evalOp_fm hx)
         | exact rmw_fm hx rfl rfl rfl rfl
         | exact rmwPair_fm hx rfl rfl rfl rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact FM.trans (projM_fm hx) (injM_fm hy))
    | (simp only [List.mem_singleton] at h; subst h; exact fenceS_fm _ .st)

/-- **FulCoh**: a promise fulfilled by a thread step ends at or below the new coherence. -/
theorem tstep_fulCoh {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) (hc : CohAt mem th.vs) :
    ∀ u ∈ th.promises, u ∉ r.2.2.promises → ∀ m, mem[u]? = some m → u ≤ r.2.2.vs.coh m.loc :=
  (tstep_fm h).2.2 hc

end TermPlantAtF

#print axioms TermPlantAtF.FM.trans
#print axioms TermPlantAtF.stepStore_fulM
#print axioms TermPlantAtF.stepRmw_fulM
#print axioms TermPlantAtF.stepRmwPair_fulM
#print axioms TermPlantAtF.tstep_fm
#print axioms TermPlantAtF.tstep_fulCoh
