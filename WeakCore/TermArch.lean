/-
# TermArch — every TSO behaviour of a `TermRun` program is an ARM behaviour

Menu item 2a, condition (a) of the ARM reference-semantics decision:
`Promises.Sim.tso_outcomes_subset_arm`, lifted from
litmus programs to `TermRun` terms.

**Statement.**  If `c` is reachable from `c0` by `TermRun.Step p k .tso`, then
some `c'` is reachable from `c0` by `Step p k .arm` with `CfgLe c' c`: the same
terms, frames, runtime types, memory locations and values, promises,
allocation counters and `undef` counts.  Only *views* differ -- in words,
thread view states and messages -- and words' read timestamps (`rts`: a spawn
bumps its argument words to the parent's `vRelSt`), and they are lower on ARM.  So final
configurations, and every observation made of values, coincide.

The statement is about the declarative machine `Step`.  The bounded explorer
(`successors`, `certB`, `soloWrites`) under-approximates it and is not the
semantics, so it is not lifted.

**Why it is mostly bookkeeping.**  `g.arch` enters `tstep` only through
`loadUnits`, `storeUnits`, `alloc` and the `cas` arm's `stepRmw`, each a
composition of `Promises` rules that already have simulation lemmas
(`Promises.Sim.stepLoad_sim` and friends).  Everything else branches on word
*values* only, and the relation keeps values equal.

Steps ("Menu 2a(a)"):
  L1 the relations;
  L2 the access helpers simulate;
  L3 `evalOp` simulates;
  L4 `tstep` simulates;
  L5 the machine: `threadSteps`, `promise`, `Solo`, `Certified`, `Step`,
     reachability.
-/
import WeakCore.TermRun
import WeakCore.TermTidLbl

namespace TermArch
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises (TValLe ThreadLe VLe MemLe)
open Promises.Sim (MemExt)

/-! ## L1 The relations

ARM on the left, TSO on the right, as in `Promises.Sim`. -/

theorem tvle_refl (w : Word) : TValLe w w := ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Word lists: same length, pointwise `TValLe`. -/
def WsLe : List Word → List Word → Prop
  | [], [] => True
  | a :: as, b :: bs => TValLe a b ∧ WsLe as bs
  | _, _ => False

theorem WsLe.refl : ∀ ws : List Word, WsLe ws ws
  | [] => trivial
  | w :: ws => ⟨tvle_refl w, WsLe.refl ws⟩

theorem WsLe.append : ∀ {a b c d : List Word}, WsLe a b → WsLe c d → WsLe (a ++ c) (b ++ d)
  | [], [], _, _, _, h => by simpa using h
  | _ :: _, _ :: _, _, _, ⟨hx, h⟩, h' => ⟨hx, WsLe.append h h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem countUndef_congr : ∀ {a b : List Word}, WsLe a b → countUndef a = countUndef b
  | [], [], _ => rfl
  | x :: a, y :: b, ⟨hx, h⟩ => by
      have ih := countUndef_congr h
      simp only [countUndef, List.filter_cons, hx.val] at ih ⊢
      split <;> simp [ih]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The ARM memory agrees *exactly* with the TSO memory at the timestamps `ps`
(a thread's outstanding promises): `Promises.Sim.Sim.prom`. -/
def Agree (ma mt : Memory) (ps : List Ts) : Prop :=
  ∀ t ∈ ps, t < ma.size ∧ ma[t]? = mt[t]?

theorem Agree.ext {ma mt ma' mt' : Memory} {ps ps' : List Ts} (h : Agree ma mt ps)
    (hm : MemLe ma mt) (ha : MemExt ma ma') (ht : MemExt mt mt')
    (hsub : ∀ t ∈ ps', t ∈ ps) : Agree ma' mt' ps' := by
  intro t htp
  obtain ⟨hlt, heq⟩ := h t (hsub t htp)
  have hlt' : t < mt.size := by rw [← hm.1]; exact hlt
  exact ⟨Nat.lt_of_lt_of_le hlt ha.size, by rw [ha.get t hlt, ht.get t hlt', heq]⟩

/-- The part of a thread the machine rules touch.  `O` is a set of timestamps
(the other threads' promises) at which the memories must also agree exactly:
the step preserves it because both memories only grow. -/
structure StLe (O : List Ts) (sa st : St) : Prop where
  mem      : MemLe sa.mem st.mem
  pairs    : sa.pairs = st.pairs
  vs       : VLe sa.vs st.vs
  promises : sa.promises = st.promises
  nalloc   : sa.nalloc = st.nalloc
  undefs   : sa.undefs = st.undefs
  agree    : Agree sa.mem st.mem st.promises
  /-- ... and at `O`, the other threads' outstanding promises. -/
  other    : Agree sa.mem st.mem O

variable {O : List Ts}

theorem mth_le {sa st : St} (h : StLe O sa st) {a0 b0 a1 b1 a2 b2 : Word}
    (h0 : TValLe a0 b0) (h1 : TValLe a1 b1) (h2 : TValLe a2 b2) :
    ThreadLe (mth sa a0 a1 a2) (mth st b0 b1 b2) := by
  refine ⟨rfl, h.promises, fun r => ?_, h.vs⟩
  show TValLe (regsOf a0 a1 a2 r) (regsOf b0 b1 b2 r)
  unfold regsOf
  split
  · exact h0
  · split
    · exact h1
    · split
      · exact h2
      · exact tvle_refl _

theorem dataE_congr {x y : Word} (h : TValLe x y) (r : WeakMem.Reg) : dataE r x = dataE r y := by
  unfold dataE; rw [h.val]

/-! ## L2 The access helpers simulate -/

/-- `loadUnits` writes nothing: only views and the `undef` count change. -/
theorem loadUnits_frame (arch : Arch) (pw : Word) (a : Address) (acq : Bool) :
    ∀ (us : List Acc) (k : Nat) (s : St) {s' : St} {ws : List Word},
    (s', ws) ∈ loadUnits arch pw a acq us k s →
    s'.mem = s.mem ∧ s'.pairs = s.pairs ∧ s'.promises = s.promises ∧ s'.nalloc = s.nalloc
  | [], k, s, s', ws, h => by
      simp only [loadUnits, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, rfl, rfl⟩
  | .one :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, _, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨h1, h2, h3, h4⟩ := loadUnits_frame arch pw a acq us _ _ hin
      exact ⟨h1, h2, h3, h4⟩
  | .two :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, _, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨h1, h2, h3, h4⟩ := loadUnits_frame arch pw a acq us _ _ hin
      exact ⟨h1, h2, h3, h4⟩

theorem loadUnits_sim {pa pt : Word} (hp : TValLe pa pt) (a : Address) (acq : Bool) :
    ∀ (us : List Acc) (k : Nat) {sa st : St}, StLe O sa st →
    ∀ {st' : St} {wt : List Word}, (st', wt) ∈ loadUnits .tso pt a acq us k st →
    ∃ sa' wa, (sa', wa) ∈ loadUnits .arm pa a acq us k sa ∧ StLe O sa' st' ∧ WsLe wa wt
  | [], k, sa, st, h, st', wt, hin => by
      simp only [loadUnits, List.mem_singleton, Prod.mk.injEq] at hin
      obtain ⟨rfl, rfl⟩ := hin
      exact ⟨sa, [], by simp [loadUnits], h, trivial⟩
  | .one :: us, k, sa, st, h, st', wt, hin => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hin
      obtain ⟨tht, htin, ⟨s2, ws2⟩, hin2, heq⟩ := hin
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [← h.pairs] at htin
      obtain ⟨tha, hain, hle⟩ :=
        Promises.Sim.stepLoad_sim h.mem (mth_le h hp hp hp) sa.pairs 1 (offs a k) [0] acq htin
      have hst : StLe O { sa with vs := tha.vs, undefs := sa.undefs + countUndef [tha.regs 1] }
          { st with vs := tht.vs, undefs := st.undefs + countUndef [tht.regs 1] } :=
        ⟨h.mem, h.pairs, hle.vs, h.promises, h.nalloc,
         by simp only [h.undefs, countUndef_congr (show WsLe [tha.regs 1] [tht.regs 1] from ⟨hle.regs 1, trivial⟩)],
         h.agree, h.other⟩
      obtain ⟨sa', wa, hin', hst', hws⟩ := loadUnits_sim hp a acq us (k + 1) hst hin2
      refine ⟨sa', tha.regs 1 :: wa, ?_, hst', hle.regs 1, hws⟩
      simp only [loadUnits, List.mem_flatMap, List.mem_map]
      exact ⟨tha, hain, (sa', wa), hin', rfl⟩
  | .two :: us, k, sa, st, h, st', wt, hin => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hin
      obtain ⟨tht, htin, ⟨s2, ws2⟩, hin2, heq⟩ := hin
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [← h.pairs] at htin
      obtain ⟨tha, hain, hle⟩ :=
        Promises.Sim.stepLoadPair_sim h.mem (mth_le h hp hp hp) sa.pairs 1 2 (offs a k) [0] acq htin
      have hst : StLe O
          { sa with vs := tha.vs, undefs := sa.undefs + countUndef [tha.regs 1, tha.regs 2] }
          { st with vs := tht.vs, undefs := st.undefs + countUndef [tht.regs 1, tht.regs 2] } :=
        ⟨h.mem, h.pairs, hle.vs, h.promises, h.nalloc,
         by simp only [h.undefs, countUndef_congr (show WsLe [tha.regs 1, tha.regs 2] [tht.regs 1, tht.regs 2]
              from ⟨hle.regs 1, hle.regs 2, trivial⟩)],
         h.agree, h.other⟩
      obtain ⟨sa', wa, hin', hst', hws⟩ := loadUnits_sim hp a acq us (k + 2) hst hin2
      refine ⟨sa', tha.regs 1 :: tha.regs 2 :: wa, ?_, hst', hle.regs 1, hle.regs 2, hws⟩
      simp only [loadUnits, List.mem_flatMap, List.mem_map]
      exact ⟨tha, hain, (sa', wa), hin', rfl⟩

/-- `storeUnits` only appends to memory and only discharges promises. -/
theorem storeUnits_ext (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St},
    s' ∈ storeUnits k arch pw a rel us ws i s →
    MemExt s.mem s'.mem ∧ (∀ t ∈ s'.promises, t ∈ s.promises)
  | [], ws, i, s, s', h => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h
      exact ⟨Promises.Sim.MemExt.refl _, fun _ h => h⟩
  | .one :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      obtain ⟨he, hp⟩ := Promises.Sim.stepStore_ext k arch _ _ _ _ _ _ hst
      obtain ⟨he', hp'⟩ := storeUnits_ext k arch pw a rel us ws _ _ hin
      exact ⟨Promises.Sim.MemExt.trans he he', fun t ht => hp t (hp' t ht)⟩
  | .two :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, [_], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, w0 :: w1 :: ws, i, s, s', h => by
      have hx := Promises.Sim.stepStorePair_ext s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      simp only [storeUnits] at h
      rw [Promises.Sim.stepStorePair_eq] at h hx
      obtain ⟨he', hp'⟩ := storeUnits_ext k arch pw a rel us ws _ _ h
      exact ⟨Promises.Sim.MemExt.trans hx.1 he', fun t ht => hx.2 t (hp' t ht)⟩

theorem storeUnits_sim (k : Promises.Knobs) {pa pt : Word} (hp : TValLe pa pt) (a : Address)
    (rel : Bool) :
    ∀ (us : List Acc) (wa wt : List Word) (i : Nat) {sa st : St}, StLe O sa st → WsLe wa wt →
    ∀ {st' : St}, st' ∈ storeUnits k .tso pt a rel us wt i st →
    ∃ sa' ∈ storeUnits k .arm pa a rel us wa i sa, StLe O sa' st'
  | [], wa, wt, i, sa, st, h, _, st', hin => by
      simp only [storeUnits, List.mem_singleton] at hin
      subst hin
      exact ⟨sa, by simp [storeUnits], h⟩
  | .one :: us, [], [], _, _, _, _, _, _, hin => by simp [storeUnits] at hin
  | .one :: us, x :: wa, y :: wt, i, sa, st, h, ⟨hxy, hw⟩, st', hin => by
      simp only [storeUnits, List.mem_flatMap] at hin
      obtain ⟨⟨mt', tt'⟩, hst, hin2⟩ := hin
      rw [← dataE_congr hxy] at hst
      obtain ⟨⟨qm, qth⟩, hq, hmq, htq⟩ := Promises.Sim.stepStore_sim k h.mem (mth_le h hp hxy hxy)
        (fun t ht => (h.agree t ht).2) (offs a i) (dataE 1 x) [0] rel hst
      have hea := Promises.Sim.stepStore_ext k .arm _ _ _ _ _ _ hq
      have het := Promises.Sim.stepStore_ext k .tso _ _ _ _ _ _ hst
      have hst2 : StLe O { sa with mem := qm, vs := qth.vs, promises := qth.promises }
          { st with mem := mt', vs := tt'.vs, promises := tt'.promises } :=
        ⟨hmq, h.pairs, htq.vs, htq.promises, h.nalloc, h.undefs,
         Agree.ext h.agree h.mem hea.1 het.1 het.2, Agree.ext h.other h.mem hea.1 het.1 (fun _ h => h)⟩
      obtain ⟨sa', hin', hst'⟩ := storeUnits_sim k hp a rel us wa wt (i + 1) hst2 hw hin2
      refine ⟨sa', ?_, hst'⟩
      simp only [storeUnits, List.mem_flatMap]
      exact ⟨(qm, qth), hq, hin'⟩
  | .two :: us, [], [], _, _, _, _, _, _, hin => by simp [storeUnits] at hin
  | .two :: us, [_], [_], _, _, _, _, _, _, hin => by simp [storeUnits] at hin
  | .two :: us, x0 :: x1 :: wa, y0 :: y1 :: wt, i, sa, st, h, ⟨hx0, hx1, hw⟩, st', hin => by
      have hea := Promises.Sim.stepStorePair_ext sa.mem sa.pairs (mth sa pa x0 x1) (offs a i)
        (dataE 1 y0) (dataE 2 y1) [0] rel
      have het := Promises.Sim.stepStorePair_ext st.mem st.pairs (mth st pt y0 y1) (offs a i)
        (dataE 1 y0) (dataE 2 y1) [0] rel
      obtain ⟨hm2, ht2⟩ := Promises.Sim.stepStorePair_sim h.mem (mth_le h hp hx0 hx1) (offs a i)
        (dataE 1 y0) (dataE 2 y1) [0] rel
      simp only [storeUnits] at hin
      rw [Promises.Sim.stepStorePair_eq] at hin hea het
      simp only [storeUnits]
      rw [dataE_congr hx0, dataE_congr hx1, Promises.Sim.stepStorePair_eq]
      refine storeUnits_sim k hp a rel us wa wt (i + 2) ?_ hw hin
      exact ⟨hm2, by rw [h.pairs, h.mem.1], ht2.vs, ht2.promises, h.nalloc, h.undefs,
        Agree.ext h.agree h.mem hea.1 het.1 het.2, Agree.ext h.other h.mem hea.1 het.1 (fun _ h => h)⟩
  | _ :: _, [], _ :: _, _, _, _, _, hw, _, _ => hw.elim
  | _ :: _, _ :: _, [], _, _, _, _, hw, _, _ => hw.elim
  | .two :: _, [_], _ :: _ :: _, _, _, _, _, ⟨_, hw⟩, _, _ => hw.elim
  | .two :: _, _ :: _ :: _, [_], _, _, _, _, ⟨_, hw⟩, _, _ => hw.elim

theorem fold_push_le (f : Nat → Msg) : ∀ (l : List Nat) {ma mt : Memory}, MemLe ma mt →
    MemLe (l.foldl (fun m j => m.push (f j)) ma) (l.foldl (fun m j => m.push (f j)) mt)
  | [], _, _, h => h
  | _ :: l, _, _, h => fold_push_le f l (Promises.Sim.MemLe.push h rfl rfl (Nat.le_refl _))

theorem fold_push_ext (f : Nat → Msg) : ∀ (l : List Nat) (m : Memory),
    MemExt m (l.foldl (fun m j => m.push (f j)) m)
  | [], m => Promises.Sim.MemExt.refl m
  | j :: l, m => Promises.Sim.MemExt.trans (Promises.Sim.MemExt.push m (f j)) (fold_push_ext f l _)

theorem vle_coh {va vt : VState} (h : VLe va vt) (lbl : AllocLabel) (n base : Nat) :
    VLe { va with coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else va.coh b }
        { vt with coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else vt.coh b } := by
  refine ⟨fun b => ?_, h.vRd, h.vWr, h.vCtrl, h.vPreBase, h.vRelSt, h.mine, h.fwd⟩
  show (if b.label = lbl ∧ b.offset < n then base + b.offset else va.coh b) ≤
    (if b.label = lbl ∧ b.offset < n then base + b.offset else vt.coh b)
  split
  · exact Nat.le_refl _
  · exact h.coh b

/-- `vle_coh` with `vWr` raised to the same timestamp on both sides (an
allocation, runtime obligation R11). -/
theorem vle_cohW {va vt : VState} (h : VLe va vt) (lbl : AllocLabel) (n base w : Nat) :
    VLe { va with coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else va.coh b
                  vWr := max va.vWr w }
        { vt with coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else vt.coh b
                  vWr := max vt.vWr w } := by
  have hc := vle_coh h lbl n base
  exact ⟨hc.coh, h.vRd, Nat.max_le.2 ⟨Nat.le_trans h.vWr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩,
    h.vCtrl, h.vPreBase, h.vRelSt, h.mine, h.fwd⟩

theorem alloc_sim (k : Promises.Knobs) (lbl : AllocLabel) (us : List Acc) {wa wt : List Word}
    (hw : WsLe wa wt) {sa st : St} (h : StLe O sa st) {st' : St} {pwt : Word}
    (hin : (st', pwt) ∈ alloc k .tso lbl us wt st) :
    ∃ sa' pwa, (sa', pwa) ∈ alloc k .arm lbl us wa sa ∧ StLe O sa' st' ∧ TValLe pwa pwt := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at hin
  obtain ⟨s2, hs2, rfl, rfl⟩ := hin
  have hsz := h.mem.1
  let f : Nat → Msg := fun j => ⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩
  have h0 : StLe O
      { sa with mem := (List.range (nWords us)).foldl (fun m j => m.push (f j)) sa.mem,
                vs := { sa.vs with
                  coh := fun b => if b.label = lbl ∧ b.offset < nWords us then sa.mem.size + b.offset else sa.vs.coh b
                  vWr := max sa.vs.vWr (sa.mem.size + nWords us - 1) },
                nalloc := sa.nalloc + 1 }
      { st with mem := (List.range (nWords us)).foldl (fun m j => m.push (f j)) st.mem,
                vs := { st.vs with
                  coh := fun b => if b.label = lbl ∧ b.offset < nWords us then st.mem.size + b.offset else st.vs.coh b
                  vWr := max st.vs.vWr (st.mem.size + nWords us - 1) },
                nalloc := st.nalloc + 1 } :=
    ⟨fold_push_le f _ h.mem, h.pairs, by rw [hsz]; exact vle_cohW h.vs _ _ _ _, h.promises,
     by simp only [h.nalloc], h.undefs,
     Agree.ext h.agree h.mem (fold_push_ext f _ _) (fold_push_ext f _ _) (fun _ ht => ht),
     Agree.ext h.other h.mem (fold_push_ext f _ _) (fold_push_ext f _ _) (fun _ ht => ht)⟩
  obtain ⟨sa', hin', hst'⟩ := storeUnits_sim k (tvle_refl _) _ false us wa wt 0 h0 hw hs2
  exact ⟨sa', _, List.mem_map.2 ⟨sa', hin', rfl⟩, hst', tvle_refl _⟩

theorem alloc_ext (k : Promises.Knobs) (arch : Arch) (lbl : AllocLabel) (us : List Acc)
    (ws : List Word) (s : St) {s' : St} {pw : Word} (hin : (s', pw) ∈ alloc k arch lbl us ws s) :
    MemExt s.mem s'.mem ∧ (∀ t ∈ s'.promises, t ∈ s.promises) := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at hin
  obtain ⟨s2, hs2, rfl, rfl⟩ := hin
  obtain ⟨he, hp⟩ := storeUnits_ext k arch _ _ false us ws 0 _ hs2
  exact ⟨Promises.Sim.MemExt.trans (fold_push_ext _ _ _) he, hp⟩

theorem allocBuf_sim (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) {sa st : St}
    (h : StLe O sa st) :
    StLe O (allocBuf lbl n zero sa).1 (allocBuf lbl n zero st).1 ∧
      (allocBuf lbl n zero sa).2 = (allocBuf lbl n zero st).2 := by
  have hsz := h.mem.1
  refine ⟨⟨fold_push_le _ _ h.mem, h.pairs, ?_, h.promises, by simp only [allocBuf, h.nalloc],
    h.undefs, Agree.ext h.agree h.mem (fold_push_ext _ _ _) (fold_push_ext _ _ _) (fun _ ht => ht),
    Agree.ext h.other h.mem (fold_push_ext _ _ _) (fold_push_ext _ _ _) (fun _ ht => ht)⟩, rfl⟩
  refine ⟨fun b => ?_, h.vs.vRd, ?_, h.vs.vCtrl, h.vs.vPreBase, h.vs.vRelSt, h.vs.mine, h.vs.fwd⟩
  · show (if b.label = lbl ∧ b.offset < n then sa.mem.size + b.offset else sa.vs.coh b) ≤
      (if b.label = lbl ∧ b.offset < n then st.mem.size + b.offset else st.vs.coh b)
    rw [hsz]
    split
    · exact Nat.le_refl _
    · exact h.vs.coh b
  · -- `newBuf` raises `vWr` to the last message in memory, the same timestamp in both
    show max sa.vs.vWr (sa.mem.size + n - 1) ≤ max st.vs.vWr (st.mem.size + n - 1)
    rw [hsz]
    exact Nat.max_le.2 ⟨Nat.le_trans h.vs.vWr (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

theorem allocBuf_ext (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) :
    MemExt s.mem (allocBuf lbl n zero s).1.mem ∧
      (∀ t ∈ (allocBuf lbl n zero s).1.promises, t ∈ s.promises) :=
  ⟨fold_push_ext _ _ _, fun _ ht => ht⟩

theorem fenceS_sim {sa st : St} (h : StLe O sa st) (f : WeakMem.Fence) : StLe O (fenceS sa f) (fenceS st f) :=
  ⟨h.mem, h.pairs,
   (Promises.Sim.fence_le (mth_le h (tvle_refl _) (tvle_refl _) (tvle_refl _)) f).vs,
   h.promises, h.nalloc, h.undefs, h.agree, h.other⟩

/-! ## L3 `evalOp` simulates -/

def EnvLe : Env → Env → Prop
  | [], [] => True
  | (x, t, wa) :: ea, (y, u, wt) :: et => x = y ∧ t = u ∧ WsLe wa wt ∧ EnvLe ea et
  | _, _ => False

def OptLe : Option (Ty × List Word) → Option (Ty × List Word) → Prop
  | none, none => True
  | some (t, wa), some (u, wt) => t = u ∧ WsLe wa wt
  | _, _ => False

theorem optle_some {oa : Option (Ty × List Word)} {t : Ty} {wt : List Word}
    (h : OptLe oa (some (t, wt))) : ∃ wa, oa = some (t, wa) ∧ WsLe wa wt := by
  match oa, h with
  | some (u, wa), ⟨hu, hw⟩ => exact ⟨wa, by rw [hu], hw⟩

theorem optle_none {oa : Option (Ty × List Word)} (h : OptLe oa none) : oa = none := by
  match oa, h with
  | none, _ => rfl

theorem optle_refl : ∀ o : Option (Ty × List Word), OptLe o o
  | none => trivial
  | some (_, ws) => ⟨rfl, WsLe.refl ws⟩

theorem lookupE_rel : ∀ {ea et : Env}, EnvLe ea et → ∀ x, OptLe (lookupE ea x) (lookupE et x)
  | [], [], _, _ => trivial
  | (y, t, wa) :: ea, (y', u, wt) :: et, ⟨hy, ht, hw, he⟩, x => by
      subst hy; subst ht
      by_cases hc : (y == x) = true
      · simp only [lookupE, List.find?_cons, hc]; exact ⟨rfl, hw⟩
      · simp only [lookupE, List.find?_cons, hc]; exact lookupE_rel he x
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem evalAt_rel {ea et : Env} (he : EnvLe ea et) : ∀ a, OptLe (evalAt ea a) (evalAt et a)
  | .var x => lookupE_rel he x
  | .lit _ => optle_refl _
  | .unit => optle_refl _

/-- The workhorse: what the TSO side evaluated, the ARM side evaluates too. -/
theorem evalAt_tso {ea et : Env} (he : EnvLe ea et) {a : At} {t : Ty} {wt : List Word}
    (hq : evalAt et a = some (t, wt)) : ∃ wa, evalAt ea a = some (t, wa) ∧ WsLe wa wt :=
  optle_some (hq ▸ evalAt_rel he a)

theorem wsle_nil {wa : List Word} (h : WsLe wa []) : wa = [] := by
  match wa, h with
  | [], _ => rfl

theorem wsle_single {wa : List Word} {y : Word} (h : WsLe wa [y]) :
    ∃ x, wa = [x] ∧ TValLe x y := by
  match wa, h with
  | [x], ⟨hx, _⟩ => exact ⟨x, rfl, hx⟩

theorem wsle_cons {wa : List Word} {y : Word} {wt : List Word} (h : WsLe wa (y :: wt)) :
    ∃ x wa', wa = x :: wa' ∧ TValLe x y ∧ WsLe wa' wt := by
  match wa, h with
  | x :: wa', ⟨hx, hw⟩ => exact ⟨x, wa', rfl, hx, hw⟩

theorem wsle_one {x y : Word} (h : TValLe x y) : WsLe [x] [y] := ⟨h, trivial⟩

theorem numOf_congr : ∀ {wa wt : List Word}, WsLe wa wt → numOf wa = numOf wt
  | [], [], _ => rfl
  | [x], [y], ⟨hx, _⟩ => by simp only [numOf, hx.val]
  | _ :: _ :: _, _ :: _ :: _, _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | [_], _ :: _ :: _, ⟨_, h⟩ => h.elim
  | _ :: _ :: _, [_], ⟨_, h⟩ => h.elim

theorem addrOf_congr {x y : Word} (h : TValLe x y) : addrOf x = addrOf y := by
  unfold addrOf; rw [h.val]

theorem tval_eta {x y : Word} (h : TValLe x y) : x = { y with view := x.view, rts := x.rts } := by
  obtain ⟨hv, _, _⟩ := h
  cases x; cases y; simp only at hv; subst hv; rfl

theorem tvle_low {y : Word} {v : Ts} (hv : v ≤ y.view) : TValLe { y with view := v } y :=
  ⟨rfl, Nat.le_refl _, hv⟩

theorem tvle_low2 {y : Word} {v r : Ts} (hv : v ≤ y.view) (hr : r ≤ y.rts) :
    TValLe { y with view := v, rts := r } y :=
  ⟨rfl, hr, hv⟩

theorem wsle_single_low {wa : List Word} {y : Word} (h : WsLe wa [y]) :
    ∃ v r, v ≤ y.view ∧ r ≤ y.rts ∧ wa = [{ y with view := v, rts := r }] := by
  obtain ⟨x, rfl, hx⟩ := wsle_single h
  exact ⟨x.view, x.rts, hx.view, hx.rts, by rw [← tval_eta hx]⟩

theorem addrOf_low (y : Word) (v : Ts) : addrOf { y with view := v } = addrOf y := rfl
theorem addrOf_low2 (y : Word) (v r : Ts) : addrOf { y with view := v, rts := r } = addrOf y := rfl
theorem numOf_low2 (y : Word) (v r : Ts) : numOf [{ y with view := v, rts := r }] = numOf [y] := rfl
theorem addW_low21 (y z : Word) (v r : Ts) : addW { y with view := v, rts := r } z = addW y z := rfl
theorem addW_low22 (y z : Word) (v r : Ts) : addW z { y with view := v, rts := r } = addW z y := rfl
theorem subW_low21 (y z : Word) (v r : Ts) : subW { y with view := v, rts := r } z = subW y z := rfl
theorem subW_low22 (y z : Word) (v r : Ts) : subW z { y with view := v, rts := r } = subW z y := rfl
theorem dataE_low2 (r0 : WeakMem.Reg) (y : Word) (v r : Ts) : dataE r0 { y with view := v, rts := r } = dataE r0 y := rfl
theorem numOf_low (y : Word) (v : Ts) : numOf [{ y with view := v }] = numOf [y] := rfl
theorem addW_low1 (y z : Word) (v : Ts) : addW { y with view := v } z = addW y z := rfl
theorem addW_low2 (y z : Word) (v : Ts) : addW z { y with view := v } = addW z y := rfl
theorem subW_low1 (y z : Word) (v : Ts) : subW { y with view := v } z = subW y z := rfl
theorem subW_low2 (y z : Word) (v : Ts) : subW z { y with view := v } = subW z y := rfl
theorem dataE_low (r : WeakMem.Reg) (y : Word) (v : Ts) : dataE r { y with view := v } = dataE r y := rfl

/- `ev a => t wt wa hw`: case on the TSO side's `evalAt et a`; the `none` case
is refuted from `hin`, and the ARM side's `evalAt ea a = some (t, wa)` with
`WsLe wa wt` is rewritten into both `hin` and the goal. -/
set_option hygiene false in
macro "ev " a:term:max " => " t:ident wt:ident wa:ident hw:ident : tactic =>
  `(tactic| (
    rcases hq : evalAt et $a with _ | ⟨$t, $wt⟩
    · simp [hq] at hin
    obtain ⟨$wa, hqa, $hw⟩ := evalAt_tso he hq
    simp only [hq, hqa, Option.bind_eq_bind, Option.bind_some] at hin ⊢
    clear hq hqa))

/- `one wt wa hw => y x hxy r hr`: the TSO words are a single word `y` (other shapes
are refuted from `hin`), so the ARM words are `[x]` with `TValLe x y`. -/
set_option hygiene false in
macro "one " wt:ident _wa:ident hw:ident " => " y:ident x:ident hxy:ident r:ident hr:ident : tactic =>
  `(tactic| (
    rcases $wt:ident with _ | ⟨$y, _ | ⟨_, _⟩⟩ <;> (try (simp at hin; done))
    obtain ⟨$x, $r, $hxy, $hr, rfl⟩ := wsle_single_low $hw
    try simp only [addrOf_low2, numOf_low2, dataE_low2, addW_low21, addW_low22, subW_low21, subW_low22] at hin ⊢))

/- `opt e => pat`: case on the option `e` (the TSO side's), refuting `none`
from `hin` and rewriting `some pat` into both `hin` and the goal. -/
set_option hygiene false in
macro "opt " e:term:max " => " pat:rcasesPat : tactic =>
  `(tactic| (
    rcases hc : $e with _ | $pat
    · simp [hc] at hin
    simp only [hc, Option.bind_eq_bind, Option.bind_some] at hin ⊢
    clear hc))

/- Finish a case whose result words are the same on both sides. -/
set_option hygiene false in
macro "fin_same" : tactic =>
  `(tactic| (simp at hin; subst hin; exact ⟨(sa, _, _), by simp, h, rfl, WsLe.refl _⟩))

theorem decodeArm_sim (tr : Tier) (as : List Ty) {wa wt : List Word} (hw : WsLe wa wt)
    {j : Nat} {pt : List Word} (hd : decodeArm tr as wt = some (j, pt)) :
    ∃ pa, decodeArm tr as wa = some (j, pa) ∧ WsLe pa pt := by
  cases tr with
  | niche =>
      rcases wt with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try (simp [decodeArm] at hd; done)
      obtain ⟨v, rr, hv, hrr, rfl⟩ := wsle_single_low hw
      simp only [decodeArm] at hd ⊢
      generalize y.val = V at hd ⊢
      cases V with
      | undef => simp at hd
      | null => simp at hd
      | num n => exact ⟨pt, hd, WsLe.refl pt⟩
      | loc a g =>
          simp only [Option.bind_eq_bind] at hd ⊢
          cases hl : ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
          | none => simp [hl] at hd
          | some q =>
              obtain ⟨j', ty⟩ := q
              simp [hl] at hd
              obtain ⟨rfl, rfl⟩ := hd
              exact ⟨[{ val := .loc a 0, view := v, rts := rr }], by simp,
                wsle_one ⟨rfl, hrr, hv⟩⟩
  | wide =>
      rcases wt with _ | ⟨y0, _ | ⟨y1, _ | ⟨_, _⟩⟩⟩ <;> try (simp [decodeArm] at hd; done)
      obtain ⟨x0, wa', rfl, hx0, hw'⟩ := wsle_cons hw
      obtain ⟨x1, rfl, hx1⟩ := wsle_single hw'
      simp only [decodeArm, hx0.val] at hd ⊢
      generalize y0.val = V at hd ⊢
      cases V with
      | num m =>
          simp only [Option.bind_eq_bind] at hd ⊢
          cases hl : as[m]? with
          | none => simp [hl] at hd
          | some arm =>
              by_cases hr : arm.rawWords = some 0
              · simp [hl, hr] at hd; obtain ⟨rfl, rfl⟩ := hd
                exact ⟨[], by simp [hr], trivial⟩
              · simp [hl, hr] at hd; obtain ⟨rfl, rfl⟩ := hd
                exact ⟨[x1], by simp [hr], hx1, trivial⟩
      | undef => simp at hd
      | loc _ _ => simp at hd
      | null => simp at hd
  | boxed => simp [decodeArm] at hd

theorem encodeArm_sim (tr : Tier) (as : List Ty) (j : Nat) {pa pt : List Word} (hp : WsLe pa pt)
    {qt : List Word} (he : encodeArm tr as j pt = some qt) :
    ∃ qa, encodeArm tr as j pa = some qa ∧ WsLe qa qt := by
  cases tr with
  | niche =>
      simp only [encodeArm, Option.bind_eq_bind] at he ⊢
      cases hl : as[j]? with
      | none => simp [hl] at he
      | some arm =>
          simp only [hl, Option.bind_some] at he ⊢
          rcases pt with _ | ⟨y, _ | ⟨_, _⟩⟩
          · obtain rfl := wsle_nil hp; exact ⟨qt, he, WsLe.refl _⟩
          · obtain ⟨v, rr, hv, hrr, rfl⟩ := wsle_single_low hp
            generalize armK arm = K at he ⊢
            cases K <;> (try simp only at he ⊢) <;> first
              | (simp at he; done)
              | (generalize y.val = V at he ⊢
                 cases V <;> first
                   | (simp at he; done)
                   | exact ⟨qt, he, WsLe.refl _⟩
                   | (simp at he; subst he; exact ⟨_, rfl, wsle_one ⟨rfl, hrr, hv⟩⟩))
          · generalize armK arm = K at he
            cases K <;> simp at he
  | wide =>
      rcases pt with _ | ⟨y, _ | ⟨_, _⟩⟩
      · obtain rfl := wsle_nil hp; exact ⟨qt, he, WsLe.refl _⟩
      · obtain ⟨x, rfl, hx⟩ := wsle_single hp
        simp only [encodeArm] at he ⊢
        simp at he; subst he
        exact ⟨_, rfl, tvle_refl _, hx, trivial⟩
      · simp [encodeArm] at he
  | boxed => simp [encodeArm] at he

theorem asArm_sim (t : Ty) {wa wt : List Word} (hw : WsLe wa wt) {j : Nat} {pt : List Word}
    (hd : asArm t wt = some (j, pt)) : ∃ pa, asArm t wa = some (j, pa) ∧ WsLe pa pt := by
  unfold asArm at hd ⊢
  by_cases hs : sumHead t = true
  · simp only [hs, ↓reduceIte] at hd ⊢; exact decodeArm_sim _ _ hw hd
  · simp only [hs] at hd ⊢; cases hd; exact ⟨wa, rfl, hw⟩

theorem ofArm_sim (t : Ty) (j : Nat) {pa pt : List Word} (hp : WsLe pa pt) {qt : List Word}
    (he : ofArm t j pt = some qt) : ∃ qa, ofArm t j pa = some qa ∧ WsLe qa qt := by
  unfold ofArm at he ⊢
  by_cases hs : sumHead t = true
  · simp only [hs, ↓reduceIte] at he ⊢; exact encodeArm_sim _ _ _ hp he
  · simp only [hs] at he ⊢
    by_cases hj : (j == 0) = true
    · simp only [hj, ↓reduceIte] at he ⊢; cases he; exact ⟨pa, rfl, hp⟩
    · simp only [hj] at he; cases he

theorem projM_sim (p : Prog) (k : Promises.Knobs) (n i lbase : Nat) (bf : Bool)
    {sa st : St} (h : StLe O sa st) (t : Ty) {wa wt : List Word} (hw : WsLe wa wt)
    {r : St × Nat × List Word} (hin : r ∈ projM ⟨p, k, .tso, n, i, lbase, bf, fun _ => False, fun _ => True⟩ st t wt) :
    ∃ ra ∈ projM ⟨p, k, .arm, n, i, lbase, bf, fun _ => False, fun _ => True⟩ sa t wa,
      StLe O ra.1 r.1 ∧ ra.2.1 = r.2.1 ∧ WsLe ra.2.2 r.2.2 := by
  unfold projM at hin ⊢
  by_cases hb : isBoxed t = true
  · simp only [hb, ↓reduceIte] at hin ⊢
    rcases wt with _ | ⟨y, _ | ⟨_, _⟩⟩ <;> try (simp at hin; done)
    obtain ⟨v, rr, hv, hrr, rfl⟩ := wsle_single_low hw
    simp only [addrOf_low2] at hin ⊢
    cases ha : addrOf y with
    | none => simp [ha] at hin
    | some b =>
        simp only [ha, List.mem_flatMap] at hin ⊢
        obtain ⟨⟨s1, tw⟩, hl, hrest⟩ := hin
        obtain ⟨sa1, twa, hl', h1, htw⟩ := loadUnits_sim (tvle_low2 hv hrr) b false [.one] 0 h hl
        rcases tw with _ | ⟨tag, _ | ⟨_, _⟩⟩ <;> try (simp at hrest; done)
        obtain ⟨vt, rt0, hvt, hrt0, rfl⟩ := wsle_single_low htw
        rcases hV : tag.val with _ | jj | ⟨_, _⟩ | _ <;> try (simp [hV] at hrest; done)
        simp only [hV] at hrest
        cases hu : (armsOf t)[jj]?.bind accs with
        | none => simp [hu] at hrest
        | some us =>
            simp only [hu, List.mem_map] at hrest
            obtain ⟨⟨s2, pl⟩, hl2, rfl⟩ := hrest
            obtain ⟨sa2, pla, hl2', h2, hpl⟩ := loadUnits_sim (tvle_low2 hv hrr) b false us 1 h1 hl2
            refine ⟨(sa2, jj, pla), ⟨(sa1, [{ tag with view := vt, rts := rt0 }]), hl', ?_⟩, h2, rfl, hpl⟩
            simp only [hV, hu, List.mem_map]
            exact ⟨(sa2, pla), hl2', rfl⟩
  · simp only [hb] at hin ⊢
    simp only [ol] at hin ⊢
    cases hd : asArm t wt with
    | none => simp [hd] at hin
    | some q =>
        obtain ⟨j, pt⟩ := q
        obtain ⟨pa, hda, hp⟩ := asArm_sim t hw hd
        simp [hd] at hin; subst hin
        exact ⟨(sa, j, pa), by simp [hda], h, rfl, hp⟩

theorem injM_sim (p : Prog) (k : Promises.Knobs) (n i lbase : Nat) (bf : Bool)
    {sa st : St} (h : StLe O sa st) (t : Ty) (j : Nat) {pa pt : List Word} (hp : WsLe pa pt)
    {r : St × List Word} (hin : r ∈ injM ⟨p, k, .tso, n, i, lbase, bf, fun _ => False, fun _ => True⟩ st t j pt) :
    ∃ ra ∈ injM ⟨p, k, .arm, n, i, lbase, bf, fun _ => False, fun _ => True⟩ sa t j pa, StLe O ra.1 r.1 ∧ WsLe ra.2 r.2 := by
  unfold injM at hin ⊢
  by_cases hb : isBoxed t = true
  · simp only [hb, ↓reduceIte] at hin ⊢
    cases hu : (armsOf t)[j]?.bind accs with
    | none => simp [hu] at hin
    | some us =>
        simp only [hu, List.mem_map] at hin ⊢
        obtain ⟨⟨st', pwt⟩, hal, rfl⟩ := hin
        rw [← h.nalloc] at hal
        obtain ⟨sa', pwa, hal', hst', hpw⟩ := alloc_sim k _ (.one :: us)
          (show WsLe (cst (.num j) :: pa) (cst (.num j) :: pt) from ⟨tvle_refl _, hp⟩) h hal
        refine ⟨_, ⟨(sa', pwa), hal', rfl⟩, ?_, hpw, trivial⟩
        cases bf
        · exact hst'
        · exact fenceS_sim hst' _
  · simp only [hb] at hin ⊢
    simp only [ol] at hin ⊢
    cases he : ofArm t j pt with
    | none => simp [he] at hin
    | some qt =>
        obtain ⟨qa, hea, hq⟩ := ofArm_sim t j hp he
        simp [he] at hin; subst hin
        exact ⟨(sa, qa), by simp [hea], h, hq⟩

def ResLe (O : List Ts) (ra rt : St × Ty × List Word) : Prop := StLe O ra.1 rt.1 ∧ ra.2.1 = rt.2.1 ∧ WsLe ra.2.2 rt.2.2

theorem evalOp_sim (p : Prog) (k : Promises.Knobs) (n i lbase : Nat) (bf : Bool)
    {ea et : Env} (he : EnvLe ea et) (σs : List Ty) {sa st : St} (h : StLe O sa st) (op : Op)
    {rt : St × Ty × List Word} (hin : rt ∈ evalOp ⟨p, k, .tso, n, i, lbase, bf, fun _ => False, fun _ => True⟩ et σs st op) :
    ∃ ra ∈ evalOp ⟨p, k, .arm, n, i, lbase, bf, fun _ => False, fun _ => True⟩ ea σs sa op , ResLe O ra rt := by
  cases op with
  | spawn => simp [evalOp] at hin
  | ext => simp [evalOp] at hin
  | atom a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, t, wa), by simp, h, rfl, hw⟩
  | pair a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      ev b => u ut ua hu
      simp at hin; subst hin
      exact ⟨(sa, _, wa ++ ua), by simp, h, rfl, WsLe.append hw hu⟩
  | add a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      ev b => u ut ua hu
      one wt wa hw => y v hv rv hrv
      one ut ua hu => y' v' hv' rv' hrv'
      fin_same
  | sub a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      ev b => u ut ua hu
      one wt wa hw => y v hv rv hrv
      one ut ua hu => y' v' hv' rv' hrv'
      fin_same
  | null μ τ => simp only [evalOp] at hin ⊢; fin_same
  | fold a τ =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, _, wa), by simp, h, rfl, hw⟩
  | pack a w τ =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, _, wa), by simp, h, rfl, hw⟩
  | packT a σ τ =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, _, wa), by simp, h, rfl, hw⟩
  | nameI a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, _, wa), by simp, h, rfl, hw⟩
  | validate y =>
      simp only [evalOp, ol] at hin ⊢
      rcases hq : lookupE et y with _ | ⟨t, wt⟩
      · simp [hq] at hin
      obtain ⟨wa, hqa, hw⟩ := optle_some (hq ▸ lookupE_rel he y)
      simp [hq] at hin; subst hin
      exact ⟨(sa, _, wa), by simp [hqa], h, rfl, hw⟩
  | mkWord r P v tok =>
      by_cases hg : P.ghost = true
      · simp only [evalOp, hg] at hin ⊢; fin_same
      · simp only [evalOp, hg, ol] at hin ⊢
        ev v => t wt wa hw
        simp at hin; subst hin
        exact ⟨(sa, _, wa), by simp, h, rfl, hw⟩
  | mkWord2 r P v0 v1 tok =>
      simp only [evalOp, ol] at hin ⊢
      ev v0 => t0 wt0 wa0 hw0
      ev v1 => t1 wt1 wa1 hw1
      simp at hin; subst hin
      exact ⟨(sa, _, wa0 ++ wa1), by simp, h, rfl, WsLe.append hw0 hw1⟩
  | ldp acq a n0 n1 =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      one wt wa hw => y v hv rv hrv
      cases hp : pairRef t
      · simp [hp] at hin
      simp only [hp, ↓reduceIte] at hin ⊢
      opt (addrOf y) => b
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨st', wt'⟩, hl, rfl⟩ := hin
      obtain ⟨sa', wa', hl', hst', hw'⟩ := loadUnits_sim (tvle_low2 hv hrv) b acq [.two] 0 h hl
      exact ⟨_, ⟨(sa', wa'), hl', rfl⟩, hst', rfl, hw'⟩
  | stp rel a v0 v1 tok =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      ev v0 => u0 ut0 ua0 hu0
      ev v1 => u1 ut1 ua1 hu1
      one wt wa hw => y v hv rv hrv
      opt (word2Of t) => ⟨r, P⟩
      opt (addrOf y) => b
      simp only [List.mem_map] at hin ⊢
      obtain ⟨st', hs, rfl⟩ := hin
      obtain ⟨sa', hs', hst'⟩ := storeUnits_sim k (tvle_low2 hv hrv) b rel [.two] (ua0 ++ ua1) (ut0 ++ ut1) 0 h
        (WsLe.append hu0 hu1) hs
      exact ⟨_, ⟨sa', hs', rfl⟩, hst', rfl, trivial⟩
  | mkEPair r P v0 v1 =>
      simp only [evalOp, ol] at hin ⊢
      ev v0 => t0 wt0 wa0 hw0
      ev v1 => t1 wt1 wa1 hw1
      simp at hin; subst hin
      exact ⟨(sa, _, wa0 ++ wa1), by simp, h, rfl, WsLe.append hw0 hw1⟩
  | mkTicket r N P v tok =>
      simp only [evalOp, ol] at hin ⊢
      ev v => t wt wa hw
      simp at hin; subst hin
      exact ⟨(sa, _, wa ++ wa), by simp, h, rfl, WsLe.append hw hw⟩
  | claim a tok => simp only [evalOp] at hin ⊢; fin_same
  | call f is a ts => simp [evalOp] at hin
  | callc f a => simp [evalOp] at hin
  | borrow c t => simp only [evalOp] at hin ⊢; fin_same
  | freeze t => simp only [evalOp] at hin ⊢; fin_same
  | endBorrow t => simp only [evalOp] at hin ⊢; fin_same
  | fence f =>
      simp only [evalOp] at hin ⊢
      simp at hin; subst hin
      exact ⟨(fenceS sa _, _, _), by simp, fenceS_sim h _, rfl, WsLe.refl _⟩
  | fnptr f =>
      simp only [evalOp] at hin ⊢
      opt (p.findIdx? (·.name == f)) => j
      opt (p.find? (·.name == f)) => d
      fin_same
  | cvt sg w a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      fin_same
  | toInt a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      fin_same
  | asLanes sg w a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      fin_same
  | fop o a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      opt (fixOf t) => ⟨sg, w⟩
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev b => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      fin_same
  | fcmp o a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      opt (fixOf t) => ⟨sg, w⟩
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev b => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      fin_same
  | fop1 o a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      opt (fixOf t) => ⟨sg, w⟩
      rw [numOf_congr hw]
      opt (numOf wt) => x
      fin_same
  | lane a j =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      opt (lanesOf t) => ⟨sg, w⟩
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev j => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      fin_same
  | setLane a j v =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      opt (lanesOf t) => ⟨sg, w⟩
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev j => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      ev v => r rt' ra' hr
      rw [numOf_congr hr]
      opt (numOf rt') => z
      fin_same
  | rem a m =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      ev m => u ut ua hu
      rw [numOf_congr hw, numOf_congr hu]
      opt (numOf wt) => x
      opt (numOf ut) => y
      simp at hin
      obtain ⟨hy, rfl⟩ := hin
      exact ⟨(sa, _, _), by simp [hy], h, rfl, WsLe.refl _⟩
  | bits o a b =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev b => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      fin_same
  | bit1 o a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      fin_same
  | vmatch lo hi b =>
      simp only [evalOp, ol] at hin ⊢
      ev lo => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev hi => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      ev b => r rt' ra' hr
      rw [numOf_congr hr]
      opt (numOf rt') => z
      fin_same
  | band a m =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => x
      ev m => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => y
      fin_same
  | zero τ =>
      simp only [evalOp, ol] at hin ⊢
      opt (zeroWords (close σs τ)) => z
      fin_same
  | new a =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      opt (accs t) => us
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨st', pwt⟩, hal, rfl⟩ := hin
      rw [← h.nalloc] at hal
      obtain ⟨sa', pwa, hal', hst', hp⟩ := alloc_sim k _ us hw h hal
      exact ⟨_, ⟨(sa', pwa), hal', rfl⟩, hst', rfl, hp, trivial⟩
  | publish a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      split at hin
      · simp at hin; subst hin
        exact ⟨(fenceS sa .st, _, wa), by simp, fenceS_sim h _, rfl, hw⟩
      · simp at hin; subst hin
        exact ⟨(fenceS sa .st, _, wa), by simp, fenceS_sim h _, rfl, hw⟩
      · simp at hin
  | intoRgn _ a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      split at hin
      · simp at hin; subst hin
        exact ⟨(fenceS sa .st, _, wa), by simp, fenceS_sim h _, rfl, hw⟩
      · simp at hin; subst hin
        exact ⟨(fenceS sa .st, _, wa), by simp, fenceS_sim h _, rfl, hw⟩
      · simp at hin
  | fld j a =>
      simp only [evalOp, ol] at hin ⊢
      ev a => t wt wa hw
      one wt wa hw => y v hv rv hrv
      opt (cellOf t) => ⟨μ, u⟩
      generalize unfold1 u = U at hin ⊢
      cases U <;> try (simp at hin; done)
      rename_i c1 c2
      generalize y.val = V at hin ⊢
      cases V <;> try (simp at hin; done)
      rename_i b gg
      by_cases hj : j = 0
      · subst hj
        simp at hin; subst hin
        exact ⟨(sa, _, [{ val := .loc (offs b 0) gg, view := v, rts := rv }]), by simp, h, rfl,
          ⟨rfl, hrv, hv⟩, trivial⟩
      · simp only [beq_iff_eq, hj, ↓reduceIte] at hin ⊢
        opt (accs c1) => us
        simp at hin; subst hin
        exact ⟨(sa, _, [{ val := .loc (offs b (nWords us)) gg, view := v, rts := rv }]),
          by simp, h, rfl, ⟨rfl, hrv, hv⟩, trivial⟩
  | idx b i =>
      simp only [evalOp, ol] at hin ⊢
      ev b => t wt wa hw
      one wt wa hw => y v hv rv hrv
      ev i => u ut ua hu
      rw [numOf_congr hu]
      opt (numOf ut) => j
      opt (bufElem t) => ⟨μ, c⟩
      opt (accs c) => us
      generalize y.val = V at hin ⊢
      cases V <;> try (simp at hin; done)
      rename_i aa gg
      simp at hin; subst hin
      exact ⟨(sa, _, [{ val := .loc (offs aa (j * nWords us)) gg, view := v, rts := rv }]),
        by simp, h, rfl, ⟨rfl, hrv, hv⟩, trivial⟩
  | loadAt b i =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (accs c) => us
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, rfl⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false us 0 h hl
      exact ⟨_, ⟨(sa1, olda), hl', rfl⟩, h1, rfl, hwo⟩
  | xchgAt b i x =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      ev x => r xt xa hx
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (accs c) => us
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, s2, hs, rfl⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false us 0 h hl
      obtain ⟨sa2, hs', h2⟩ := storeUnits_sim k (tvle_low2 hv hrv) _ false us xa xt 0 h1 hx hs
      exact ⟨_, ⟨(sa1, olda), hl', sa2, hs', rfl⟩, h2, rfl, hwo⟩
  | loadAtF b i q =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (accs c) => us
      opt (compOff c q) => ⟨cc, o⟩
      opt (accs cc) => cs
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, rfl⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false cs 0 h hl
      exact ⟨_, ⟨(sa1, olda), hl', rfl⟩, h1, rfl, hwo⟩
  | xchgAtF b i q x =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      ev x => r xt xa hx
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (accs c) => us
      opt (compOff c q) => ⟨cc, o⟩
      opt (accs cc) => cs
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, s2, hs, rfl⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false cs 0 h hl
      obtain ⟨sa2, hs', h2⟩ := storeUnits_sim k (tvle_low2 hv hrv) _ false cs xa xt 0 h1 hx hs
      exact ⟨_, ⟨(sa1, olda), hl', sa2, hs', rfl⟩, h2, rfl, hwo⟩
  | ldl b i =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (lanesOf c) => ⟨sg, w⟩
      simp only [List.mem_filterMap] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, hf⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false [.one] 0 h hl
      rw [← numOf_congr hwo] at hf
      cases hx : numOf olda with
      | none => simp [hx] at hf
      | some x =>
          simp [hx] at hf; subst hf
          exact ⟨(sa1, _, _), ⟨(sa1, olda), hl', by simp [hx]⟩, h1, rfl, WsLe.refl _⟩
  | ldlw b wi jl =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev wi => u ut ua hu
      ev jl => r jt ja hj
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu, numOf_congr hj]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => ii
      opt (numOf jt) => jj
      opt (addrOf y) => aa
      opt (lanesOf c) => ⟨sg, w⟩
      simp only [List.mem_filterMap] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, hf⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false [.one] 0 h hl
      rw [← numOf_congr hwo] at hf
      cases hx : numOf olda with
      | none => simp [hx] at hf
      | some x =>
          simp [hx] at hf; subst hf
          exact ⟨(sa1, _, _), ⟨(sa1, olda), hl', by simp [hx]⟩, h1, rfl, WsLe.refl _⟩
  | stl b i x =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      ev x => r xt xa hx
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu, numOf_congr hx]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (numOf xt) => yy
      opt (addrOf y) => aa
      opt (lanesOf c) => ⟨sg, w⟩
      simp only [List.mem_flatMap] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, hs⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false [.one] 0 h hl
      rw [← numOf_congr hwo] at hs
      cases hn : numOf olda with
      | none => simp [hn] at hs
      | some z =>
          simp only [hn, List.mem_map] at hs
          obtain ⟨s2, hs2, rfl⟩ := hs
          obtain ⟨sa2, hs2', h2⟩ :=
            storeUnits_sim k (tvle_low2 hv hrv) _ false [.one] _ _ 0 h1 (WsLe.refl _) hs2
          exact ⟨(sa2, .unit, []), ⟨(sa1, olda), hl', by simp only [hn, List.mem_map]; exact ⟨sa2, hs2', rfl⟩⟩,
            h2, rfl, trivial⟩
  | stlw b wi jl x =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev wi => u ut ua hu
      ev jl => r jt ja hj
      ev x => q xt xa hx
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu, numOf_congr hj, numOf_congr hx]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => ii
      opt (numOf jt) => jj
      opt (numOf xt) => yy
      opt (addrOf y) => aa
      opt (lanesOf c) => ⟨sg, w⟩
      simp only [List.mem_flatMap] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, hs⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) _ false [.one] 0 h hl
      rw [← numOf_congr hwo] at hs
      cases hn : numOf olda with
      | none => simp [hn] at hs
      | some z =>
          simp only [hn, List.mem_map] at hs
          obtain ⟨s2, hs2, rfl⟩ := hs
          obtain ⟨sa2, hs2', h2⟩ :=
            storeUnits_sim k (tvle_low2 hv hrv) _ false [.one] _ _ 0 h1 (WsLe.refl _) hs2
          exact ⟨(sa2, .unit, []), ⟨(sa1, olda), hl', by simp only [hn, List.mem_map]; exact ⟨sa2, hs2', rfl⟩⟩,
            h2, rfl, trivial⟩
  | bufInit b i x =>
      simp only [evalOp] at hin ⊢
      ev b => t wt wa hw
      ev i => u ut ua hu
      ev x => r xt xa hx
      one wt wa hw => y v hv rv hrv
      rw [numOf_congr hu]
      opt (bufElem t) => ⟨μ, c⟩
      opt (numOf ut) => j
      opt (addrOf y) => aa
      opt (accs c) => us
      split at hin
      · simp only [List.mem_map] at hin ⊢
        obtain ⟨st', hs, rfl⟩ := hin
        obtain ⟨sa', hs', hst'⟩ := storeUnits_sim k (tvle_low2 hv hrv) _ false _ xa xt 0 h hx hs
        exact ⟨_, ⟨sa', hs', rfl⟩, hst', rfl, tvle_low2 hv hrv, trivial⟩
      · simp at hin
  | newBuf m τ =>
      simp only [evalOp, ol] at hin ⊢
      ev m => t wt wa hw
      rw [numOf_congr hw]
      opt (numOf wt) => kk
      opt (accs (close σs τ)) => us
      rw [h.nalloc]
      simp at hin
      subst hin
      generalize (if zeroableIn [] [] (close σs τ) = true then zeroWords (close σs τ) else none) = Z
      obtain ⟨hA, hB⟩ := allocBuf_sim (freshLabel lbase n i st.nalloc) (kk * nWords us) Z h
      exact ⟨((allocBuf (freshLabel lbase n i st.nalloc) (kk * nWords us) Z sa).1, _,
          [(allocBuf (freshLabel lbase n i st.nalloc) (kk * nWords us) Z sa).2]), by simp, hA, rfl,
        by rw [hB]; exact WsLe.refl _⟩
  | load acq a =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      one wt wa hw => y v hv rv hrv
      opt (cellOf t) => ⟨μ, u⟩
      opt (addrOf y) => b
      opt (accs u) => us
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨st', wt'⟩, hl, rfl⟩ := hin
      obtain ⟨sa', wa', hl', hst', hw'⟩ := loadUnits_sim (tvle_low2 hv hrv) b acq us 0 h hl
      exact ⟨_, ⟨(sa', wa'), hl', rfl⟩, hst', rfl, hw'⟩
  | store rel a x tok =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      ev x => u ut ua hu
      one wt wa hw => y v hv rv hrv
      opt (cellOf t) => ⟨μ, c⟩
      opt (addrOf y) => b
      opt (accs c) => us
      simp only [List.mem_map] at hin ⊢
      obtain ⟨st', hs, rfl⟩ := hin
      obtain ⟨sa', hs', hst'⟩ := storeUnits_sim k (tvle_low2 hv hrv) b rel us ua ut 0 h hu hs
      exact ⟨_, ⟨sa', hs', rfl⟩, hst', rfl, trivial⟩
  | xchg a x =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      ev x => u ut ua hu
      one wt wa hw => y v hv rv hrv
      opt (cellOf t) => ⟨μ, c⟩
      opt (addrOf y) => b
      opt (accs c) => us
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, old⟩, hl, s2, hs, rfl⟩ := hin
      obtain ⟨sa1, olda, hl', h1, hwo⟩ := loadUnits_sim (tvle_low2 hv hrv) b false us 0 h hl
      obtain ⟨sa2, hs', h2⟩ := storeUnits_sim k (tvle_low2 hv hrv) b false us ua ut 0 h1 hu hs
      exact ⟨_, ⟨(sa1, olda), hl', sa2, hs', rfl⟩, h2, rfl, hwo⟩
  | fetch o acq rel a v =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      ev v => u ut ua hu
      one wt wa hw => pw v1 hv1 rv1 hrv1
      one ut ua hu => nw v3 hv3 rv3 hrv3
      opt (addrOf pw) => b
      simp only [List.mem_map, h.pairs] at hin ⊢
      obtain ⟨⟨mt', tt'⟩, hr, rfl⟩ := hin
      obtain ⟨⟨qm, qth⟩, hq, hmq, htq⟩ := Promises.Sim.stepRmw_sim k h.mem
        (mth_le h (tvle_low2 hv1 hrv1) (tvle_low2 hv3 hrv3) (tvle_low2 hv3 hrv3)) (fun t ht => (h.agree t ht).2)
        st.pairs 1 b o.kind (dataE 1 nw) [0] acq rel hr
      have hea := Promises.Sim.stepRmw_ext k .arm _ _ _ _ _ _ _ _ _ _ hq
      have het := Promises.Sim.stepRmw_ext k .tso _ _ _ _ _ _ _ _ _ _ hr
      refine ⟨_, ⟨(qm, qth), hq, rfl⟩, ?_, rfl, wsle_one (htq.regs 1)⟩
      exact { mem := hmq, pairs := rfl, vs := htq.vs, promises := htq.promises,
              nalloc := h.nalloc,
              undefs := by simp only [h.undefs, countUndef_congr (wsle_one (htq.regs 1))],
              agree := Agree.ext h.agree h.mem hea.1 het.1 het.2,
              other := Agree.ext h.other h.mem hea.1 het.1 (fun _ h => h) }
  | inl τ a =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, j, pl⟩, hpr, ⟨s2, q⟩, hij, rfl⟩ := hin
      obtain ⟨⟨sa1, ja, pla⟩, hpr', h1, hj, hpl⟩ := projM_sim p k n i lbase bf h t hw hpr
      simp only at hj; subst hj
      obtain ⟨⟨sa2, qa⟩, hij', h2, hq⟩ := injM_sim p k n i lbase bf h1 _ _ hpl hij
      exact ⟨_, ⟨(sa1, ja, pla), hpr', (sa2, qa), hij', rfl⟩, h2, rfl, hq⟩
  | inr τ a =>
      simp only [evalOp] at hin ⊢
      ev a => t wt wa hw
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, j, pl⟩, hpr, ⟨s2, q⟩, hij, rfl⟩ := hin
      obtain ⟨⟨sa1, ja, pla⟩, hpr', h1, hj, hpl⟩ := projM_sim p k n i lbase bf h t hw hpr
      simp only at hj; subst hj
      obtain ⟨⟨sa2, qa⟩, hij', h2, hq⟩ := injM_sim p k n i lbase bf h1 _ _ hpl hij
      exact ⟨_, ⟨(sa1, ja, pla), hpr', (sa2, qa), hij', rfl⟩, h2, rfl, hq⟩

/-! ## L4 `tstep` simulates -/

def FrameLe (fa ft : Frame) : Prop :=
  fa.x = ft.x ∧ fa.body = ft.body ∧ EnvLe fa.env ft.env ∧ fa.σs = ft.σs ∧ fa.ty = ft.ty

def StackLe : List Frame → List Frame → Prop
  | [], [] => True
  | fa :: sa, ft :: st => FrameLe fa ft ∧ StackLe sa st
  | _, _ => False

/-- (D4) Permits: both absent, or both present with ARM's view lower. -/
abbrev PermLe (a b : Option Ts) : Prop := Option.Rel (· ≤ ·) a b

theorem PermLe.refl : ∀ o : Option Ts, PermLe o o
  | none => .none
  | some v => .some (Nat.le_refl v)

theorem PermLe.getD {a b : Option Ts} (h : PermLe a b) : a.getD 0 ≤ b.getD 0 := by
  cases h with
  | none => exact Nat.le_refl _
  | some h => exact h

theorem permLe_park {a b : Option Ts} (h : PermLe a b) (n : ExtName) :
    PermLe (if n = .park then none else a) (if n = .park then none else b) := by
  split
  · exact .none
  · exact h

/-- (D4) The release view an `unpark` publishes is monotone in the view state. -/
theorem relView_le {va vt : VState} (h : VLe va vt) : relView va ≤ relView vt := by
  have h1 : va.vRd ≤ vt.vRd := h.vRd
  have h2 : va.vWr ≤ vt.vWr := h.vWr
  have h3 : va.vRelSt ≤ vt.vRelSt := h.vRelSt
  unfold relView
  exact Nat.max_le.2 ⟨Nat.le_trans h3 (Nat.le_max_left _ _), Nat.le_trans (Nat.max_le.2
    ⟨Nat.le_trans h1 (Nat.le_max_left _ _), Nat.le_trans h2 (Nat.le_max_right _ _)⟩) (Nat.le_max_right _ _)⟩

/-- (D4) `park`'s acquire is monotone in the view and the permit (the same memory size). -/
theorem parkVs_le {na nt : Nat} {ta tt : TTh} (hn : na = nt) (hv : VLe ta.vs tt.vs)
    (hp : PermLe ta.permit tt.permit) : VLe (parkVs na ta) (parkVs nt tt) := by
  subst hn
  unfold parkVs
  generalize ta.permit = pa at hp ⊢
  generalize tt.permit = pt at hp ⊢
  cases hp with
  | none => exact hv
  | some hab =>
    have h1 : ta.vs.vRd ≤ tt.vs.vRd := hv.vRd
    have h2 : ta.vs.vPreBase ≤ tt.vs.vPreBase := hv.vPreBase
    have h3 := Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ na) hab, Nat.min_le_right _ na⟩
    refine ⟨hv.coh, ?_, hv.vWr, hv.vCtrl, ?_, hv.vRelSt, hv.mine, hv.fwd⟩
    · exact Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left _ _), Nat.le_trans h3 (Nat.le_max_right _ _)⟩
    · exact Nat.max_le.2 ⟨Nat.le_trans h2 (Nat.le_max_left _ _), Nat.le_trans h3 (Nat.le_max_right _ _)⟩

theorem parkVs_le_if {na nt : Nat} {ta tt : TTh} (hn : na = nt) (hv : VLe ta.vs tt.vs)
    (hp : PermLe ta.permit tt.permit) (n : ExtName) :
    VLe (if n = .park then parkVs na ta else ta.vs) (if n = .park then parkVs nt tt else tt.vs) := by
  split
  · exact parkVs_le hn hv hp
  · exact hv

/-- A thread: the same term, frames and types; words' views and `rts`, and view state, lower. -/
structure TThLe (ta tt : TTh) : Prop where
  term     : ta.term = tt.term
  env      : EnvLe ta.env tt.env
  σs       : ta.σs = tt.σs
  stack    : StackLe ta.stack tt.stack
  vs       : VLe ta.vs tt.vs
  promises : ta.promises = tt.promises
  nalloc   : ta.nalloc = tt.nalloc
  undefs   : ta.undefs = tt.undefs
  /-- (D4) the park permit: both absent, or both present with a lower view -/
  permit   : PermLe ta.permit tt.permit

/-- A `tstep` result (memory, pairs, thread), with the agreement invariant. -/
def RLe (O : List Ts) (ra rt : Memory × List Ts × TTh) : Prop :=
  MemLe ra.1 rt.1 ∧ ra.2.1 = rt.2.1 ∧ TThLe ra.2.2 rt.2.2 ∧
    Agree ra.1 rt.1 rt.2.2.promises ∧ Agree ra.1 rt.1 O

theorem wsle_take : ∀ (n : Nat) {wa wt : List Word}, WsLe wa wt → WsLe (wa.take n) (wt.take n)
  | 0, _, _, _ => by simp only [List.take_zero]; trivial
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, ⟨hx, h⟩ => ⟨hx, wsle_take n h⟩
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

theorem wsle_drop : ∀ (n : Nat) {wa wt : List Word}, WsLe wa wt → WsLe (wa.drop n) (wt.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => trivial
  | n + 1, _ :: _, _ :: _, ⟨_, h⟩ => wsle_drop n h
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

/- `pick`: turn `∃ ra ∈ ol (some X), P ra` into `P X`. -/
macro "pick" : tactic =>
  `(tactic| simp only [ol, Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some,
      Option.toList_some, List.mem_singleton, exists_eq_left])

theorem tstep_sim (p : Prog) (k : Promises.Knobs) (n i lbase : Nat) (bf : Bool)
    {ma mt : Memory} (pairs : List Ts) {ta tt : TTh}
    (h : StLe O (stOf ma pairs ta) (stOf mt pairs tt)) (ht : TThLe ta tt)
    {r : Memory × List Ts × TTh} (hin : r ∈ tstep ⟨p, k, .tso, n, i, lbase, bf, fun _ => False, fun _ => True⟩ mt pairs tt) :
    ∃ ra ∈ tstep ⟨p, k, .arm, n, i, lbase, bf, fun _ => False, fun _ => True⟩ ma pairs ta, RLe O ra r := by
  obtain ⟨term, ea, σs, stka, vsa, pr, na, ua, tla, pma⟩ := ta
  obtain ⟨term', et, σs', stkt, vst, pr', nt, ut, tlt, pmt⟩ := tt
  obtain ⟨hterm, he, hσ, hstk, hvs, hpr, hna, hua, hpm⟩ := ht
  simp only at hterm hσ hpr hna hua he hstk hvs hpm
  subst hterm hσ hpr hna hua
  have same : ∀ {e : Expr} {ea' et' : Env} {σs'' : List Ty} {fa ft : List Frame},
      EnvLe ea' et' → StackLe fa ft →
      RLe O (ma, pairs, ⟨e, ea', σs'', fa, vsa, pr, na, ua, tla, pma⟩)
        (mt, pairs, ⟨e, et', σs'', ft, vst, pr, na, ua, tlt, pmt⟩) :=
    fun hE hS => ⟨h.mem, rfl, ⟨rfl, hE, rfl, hS, hvs, rfl, rfl, rfl, hpm⟩, h.agree, h.other⟩
  cases term with
  | let_ x op e =>
      cases op
      case call f is a ts =>
        simp only [tstep, callFrame, enter, ol] at hin ⊢
        opt (p.find? (·.name == f)) => d
        ev a => t wt wa hw
        simp at hin; subst hin
        pick
        exact ⟨h.mem, rfl, ⟨rfl, ⟨rfl, rfl, hw, trivial⟩, rfl, ⟨⟨rfl, rfl, he, rfl, rfl⟩, hstk⟩, hvs,
          rfl, rfl, rfl, hpm⟩, h.agree, h.other⟩
      case callc f a =>
        simp only [tstep] at hin ⊢
        ev f => tf wt wa hw
        one wt wa hw => y v hv rv hrv
        generalize y.val = V at hin ⊢
        cases V <;> try (simp at hin; done)
        rename_i ii
        opt (p[ii]?) => d
        simp only [callFrame, enter, ol] at hin ⊢
        opt (p.find? (·.name == d.name)) => d'
        ev a => t ut ua hu
        simp at hin; subst hin
        pick
        exact ⟨h.mem, rfl, ⟨rfl, ⟨rfl, rfl, hu, trivial⟩, rfl, ⟨⟨rfl, rfl, he, rfl, rfl⟩, hstk⟩, hvs,
          rfl, rfl, rfl, hpm⟩, h.agree, h.other⟩
      all_goals
        simp only [tstep, List.mem_map] at hin ⊢
        obtain ⟨⟨s', t, ws⟩, hev, rfl⟩ := hin
        obtain ⟨⟨sa', ta', wa'⟩, hev', hs, htt, hws⟩ := evalOp_sim p k n i lbase bf he σs h _ hev
        refine ⟨_, ⟨(sa', ta', wa'), hev', rfl⟩, ?_⟩
        simp only at htt; subst htt
        exact ⟨hs.mem, hs.pairs, ⟨rfl, ⟨rfl, rfl, hws, he⟩, rfl, hstk, hs.vs, hs.promises, hs.nalloc,
          hs.undefs, hpm⟩, hs.agree, hs.other⟩
  | split a x y e =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      rename_i u w
      opt (accs u) => us
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, wsle_drop _ hw, ⟨rfl, rfl, wsle_take _ hw, he⟩⟩ hstk
  | unpack a w x e =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, hw, he⟩ hstk
  | unpackT a w x e =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, hw, he⟩ hstk
  | region a w pn tn e =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      -- D1: `region` fences, as `publish` does
      have hs := fenceS_sim h .st
      cases t <;> try (simp at hin; done)
      all_goals first
        | (simp at hin; subst hin; pick
           exact ⟨hs.mem, hs.pairs, ⟨rfl, ⟨rfl, rfl, trivial, ⟨rfl, rfl, hw, he⟩⟩, rfl, hstk, hs.vs, hs.promises,
             hs.nalloc, hs.undefs, hpm⟩, hs.agree, hs.other⟩)
        | (rename_i t' ψ
           cases t' <;> try (simp at hin; done)
           simp at hin; subst hin; pick
           exact ⟨hs.mem, hs.pairs, ⟨rfl, ⟨rfl, rfl, trivial, ⟨rfl, rfl, hw, he⟩⟩, rfl, hstk, hs.vs, hs.promises,
             hs.nalloc, hs.undefs, hpm⟩, hs.agree, hs.other⟩)
  | openPub a w pn cn e =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, trivial, ⟨rfl, rfl, hw, he⟩⟩ hstk
  | case a x e₁ y e₂ =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      simp only [List.mem_flatMap, List.mem_map] at hin ⊢
      obtain ⟨⟨s1, j, pl⟩, hpr, ⟨s2, q⟩, hij, rfl⟩ := hin
      obtain ⟨⟨sa1, ja, pla⟩, hpr', h1, hj, hpl⟩ := projM_sim p k n i lbase bf h _ hw hpr
      simp only at hj; subst hj
      obtain ⟨⟨sa2, qa⟩, hij', h2, hq⟩ := injM_sim p k n i lbase bf h1 _ _ hpl hij
      refine ⟨_, ⟨(sa1, ja, pla), hpr', (sa2, qa), hij', rfl⟩, ?_⟩
      exact ⟨h2.mem, h2.pairs, ⟨rfl, ⟨rfl, rfl, hq, he⟩, rfl, hstk, h2.vs, h2.promises, h2.nalloc,
        h2.undefs, hpm⟩, h2.agree, h2.other⟩
  | ifnull a e₁ y e₂ =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      cases t <;> try (simp at hin; done)
      one wt wa hw => yy v hv rv hrv
      rcases hV : yy.val with _ | nn | ⟨aa, gg⟩ | _ <;> simp only [hV] at hin ⊢ <;>
        try (simp at hin; done)
      · simp at hin; subst hin
        pick
        exact same ⟨rfl, rfl, wsle_one ⟨by simp [hV], hrv, hv⟩, he⟩ hstk
      · simp at hin; subst hin
        pick
        exact same he hstk
  | parity a w ev' od =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      one wt wa hw => yy v hv rv hrv
      generalize yy.val = V at hin ⊢
      cases V <;> try (simp at hin; done)
      simp only [List.mem_singleton] at hin; subst hin
      pick
      exact same he hstk
  | ifeq a b yes no =>
      simp only [tstep] at hin ⊢
      ev a => t wt wa hw
      ev b => u ut ua hu
      one wt wa hw => y1 v1 hv1 rv1 hrv1
      one ut ua hu => y2 v2 hv2 rv2 hrv2
      generalize y1.val = V1 at hin ⊢
      generalize y2.val = V2 at hin ⊢
      cases V1 <;> cases V2 <;> try (simp at hin; done)
      all_goals (simp only [List.mem_singleton] at hin; subst hin; pick; exact same he hstk)
  | cas acq rel w e v t ok fail =>
      simp only [tstep] at hin ⊢
      ev w => t1 w1 wa1 hw1
      ev e => t2 w2 wa2 hw2
      ev v => t3 w3 wa3 hw3
      one w1 wa1 hw1 => pw v1 hv1 rv1 hrv1
      one w2 wa2 hw2 => ew v2 hv2 rv2 hrv2
      one w3 wa3 hw3 => nw v3 hv3 rv3 hrv3
      opt (addrOf pw) => b
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨mt', tt'⟩, hr, rfl⟩ := hin
      obtain ⟨⟨qm, qth⟩, hq, hmq, htq⟩ := Promises.Sim.stepRmw_sim k h.mem
        (mth_le h (tvle_low2 hv1 hrv1) (tvle_low2 hv3 hrv3) (tvle_low2 hv3 hrv3)) (fun t ht => (h.agree t ht).2)
        pairs 1 b (.cas ew.val) (dataE 1 nw) [0] acq rel hr
      have hea := Promises.Sim.stepRmw_ext k .arm _ _ _ _ _ _ _ _ _ _ hq
      have het := Promises.Sim.stepRmw_ext k .tso _ _ _ _ _ _ _ _ _ _ hr
      refine ⟨_, ⟨(qm, qth), hq, rfl⟩, ?_⟩
      have hrd : (qth.regs 1).val = (tt'.regs 1).val := (htq.regs 1).val
      have hcu : countUndef [qth.regs 1] = countUndef [tt'.regs 1] :=
        countUndef_congr (wsle_one (htq.regs 1))
      have hag := Agree.ext h.agree h.mem hea.1 het.1 het.2
      have hot := Agree.ext h.other h.mem hea.1 het.1 (fun _ h => h)
      simp only [hrd, hcu]
      by_cases hc : ((tt'.regs 1).val == ew.val) = true
      · simp only [hc, ↓reduceIte]
        exact ⟨hmq, rfl, ⟨rfl, ⟨rfl, rfl, trivial, he⟩, rfl, hstk, htq.vs, htq.promises, rfl, rfl, hpm⟩,
          hag, hot⟩
      · simp only [hc]
        exact ⟨hmq, rfl, ⟨rfl, he, rfl, hstk, htq.vs, htq.promises, rfl, rfl, hpm⟩, hag, hot⟩
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
      simp only [tstep] at hin ⊢
      ev w => t1 w1 wa1 hw1
      ev e0 => t2 w2 wa2 hw2
      ev e1 => t3 w3 wa3 hw3
      ev v0 => t4 w4 wa4 hw4
      ev v1 => t5 w5 wa5 hw5
      one w1 wa1 hw1 => pw v1 hv1 rv1 hrv1
      one w2 wa2 hw2 => x0 v2 hv2 rv2 hrv2
      one w3 wa3 hw3 => x1 v3 hv3 rv3 hrv3
      one w4 wa4 hw4 => n0 v4 hv4 rv4 hrv4
      one w5 wa5 hw5 => n1 v5 hv5 rv5 hrv5
      opt (addrOf pw) => b
      simp only [List.mem_map] at hin ⊢
      obtain ⟨⟨mt', pt', tt'⟩, hr, rfl⟩ := hin
      obtain ⟨⟨qm, qp, qth⟩, hq, hmq, hpq, htq⟩ := Promises.Sim.stepRmwPair_sim h.mem
        (mth_le h (tvle_low2 hv1 hrv1) (tvle_low2 hv4 hrv4) (tvle_low2 hv5 hrv5)) (fun t ht => (h.agree t ht).2)
        pairs 1 2 b x0.val x1.val (dataE 1 n0) (dataE 2 n1) [0] acq rel hr
      have hea := Promises.Sim.stepRmwPair_ext .arm _ _ _ _ _ _ _ _ _ _ _ _ _ hq
      have het := Promises.Sim.stepRmwPair_ext .tso _ _ _ _ _ _ _ _ _ _ _ _ _ hr
      simp only at hpq; subst hpq
      refine ⟨_, ⟨(qm, qp, qth), hq, rfl⟩, ?_⟩
      have hrd0 : (qth.regs 1).val = (tt'.regs 1).val := (htq.regs 1).val
      have hrd1 : (qth.regs 2).val = (tt'.regs 2).val := (htq.regs 2).val
      have hcu : countUndef [qth.regs 1, qth.regs 2] = countUndef [tt'.regs 1, tt'.regs 2] :=
        countUndef_congr ⟨htq.regs 1, htq.regs 2, trivial⟩
      have hag := Agree.ext h.agree h.mem hea.1 het.1 het.2
      have hot := Agree.ext h.other h.mem hea.1 het.1 (fun _ h => h)
      simp only [hrd0, hrd1, hcu]
      by_cases hc : ((tt'.regs 1).val == x0.val && (tt'.regs 2).val == x1.val) = true
      · simp only [hc, ↓reduceIte]
        exact ⟨hmq, rfl, ⟨rfl, ⟨rfl, rfl, trivial, he⟩, rfl, hstk, htq.vs, htq.promises, rfl, rfl, hpm⟩,
          hag, hot⟩
      · simp only [hc]
        exact ⟨hmq, rfl, ⟨rfl, he, rfl, hstk, htq.vs, htq.promises, rfl, rfl, hpm⟩, hag, hot⟩
  | ret a =>
      simp only [tstep] at hin ⊢
      rcases stkt with _ | ⟨ft, rt'⟩
      · simp at hin
      rcases stka with _ | ⟨fa, ra'⟩
      · exact hstk.elim
      obtain ⟨hf, hstk'⟩ := hstk
      obtain ⟨fx, fb, fe, fσ, fty⟩ := fa
      obtain ⟨gx, gb, ge, gσ, gty⟩ := ft
      obtain ⟨hx, hb, hfe, hfs, hty⟩ := hf
      simp only at hx hb hfs hty hfe
      subst hx hb hfs hty
      ev a => t wt wa hw
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, hw, hfe⟩ hstk'
  | tail f w a ts =>
      simp only [tstep, enter, ol] at hin ⊢
      opt (p.find? (·.name == f)) => d
      ev a => t wt wa hw
      simp at hin; subst hin
      pick
      exact same ⟨rfl, rfl, hw, trivial⟩ hstk

/-! ## L5 The machine

`CfgLe` lifts the thread relation to configurations.  Its agreement invariant
is at *every* thread's outstanding promises (`allP`): a promise step pushes the
same message on both sides, and a thread step preserves agreement at the old
promises (`RLe`) and at the stepping thread's new ones. -/

theorem EnvLe.refl : ∀ e : Env, EnvLe e e
  | [] => trivial
  | (_, _, ws) :: e => ⟨rfl, rfl, WsLe.refl ws, EnvLe.refl e⟩

theorem StackLe.refl : ∀ s : List Frame, StackLe s s
  | [] => trivial
  | f :: s => ⟨⟨rfl, rfl, EnvLe.refl f.env, rfl, rfl⟩, StackLe.refl s⟩

theorem TThLe.refl (t : TTh) : TThLe t t :=
  ⟨rfl, EnvLe.refl _, rfl, StackLe.refl _, Promises.VLe.refl _, rfl, rfl, rfl, PermLe.refl _⟩

/-- Threads pairwise `TThLe`, with the same `ThreadId` box label (the extern moves agree). -/
def ThsLe (A B : Array TTh) : Prop :=
  A.size = B.size ∧ ∀ (j : Nat) (ta tt : TTh), A[j]? = some ta → B[j]? = some tt →
    TThLe ta tt ∧ ta.tidLbl = tt.tidLbl

theorem ThsLe.refl (A : Array TTh) : ThsLe A A :=
  ⟨rfl, fun _ _ _ ha hb => by rw [ha] at hb; cases hb; exact ⟨TThLe.refl _, rfl⟩⟩

theorem ths_some_tid {A B : Array TTh} (h : ThsLe A B) {j : Nat} {tt : TTh} (hb : B[j]? = some tt) :
    ∃ ta, A[j]? = some ta ∧ TThLe ta tt ∧ ta.tidLbl = tt.tidLbl := by
  have hj : j < B.size := by
    rcases Nat.lt_or_ge j B.size with hj | hj
    · exact hj
    · rw [Array.getElem?_eq_none hj] at hb; cases hb
  have hja : j < A.size := h.1 ▸ hj
  exact ⟨A[j], Array.getElem?_eq_getElem hja, h.2 j _ _ (Array.getElem?_eq_getElem hja) hb⟩

theorem ths_some {A B : Array TTh} (h : ThsLe A B) {j : Nat} {tt : TTh} (hb : B[j]? = some tt) :
    ∃ ta, A[j]? = some ta ∧ TThLe ta tt := by
  have hj : j < B.size := by
    rcases Nat.lt_or_ge j B.size with hj | hj
    · exact hj
    · rw [Array.getElem?_eq_none hj] at hb; cases hb
  have hja : j < A.size := h.1 ▸ hj
  exact ⟨A[j], Array.getElem?_eq_getElem hja, (h.2 j _ _ (Array.getElem?_eq_getElem hja) hb).1⟩

theorem ths_none {A B : Array TTh} (h : ThsLe A B) {j : Nat} (hb : B[j]? = none) : A[j]? = none := by
  rcases Nat.lt_or_ge j B.size with hj | hj
  · rw [Array.getElem?_eq_getElem hj] at hb; cases hb
  · exact Array.getElem?_eq_none (h.1 ▸ hj)

theorem thsLe_set {A B : Array TTh} (h : ThsLe A B) (j : Nat) {ta tt : TTh} (ht : TThLe ta tt)
    (htl : ta.tidLbl = tt.tidLbl) : ThsLe (A.set! j ta) (B.set! j tt) := by
  refine ⟨by simp [Array.set!, h.1], ?_⟩
  intro l xa xt hxa hxt
  simp only [Array.set!, Array.getElem?_setIfInBounds] at hxa hxt
  by_cases hjl : j = l
  · subst hjl
    by_cases hja : j < A.size
    · have hjb : j < B.size := h.1 ▸ hja
      simp only [hja, hjb, ↓reduceIte, Option.some.injEq] at hxa hxt
      subst hxa hxt; exact ⟨ht, htl⟩
    · simp [hja] at hxa
  · simp only [hjl, ↓reduceIte] at hxa hxt; exact h.2 l xa xt hxa hxt

/-- Every thread's outstanding promises. -/
def allP (c : Cfg) : List Ts := c.ths.toList.flatMap (·.promises)

theorem mem_allP {c : Cfg} {j : Nat} {th : TTh} (hj : c.ths[j]? = some th) {t : Ts}
    (ht : t ∈ th.promises) : t ∈ allP c := by
  simp only [allP, List.mem_flatMap]
  exact ⟨th, by simpa using Array.mem_of_getElem? hj, ht⟩

theorem allP_set {c c' : Cfg} {i : Nat} {th : TTh} (hc : c'.ths = c.ths.set! i th) {t : Ts}
    (ht : t ∈ allP c') : t ∈ th.promises ∨ t ∈ allP c := by
  simp only [allP, List.mem_flatMap, hc] at ht ⊢
  obtain ⟨x, hx, htx⟩ := ht
  have e : (c.ths.set! i th).toList = c.ths.toList.set i th := by simp [Array.set!]
  rw [e] at hx
  rcases List.mem_or_eq_of_mem_set hx with hx | hx
  · exact Or.inr ⟨x, hx, htx⟩
  · subst hx; exact Or.inl htx

/-- Configurations: ARM on the left, TSO on the right. -/
structure CfgLe (ca ct : Cfg) : Prop where
  mem      : MemLe ca.mem ct.mem
  pairs    : ca.pairs = ct.pairs
  ths      : ThsLe ca.ths ct.ths
  lbase    : ca.lbase = ct.lbase
  boxFence : ca.boxFence = ct.boxFence
  agree    : Agree ca.mem ct.mem (allP ct)
  cap      : ca.cap = ct.cap
  /-- (M1) the same trace: extern results read it (`resultsL`) -/
  trace    : ca.trace = ct.trace

theorem CfgLe.refl (c : Cfg) (hwf : ∀ t ∈ allP c, t < c.mem.size) : CfgLe c c :=
  ⟨Promises.Sim.MemLe.refl _, rfl, ThsLe.refl _, rfl, rfl, fun t ht => ⟨hwf t ht, rfl⟩, rfl, rfl⟩

theorem threadSteps_sim (p : Prog) (k : Promises.Knobs) {ca ct c' : Cfg} (h : CfgLe ca ct)
    (i : Nat) (hin : c' ∈ threadSteps p k .tso ct i) :
    ∃ ca' ∈ threadSteps p k .arm ca i, CfgLe ca' c' := by
  unfold threadSteps at hin ⊢
  rcases hb : ct.ths[i]? with _ | tt
  · rw [hb] at hin; simp at hin
  obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.ths hb
  rw [hb] at hin; rw [ha]
  simp only [List.mem_map] at hin ⊢
  obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := hin
  have hs : StLe (allP ct) (stOf ca.mem ct.pairs ta) (stOf ct.mem ct.pairs tt) :=
    ⟨h.mem, rfl, hta.vs, hta.promises, hta.nalloc, hta.undefs,
     fun t ht => h.agree t (mem_allP hb ht), h.agree⟩
  simp only [gOf] at hr ⊢
  rw [show ca.n = ct.n by simp only [Cfg.n, h.ths.1, h.cap], h.lbase, h.boxFence, h.pairs]
  obtain ⟨⟨ma', pa', ta'⟩, hra, hR⟩ := tstep_sim p k ct.n i ct.lbase ct.boxFence ct.pairs hs hta hr
  obtain ⟨hm, hp, ht', hag1, hag2⟩ := hR
  refine ⟨_, ⟨(ma', pa', ta'), hra, rfl⟩, ?_⟩
  refine ⟨hm, hp, thsLe_set h.ths i ht'
    (by rw [TermTidLbl.tstep_tidLbl hra, TermTidLbl.tstep_tidLbl hr]; exact htl), rfl, rfl, ?_, h.cap, h.trace⟩
  intro t ht
  rcases allP_set (c := ct) (i := i) (th := th') rfl ht with ht | ht
  · exact hag1 t ht
  · exact hag2 t ht

theorem promise_sim {ca ct : Cfg} (h : CfgLe ca ct) (i : Nat) (a : Address) (v : Val) (w : Ts) :
    CfgLe (promise ca i a v w) (promise ct i a v w) := by
  unfold promise
  rcases hb : ct.ths[i]? with _ | tt
  · rw [ths_none h.ths hb]; exact h
  obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.ths hb
  simp only [ha]
  have hsz := h.mem.1
  refine ⟨Promises.Sim.MemLe.push h.mem rfl rfl (Nat.le_refl _), h.pairs, thsLe_set h.ths i ?_ htl,
    h.lbase, h.boxFence, ?_, h.cap, h.trace⟩
  · exact ⟨hta.term, hta.env, hta.σs, hta.stack, hta.vs, by simp [hta.promises, hsz],
      hta.nalloc, hta.undefs, hta.permit⟩
  · intro t ht
    rcases allP_set (c := ct) (i := i) rfl ht with ht | ht
    · rcases List.mem_append.mp ht with ht | ht
      · exact Agree.ext h.agree h.mem (Promises.Sim.MemExt.push _ _) (Promises.Sim.MemExt.push _ _)
          (fun t ht => mem_allP hb ht) t ht
      · simp only [List.mem_singleton] at ht; subst ht
        refine ⟨by simp [hsz], ?_⟩
        rw [Array.getElem?_push, Array.getElem?_push, hsz]; simp
    · exact Agree.ext h.agree h.mem (Promises.Sim.MemExt.push _ _) (Promises.Sim.MemExt.push _ _)
        (fun t ht => ht) t ht

theorem noPromises_congr {A B : Cfg} (h : ThsLe A.ths B.ths) (i : Nat) :
    noPromises A i = noPromises B i := by
  unfold noPromises
  rcases hb : B.ths[i]? with _ | tt
  · rw [ths_none h hb]
  · obtain ⟨ta, ha, hta⟩ := ths_some h hb; rw [ha]; simp [hta.promises]

/-- An extern call's events read only the argument values (and the results). -/
theorem events_congr (n : ExtName) {wa wt : List Word} (hw : WsLe wa wt) (rs : List Word) :
    n.events wa rs = n.events wt rs := by
  match wa, wt, hw with
  | [], [], _ => rfl
  | [x], [y], hw =>
      have hv : x.val = y.val := hw.1.val
      have hn : wordNum x = wordNum y := by simp only [wordNum, hv]
      cases n <;> (try rcases rs with _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, rs⟩⟩⟩) <;>
        first | rfl | simp only [CoreTerm.ExtName.events, hv, hn]
  | [x1, x2], [y1, y2], hw =>
      have hn1 : wordNum x1 = wordNum y1 := by simp only [wordNum, hw.1.val]
      have hn2 : wordNum x2 = wordNum y2 := by simp only [wordNum, hw.2.1.val]
      cases n <;> (try rcases rs with _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, rs⟩⟩⟩) <;>
        first | rfl | simp only [CoreTerm.ExtName.events, hn1, hn2]
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ =>
      cases n <;> (try rcases rs with _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, rs⟩⟩⟩) <;> rfl

/-- (M1) An extern call's admitted results read only the argument values (and the trace). -/
theorem resultsL_congr (n : ExtName) (i : Nat) {wa wt : List Word} (hw : WsLe wa wt) (tr : List Event) :
    n.resultsL i wa tr = n.resultsL i wt tr := by
  match wa, wt, hw with
  | [], [], _ => rfl
  | [x], [y], hw =>
      have hn : wordNum x = wordNum y := by simp only [wordNum, hw.1.val]
      cases n <;> first | rfl | simp only [CoreTerm.ExtName.resultsL, hn]
  | [x1, x2], [y1, y2], hw =>
      have hn1 : wordNum x1 = wordNum y1 := by simp only [wordNum, hw.1.val]
      cases n <;> first | rfl | simp only [CoreTerm.ExtName.resultsL, hn1]
  | _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => cases n <;> rfl

/-- **`extCfg` simulates, for every call**: the same binding (the results `rs`), and
traces that grow alike (`events_congr`).  Shared by `extSteps_sim` (certificates) and
`TermArchE.Ext_sim` (the `Ext` step, whose `ExtNeedsNoProm` calls `extSteps` excludes). -/
theorem extCfg_sim {ca ct : Cfg} (h : CfgLe ca ct) {i : Nat} {ta tt : TTh} (hb : ct.ths[i]? = some tt)
    (hta : TThLe ta tt) (htl : ta.tidLbl = tt.tidLbl) (x : String) (n : ExtName) (e : Expr)
    {wa wt : List Word} (hw : WsLe wa wt) (rs : List Word) :
    CfgLe (extCfg ca i ta x n e wa rs) (extCfg ct i tt x n e wt rs) ∧
      (ca.trace = ct.trace → (extCfg ca i ta x n e wa rs).trace = (extCfg ct i tt x n e wt rs).trace) := by
  have hagree : ∀ th' : TTh, th'.promises = tt.promises →
      Agree ca.mem ct.mem (allP { ct with ths := ct.ths.set! i th' }) := fun th' hp t ht => by
    rcases allP_set (c := ct) (i := i) (th := th') rfl ht with ht | ht
    · rw [hp] at ht; exact h.agree t (mem_allP hb ht)
    · exact h.agree t ht
  have hn : ca.n = ct.n := by simp only [Cfg.n, h.ths.1, h.cap]
  suffices hs : CfgLe (extCfg ca i ta x n e wa rs) (extCfg ct i tt x n e wt rs) from ⟨hs, fun _ => hs.trace⟩
  cases n
  case current =>
      cases hl : tt.tidLbl with
      | some l =>
          have hla : ta.tidLbl = some l := htl.trans hl
          simp only [extCfg, curCfg, hl, hla]
          exact ⟨h.mem, h.pairs, thsLe_set h.ths i
            ⟨rfl, ⟨rfl, rfl, WsLe.refl _, hta.env⟩, hta.σs, hta.stack, hta.vs, hta.promises, hta.nalloc,
              hta.undefs, hta.permit⟩ rfl, h.lbase, h.boxFence, hagree _ rfl, h.cap, h.trace⟩
      | none =>
          have hla : ta.tidLbl = none := htl.trans hl
          simp only [extCfg, curCfg, hl, hla, h.lbase, hn, hta.nalloc]
          exact ⟨h.mem, h.pairs, thsLe_set h.ths i
            ⟨rfl, ⟨rfl, rfl, WsLe.refl _, hta.env⟩, hta.σs, hta.stack, hta.vs, hta.promises, rfl,
              hta.undefs, hta.permit⟩ rfl, rfl, h.boxFence, hagree _ rfl, h.cap, h.trace⟩
  all_goals
    refine ⟨h.mem, h.pairs, thsLe_set h.ths i
        ⟨rfl, ⟨rfl, rfl, WsLe.refl _, hta.env⟩, hta.σs, hta.stack,
          by dsimp only; first | exact hta.vs | exact parkVs_le h.mem.1 hta.vs hta.permit | exact parkVs_le_if h.mem.1 hta.vs hta.permit _,
          hta.promises, hta.nalloc, hta.undefs,
          by dsimp only; first | exact hta.permit | exact .none | exact permLe_park hta.permit _⟩ htl, h.lbase, h.boxFence, hagree _ rfl, h.cap, ?_⟩
    show ca.trace ++ _ = ct.trace ++ _
    rw [h.trace, events_congr _ hw]

/-- (D4) `thrOfTid` reads only the word's value and the threads' box labels. -/
theorem thrOfTid_congr {ca ct : Cfg} (h : ThsLe ca.ths ct.ths) {x y : Word} (hv : x.val = y.val) :
    TermRun.thrOfTid ca x = TermRun.thrOfTid ct y := by
  have hj : ∀ j : Nat, (ca.ths[j]?.bind TTh.tidLbl) = (ct.ths[j]?.bind TTh.tidLbl) := by
    intro j
    rcases hb : ct.ths[j]? with _ | tt
    · rw [ths_none h hb]
    · obtain ⟨ta, ha, -, htl⟩ := ths_some_tid h hb
      rw [ha]; exact htl
  unfold TermRun.thrOfTid
  rw [hv]
  split
  · rw [h.1]
    congr 1
    funext j
    exact congrArg (fun o => o == _) (hj j)
  · rfl

/-- (D4) Setting one permit is simulated (with a lower view). -/
theorem setPermit_sim {ca ct : Cfg} (h : CfgLe ca ct) (j : Nat) {va vt : Ts} (hv : va ≤ vt) :
    CfgLe (setPermit ca j va) (setPermit ct j vt) := by
  unfold setPermit
  rcases hb : ct.ths[j]? with _ | tt
  · rw [ths_none h.ths hb]; exact h
  · obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.ths hb
    rw [ha]
    refine ⟨h.mem, h.pairs, thsLe_set h.ths j
      ⟨hta.term, hta.env, hta.σs, hta.stack, hta.vs, hta.promises, hta.nalloc, hta.undefs,
        .some (Nat.max_le.2 ⟨Nat.le_trans hta.permit.getD (Nat.le_max_left _ _),
          Nat.le_trans hv (Nat.le_max_right _ _)⟩)⟩ htl,
      h.lbase, h.boxFence, fun t ht => ?_, h.cap, h.trace⟩
    rcases allP_set (c := ct) (i := j) (th := { tt with permit := some (max (tt.permit.getD 0) vt) }) rfl ht
      with ht | ht
    · exact h.agree t (mem_allP hb ht)
    · exact h.agree t ht

/-- (D4) `wake` is simulated (the woken thread is found from the word's value; ARM's release view lower). -/
theorem wake_sim {ca ct : Cfg} (h : CfgLe ca ct) (i : Nat) {va vt : Ts} (hv : va ≤ vt) (n : ExtName)
    {wa wt : List Word} (hw : WsLe wa wt) : CfgLe (wake ca i va n wa) (wake ct i vt n wt) := by
  cases n
  case unpark =>
    rcases wt with _ | ⟨y, _ | ⟨y2, wt⟩⟩
    · rw [wsle_nil hw]; exact h
    · obtain ⟨x, rfl, hx⟩ := wsle_single hw
      have e := thrOfTid_congr h.ths hx.val
      simp only [wake, e]
      split
      · exact setPermit_sim h _ (by split; exact Nat.le_refl _; exact hv)
      · exact h
    · obtain ⟨x, wa', rfl, -, hw'⟩ := wsle_cons hw
      obtain ⟨x2, wa'', rfl, -, -⟩ := wsle_cons hw'
      exact h
  all_goals exact h

/-- The extern move is simulated: the same binding (a `()` or the box word), the trace aside. -/
theorem extSteps_sim {ca ct c' : Cfg} (h : CfgLe ca ct) (i : Nat) (hin : c' ∈ extSteps ct i) :
    ∃ ca' ∈ extSteps ca i, CfgLe ca' c' := by
  obtain ⟨tt, x, n, a, e, rt, ws, rs, hb, hterm, hn, hev, hrs, rfl⟩ := extSteps_elim hin
  obtain ⟨ta, ha, hta, htl⟩ := ths_some_tid h.ths hb
  have hterm' : ta.term = .let_ x (.ext n a) e := hta.term.trans hterm
  have hn' : ¬ ExtNeedsNoProm n ta := by simpa only [ExtNeedsNoProm, htl] using hn
  obtain ⟨wa, hqa, hw⟩ := evalAt_tso hta.env hev
  have hrs' : rs ∈ n.resultsL i wa ca.trace := by rw [resultsL_congr n i hw, h.trace]; exact hrs
  exact ⟨_, extSteps_intro ha hterm' hn' hqa hrs', (extCfg_sim h hb hta htl x n e hw rs).1⟩

theorem Solo_sim (p : Prog) (k : Promises.Knobs) (i : Nat) {ct ct' : Cfg}
    (hs : Solo p k .tso i ct ct') :
    ∀ {ca}, CfgLe ca ct → ∃ ca', Solo p k .arm i ca ca' ∧ CfgLe ca' ct' := by
  induction hs with
  | refl c => intro ca h; exact ⟨ca, .refl _, h⟩
  | thread hin _ ih =>
      intro ca h
      obtain ⟨ca1, h1, hl⟩ := threadSteps_sim p k h i hin
      obtain ⟨ca2, h2, hl2⟩ := ih hl
      exact ⟨ca2, .thread h1 h2, hl2⟩
  | prom a v w hw _ ih =>
      intro ca h
      obtain ⟨ca2, h2, hl2⟩ := ih (promise_sim h i a v w)
      exact ⟨ca2, .prom a v w (by rw [h.mem.1]; exact hw) h2, hl2⟩
  | ext hin _ ih =>
      intro ca h
      obtain ⟨ca1, h1, hl⟩ := extSteps_sim h i hin
      obtain ⟨ca2, h2, hl2⟩ := ih hl
      exact ⟨ca2, .ext h1 h2, hl2⟩

theorem Certified_sim {p : Prog} {k : Promises.Knobs} {i : Nat} {ca ct : Cfg} (h : CfgLe ca ct)
    (hc : Certified p k .tso ct i) : Certified p k .arm ca i := by
  obtain ⟨c', hs, hn⟩ := hc
  obtain ⟨ca', hs', hl⟩ := Solo_sim p k i hs h
  exact ⟨ca', hs', by rw [noPromises_congr hl.ths]; exact hn⟩

theorem Step_sim {p : Prog} {k : Promises.Knobs} {ca ct ct' : Cfg} (h : CfgLe ca ct)
    (hs : Step p k .tso ct ct') : ∃ ca', Step p k .arm ca ca' ∧ CfgLe ca' ct' := by
  cases hs with
  | thread i hin hc =>
      obtain ⟨ca', h1, hl⟩ := threadSteps_sim p k h i hin
      exact ⟨ca', .thread i h1 (Certified_sim hl hc), hl⟩
  | prom i a v w hi hw hc =>
      have hl := promise_sim h i a v w
      exact ⟨_, .prom i a v w (by rw [h.ths.1]; exact hi) (by rw [h.mem.1]; exact hw)
        (Certified_sim hl hc), hl⟩

/-- Reachability by machine steps. -/
inductive Reach (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop
  | refl (c) : Reach p k arch c c
  | step {c c' c''} : Reach p k arch c c' → Step p k arch c' c'' → Reach p k arch c c''

theorem isDone_congr {ta tt : TTh} (h : TThLe ta tt) : isDone ta = isDone tt := by
  have hs := h.stack
  unfold isDone; rw [h.term]
  generalize tt.term = e
  generalize ta.stack = sa at hs
  generalize tt.stack = st at hs
  cases sa <;> cases st <;> simp only [StackLe] at hs <;> cases e <;> rfl

theorem final_congr {ca ct : Cfg} (h : CfgLe ca ct) : ca.final = ct.final := by
  have el : ∀ j (ha : j < ca.ths.size) (hb : j < ct.ths.size),
      (isDone ca.ths[j] && ca.ths[j].promises.isEmpty) =
        (isDone ct.ths[j] && ct.ths[j].promises.isEmpty) := by
    intro j ha hb
    have hl := (h.ths.2 j _ _ (Array.getElem?_eq_getElem ha) (Array.getElem?_eq_getElem hb)).1
    rw [isDone_congr hl, hl.promises]
  have hs : ca.ths.size = ct.ths.size := h.ths.1
  unfold Cfg.final
  rw [Bool.eq_iff_iff]
  simp only [Array.all_eq, decide_eq_true_eq]
  constructor
  · intro H j hj; rw [← el j (hs ▸ hj) hj]; exact H j _
  · intro H j hj; rw [el j hj (hs ▸ hj)]; exact H j _

/-- **Headline.**  Every configuration reachable under TSO is matched by one
reachable under ARM with the same terms, frames, values, promises and
counters, and views no higher.  (`hwf`: the initial outstanding promises are
in memory; it holds trivially when there are none.) -/
theorem tso_reach_subset_arm (p : Prog) (k : Promises.Knobs) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : Reach p k .tso c0 c) :
    ∃ c', Reach p k .arm c0 c' ∧ CfgLe c' c := by
  induction h with
  | refl => exact ⟨_, .refl _, CfgLe.refl _ hwf⟩
  | step _ hs ih =>
      obtain ⟨ca, hr, hl⟩ := ih
      obtain ⟨ca', hs', hl'⟩ := Step_sim hl hs
      exact ⟨ca', .step hr hs', hl'⟩

/-- In particular, TSO final configurations are ARM final configurations up to views. -/
theorem tso_final_subset_arm (p : Prog) (k : Promises.Knobs) {c0 c : Cfg}
    (hwf : ∀ t ∈ allP c0, t < c0.mem.size) (h : Reach p k .tso c0 c) (hf : c.final = true) :
    ∃ c', Reach p k .arm c0 c' ∧ CfgLe c' c ∧ c'.final = true := by
  obtain ⟨c', hr, hl⟩ := tso_reach_subset_arm p k hwf h
  exact ⟨c', hr, hl, by rw [final_congr hl]; exact hf⟩

end TermArch

#print axioms TermArch.tso_reach_subset_arm
#print axioms TermArch.tso_final_subset_arm
#print axioms TermArch.ths_some_tid
#print axioms TermArch.extSteps_sim
#print axioms TermArch.events_congr
#print axioms TermArch.extCfg_sim
