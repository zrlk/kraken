/-
Part 7: **the Michael–Scott queue with two competing
dequeuers `msqueue3.kl`, end to end** (on `EnvGCAdj`): `msqueue3_envG`, the
`.kl`'s property `(1:X10=1 ∧ 2:X10=2) ∨ (1:X10=2 ∧ 2:X10=1)` at every final
configuration reachable under `Arch.armv8`, for all layouts.

- **Shared postcondition** (`MB3`), three pairwise exclusive disjuncts:
  - dequeuer `1` done (`DoneK … 1`), the initial values (`InitV2`), and the
    acquire id `0` of every queue word on the resource;
  - dequeuer `2` done (`DoneK … 2`) and `tokD2` whole;
  - `tokE` whole (the enqueuer).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdj` from msqueue2's
  `enq2_envGCAdj` and from `deqA3_envGCAdj` / `deqB3_envGCAdj`
  (`EnvG/MsQueue3VCGen.lean`), with their no-fault lemmas.
- **Start**: the split `tRes3` (`EnvG/MsQueue3Ghost.lean`, satisfiable by
  `erase_init3`).
- **Assembly**: `final_of_relPureSafelyF` with purity `msqPureSpec3_init`.
  Two threads cannot give the same disjunct (`acq_pair_false`,
  `tokD2_pair_false`, `tokE_pair_false`), so the three threads give all
  three, and `final_values3` (`EnvG/MsQueue3Final.lean`) gives the values.
-/
import Kraken.Promising.SLR.EnvG.MsQueue3RelPure
import Kraken.Promising.SLR.EnvG.MsQueue2Public

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The shared postcondition of `msqueue3.kl`**. -/
def MB3 (P : Params2) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧ DoneK c.mem P 1 th.st.st.1.regs.X10.toBitVec ∧ InitV2 c.mem P ∧
      ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨
    (∃ th, c.threads[2]? = some th ∧ DoneK c.mem P 2 th.st.st.1.regs.X10.toBitVec ∧ 1 ≤ (r.wr (tokD2 P)).q) ∨
    1 ≤ (r.wr P.tokE).q

/-- **The `.kl`'s property**: the two dequeuers read `1` and `2`, one
each. -/
def MsQueue3Final (c : Config isa) : Prop :=
  ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
    ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
      (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1))

section RuleE

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enq2Prog)]

omit [Executable.ValidLayout (layout enq2Prog)] in
theorem hB_E3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postE2 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inr hcom.2.2.1)
  · rw [hp] at hts; cases hts

/-- **The enqueuer's rule** (msqueue2's enqueuer, postcondition `MB3`). -/
noncomputable def enq3Rule (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postE2 P) (planE2_valid P) enq2Prog_rmwLive
    enq2Prog_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_E3 P)

/-- **The enqueuer's rule excludes faults**. -/
theorem enq3Rule_noFault (P : Params2) : NoFaultRuleF (enq3Rule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ enq2Prog_noFault

end RuleE

section RuleDA

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqProg)]

/-- The first dequeuer's postcondition: the end of its text and `Dn3 … 1`. -/
abbrev postDA3 (P : Params2) : MachineState × EStateA → Prop :=
  postOf deqProg fun s σ => ∃ _ : Nat, Dn3 P 1 s.regs.X10.toBitVec σ

omit [Executable.ValidLayout (layout deqProg)] in
theorem hB_DA3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDA3 P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1.1 rfl⟩
  · rw [hp] at hts; cases hts

/-- **The first dequeuer's rule** (thread `1`). -/
noncomputable def deqA3Rule (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postDA3 P) (planD2_valid P) deqProg_rmwLive
    deqProg_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_DA3 P)

/-- **The first dequeuer's rule excludes faults**. -/
theorem deqA3Rule_noFault (P : Params2) : NoFaultRuleF (deqA3Rule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ deqProg_noFault

end RuleDA

section RuleDB

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqBProg)]

/-- The second dequeuer's postcondition: the end of its text and
`Dn3 … 2`. -/
abbrev postDB3 (P : Params2) : MachineState × EStateA → Prop :=
  postOf deqBProg fun s σ => ∃ _ : Nat, Dn3 P 2 s.regs.X10.toBitVec σ

omit [Executable.ValidLayout (layout deqBProg)] in
theorem hB_DB3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDB3 P (t.st.st, σ) → t.prom = [] → EnvRel 2 (planD2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.1.2 rfl⟩)
  · rw [hp] at hts; cases hts

/-- **The second dequeuer's rule** (thread `2`). -/
noncomputable def deqB3Rule (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 2 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postDB3 P) (planD2_valid P) deqBProg_rmwLive
    deqBProg_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_DB3 P)

/-- **The second dequeuer's rule excludes faults**. -/
theorem deqB3Rule_noFault (P : Params2) : NoFaultRuleF (deqB3Rule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ deqBProg_noFault

end RuleDB

/-! ## The start -/

/-- **`Start` of phase 1 at the start** (on `resE3`): half of
`head`/`tail`, every other location but `tokD2` whole. -/
theorem start1_init3 {P : Params2} (hL : QLocs2 P) (c : Config isa) :
    Start P (ph1 P) (σInit c (resE3 c.mem P) (ghost2 P)) := by
  have hq : ∀ x, ((σInit c (resE3 c.mem P) (ghost2 P)).r.wr x).q = fracE3 P x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (resE3 c.mem P) (ghost2 P)).r.wr x).X p ↔
      0 < fracE3 P x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  have hF : ∀ δ : Loc, δ.bytes = 4 → Fresh δ (σInit c (resE3 c.mem P) (ghost2 P)) := by
    intro δ hb
    refine ⟨_, Perm.unit, (Perm.op_unit _).symm, ?_, fun p hp => ?_⟩
    · have hne : ¬(δ = P.head ∨ δ = P.tail) := by rintro (h | h) <;> rw [h] at hb <;> cases hb
      have hne' : δ ≠ tokD2 P := by rintro rfl; cases hb
      rw [hq]; simp [fracE3, hne, hne']
    · rw [((hX _ _).mp hp).2]
  refine ⟨⟨ghost2_gw P, fun a => ?_, ?_, fun f hf => ?_⟩, hF _ rfl, hF _ rfl⟩
  · rw [hq]; unfold fracE3; simp only [tokD2_ne_of_8, ↓reduceIte]; split <;> grind
  · rw [hq]; simp [fracE3, tokE_ne_head, tokE_ne_tail, tokE_tokD2 hL]
  · simp [σInit, Views.getFwd] at hf

/-- **`ComD3 … 1` at the start**. -/
theorem comDa3_init (P : Params2) (c : Config isa) (hi : InitV2 c.mem P) :
    ComD3 P 1 (σInit c (resDa3 c.mem P) (ghost2 P)) := by
  have hq : ∀ x, ((σInit c (resDa3 c.mem P) (ghost2 P)).r.wr x).q = fracDa3 P x := fun _ => rfl
  refine ⟨ghost2_gw P, ?_, ?_, ⟨fun _ x hx => ?_, fun h => absurd h (by decide)⟩, hi, ?_⟩
  · rw [hq]; simp only [fracDa3, true_or, ↓reduceIte]; grind
  · rw [hq]; simp only [fracDa3, or_true, ↓reduceIte]; grind
  · show 1 ≤ (if P.IsW x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx]
  · intro l f hf; simp [σInit, Views.getFwd] at hf

/-- **`ComD3 … 2` at the start**. -/
theorem comDb3_init (P : Params2) (c : Config isa) (hi : InitV2 c.mem P) :
    ComD3 P 2 (σInit c (resDb3 c.mem P) (ghost2 P)) := by
  have hq : ∀ x, ((σInit c (resDb3 c.mem P) (ghost2 P)).r.wr x).q = fracDb3 P x := fun _ => rfl
  have hne : ¬(tokD2 P = P.head ∨ tokD2 P = P.tail) := by
    rintro (h | h) <;> simp [tokD2, Params.head, Params.tail] at h
  refine ⟨ghost2_gw P, ?_, ?_, ⟨fun h => absurd h (by decide), fun _ => ?_⟩, hi, ?_⟩
  · rw [hq]; simp only [fracDb3, true_or, ↓reduceIte]; grind
  · rw [hq]; simp only [fracDb3, or_true, ↓reduceIte]; grind
  · rw [hq]; simp [fracDb3, hne]
  · intro l f hf; simp [σInit, Views.getFwd] at hf

section Start

variable {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}

theorem invE3_init (l0 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)] {P : Params2} (hL : QLocs2 P)
    (hS : StartE2 (layout := l0) P.t P.n1 P.n2 s0) :
    (enq3Rule (layout := l0) P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 0) (ghost2 P) := by
  letI : CodeEnv := ⟨l0 enq2Prog⟩
  exact invGFCAdj_init (tid := 0) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l0)
    (enq2_envGCAdj (layout := l0) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x1, hS.d8, hS.d4, hS.x13, hS.x12, start1_init3 hL _⟩)

theorem invDa3_init (l1 : _root_.Layout) [Executable.ValidLayout (l1 deqProg)] {P : Params2} (hL : QLocs2 P)
    (hS : StartD (layout := l1) P.h P.t s1) (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqA3Rule (layout := l1) P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 1) (ghost2 P) := by
  letI : CodeEnv := ⟨l1 deqProg⟩
  exact invGFCAdj_init (tid := 1) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l1)
    (deqA3_envGCAdj (layout := l1) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, comDa3_init P _ hi⟩)

theorem invDb3_init (l2 : _root_.Layout) [Executable.ValidLayout (l2 deqBProg)] {P : Params2} (hL : QLocs2 P)
    (hS : StartDB (layout := l2) P.h P.t s2) (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqB3Rule (layout := l2) P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 2) (ghost2 P) := by
  letI : CodeEnv := ⟨l2 deqBProg⟩
  exact invGFCAdj_init (tid := 2) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l2)
    (deqB3_envGCAdj (layout := l2) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, comDb3_init P _ hi⟩)

end Start

/-- **The `NPSafeF` side of Theorem 1′ for `msqueue3.kl`**. -/
theorem msqueue3_npSafeF (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deqProg)] [Executable.ValidLayout (l2 deqBProg)] {P : Params2} (hL : QLocs2 P)
    {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)} (h0 : StartE2 (layout := l0) P.t P.n1 P.n2 s0)
    (h1 : StartD (layout := l1) P.h P.t s1) (h2 : StartDB (layout := l2) P.h P.t s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    ∀ tid, tid < [s0, s1, s2].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB3 P) tid k j True
      (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem).mem P tid) (ghost2 P) := by
  intro tid htid k j
  rcases tid with _ | _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invE3_init l0 hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDa3_init l1 hL h1 hi)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDb3_init l2 hL h2 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **Three threads giving three pairwise exclusive disjuncts give all
three**: in particular the first and the second. -/
theorem pigeon3 {A B C : Nat → Prop} (h0 : A 0 ∨ B 0 ∨ C 0) (h1 : A 1 ∨ B 1 ∨ C 1) (h2 : A 2 ∨ B 2 ∨ C 2)
    (hA : ∀ i j, i ≠ j → A i → A j → False) (hB : ∀ i j, i ≠ j → B i → B j → False)
    (hC : ∀ i j, i ≠ j → C i → C j → False) : (∃ i, A i) ∧ ∃ j, B j := by
  rcases h0 with a0 | b0 | c0 <;> rcases h1 with a1 | b1 | c1 <;> rcases h2 with a2 | b2 | c2
  all_goals first
    | exact ⟨⟨_, a0⟩, ⟨_, b1⟩⟩ | exact ⟨⟨_, a0⟩, ⟨_, b2⟩⟩ | exact ⟨⟨_, a1⟩, ⟨_, b0⟩⟩
    | exact ⟨⟨_, a1⟩, ⟨_, b2⟩⟩ | exact ⟨⟨_, a2⟩, ⟨_, b0⟩⟩ | exact ⟨⟨_, a2⟩, ⟨_, b1⟩⟩
    | exact (hA 0 1 (by decide) a0 a1).elim | exact (hA 0 2 (by decide) a0 a2).elim
    | exact (hA 1 2 (by decide) a1 a2).elim | exact (hB 0 1 (by decide) b0 b1).elim
    | exact (hB 0 2 (by decide) b0 b2).elim | exact (hB 1 2 (by decide) b1 b2).elim
    | exact (hC 0 1 (by decide) c0 c1).elim | exact (hC 0 2 (by decide) c0 c2).elim
    | exact (hC 1 2 (by decide) c1 c2).elim

/-- **The final step of `msqueue3_envG`** (and of `msqueue3_envG_whole`,
`EnvG/A64WholeMsQueue3.lean`): from `final_of_relPureSafelyF`'s final
erasure `E'`, ghost growth `hle`, thread count `hsize` and per-thread `B`
(`hB`), the final values. -/
theorem msqueue3_final_of_hB {h t d n1 n2 : BitVec 64} (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {cfg : Config isa}
    (hf : cfg.final = true) {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg)
    (hle : (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).Le g') (hsize : cfg.threads.size = 3)
    (hB : ∀ tid, cfg.Done tid → MB3 ⟨⟨h, t, d, n1⟩, n2⟩ cfg (rF' tid) g') : MsQueue3Final cfg := by
  have hlt : ∀ i, i < 3 → i < cfg.threads.size := fun i hi => by rw [hsize]; simpa using hi
  have hW := (ghost2_gw ⟨⟨h, t, d, n1⟩, n2⟩).mono hle
  have hno := Config.final_not_outstanding hf
  obtain ⟨⟨i, hA⟩, ⟨j, hB'⟩⟩ := pigeon3
    (A := fun i => i < 3 ∧ ∃ th : Thread isa, cfg.threads[1]? = some th ∧
      DoneK cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ 1 th.st.st.1.regs.X10.toBitVec ∧ InitV2 cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ ∧
      ∀ x, Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ x → 1 ≤ (rF' i).acq x 0)
    (B := fun i => i < 3 ∧ ∃ th : Thread isa, cfg.threads[2]? = some th ∧
      DoneK cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ 2 th.st.st.1.regs.X10.toBitVec ∧
      1 ≤ ((rF' i).wr (tokD2 ⟨⟨h, t, d, n1⟩, n2⟩)).q)
    (C := fun i => i < 3 ∧ 1 ≤ ((rF' i).wr (Params.tokE ⟨h, t, d, n1⟩)).q)
    ((hB 0 (Config.final_done hf (hlt 0 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    ((hB 1 (Config.final_done hf (hlt 1 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    ((hB 2 (Config.final_done hf (hlt 2 (by decide)))).imp (⟨by decide, ·⟩)
      (Or.imp (⟨by decide, ·⟩) (⟨by decide, ·⟩)))
    (fun i j hij ⟨hi3, _, _, _, _, ha⟩ ⟨hj3, _, _, _, _, hb⟩ =>
      TreiberCommon.acq_pair_false E' (hlt i hi3) (hlt j hj3) hij (ha _ (.inl rfl)) (hb _ (.inl rfl)))
    (fun i j hij ⟨hi3, _, _, _, ha⟩ ⟨hj3, _, _, _, hb⟩ => tokD2_pair_false E' (hlt i hi3) (hlt j hj3) hij ha hb)
    (fun i j hij ⟨hi3, ha⟩ ⟨hj3, hb⟩ =>
      tokE_pair_false (P := (⟨h, t, d, n1⟩ : Params)) E' (hlt i hi3) (hlt j hj3) hij ha hb)
  obtain ⟨hi3, th1, hth1, hd1, hiv, hacq⟩ := hA
  obtain ⟨-, th2, hth2, hd2, -⟩ := hB'
  exact ⟨th1, th2, hth1, hth2, final_values3 E' hW hL hiv
    (fun x hx => TreiberCommon.total_acq_of_ge E' (hlt i hi3) (hacq x hx)) hno hd1 hd2⟩

/-- **The Michael–Scott queue with two competing dequeuers `msqueue3.kl` for
AArch64 under `Arch.armv8`, on `EnvGCAdj`**: for all layouts `l0`
(enqueuer), `l1` (first dequeuer) and `l2` (second dequeuer), all addresses
`h` of `head`, `t` of `tail` (8 bytes), `d` of the dummy node and `n1`, `n2`
of the enqueued nodes (data `[n]`, 4 bytes; link `[n + 8]`, 8 bytes) with
`h ≠ t`, `h`, `t` distinct from the three links, `d`, `n1`, `n2` pairwise
distinct and `n1`, `n2` non-zero: if
- thread `0` starts the enqueuer (`enq1:` onwards) with `x1 = t`,
  `x12 = n1`, `x13 = n2` (`StartE2`), thread `1` the first dequeuer
  (`deq1a:` onwards, `StartD`) and thread `2` the second (`deq2a:` onwards,
  `StartDB`), both with `x0 = h`, `x1 = t`, all three with **an empty
  private memory** (`dmem` maps no 8-byte and no 4-byte word), and
- the initial memory has `head = tail = d` and the three links `0` (64 bits,
  `InitV2`),

then every final configuration reachable under `Arch.armv8` has
`(1:X10 = 1 ∧ 2:X10 = 2) ∨ (1:X10 = 2 ∧ 2:X10 = 1)` (the `.kl`'s `forall`).

Only the addresses' `Loc`s are distinguished: the model's mixed-size gap as
in `treiber_pp_envG`. -/
theorem msqueue3_envG {fuel : Nat} (l0 l1 l2 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deqProg)] [Executable.ValidLayout (l2 deqBProg)] (h t d n1 n2 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0)
    (hn2 : n2 ≠ 0) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartE2 (layout := l0) t n1 n2 s0) (h1 : StartD (layout := l1) h t s1)
    (h2 : StartDB (layout := l2) h t s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1 th2, cfg.threads[1]? = some th1 ∧ cfg.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB3 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue3Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init3 hL _) (ghost2_pend _) (msqPureSpec3 l0 l1 l2 _)
    (msqPureSpec3_init l0 l1 l2 (fun v => ?_) (fun v => ?_) h0 h1 h2) (msqueue3_npSafeF l0 l1 l2 hL h0 h1 h2 hi)
    hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
    rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v
  exact msqueue3_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue
