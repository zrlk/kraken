/-
Msqueue2 part 7: **the two-node Michael–Scott queue
`msqueue2.kl`, end to end** (on `EnvGCAdj`): `msqueue2_envG`, the `.kl`'s
property `1:X10=1 ∧ 1:X11=2` at every final configuration reachable under
`Arch.armv8`, for all layouts. Modelled on `EnvG/MsQueuePublic.lean`.

- **Shared postcondition** (`MB2`): the dequeuer (thread `1`) done
  (`DoneD2`), the initial values (`InitV2`) and the acquire id `0` of every
  queue word on the resource; or the enqueuer's token `tokE` whole.
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdj` from `enq2_envGCAdj` /
  `deq2_envGCAdj` (`EnvG/MsQueue2VCGen.lean`), with their no-fault lemmas.
- **Start**: msqueue1's split (`resE`/`resD2` in `tRes2`, satisfiable by
  `erase_init2`): the enqueuer's `Start` of phase 1 (`start1_init`: both data
  words whole at timestamp `0`), the dequeuer's `ComD2` (`comD2_init`).
- **Assembly**: `final_of_relPureSafelyF` with purity `msqPureSpec2_init`;
  `tokE_pair_false` excludes both threads giving the token, and
  `final_values2` (`EnvG/MsQueue2Final.lean`) gives the values.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2RelPure
import Kraken.Promising.SLR.EnvG.MsQueuePublic

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG

/-- **The shared postcondition of `msqueue2.kl`**. -/
def MB2 (P : Params2) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧
    DoneD2 c.mem P th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧ InitV2 c.mem P ∧
    ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨ 1 ≤ (r.wr P.tokE).q

/-- **The `.kl`'s property**: the dequeuer read `1` then `2`. -/
def MsQueue2Final (c : Config isa) : Prop :=
  ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧ th1.st.st.1.regs.X11.toBitVec = 2

section RuleE

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enq2Prog)]

/-- The enqueuer's postcondition: the end of its text and `ComE2`. -/
abbrev postE2 (P : Params2) : MachineState × EStateA → Prop :=
  postOf enq2Prog fun _ σ => ∃ _ : Nat, ComE2 P σ

omit [Executable.ValidLayout (layout enq2Prog)] in
theorem hB_E2 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postE2 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE2 P) σ c t r g cl → cl → MB2 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2.1
  · rw [hp] at hts; cases hts

/-- **The enqueuer's rule**. -/
noncomputable def enq2Rule (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postE2 P) (planE2_valid P) enq2Prog_rmwLive
    enq2Prog_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_E2 P)

/-- **The enqueuer's rule excludes faults**. -/
theorem enq2Rule_noFault (P : Params2) : NoFaultRuleF (enq2Rule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ enq2Prog_noFault

end RuleE

section RuleD

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deq2Prog)]

/-- The dequeuer's postcondition: the end of its text and `Dn2`. -/
abbrev postD2 (P : Params2) : MachineState × EStateA → Prop :=
  postOf deq2Prog fun s σ => ∃ _ : Nat, Dn2 P s.regs.X10.toBitVec s.regs.X11.toBitVec σ

omit [Executable.ValidLayout (layout deq2Prog)] in
theorem hB_D2 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postD2 P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MB2 P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The dequeuer's rule**. -/
noncomputable def deq2Rule (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postD2 P) (planD2_valid P) deq2Prog_rmwLive
    deq2Prog_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_D2 P)

/-- **The dequeuer's rule excludes faults**. -/
theorem deq2Rule_noFault (P : Params2) : NoFaultRuleF (deq2Rule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ deq2Prog_noFault

end RuleD

/-! ## The start -/

/-- **`Start` of phase 1 at the start**: half of `head`/`tail`, every other
location whole (both data words `Fresh`: written at `0`), no forwarding
item. -/
theorem start1_init (P : Params2) (c : Config isa) : Start P (ph1 P) (σInit c (resE c.mem P.toParams) (ghost2 P)) := by
  have hq : ∀ x, ((σInit c (resE c.mem P.toParams) (ghost2 P)).r.wr x).q = fracE P.toParams x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (resE c.mem P.toParams) (ghost2 P)).r.wr x).X p ↔
      0 < fracE P.toParams x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  have hF : ∀ δ : Loc, δ.bytes = 4 → Fresh δ (σInit c (resE c.mem P.toParams) (ghost2 P)) := by
    intro δ hb
    refine ⟨_, Perm.unit, (Perm.op_unit _).symm, ?_, fun p hp => ?_⟩
    · have hne : ¬(δ = P.head ∨ δ = P.tail) := by rintro (h | h) <;> rw [h] at hb <;> cases hb
      rw [hq]; simp [fracE, hne]
    · rw [((hX _ _).mp hp).2]
  refine ⟨⟨ghost2_gw P, fun a => ?_, ?_, fun f hf => ?_⟩, hF _ rfl, hF _ rfl⟩
  · rw [hq]; unfold fracE; split <;> grind
  · rw [hq]; simp [fracE, tokE_ne_head, tokE_ne_tail]
  · simp [σInit, Views.getFwd] at hf

/-- **`ComD2` at the start**. -/
theorem comD2_init (P : Params2) (c : Config isa) (hi : InitV2 c.mem P) :
    ComD2 P (σInit c (resD2 c.mem P) (ghost2 P)) := by
  have hq : ∀ x, ((σInit c (resD2 c.mem P) (ghost2 P)).r.wr x).q = fracD P.toParams x := fun _ => rfl
  refine ⟨ghost2_gw P, ?_, ?_, fun x hx => ?_, hi, ?_⟩
  · rw [hq]; simp [fracD]; grind
  · rw [hq]; simp [fracD]; grind
  · show 1 ≤ (if P.IsW x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx]
  · intro l f hf; simp [σInit, Views.getFwd] at hf

section Start

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

theorem invE2_init (l0 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)] {P : Params2} (hL : QLocs2 P)
    (hS : StartE2 (layout := l0) P.t P.n1 P.n2 s0) :
    (enq2Rule (layout := l0) P).Inv True (Config.init [s0, s1] initMem)
      (tRes2 (Config.init [s0, s1] initMem).mem P 0) (ghost2 P) := by
  letI : CodeEnv := ⟨l0 enq2Prog⟩
  exact invGFCAdj_init (tid := 0) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l0)
    (enq2_envGCAdj (layout := l0) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x1, hS.d8, hS.d4, hS.x13, hS.x12, start1_init P _⟩)

theorem invD2_init (l1 : _root_.Layout) [Executable.ValidLayout (l1 deq2Prog)] {P : Params2} (hL : QLocs2 P)
    (hS : StartD2 (layout := l1) P.h P.t s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem P) :
    (deq2Rule (layout := l1) P).Inv True (Config.init [s0, s1] initMem)
      (tRes2 (Config.init [s0, s1] initMem).mem P 1) (ghost2 P) := by
  letI : CodeEnv := ⟨l1 deq2Prog⟩
  exact invGFCAdj_init (tid := 1) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l1)
    (deq2_envGCAdj (layout := l1) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, comD2_init P _ hi, trivial⟩)

end Start

/-- **The `NPSafeF` side of Theorem 1′ for `msqueue2.kl`**. -/
theorem msqueue2_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deq2Prog)] {P : Params2} (hL : QLocs2 P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartE2 (layout := l0) P.t P.n1 P.n2 s0)
    (h1 : StartD2 (layout := l1) P.h P.t s1) (hi : InitV2 (Config.init [s0, s1] initMem).mem P) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB2 P) tid k j True
      (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem).mem P tid) (ghost2 P) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invE2_init l0 hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invD2_init l1 hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The final step of `msqueue2_envG`** (and of `msqueue2_envG_whole`,
`EnvG/A64WholeMsQueue2.lean`): from `final_of_relPureSafelyF`'s final
erasure `E'`, ghost growth `hle`, thread count `hsize` and per-thread `B`
(`hB`), the final values. -/
theorem msqueue2_final_of_hB {h t d n1 n2 : BitVec 64} (hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩) {cfg : Config isa}
    (hf : cfg.final = true) {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg)
    (hle : (ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).Le g') (hsize : cfg.threads.size = 2)
    (hB : ∀ tid, cfg.Done tid → MB2 ⟨⟨h, t, d, n1⟩, n2⟩ cfg (rF' tid) g') : MsQueue2Final cfg := by
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost2_gw ⟨⟨h, t, d, n1⟩, n2⟩).mono hle
  have hno := Config.final_not_outstanding hf
  have fin : ∀ i, i < cfg.threads.size → (∃ th, cfg.threads[1]? = some th ∧
      DoneD2 cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ th.st.st.1.regs.X10.toBitVec th.st.st.1.regs.X11.toBitVec ∧
      InitV2 cfg.mem ⟨⟨h, t, d, n1⟩, n2⟩ ∧ ∀ x, Params2.IsW ⟨⟨h, t, d, n1⟩, n2⟩ x → 1 ≤ (rF' i).acq x 0) →
      MsQueue2Final cfg := by
    rintro i hi ⟨th, hth, hd, hiv, hacq⟩
    exact ⟨th, hth, final_values2 E' hW hL hiv (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hno hd⟩
  rcases hB 0 (Config.final_done hf hi0) with hd0 | hq0
  · exact fin 0 hi0 hd0
  rcases hB 1 (Config.final_done hf hi1) with hd1 | hq1
  · exact fin 1 hi1 hd1
  exact (tokE_pair_false (P := (⟨h, t, d, n1⟩ : Params)) E' hi0 hi1 (by decide) hq0 hq1).elim

/-- **The two-node Michael–Scott queue `msqueue2.kl` for AArch64 under
`Arch.armv8`, on `EnvGCAdj`**: for all layouts `l0` (enqueuer) and `l1`
(dequeuer), all addresses `h` of `head`, `t` of `tail` (8 bytes), `d` of the
dummy node and `n1`, `n2` of the enqueued nodes (data `[n]`, 4 bytes; link
`[n + 8]`, 8 bytes) with `h ≠ t`, `h`, `t` distinct from the three links,
`d`, `n1`, `n2` pairwise distinct and `n1`, `n2` non-zero: if
- thread `0` starts the enqueuer (`enq1:` onwards) with `x1 = t`,
  `x12 = n1`, `x13 = n2`, and thread `1` the dequeuer (`deq1a:` onwards)
  with `x0 = h`, `x1 = t` (`StartE2`, `StartD2`), both with **an empty
  private memory** (`dmem` maps no 8-byte and no 4-byte word: every load
  reads the shared memory), and
- the initial memory has `head = tail = d` and the three links `0` (64 bits,
  `InitV2`),

then every final configuration reachable under `Arch.armv8` has
`1:X10 = 1 ∧ 1:X11 = 2` (the `.kl`'s `forall`).

Only the addresses' `Loc`s are distinguished: the model's mixed-size gap as
in `treiber_pp_envG`. -/
theorem msqueue2_envG {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enq2Prog)]
    [Executable.ValidLayout (l1 deq2Prog)] (h t d n1 n2 : BitVec 64) (hht : h ≠ t) (hhd : h ≠ d + 8)
    (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8)
    (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartE2 (layout := l0) t n1 n2 s0) (h1 : StartD2 (layout := l1) h t s1)
    (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
      th1.st.st.1.regs.X11.toBitVec = 2 := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB2 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue2Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) (ghost2_pend _) (msqPureSpec2 l0 l1 _)
    (msqPureSpec2_init l0 l1 (fun v => ?_) (fun v => ?_) h0 h1) (msqueue2_npSafeF l0 l1 hL h0 h1 hi) hc hf
    fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
    rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v
  exact msqueue2_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue
