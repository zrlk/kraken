/-
Part 8: **the one-node Michael–Scott queue
`msqueue1.kl`, end to end** (on the adjacency environment `EnvGCAdj`):
`msqueue1_envG`, the `.kl`'s property `1:X10=1` at every final
configuration reachable under `Arch.armv8`, for all layouts.

- **Parameters** (`Params`): `head = ⟨h, 8⟩`, `tail = ⟨t, 8⟩`, the dummy
  node `d` and the enqueued node `n1` (data `[n]`, 4 bytes; link `[n + 8]`,
  8 bytes); `QLocs` from the raw address inequalities.
- **Shared postcondition** (`MB`): either the dequeuer (thread `1`) is done
  (`DoneD` at the configuration's memory, `EnvG/MsQueueFinal.lean`), the
  initial values hold, and the resource holds the acquire id `0` of every
  queue word; or the resource holds the enqueuer's identity token `tokE`
  whole. The enqueuer gives the second (`hB_E`, from `ComE`), the dequeuer
  the first (`hB_D`, from `Dn`: its anchor's facts lift to the final memory
  by `DoneD.mono`, and `prom = []` makes the resource the thread's).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdj` from `enq_envGCAdj` /
  `deq_envGCAdj` (`EnvG/MsQueueVCGen.lean`); per-thread no-fault by
  `noFaultRuleF_ofSafelyEnvGFCAdj_struct` (`enqRule_noFault`,
  `deqRule_noFault`).
- **Start**: `invGFCAdj_init` at `σInit` with `tRes`/`ghost₀`
  (`EnvG/MsQueueGhost.lean`): the enqueuer holds half of `head`/`tail` and
  every other location whole (`E0`, `e0_init`), the dequeuer the other
  halves and the acquire id `0` of every queue word (`ComD`, `comD_init`);
  `erase_init` shows this split satisfiable.
- **Assembly**: `final_of_relPureSafelyF` (`EnvG/A64RmwFailFinal.lean`),
  purity `msqPureSpec_init` (`EnvG/MsQueueRelPure.lean`). At the final
  configuration both threads give `MB` on their resources; both holding
  `tokE` whole contradicts validity (`tokE_pair_false`), so one gives the
  dequeuer's facts and `final_value` gives `X10 = 1`.
-/
import Kraken.Promising.SLR.EnvG.MsQueueVCGen
import Kraken.Promising.SLR.EnvG.MsQueueRelPure
import Kraken.Promising.SLR.EnvG.A64RmwFailFinal
import Kraken.Promising.SLR.EnvG.AdjVCGenA64

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.EnvG.Treiber (initVal_eq)

/-! ## The shared postcondition -/

/-- **The shared postcondition**: the dequeuer done with the acquire ids on
the resource, or the enqueuer's token on the resource. -/
def MB (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧ DoneD c.mem P th.st.st.1.regs.X10.toBitVec ∧ InitV c.mem P ∧
    ∀ x, P.IsQ x → 1 ≤ r.acq x 0) ∨ 1 ≤ (r.wr P.tokE).q

/-- **The `.kl`'s property**: the dequeuer read `1`. -/
def MsQueue1Final (c : Config isa) : Prop :=
  ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1

/-! ## The rules -/

section RuleE

variable [layout : _root_.Layout] [Executable.ValidLayout (layout enqProg)]

/-- The enqueuer's postcondition: the end of its text and `ComE`. -/
abbrev postE (P : Params) : MachineState × EStateA → Prop :=
  postOf enqProg fun _ σ => ∃ _ : Nat, ComE P σ

omit [Executable.ValidLayout (layout enqProg)] in
/-- **`hB` for the enqueuer**: `ComE` holds `tokE` whole. -/
theorem hB_E (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postE P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MB P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

/-- **The enqueuer's rule**. -/
noncomputable def enqRule (P : Params) : ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postE P) (planE_valid P) enqProg_rmwLive
    enqProg_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_E P)

/-- **The enqueuer's rule excludes faults** (unconditional in promises). -/
theorem enqRule_noFault (P : Params) : NoFaultRuleF (enqRule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ enqProg_noFault

end RuleE

section RuleD

variable [layout : _root_.Layout] [Executable.ValidLayout (layout deqProg)]

/-- The dequeuer's postcondition: the end of its text and `Dn`. -/
abbrev postD (P : Params) : MachineState × EStateA → Prop :=
  postOf deqProg fun s σ => ∃ _ : Nat, Dn P s.regs.X10.toBitVec σ

omit [Executable.ValidLayout (layout deqProg)] in
/-- **`hB` for the dequeuer**: `Dn` at the anchor gives `DoneD` and the
initial values at the configuration (the anchor's memory is a prefix); with
no promise the resource is the thread's. -/
theorem hB_D (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postD P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD P) σ c t r g cl → cl → MB P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The dequeuer's rule**. -/
noncomputable def deqRule (P : Params) : ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postD P) (planD_valid P) deqProg_rmwLive
    deqProg_phase1F postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_D P)

/-- **The dequeuer's rule excludes faults** (unconditional in promises). -/
theorem deqRule_noFault (P : Params) : NoFaultRuleF (deqRule P) :=
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ deqProg_noFault

end RuleD

/-! ## The start -/

theorem tokE_ne_head (P : Params) : P.tokE ≠ P.head := Ne.symm (head_tokE P)
theorem tokE_ne_tail (P : Params) : P.tokE ≠ P.tail := Ne.symm (tail_tokE P)

/-- **`E0` at the start**: half of `head`/`tail`, every other location
whole, every write at timestamp `0`. -/
theorem e0_init (P : Params) (c : Config isa) : E0 P (σInit c (resE c.mem P) (ghost₀ P)) := by
  have hq : ∀ x, ((σInit c (resE c.mem P) (ghost₀ P)).r.wr x).q = fracE P x := fun _ => rfl
  have hX : ∀ x p, ((σInit c (resE c.mem P) (ghost₀ P)).r.wr x).X p ↔
      0 < fracE P x ∧ p = (c.mem.initVal x, 0) := fun _ _ => Iff.rfl
  refine ⟨⟨ghost₀_gw P, fun a => ?_, ?_⟩, ?_, fun p hp => ?_⟩
  · rw [hq]; unfold fracE; split <;> grind
  · rw [hq]; simp [fracE, tokE_ne_head, tokE_ne_tail]
  · rw [hq]; simp [fracE, Ne.symm (head_dat P), Ne.symm (tail_dat P)]
  · rw [((hX _ _).mp hp).2]; exact Nat.zero_le _

/-- **`ComD` at the start**: the other halves of `head`/`tail`, the acquire
id `0` of every queue word, the initial values (`InitV`), no forwarding
item. -/
theorem comD_init (P : Params) (c : Config isa) (hi : InitV c.mem P) :
    ComD P (σInit c (resD c.mem P) (ghost₀ P)) := by
  have hq : ∀ x, ((σInit c (resD c.mem P) (ghost₀ P)).r.wr x).q = fracD P x := fun _ => rfl
  refine ⟨ghost₀_gw P, ?_, ?_, fun x hx => ?_, hi, ?_⟩
  · rw [hq]; simp [fracD]; grind
  · rw [hq]; simp [fracD]; grind
  · show 1 ≤ (if P.IsQ x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx]
  · intro l f hf; simp [σInit, Views.getFwd] at hf

section Start

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **The enqueuer's initial invariant**. -/
theorem invE_init (l0 : _root_.Layout) [Executable.ValidLayout (l0 enqProg)] {P : Params} (hL : QLocs P)
    (hS : StartE (layout := l0) P.t P.n1 s0) :
    (enqRule (layout := l0) P).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem P 0) (ghost₀ P) := by
  letI : CodeEnv := ⟨l0 enqProg⟩
  exact invGFCAdj_init (tid := 0) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l0)
    (enq_envGCAdj (layout := l0) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x1, hS.d8, hS.d4, hS.x12, e0_init P _⟩)

/-- **The dequeuer's initial invariant**. -/
theorem invD_init (l1 : _root_.Layout) [Executable.ValidLayout (l1 deqProg)] {P : Params} (hL : QLocs P)
    (hS : StartD (layout := l1) P.h P.t s1) (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    (deqRule (layout := l1) P).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem P 1) (ghost₀ P) := by
  letI : CodeEnv := ⟨l1 deqProg⟩
  exact invGFCAdj_init (tid := 1) rfl rfl (qa64CAdj_of_partialTripleEnv (layout := l1)
    (deq_envGCAdj (layout := l1) P hL).uncount rfl hS.exe hS.decls hS.endPc hS.pc
    ⟨0, hS.x0, hS.x1, hS.d8, hS.d4, comD_init P _ hi⟩)

end Start

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for `msqueue1.kl`**: both threads at
the initial configuration, through their rules. -/
theorem msqueue1_npSafeF (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enqProg)]
    [Executable.ValidLayout (l1 deqProg)] {P : Params} (hL : QLocs P) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) P.t P.n1 s0)
    (h1 : StartD (layout := l1) P.h P.t s1) (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB P) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P tid) (ghost₀ P) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invE_init l0 hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invD_init l1 hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- Two thread resources each holding `tokE` whole contradict erasure. -/
theorem tokE_pair_false {P : Params} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa}
    (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (h1 : 1 ≤ ((rF i).wr P.tokE).q) (h2 : 1 ≤ ((rF j).wr P.tokE).q) : False :=
  wr_pair_false E hi hj hij h1 h2

/-- **The final step of `msqueue1_envG`** (and of `msqueue1_envG_whole`,
`EnvG/A64WholeMsQueue1.lean`): from `final_of_relPureSafelyF`'s final
erasure `E'`, ghost growth `hle`, thread count `hsize` and per-thread `B`
(`hB`), the final values. -/
theorem msqueue1_final_of_hB {h t d n1 : BitVec 64} (hL : QLocs ⟨h, t, d, n1⟩) {cfg : Config isa}
    (hf : cfg.final = true) {rF' : Nat → Res} {g' : Ghost} (E' : Erase rF' g' (fun _ => False) cfg)
    (hle : (ghost₀ ⟨h, t, d, n1⟩).Le g') (hsize : cfg.threads.size = 2)
    (hB : ∀ tid, cfg.Done tid → MB ⟨h, t, d, n1⟩ cfg (rF' tid) g') : MsQueue1Final cfg := by
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw ⟨h, t, d, n1⟩).mono hle
  have hno := Config.final_not_outstanding hf
  have fin : ∀ i, i < cfg.threads.size → (∃ th, cfg.threads[1]? = some th ∧
      DoneD cfg.mem ⟨h, t, d, n1⟩ th.st.st.1.regs.X10.toBitVec ∧ InitV cfg.mem ⟨h, t, d, n1⟩ ∧
      ∀ x, Params.IsQ ⟨h, t, d, n1⟩ x → 1 ≤ (rF' i).acq x 0) → MsQueue1Final cfg := by
    rintro i hi ⟨th, hth, hd, hiv, hacq⟩
    exact ⟨th, hth, final_value E' hW hL hiv hno (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
  rcases hB 0 (Config.final_done hf hi0) with hd0 | hq0
  · exact fin 0 hi0 hd0
  rcases hB 1 (Config.final_done hf hi1) with hd1 | hq1
  · exact fin 1 hi1 hd1
  exact (tokE_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim

/-- **The one-node Michael–Scott queue `msqueue1.kl` for AArch64 under
`Arch.armv8`, on `EnvGCAdj`**: for all layouts `l0` (enqueuer) and `l1`
(dequeuer), all addresses `h` of `head`, `t` of `tail` (8 bytes), `d` of the
dummy node and `n1` of the enqueued node (data `[n]`, 4 bytes; link
`[n + 8]`, 8 bytes) with `h ≠ t`, `h ≠ d + 8`, `h ≠ n1 + 8`, `t ≠ d + 8`,
`t ≠ n1 + 8`, `d ≠ n1`: if
- thread `0` starts the enqueuer (`enq1:` onwards) with `x1 = t`,
  `x12 = n1`, and thread `1` the dequeuer (`deq1:` onwards) with `x0 = h`,
  `x1 = t` (`StartE`, `StartD`), both with **an empty private memory**
  (`dmem` maps no 8-byte and no 4-byte word: every load reads the shared
  memory), and
- the initial memory has `head = tail = d` and both links `0` (64 bits,
  `InitV`),

then every final configuration reachable under `Arch.armv8` has
`1:X10 = 1` (the `.kl`'s `forall`).

Only the addresses' `Loc`s are distinguished: the model's mixed-size gap as
in `treiber_pp_envG`. -/
theorem msqueue1_envG {fuel : Nat} (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 enqProg)]
    [Executable.ValidLayout (l1 deqProg)] (h t d n1 : BitVec 64) (hht : h ≠ t) (hhd : h ≠ d + 8)
    (hhn : h ≠ n1 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (hdn : d ≠ n1) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartE (layout := l0) t n1 s0) (h1 : StartD (layout := l1) h t s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem ⟨h, t, d, n1⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 := by
  have hL : QLocs ⟨h, t, d, n1⟩ := ⟨hht, hhd, hhn, htd, htn, hdn⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB ⟨h, t, d, n1⟩) (Φ := MsQueue1Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (msqPureSpec l0 l1 _)
    (msqPureSpec_init l0 l1 (fun v => ?_) h0 h1) (msqueue1_npSafeF l0 l1 hL h0 h1 hi) hc hf
    fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ ⟨h, t, d, n1⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost₀_rel_ne (not_isQ_dat _)]; exact Pred.emp_pure v
  exact msqueue1_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue
