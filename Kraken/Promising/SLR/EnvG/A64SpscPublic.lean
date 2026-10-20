/-
**Part 7: the AArch64 SPSC ring, end to
end** (`Examples/LockFree/AArch64/spsc_queue.kl` under `Arch.armv8`, in the
shape of `X64SpscPublic.x64_spsc_envG`, on the cumulative take route).

**`a64_spsc_envG`**: at every reachable final configuration the consumer
(thread `1`) has `W10 = 1`, `W11 = 2`, `W12 = 3`.

- **Postcondition** `SpscPost P`: the thread holds all of `tail` (`T`) (the
  producer's end), or the consumer has received `1, 2, 3` (`ConsDone`).
- **Both threads on the cumulative take route**:
  `ThreadRuleRXGS.ofSafelyEnvGTU` from the `vcgen` proofs
  `spscProdA_envGTU`, `spscConsA_envGTU` (`EnvG/A64SpscVCGen.lean`), with
  `hB_P`, `hB_C`; starts by `invGTU_init` (`PR 1`, `CE 1` at `σInit`:
  `PR_init`, `CE_init`); `NPSafeP.of_ruleRXGS`. No fault: `prodRule_noFault`,
  `consRule_noFault` (`noFaultRule_ofSafelyEnvGTU_struct`).
- **Final argument** `spsc_final`: the two threads cannot both hold all of
  `T` (`Erase.q_add_le_one`), and the consumer's `hB` gives `ConsDone`
  under the clean flag.
- **Assembly**: `final_of_relPureSafelyS` with the purity specifications
  `spscPureSpec` (`EnvG/A64SpscRelPure.lean`: the slots' release predicates
  are `emp`), the initial resources and ghost `spscRes`, `spscGhost` and
  their erasure `erase_spscInit`.
-/
import Kraken.Promising.SLR.EnvG.A64SpscRelPure
import Kraken.Promising.SLR.EnvG.TakeFinal

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

set_option linter.unusedSimpArgs false

/-! ## The postcondition and the final argument -/

/-- The consumer (thread `1`) has received `1, 2, 3` (on the low 32 bits). -/
def ConsDone (c : Config isa) : Prop :=
  ∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X10.toBitVec = 1 ∧
    BitVec.setWidth 32 t.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 t.st.st.1.regs.X12.toBitVec = 3

/-- **The shared postcondition**: all of `tail` (the producer), or
`ConsDone` (the consumer). -/
def SpscPost (P : SP) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  1 ≤ (r.wr P.T).q ∨ ConsDone c

/-- **The final argument**: from erasure at a final configuration of two
threads whose final resources satisfy `SpscPost`. -/
theorem spsc_final {P : SP} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hB : ∀ tid, c.Done tid → SpscPost P c (rF tid) g) : ConsDone c := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  rcases hB 1 (Config.final_done hf h1) with hq1 | hd
  · rcases hB 0 (Config.final_done hf h0) with hq0 | hd
    · have := E.q_add_le_one h0 h1 (by decide) P.T
      exfalso
      grind
    · exact hd
  · exact hd

/-! ## The producer -/

section Producer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProdA)]

omit [Executable.ValidLayout (layout spscProdA)] in
theorem spscProdA_rmwLive : (layout spscProdA).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem spscProdA_phase1 : Phase1Tree Arch.armv8 (layout spscProdA) :=
  phase1Tree_of_dirs (by
    dirs_phase1 spscProdA
    -- `B.EQ`: the branch is inside `toEv`, which the tactic's `split` misses
    all_goals (by_cases hz : s.status.z = true <;> simp [hz, DetAccess, SingleAccessS, toEv]))

omit [Executable.ValidLayout (layout spscProdA)] in
theorem spscProdA_noFault : DirsNoFault (layout spscProdA) := by dirs_no_fault' spscProdA

/-- The producer's postcondition: the end of its text and all of `T` (the
counter of `spscProdA_envGTU` projected away). -/
abbrev postP (P : SP) : MachineState × EStateA → Prop :=
  postOf spscProdA fun _ σ => ∃ _ : Nat, (σ.r.wr P.T).q = 1

omit [Executable.ValidLayout (layout spscProdA)] in
/-- **`hB` for the producer**: with no promise its resource is the env's,
which holds all of `T`. -/
theorem hB_P (P : SP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postP P (t.st.st, σ) → t.prom = [] → EnvRel tid (prodPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hq⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inl (by rw [hq]; decide)

/-- **The AArch64 SPSC producer's rule** (cumulative take route). -/
def prodRule (P : SP) (hL : SpscLocs P) (tid : Nat) : ThreadRuleRXGS G₀ Arch.armv8 (SpscPost P) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTU (e := layout spscProdA) (post := postP P) (prodPlan_valid hL) spscProdA_rmwLive
    spscProdA_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_P P tid)

/-- **The AArch64 SPSC producer's no-fault rule**, unconditional in the
thread's promises. -/
theorem prodRule_noFault (P : SP) (hL : SpscLocs P) (tid : Nat) : NoFaultRuleS (prodRule P hL tid) :=
  noFaultRule_ofSafelyEnvGTU_struct _ _ _ _ _ _ spscProdA_noFault

end Producer

/-! ## The consumer -/

section Consumer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsA)]

omit [Executable.ValidLayout (layout spscConsA)] in
theorem spscConsA_rmwLive : (layout spscConsA).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem spscConsA_phase1 : Phase1Tree Arch.armv8 (layout spscConsA) :=
  phase1Tree_of_dirs (by
    dirs_phase1 spscConsA
    -- `B.EQ`: the branch is inside `toEv`, which the tactic's `split` misses
    all_goals (by_cases hz : s.status.z = true <;> simp [hz, DetAccess, SingleAccessS, toEv]))

omit [Executable.ValidLayout (layout spscConsA)] in
theorem spscConsA_noFault : DirsNoFault (layout spscConsA) := by dirs_no_fault' spscConsA

/-- The consumer's postcondition: the end of its text and, under the clean
flag, `1, 2, 3` (the counter of `spscConsA_envGTU` projected away). -/
abbrev postC : MachineState × EStateA → Prop :=
  postOf spscConsA fun s σ => ∃ _ : Nat, σ.cl → s.regs.X10.toBitVec.setWidth 32 = 1 ∧
    s.regs.X11.toBitVec.setWidth 32 = 2 ∧ s.regs.X12.toBitVec.setWidth 32 = 3

omit [Executable.ValidLayout (layout spscConsA)] in
/-- **`hB` for the consumer** (thread `1`): `ConsDone` under the clean flag. -/
theorem hB_C (P : SP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postC (t.st.st, σ) → t.prom = [] → EnvRel 1 (consPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ hpost - hrel hcl
  obtain ⟨-, -, hx⟩ := hpost.resolve_right id
  obtain ⟨h10, h11, h12⟩ := hx (hrel.cl hcl)
  exact .inr ⟨t, hrel.ht, h10, h11, h12⟩

/-- **The AArch64 SPSC consumer's rule** (cumulative take route, thread `1`). -/
def consRule (P : SP) (hL : SpscLocs P) : ThreadRuleRXGS G₀ Arch.armv8 (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTU (e := layout spscConsA) (post := postC) (consPlan_valid hL) spscConsA_rmwLive
    spscConsA_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_C P)

/-- **The AArch64 SPSC consumer's no-fault rule**, unconditional in the
thread's promises. -/
theorem consRule_noFault (P : SP) (hL : SpscLocs P) : NoFaultRuleS (consRule P hL) :=
  noFaultRule_ofSafelyEnvGTU_struct _ _ _ _ _ _ spscConsA_noFault

end Consumer

/-! ## The start -/

section Start

variable {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **`PR 1` at the start** (thread `0`). -/
theorem PR_init {P : SP} (hL : SpscLocs P)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    PR P 1 (σInit (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 0)
      (spscGhost P)) := by
  have hHT := hL.h_t
  have hB0 := hL.b0_t
  have hB1 := hL.b1_t
  have hup : ∀ (Q : BitVec 64 → Prop), Q 0 → UpTo (Config.init [sP, sC] initMem).mem P.H 0 Q :=
    fun Q hQ t ht u hr => by
      obtain rfl := Nat.le_zero.mp ht
      simp [Memory.read?, hH0] at hr
      subst hr; exact hQ
  refine ⟨rfl, ⟨?_, ?_⟩, fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, 0, ⟨?_, ?_, ?_, 1, ?_, ?_, OkPred.refl _ _⟩,
    hup _ (by decide), hup _ rfl⟩, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  all_goals first
    | (simp [σInit, spscRes, prodRes, Res.initOf, Perm.init, prodFrac]; done)
    | (simp [σInit, Views.getFwd]; done)
    | (simp [σInit, Memory.read?, hH0]; done)
    | (show 1 < (spscGhost P).acqTab.length; rw [spscGhost_len]; decide)
    | (simp [σInit, spscRes, prodRes, Res.initOf, Perm.init, prodFrac]; grind)

/-- **`CE 1` at the start** (thread `1`). -/
theorem CE_init {P : SP} (hL : SpscLocs P) (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0) :
    CE P 1 (σInit (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 1)
      (spscGhost P)) := by
  have hHT := hL.h_t
  refine ⟨rfl, ?_, fun _ => ⟨?_, ⟨?_, ?_, ?_, 0, ?_, ?_, OkPred.refl _ _⟩, fun t ht u hr => ?_⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  all_goals first
    | (simp [σInit, spscRes, consRes, Res.initOf, Perm.init, consFrac]; done)
    | (simp [σInit, Views.getFwd]; done)
    | (simp [σInit, Memory.read?, hT0]; done)
    | (show 0 < (spscGhost P).acqTab.length; rw [spscGhost_len]; decide)
    | (simp [σInit, spscRes, consRes, Res.initOf, Perm.init, consFrac]; grind)
    | skip
  obtain rfl := Nat.le_zero.mp ht
  simp [σInit, Memory.read?, hT0] at hr
  subst hr; rfl

end Start

/-- **A thread's start state** (`p` at its first instruction, end address
the end of `p`, no declarations, the base registers `X0 = buf`,
`X1 = head`, `X2 = tail` and no private byte at the four shared words). -/
structure StartA [layout : _root_.Layout] (p : Program) (P : SP) (s : isa.State) : Prop where
  exe : s.exe = layout p
  decls : s.decls = {}
  endPc : s.endPc = (layout p).addrOf p.length
  pc : s.st.2 = (layout p).addrOf 0
  frame : FrameP P s.st.1

/-! ## The initial invariants, `NPSafeP` and the theorem -/

section Inv

variable [layout : _root_.Layout] {P : SP} {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **`NPSafeP` for the producer** (thread `0`): `PR 1` at `σInit`. -/
theorem prod_npSafeP [Executable.ValidLayout (layout spscProdA)] (hL : SpscLocs P) (hP : StartA spscProdA P sP)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 0 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 0) (spscGhost P) := by
  letI : CodeEnv := ⟨layout spscProdA⟩
  exact npSafeP_of_safelyEnvGTU (e := layout spscProdA) (post := postP P) (prodPlan_valid hL) spscProdA_rmwLive
    spscProdA_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_P P 0) n m
    (invGTU_init (s := sP) rfl rfl (qa64TU_of_partialTripleEnv (spscProdA_envGTU P hL 0).uncount rfl hP.exe
      hP.decls hP.endPc hP.pc ⟨0, hP.frame, PR_init hL hH0⟩))

/-- **`NPSafeP` for the consumer** (thread `1`): `CE 1` at `σInit`. -/
theorem cons_npSafeP [Executable.ValidLayout (layout spscConsA)] (hL : SpscLocs P) (hC : StartA spscConsA P sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 1 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 1) (spscGhost P) := by
  letI : CodeEnv := ⟨layout spscConsA⟩
  exact npSafeP_of_safelyEnvGTU (e := layout spscConsA) (post := postC) (consPlan_valid hL) spscConsA_rmwLive
    spscConsA_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_C P) n m
    (invGTU_init (s := sC) rfl rfl (qa64TU_of_partialTripleEnv (spscConsA_envGTU P hL 1).uncount rfl hC.exe
      hC.decls hC.endPc hC.pc ⟨0, hC.frame, CE_init hL hT0⟩))

end Inv

/-- **The `NPSafeP` side for the AArch64 SPSC ring**: both threads through
the cumulative take route. -/
theorem a64_spsc_npSafe (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProdA)]
    [Executable.ValidLayout (lC spscConsA)] {P : SP} (hL : SpscLocs P) {sP sC : isa.State}
    {initMem : List (Loc × Val)} (hP : StartA (layout := lP) spscProdA P sP)
    (hC : StartA (layout := lC) spscConsA P sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (SpscPost P) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem P tid) (spscGhost P) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact prod_npSafeP (layout := lP) hL hP hH0 n m
  · exact cons_npSafeP (layout := lC) hL hC hT0 n m
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- The threads' purity specifications: the producer (layout `lP`) at
thread `0`, the consumer (layout `lC`) elsewhere. -/
def spscPureSpec (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProdA)]
    [Executable.ValidLayout (lC spscConsA)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lP) spscProdA fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := lC) spscConsA fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states.** -/
theorem spscPureSpec_init (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProdA)]
    [Executable.ValidLayout (lC spscConsA)] {P : SP} (hL : SpscLocs P) {sP sC : isa.State}
    (hP : StartA (layout := lP) spscProdA P sP) (hC : StartA (layout := lC) spscConsA P sC) :
    ∀ tid s, [sP, sC][tid]? = some s → (spscPureSpec lP lC (spscGhost P).rel tid).Holds s := by
  intro tid s hs
  match tid, hs with
  | 0, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hfr⟩ := hP
    letI : CodeEnv := ⟨lP spscProdA⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lP)
      (spscProdA_relPure (layout := lP) P _ (fun v => by rw [spscGhost_rel, relS_B0 hL]; exact Pred.emp_pure v)
        (fun v => by rw [spscGhost_rel, relS_B1 hL]; exact Pred.emp_pure v)).uncount
      rfl he hds hend hpc ⟨0, hfr⟩
  | 1, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hfr⟩ := hC
    letI : CodeEnv := ⟨lC spscConsA⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lC) (spscConsA_relPure (layout := lC) P _).uncount
      rfl he hds hend hpc ⟨0, hfr⟩
  | _ + 2, hs => cases hs

/-- **The AArch64 SPSC ring under `Arch.armv8`**
(`Examples/LockFree/AArch64/spsc_queue.kl`,
`forall (1:X10=1 /\ 1:X11=2 /\ 1:X12=3)`, on the low 32 bits).

For valid layouts `lP` of `spscProdA` and `lC` of `spscConsA` and addresses
`b` (`buf`; slot `1` is `b ^^^ 8`), `h` (`head`), `t` (`tail`) whose four
words are distinct (`SpscLocs`): if thread `0` runs the producer and thread
`1` the consumer, each at its start with `X0 = b`, `X1 = h`, `X2 = t` and
no private byte at the four shared words (`StartA`), and the initial memory
has `tail` and `head` at `0`, then every configuration `Reachable` under
`Arch.armv8` that is final has the consumer's `W10 = 1`, `W11 = 2`,
`W12 = 3`. Every layout is covered; the slots' initial values are not
needed.

**Deviation (per-thread image)**: each thread runs its own part of the
`.kl`'s `code` block as its executable — `spscProdA` and `spscConsA`, with
`spscProdA ++ spscNop ++ spscConsA` equal to the block
(`A64SpscConcrete.codeMatches`) — rather than the whole block with the
thread's start label; the whole-image form needs the guarded exit link
(`Litmus/KNOWN_GAPS.md`). The frame "no private byte at the shared words"
holds for the `.kl` (its threads have no private data). Only final
configurations are constrained (no fairness), and faults are not covered by
the conclusion (`prodRule_noFault`, `consRule_noFault` are the per-thread
no-fault facts). -/
theorem a64_spsc_envG {fuel : Nat} (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProdA)]
    [Executable.ValidLayout (lC spscConsA)] (b h t : BitVec 64) (hL : SpscLocs ⟨b, h, t⟩)
    {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartA (layout := lP) spscProdA ⟨b, h, t⟩ sP) (hC : StartA (layout := lC) spscConsA ⟨b, h, t⟩ sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := SpscPost ⟨b, h, t⟩) (Φ := ConsDone)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_spscInit hL _ hT0 hH0) pend_spscGhost
    (spscPureSpec lP lC _) (spscPureSpec_init lP lC hL hP hC) (a64_spsc_npSafe lP lC hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG
#print axioms Kraken.Promising.SLR.EnvG.SpscA.prodRule_noFault
#print axioms Kraken.Promising.SLR.EnvG.SpscA.consRule_noFault
