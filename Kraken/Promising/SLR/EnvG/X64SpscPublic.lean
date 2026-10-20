/-
**Part 7: the x64 SPSC queue, end to end**
(`Examples/LockFree/X64/spsc_queue.kl` under `Arch.tso`, in the shape of
`X64TakeMpPublic.x64_takeMp_public`).

**`x64_spsc_envG`**: at every reachable final configuration the consumer
(thread `1`) has `r12d = 1`, `r13d = 2`, `r14d = 3`.

- **Postcondition** `SpscPost P`: the thread holds all of `tail` (`T`)
  (the producer's end), or the consumer has received `1, 2, 3`
  (`ConsDone`).
- **Both threads on the take route**: `ThreadRuleRXGS.ofSafelyEnvGTX` from
  the `vcgen` proofs `spscProducerX_envGT`, `spscConsumerX_envGT`
  (`EnvG/X64SpscVCGen.lean`), with `hB_P`, `hB_C`; starts by `invGTX_init`
  (`PR 1`, `CS` at `σInitX`: `PR_init`, `CS_init`); `NPSafeP.of_ruleRXGS`.
  No fault: `prodRule_noFault`, `consRule_noFault`
  (`noFaultRule_ofSafelyEnvGTX_struct`).
- **Final argument** `spsc_final`: the two threads cannot both hold all of
  `T` (`Erase.q_add_le_one`), and the consumer's `hB` gives `ConsDone`
  under the clean flag, so `ConsDone` holds.
- **Assembly**: `final_of_relPureSafelyQX_tsoS` with the all-release
  specifications `spscNoNTSpecX` (`EnvG/X64SpscRelPure.lean`, both at the
  whole address space `sAll`, which needs a private memory that maps no
  byte: `StartPX.dmem`, `StartCX.dmem`), the initial resources and ghost
  `spscRes`, `spscGhost` and their erasure `erase_spscInit`.
-/
import Kraken.Promising.SLR.EnvG.X64SpscVCGen
import Kraken.Promising.SLR.EnvG.X64SpscRelPure
import Kraken.Promising.SLR.EnvG.TakeX64Final

namespace Kraken.Promising.X64.EnvG.SpscX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

/-! ## The postcondition and the final argument -/

/-- The consumer (thread `1`) has received `1, 2, 3`. -/
def ConsDone (c : Config isa) : Prop :=
  ∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .r12) = 1 ∧
    BitVec.setWidth 32 (t.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .r14) = 3

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

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscProducerX)]

theorem spscProducerX_phase1 : Phase1TreeX Arch.tso (layout spscProducerX) := by
  refine phase1TreeX_of_dirs ?_
  dirs_phase1X spscProducerX
  -- `je pfull`, `jne produce`: the branch is inside `toEv`, which the tactic's `split` misses
  all_goals first
    | (by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]; done)
    -- `jmp`: `RelRegOrMem.interp` is not a `kstep` definition
    | simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]

omit [Executable.ValidLayout (layout spscProducerX)] in
theorem spscProducerX_noFault : DirsNoFault (layout spscProducerX) := by
  dirs_no_fault spscProducerX
  all_goals first
    | (by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]; done)
    | simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The producer's postcondition: the end of its text and all of `T` (the
counter of `spscProducerX_envGT` projected away). -/
abbrev postPX (P : SP) : MachineState × EStateX → Prop :=
  postOfX spscProducerX fun _ σ => ∃ _ : Nat, (σ.r.wr P.T).q = 1

omit [Executable.ValidLayout (layout spscProducerX)] in
/-- **`hB` for the producer**: with no promise its resource is the env's,
which holds all of `T`. -/
theorem hB_P (P : SP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPX P (t.st.st, σ) → t.prom = [] → EnvRel tid (prodPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, -, hq⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inl (by rw [hq]; decide)

/-- **The x64 SPSC producer's rule** (take route, `Arch.tso`). -/
def prodRule (P : SP) (hL : SpscLocs P) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTX (S := spscS P) (post := postPX P) (prodPlan_valid hL) (spscS_le16 P)
    spscProducerX_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_P P tid)

/-- **The x64 SPSC producer's no-fault rule**, unconditional in the thread's
promises. -/
theorem prodRule_noFault (P : SP) (hL : SpscLocs P) (tid : Nat) :
    NoFaultRuleSX (prodRule (layout := layout) P hL tid) :=
  noFaultRule_ofSafelyEnvGTX_struct _ _ _ _ _ _ spscProducerX_noFault

end Producer

/-! ## The consumer -/

section Consumer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscConsumerX)]

theorem spscConsumerX_phase1 : Phase1TreeX Arch.tso (layout spscConsumerX) := by
  refine phase1TreeX_of_dirs ?_
  dirs_phase1X spscConsumerX
  -- `je cemptyK`, as in `spscProducerX_phase1`
  all_goals first
    | (by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]; done)
    -- `jmp`: `RelRegOrMem.interp` is not a `kstep` definition
    | simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]

omit [Executable.ValidLayout (layout spscConsumerX)] in
theorem spscConsumerX_noFault : DirsNoFault (layout spscConsumerX) := by
  dirs_no_fault spscConsumerX
  all_goals first
    | (by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]; done)
    | simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The consumer's postcondition: the end of its text and, under the clean
flag, `Got 3` (the counter of `spscConsumerX_envGT` projected away). -/
abbrev postCX : MachineState × EStateX → Prop :=
  postOfX spscConsumerX fun s σ => ∃ _ : Nat, σ.cl → Got 3 s

omit [Executable.ValidLayout (layout spscConsumerX)] in
/-- **`hB` for the consumer** (thread `1`): `ConsDone` under the clean flag. -/
theorem hB_C (P : SP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postCX (t.st.st, σ) → t.prom = [] → EnvRel 1 (consPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ hpost - hrel hcl
  obtain ⟨-, -, hx⟩ := hpost.resolve_right id
  obtain ⟨h12, h13, h14⟩ := hx (hrel.cl hcl)
  exact .inr ⟨t, hrel.ht, h12 (by decide), h13 (by decide), h14 (by decide)⟩

/-- **The x64 SPSC consumer's rule** (take route, `Arch.tso`, thread `1`). -/
def consRule (P : SP) (hL : SpscLocs P) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTX (S := spscS P) (post := postCX) (consPlan_valid hL) (spscS_le16 P)
    spscConsumerX_phase1 postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_C P)

/-- **The x64 SPSC consumer's no-fault rule**, unconditional in the thread's
promises. -/
theorem consRule_noFault (P : SP) (hL : SpscLocs P) : NoFaultRuleSX (consRule (layout := layout) P hL) :=
  noFaultRule_ofSafelyEnvGTX_struct _ _ _ _ _ _ spscConsumerX_noFault

end Consumer

/-! ## The start -/

section Start

variable {sP sC : isa.State} {initMem : List (Loc × Val)}

theorem read?_init_zero {c : Config isa} {l : Loc} (h : c.mem.initVal l = 0) : c.mem.read? l 0 = some 0#128 := by
  simp [Memory.read?, h]

/-- **`PR 1` at the start** (thread `0`). -/
theorem PR_init {P : SP} (hL : SpscLocs P) (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    PR P 1 (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 0)
      (spscGhost P)) := by
  have hHT := hL.h_t
  have hB0 := hL.b0_t
  have hB1 := hL.b1_t
  refine ⟨rfl, ⟨?_, 0, ?_, ?_, ?_⟩, fun _ => ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, 0, ⟨?_, ?_, ?_, 1, ?_, ?_, OkPred.refl _ _⟩⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  all_goals first
    | (simp [σInitX, spscRes, prodRes, Res.initOf, Perm.init, prodFrac, hT0, eT]; done)
    | (simp [σInitX, Views.getFwd]; done)
    | (simp [σInitX, Memory.read?, hH0]; done)
    | (show 1 < (spscGhost P).acqTab.length; rw [spscGhost_len]; decide)
    | (simp [σInitX, spscRes, prodRes, Res.initOf, Perm.init, prodFrac, eT]; exact ⟨by grind, hT0.symm⟩)

/-- **`CS` at the start** (thread `1`). -/
theorem CS_init {P : SP} (hL : SpscLocs P) (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    CS P (σInitX (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 1)
      (spscGhost P)) := by
  have hHT := hL.h_t
  refine ⟨rfl, ⟨?_, 0, ?_, ?_, ?_⟩, ?_, 0, ⟨?_, ?_, ?_, 0, ?_, ?_, OkPred.refl _ _⟩⟩
  all_goals first
    | (simp [σInitX, spscRes, consRes, Res.initOf, Perm.init, consFrac, hH0]; done)
    | (simp [σInitX, Views.getFwd]; done)
    | (simp [σInitX, Memory.read?, hT0]; done)
    | (show 0 < (spscGhost P).acqTab.length; rw [spscGhost_len]; decide)
    | (simp [σInitX, spscRes, consRes, Res.initOf, Perm.init, consFrac]; exact ⟨by grind, hH0.symm⟩)

end Start

/-! ## The initial invariants, `NPSafeP` and the theorem -/

section Inv

variable [layout : _root_.Layout] {b h t : BitVec 64} {sP sC : isa.State} {initMem : List (Loc × Val)}

/-- **The producer's initial invariant** (thread `0`): `PR 1` at `σInitX`. -/
theorem invPX_init [Executable.ValidLayout (layout spscProducerX)] (hL : SpscLocs ⟨b, h, t⟩)
    (hP : StartPX b h t sP) (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 4⟩ = 0) :
    (prodRule ⟨b, h, t⟩ hL 0).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem ⟨b, h, t⟩ 0) (spscGhost ⟨b, h, t⟩) := by
  letI : CodeEnv := ⟨layout spscProducerX⟩
  exact invGTX_init (s := sP) rfl rfl (qx64T_of_partialTripleEnv (spscProducerX_envGT _ hL 0).uncount rfl hP.exe
    hP.decls hP.endPc hP.pc (split_of_empty hP.dmem)
    ⟨0, ⟨hP.rbx, hP.rdi, hP.rsi, dFrame_of_empty hP.dmem⟩, PR_init hL hT0 hH0⟩)

/-- **The consumer's initial invariant** (thread `1`): `CS` at `σInitX`. -/
theorem invCX_init [Executable.ValidLayout (layout spscConsumerX)] (hL : SpscLocs ⟨b, h, t⟩)
    (hC : StartCX b h t sC) (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 4⟩ = 0) :
    (consRule ⟨b, h, t⟩ hL).Inv True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem ⟨b, h, t⟩ 1) (spscGhost ⟨b, h, t⟩) := by
  letI : CodeEnv := ⟨layout spscConsumerX⟩
  exact invGTX_init (s := sC) rfl rfl (qx64T_of_partialTripleEnv (spscConsumerX_envGT _ hL 1).uncount rfl hC.exe
    hC.decls hC.endPc hC.pc (split_of_empty hC.dmem)
    ⟨0, ⟨hC.rbx, hC.rdi, hC.rsi, dFrame_of_empty hC.dmem⟩, CS_init hL hT0 hH0⟩)

end Inv

/-- **The `NPSafeP` side for the x64 SPSC queue**: both threads through the
take route. -/
theorem x64_spsc_npSafe (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProducerX)]
    [Executable.ValidLayout (lC spscConsumerX)] {b h t : BitVec 64} (hL : SpscLocs ⟨b, h, t⟩)
    {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPX (layout := lP) b h t sP) (hC : StartCX (layout := lC) b h t sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 4⟩ = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.tso (SpscPost ⟨b, h, t⟩) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem ⟨b, h, t⟩ tid) (spscGhost ⟨b, h, t⟩) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafeP.of_ruleRXGS (prodRule (layout := lP) _ hL 0) n m _ _ _ _ (invPX_init (layout := lP) hL hP hT0 hH0)
  · exact NPSafeP.of_ruleRXGS (consRule (layout := lC) _ hL) n m _ _ _ _ (invCX_init (layout := lC) hL hC hT0 hH0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The x64 SPSC queue under `Arch.tso`** (`Examples/LockFree/X64/spsc_queue.kl`,
`forall (1:r12=1 /\ 1:r13=2 /\ 1:r14=3)`, on the low 32 bits).

For valid layouts `lP` of `spscProducerX` and `lC` of `spscConsumerX` and
addresses `b` (`buf0`; `buf1` is `b + 256`), `h` (`head`), `t` (`tail`)
whose four words are pairwise distinct (`SpscLocs`): if thread `0` is the
producer and thread `1` the consumer, each at its start with `rbx = b`,
`rdi = t`, `rsi = h` and **a private memory that maps no byte**
(`StartPX`, `StartCX`), and the initial memory has `tail` and `head` at `0`,
then every configuration `Reachable` under `Arch.tso` that is final has the
consumer's `r12d = 1`, `r13d = 2`, `r14d = 3`.

Deviations from the `.kl`: `(tail)` and `(head)` are addressed through
`rdi`, `rsi` (`EnvG/X64SpscProg.lean`, the spinlock2 precedent); the empty
private memory is needed by the all-release side (`spscNoNTSpecX`, at the
whole address space `sAll`), a frame condition the `.kl` meets (its threads
have no private data). The initial values of the slots are not needed.
Only final configurations are constrained (no fairness), and faults are not
covered by the conclusion (`prodRule_noFault`, `consRule_noFault` are the
per-thread no-fault facts). -/
theorem x64_spsc_envG {fuel : Nat} (lP lC : _root_.Layout) [Executable.ValidLayout (lP spscProducerX)]
    [Executable.ValidLayout (lC spscConsumerX)] (b h t : BitVec 64) (hL : SpscLocs ⟨b, h, t⟩)
    {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPX (layout := lP) b h t sP) (hC : StartCX (layout := lC) b h t sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 4⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r12) = 1 ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r13) = 2 ∧ BitVec.setWidth 32 (th.st.st.1.regs.get64 .r14) = 3 :=
  final_of_relPureSafelyQX_tsoS fuel (B := SpscPost ⟨b, h, t⟩) (Φ := ConsDone)
    (erase_spscInit hL _ hT0 hH0) pend_spscGhost (spscNoNTSpecX lP lC) (spscNoNTSpecX_init lP lC hP hC)
    (x64_spsc_npSafe lP lC hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

end Kraken.Promising.X64.EnvG.SpscX

#print axioms Kraken.Promising.X64.EnvG.SpscX.x64_spsc_envG
#print axioms Kraken.Promising.X64.EnvG.SpscX.prodRule_noFault
#print axioms Kraken.Promising.X64.EnvG.SpscX.consRule_noFault
