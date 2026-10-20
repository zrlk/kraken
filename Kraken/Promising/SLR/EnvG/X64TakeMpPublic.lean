/-
**Part 7: x64 message passing with a writing
reader, end to end** (`EnvG/TakeMpPublic.lean` for x64 under `Arch.tso`, in
the shape of `X64MpPublic.x64_mp_public`).

The writer is x64 MP's `mpWriterX` (thread `0`), the reader is `takeReaderX`
(thread `1`, `EnvG/X64TakeMp.lean`): it spins on the flag, then stores `43`
to the data and loads it back into `ebx`. **`x64_takeMp_public`**: at every
reachable final configuration the reader's `ebx` is `43` and the data word's
final value is `43`.

- **Postcondition** `TPostX P rd`: the writer keeps the token `W` (as
  `MpPost`), the reader holds all of `Dt` with maximal write `(43, tw)`
  (`Own43`) and has `ebx = 43`.
- **Writer**: `takeRuleWX`, `ThreadRuleRX.ofSafelyEnvGX` from x64 MP's
  `vcgen` proof (`mpWriterX_envG`) with `hB_TWX`; its invariant at the start
  is x64 MP's (`invWX_init`, the rule's invariant does not mention `B`). Into
  the take route by `NPSafe.toP` (`K2₀.toScope`).
- **Reader**: `npSafeP_of_safelyEnvGTX` (`EnvG/TakeX64Link.lean`) from
  `takeReaderX_envGT`, with `hB_TX` and the start `invTX_init` (`invGTX_init`,
  `K1` at `σInitX`). No fault: `takeRuleRX_noFault`
  (`noFaultRule_ofSafelyEnvGTX_struct`); the writer's is
  `mpRuleW_envGX_noFault` (its proof does not depend on `hB`).
- **Final argument** `takeMp_finalX`: both threads cannot hold `W`, so the
  reader's disjunct holds; it holds all of `Dt`, so its maximal write is the
  total's (`SLR.total_max_of_thread`), hence the final value.
- **Assembly**: `final_of_relPureSafelyQX_tsoS` (`EnvG/TakeX64Final.lean`):
  one all-release specification per thread (`mpWriterX_noNT`,
  `takeReaderX_noNT`) gives `NTFree Arch.tso` and purity; x64 MP's initial
  resources/ghost and erasure (`mpRes`, `mpGhost`, `erase_mpInit`).
-/
import Kraken.Promising.SLR.EnvG.X64MpPublic
import Kraken.Promising.SLR.EnvG.X64TakeMpVCGen
import Kraken.Promising.SLR.EnvG.X64TakeMpRelPure
import Kraken.Promising.SLR.EnvG.TakeX64Final

namespace Kraken.Promising.X64.EnvG.TakeMp

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp Kraken.Promising.X64.EnvG.MpSmoke
open Kraken.Promising.X64.EnvG.MpLink Kraken.Promising.X64.EnvG.MpRelPure Kraken.Promising.X64.EnvG.MpPublic

/-! ## The postcondition and the final argument -/

/-- **The shared postcondition**: the writer keeps the token `W`; the reader
(thread `rd`) holds all of `Dt` with maximal write `(43, tw)` and has
`ebx = 43`. -/
def TPostX (P : Params) (rd : Nat) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    ((∃ t, c.threads[rd]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧ Own43 P r)

/-- **The final argument**: from erasure at a final configuration of two
threads whose final resources satisfy `TPostX P 1`. -/
theorem takeMp_finalX {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hB : ∀ tid, c.Done tid → TPostX P 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal P.Dt = 43#128 := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hR : ∃ j, j < c.threads.size ∧
      (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧ Own43 P (rF j) := by
    rcases hB 0 (Config.final_done hf h0) with hw0 | hr0
    · rcases hB 1 (Config.final_done hf h1) with hw1 | hr1
      · have := E.q_add_le_one h0 h1 (by decide) P.W
        exfalso
        grind
      · exact ⟨1, h1, hr1⟩
    · exact ⟨0, h0, hr0⟩
  obtain ⟨j, hj, hx, hq, tw, hX, hmax⟩ := hR
  obtain ⟨hpos, hXT, hmaxT⟩ := SLR.total_max_of_thread E hj hq hX hmax
  exact ⟨hx, E.finalVal_of_max hf hpos hXT hmaxT⟩

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- The x64 writing reader at its start (the label `spin`), as `StartRX`. -/
structure StartTX (f d : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout takeReaderX
  decls : s.decls = {}
  endPc : s.endPc = (layout takeReaderX).addrOf takeReaderX.length
  pc : s.st.2 = (layout takeReaderX).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = f
  rsi : s.st.1.regs.get64 .rsi = d
  split : Split [(f, 4), (d, 4)] s.st.1.dmem

end Start

/-! ## The writer -/

section Writer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpWriterX)]

omit [Executable.ValidLayout (layout mpWriterX)] in
/-- **`hB` for the writer**: it keeps the token `W` (`hB_W`). -/
theorem hB_TWX (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postW P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → TPostX P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The x64 writer's rule** for `TPostX` (`mpRuleW_envGX` with `hB_TWX`). -/
def takeRuleWX (P : Params) (hL : MpLocs P) (tid rd : Nat) :
    ThreadRuleRX (I := isa) Arch.tso (TPostX P rd) tid :=
  ThreadRuleRX.ofSafelyEnvGX (S := mpS P) (post := postW P) (mpPlan_valid hL) (mpS_le16 P) mpWriterX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 0) (hB_TWX P tid rd)

end Writer

/-! ## The reader -/

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReaderX)]

theorem takeReaderX_phase1 : Phase1TreeX Arch.tso (layout takeReaderX) := by
  refine phase1TreeX_of_dirs ?_
  dirs_phase1X takeReaderX
  -- `je spin`: the branch is inside `toEv`, which the tactic's `split` misses
  all_goals by_cases h : s.status.zf = true <;>
    simp [h, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS]

omit [Executable.ValidLayout (layout takeReaderX)] in
theorem takeReaderX_noFault : DirsNoFault (layout takeReaderX) := by
  dirs_no_fault takeReaderX
  -- `je spin`, as in `takeReaderX_phase1`
  all_goals by_cases h : s.status.zf = true <;> simp [h, Kraken.Promising.X64.toEv, EvTree.NoFault]

/-- The reader's postcondition: the end of its text, `Own43`, and `ebx = 43`
under the clean flag (the counter of `takeReaderX_envGT` projected away). -/
abbrev postTX (P : Params) : MachineState × EStateX → Prop :=
  postOfX takeReaderX fun s σ => ∃ _ : Nat, Own43 P σ.r ∧ (σ.cl → (s.regs.get64 .rbx).setWidth 32 = 43)

omit [Executable.ValidLayout (layout takeReaderX)] in
/-- **`hB` for the reader**: with no promise its resource is the env's, so
`Own43`; `ebx = 43` under the clean flag. -/
theorem hB_TX (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postTX P (t.st.st, σ) → t.prom = [] → EnvRel tid rdPlanX σ c t r g cl → cl → TPostX P tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, hown, hx⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨t, hrel.ht, hx (hrel.cl hcl)⟩, hown⟩

/-- **The x64 reader's rule on the take route** (`Arch.tso`, frame
`K2Scope AllocIds`). -/
def takeRuleRX (P : Params) (tid : Nat) : ThreadRuleRXGS (I := isa) G₀ Arch.tso (TPostX P tid) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTX (S := mpS P) (post := postTX P) rdPlanX_valid (mpS_le16 P) takeReaderX_phase1
    postOfX_end (not_instrStepEnv_of_end_labels _ 1) (hB_TX P tid)

/-- **The x64 reader's no-fault rule** (`NoFaultRuleSX` of its take-route
rule), unconditional in the thread's promises. -/
theorem takeRuleRX_noFault (P : Params) (tid : Nat) : NoFaultRuleSX (takeRuleRX (layout := layout) P tid) :=
  noFaultRule_ofSafelyEnvGTX_struct _ _ _ _ _ _ takeReaderX_noFault

end Reader

/-! ## `NPSafeP` and the theorem -/

section Start

variable [layout : _root_.Layout] {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The reader's initial invariant** (thread `1`): `K1` at `σInitX`. -/
theorem invTX_init [Executable.ValidLayout (layout takeReaderX)] (hfd : f ≠ d) (hR : StartTX f d sR) :
    (takeRuleRX (ghostParams f d) 1).Inv True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout takeReaderX⟩
  have hL := ghostParams_mpLocs hfd
  refine invGTX_init (s := sR) rfl rfl (qx64T_of_partialTripleEnv (takeReaderX_envGT _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc hR.split ⟨0, ⟨hR.rdi, hR.rsi, split_df hR.split, split_dd hR.split⟩,
      mpGhost_rel_Fl, fun v => ?_, ?_, 0, Nat.zero_lt_one, ?_, OkPred.flag⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp [σInitX, Views.getFwd]
  · simp [σInitX, mpRes, readerRes]

end Start

/-- **The `NPSafeP` side for x64 MP with a writing reader**: the writer
through its `ThreadRuleRX` (`NPSafe.toP`), the reader through the take
route. -/
theorem x64_takeMp_npSafe (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR takeReaderX)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartWX (layout := lW) f d sW) (hR : StartTX (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafeP (model isa) Arch.tso (TPostX (ghostParams f d) 1) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid) (mpGhost (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (takeRuleWX (layout := lW) _ (ghostParams_mpLocs hfd) 0 1) n m _ _ _ _
        (invWX_init (layout := lW) hfd hW))
  · exact NPSafeP.of_ruleRXGS (takeRuleRX (layout := lR) _ 1) n m _ _ _ _ (invTX_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- The threads' all-release specifications: the writer (layout `lW`) at
thread `0`, the writing reader (layout `lR`) elsewhere. -/
def takeNoNTSpecX (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR takeReaderX)] (f d : BitVec 64) :
    Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 => RelPureSpecQX.ofProgram (layout := lW) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) mpWriterX
      fun _ _ => True
  | _ + 1 => RelPureSpecQX.ofProgram (layout := lR) [(f, 4), (d, 4)] (mpS_le16 ⟨f, d, ⟨0, 5⟩⟩) takeReaderX
      fun _ _ => ∃ _ : Nat, True

/-- **The all-release specifications hold at the start states.** -/
theorem takeNoNTSpecX_init (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR takeReaderX)] {f d : BitVec 64} {sW sR : isa.State}
    (hW : StartWX (layout := lW) f d sW) (hR : StartTX (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (takeNoNTSpecX lW lR f d tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hW
    letI : CodeEnv := ⟨lW mpWriterX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lW) (mpWriterX_noNT (layout := lW) f d).partial rfl
      he hds hend hpc hsp ⟨hx0, hx1⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hsp⟩ := hR
    letI : CodeEnv := ⟨lR takeReaderX⟩
    exact RelPureSpecQX.holds_of_partialTripleEnv (layout := lR) (takeReaderX_noNT (layout := lR) f d).uncount
      rfl he hds hend hpc hsp ⟨0, hx0, hx1, split_df hsp, split_dd hsp⟩
  | _ + 2, _, hs => by cases hs

/-- **Message passing with a writing reader for x64 under `Arch.tso`**
(the shape of `x64_mp_public`).

For valid layouts `lW` of `mpWriterX` and `lR` of `takeReaderX` and
addresses `f ≠ d`: if thread `0` is the writer and thread `1` the writing
reader, each at its start with `rdi = f`, `rsi = d` and neither word in its
private memory (`StartWX`, `StartTX`), and the initial memory has the flag
word `⟨f, 4⟩` at `0`, then every configuration `Reachable` under `Arch.tso`
that is final has the reader's `ebx` at `43` and the data word `⟨d, 4⟩` at
`43`. The reader takes all of the data at its flag load (the take route,
`npSafeP_of_safelyEnvGTX`) and then writes it.

As for `x64_mp_public`: only final configurations are constrained (no
fairness), `f ≠ d` does not exclude overlapping words, and faults are not
covered by the conclusion (`mpRuleW_envGX_noFault`, `takeRuleRX_noFault` are
the per-thread no-fault facts). -/
theorem x64_takeMp_public {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriterX)]
    [Executable.ValidLayout (lR takeReaderX)] (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartWX (layout := lW) f d sW) (hR : StartTX (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyQX_tsoS fuel (B := TPostX (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 (t.st.st.1.regs.get64 .rbx) = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (erase_mpInit _ _ hF0) pend_mpGhost (takeNoNTSpecX lW lR f d) (takeNoNTSpecX_init lW lR hW hR)
    (x64_takeMp_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' _ hsize hB => takeMp_finalX E' hf hsize hB

end Kraken.Promising.X64.EnvG.TakeMp

#print axioms Kraken.Promising.X64.EnvG.TakeMp.x64_takeMp_public
#print axioms Kraken.Promising.X64.EnvG.TakeMp.takeRuleRX_noFault
