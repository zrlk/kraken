/-
**Part 8: message passing with a writing
reader, end to end** (the `EnvG/MpEnvGPublic.lean`/`MpEnvGPublic2.lean`
pattern, on the take route).

The writer is MP's `mpWriter` (thread `0`), the reader is `takeReader`
(thread `1`, `EnvG/TakeMp.lean`): it spins on `ldar` of the flag, then stores
`43` to the data and loads it back. **`takeMp_envG`**: at every reachable
final configuration the reader's `W4` is `43` and the data word's final value
is `43`.

- **Postcondition** `TPost P rd`: the writer keeps the token `W` (as
  `MpPost`), the reader holds all of `Dt` with maximal write `(43, tw)`
  (`Own43`) and has `W4 = 43`.
- **Writer**: `takeRuleW`, `ThreadRuleRX.ofSafelyEnvG` from MP's `vcgen`
  proof (`mpWriter_envG`) with `hB_TW`; its invariant at the start is MP's
  (`invW_envG_init`). Into the take route by `NPSafe.toP` (`K2₀.toScope`).
- **Reader**: `npSafeP_of_safelyEnvGT` from `takeReader_envGT`, with `hB_T`
  and the start `invT_init` (`invGT_init`, `K1` at `σInit`: the flag's
  release predicate `φ`, `Dt` pure, MP's acquire id `0` with predicate `φ`).
  No fault: `takeRuleR_noFault` (`noFaultRule_ofSafelyEnvGT_struct`).
- **Final argument** `takeMp_final`: both threads cannot hold `W`, so the
  reader's disjunct holds; it holds all of `Dt`, so its maximal write is the
  total's (`total_max_of_thread`), hence the final value.
- **Assembly**: `final_of_relPureSafelyS` (`EnvG/TakeFinal.lean`), purity by
  `vcgen` (`mpWriter_relPure`, `takeReader_relPure`), MP's initial
  resources/ghost and erasure (`mpRes`, `mpGhost`, `erase_mpInit`).
-/
import Kraken.Promising.SLR.EnvG.TakeMpVCGen
import Kraken.Promising.SLR.EnvG.TakeMpRelPure
import Kraken.Promising.SLR.EnvG.TakeA64Rule
import Kraken.Promising.SLR.EnvG.TakeFinal
import Kraken.Promising.SLR.EnvG.MpEnvGPublic2

namespace Kraken.Promising.SLR.EnvG.TakeMp

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Mp Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.EnvG.MpSmoke Kraken.Promising.SLR.EnvG.MpLink Kraken.Promising.SLR.MpPublic
open Kraken.Promising.SLR.EnvG.MpRelPure Kraken.Promising.SLR.EnvG.TakeSmoke

/-! ## The postcondition and the final argument -/

/-- **The shared postcondition**: the writer keeps the token `W`; the reader
(thread `rd`) holds all of `Dt` with maximal write `(43, tw)` and has
`W4 = 43`. -/
def TPost (P : Params) (rd : Nat) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  1 ≤ (r.wr P.W).q ∨
    ((∃ t, c.threads[rd]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧ Own43 P r)

/-- **A thread holding all of `x` holds the total's maximal write** (clean
erasure): `total_max_of_slot` for a thread. The AArch64 instance of the
ISA-generic `SLR.total_max_of_thread` (`SLR/StoreHelpers.lean`). -/
theorem total_max_of_thread {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa}
    (E : Erase rF g T c) {j : Nat} (hj : j < c.threads.size) {x : Loc} (hq : ((rF j).wr x).q = 1)
    {v0 : Val} {ts : Time} (hX : ((rF j).wr x).X (v0, ts)) (hmax : ∀ p, ((rF j).wr x).X p → p.2 ≤ ts) :
    0 < ((total rF g c).wr x).q ∧ ((total rF g c).wr x).X (v0, ts) ∧
      ∀ p, ((total rF g c).wr x).X p → p.2 ≤ ts :=
  SLR.total_max_of_thread E hj hq hX hmax

/-- **The final argument**: from erasure at a final configuration of two
threads whose final resources satisfy `TPost P 1`. -/
theorem takeMp_final {P : Params} {c : Config isa} {rF : Nat → Res} {g : Ghost}
    (E : Erase rF g (fun _ => False) c) (hf : c.final = true) (hsize : c.threads.size = 2)
    (hB : ∀ tid, c.Done tid → TPost P 1 c (rF tid) g) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal P.Dt = 43#128 := by
  have h0 : (0 : Nat) < c.threads.size := by rw [hsize]; decide
  have h1 : (1 : Nat) < c.threads.size := by rw [hsize]; decide
  have hR : ∃ j, j < c.threads.size ∧
      (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧ Own43 P (rF j) := by
    rcases hB 0 (Config.final_done hf h0) with hw0 | hr0
    · rcases hB 1 (Config.final_done hf h1) with hw1 | hr1
      · have := E.q_add_le_one h0 h1 (by decide) P.W
        exfalso
        grind
      · exact ⟨1, h1, hr1⟩
    · exact ⟨0, h0, hr0⟩
  obtain ⟨j, hj, hx4, hq, tw, hX, hmax⟩ := hR
  obtain ⟨hpos, hXT, hmaxT⟩ := total_max_of_thread E hj hq hX hmax
  exact ⟨hx4, E.finalVal_of_max hf hpos hXT hmaxT⟩

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- The writing reader at its start (the label `spin`), as `StartR`. -/
structure StartT (f d : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout takeReader
  decls : s.decls = {}
  endPc : s.endPc = (layout takeReader).addrOf 7
  pc : s.st.2 = (layout takeReader).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = f
  x1 : s.st.1.regs.X1.toBitVec = d
  df : Mem.loadInt s.st.1.dmem f 4 = none
  dd : Mem.loadInt s.st.1.dmem d 4 = none

end Start

/-! ## The writer -/

section Writer

variable [layout : _root_.Layout] [Executable.ValidLayout (layout mpWriter)]

omit [Executable.ValidLayout (layout mpWriter)] in
/-- **`hB` for the writer**: it keeps the token `W` (`hB_W`). -/
theorem hB_TW (P : Params) (tid rd : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postW P (t.st.st, σ) → t.prom = [] → EnvRel tid (mpPlan P) σ c t r g cl → cl → TPost P rd c r g := by
  rintro c t r g cl σ hpost hp hrel -
  obtain ⟨-, hW⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hW.2
  · rw [hp] at hts; cases hts

/-- **The writer's rule** for `TPost` (`mpRuleW_envG` with `hB_TW`). -/
def takeRuleW (P : Params) (hL : MpLocs P) (tid rd : Nat) : ThreadRuleRX (I := isa) Arch.armv8 (TPost P rd) tid :=
  ThreadRuleRX.ofSafelyEnvG (post := postW P) (mpPlan_valid hL) mpWriter_rmwLive mpWriter_phase1 postOf_end
    (not_instrStepEnv_of_end_labels _ 1) (hB_TW P tid rd)

end Writer

/-! ## The reader -/

section Reader

variable [layout : _root_.Layout] [Executable.ValidLayout (layout takeReader)]

omit [Executable.ValidLayout (layout takeReader)] in
theorem takeReader_rmwLive : (layout takeReader).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem takeReader_phase1 : Phase1Tree Arch.armv8 (layout takeReader) :=
  phase1Tree_of_dirs (by dirs_phase1 takeReader)

omit [Executable.ValidLayout (layout takeReader)] in
theorem takeReader_noFault : DirsNoFault (layout takeReader) := by dirs_no_fault' takeReader

/-- The reader's postcondition: the end of its text, `Own43`, and `W4 = 43`
under the clean flag (the counter of `takeReader_envGT` projected away). -/
abbrev postT (P : Params) : MachineState × EStateA → Prop :=
  postOf takeReader fun s σ => ∃ _ : Nat, Own43 P σ.r ∧ (σ.cl → s.regs.X4.toBitVec.setWidth 32 = 43)

omit [Executable.ValidLayout (layout takeReader)] in
/-- **`hB` for the reader**: with no promise its resource is the env's, so
`Own43`; `W4 = 43` under the clean flag. -/
theorem hB_T (P : Params) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postT P (t.st.st, σ) → t.prom = [] → EnvRel tid rdPlan σ c t r g cl → cl → TPost P tid c r g := by
  rintro c t r g cl σ hpost hp hrel hcl
  obtain ⟨-, -, hown, hx4⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inr ⟨⟨t, hrel.ht, hx4 (hrel.cl hcl)⟩, hown⟩

/-- **The reader's no-fault rule** (`NoFaultRuleS` of its take-route rule). -/
theorem takeRuleR_noFault (P : Params) (tid : Nat) :
    NoFaultRuleS (ThreadRuleRXGS.ofSafelyEnvGT (e := layout takeReader) (post := postT P) rdPlan_valid
      takeReader_rmwLive takeReader_phase1 postOf_end (not_instrStepEnv_of_end_labels _ 1) (hB_T P tid)) :=
  noFaultRule_ofSafelyEnvGT_struct _ _ _ _ _ _ takeReader_noFault

end Reader

/-! ## `NPSafeP` and the theorem -/

section Start

variable [layout : _root_.Layout] {f d : BitVec 64} {sW sR : isa.State} {initMem : List (Loc × Val)}

/-- **The reader's initial invariant** (thread `1`): `K1` at `σInit`. -/
theorem invT_init [Executable.ValidLayout (layout takeReader)] (hfd : f ≠ d) (hR : StartT f d sR) :
    InvG (I := isa) Arch.armv8 1 rdPlan
      (QA64T Arch.armv8 1 rdPlan (layout takeReader) ((layout takeReader).addrOf takeReader.length) (postT (ghostParams f d)))
      True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) 1) (mpGhost (ghostParams f d)) := by
  letI : CodeEnv := ⟨layout takeReader⟩
  have hL := ghostParams_mpLocs hfd
  refine invGT_init (s := sR) rfl rfl (qa64T_of_partialTripleEnv (takeReader_envGT _ 1).uncount rfl hR.exe
    hR.decls hR.endPc hR.pc ⟨0, hR.x0, hR.x1, hR.df, hR.dd, mpGhost_rel_Fl, fun v => ?_, ?_, 0, Nat.zero_lt_one,
      ?_, OkPred.flag⟩)
  · show Pred.Pure ((mpGhost _).rel _) v
    rw [mpGhost_rel_ne (Ne.symm hL.fl_dt)]; exact Pred.emp_pure v
  · simp [σInit, Views.getFwd]
  · simp [σInit, mpRes, readerRes]

end Start

/-- **The `NPSafeP` side for MP with a writing reader**: the writer through
its `ThreadRuleRX` (`NPSafe.toP`), the reader through the take route. -/
theorem takeMp_npSafe (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartW (layout := lW) f d sW) (hR : StartT (layout := lR) f d sR) :
    ∀ tid, tid < [sW, sR].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (TPost (ghostParams f d) 1) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sW, sR] initMem)
      (mpRes (Config.init [sW, sR] initMem).mem (ghostParams f d) tid) (mpGhost (ghostParams f d)) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact NPSafe.toP (fun _ _ _ _ _ h => h) (fun _ _ _ h => K2₀.toScope _ h)
      (NPSafe.of_ruleRX (takeRuleW (layout := lW) _ (ghostParams_mpLocs hfd) 0 1) n m _ _ _ _
        (invW_envG_init (layout := lW) hfd hW))
  · exact npSafeP_of_safelyEnvGT (e := lR takeReader) (post := postT (layout := lR) _) rdPlan_valid
      (takeReader_rmwLive (layout := lR)) (takeReader_phase1 (layout := lR)) postOf_end
      (not_instrStepEnv_of_end_labels _ 1) (hB_T (layout := lR) _ 1) n m (invT_init (layout := lR) hfd hR)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- The threads' purity specifications: the writer (layout `lW`) at thread
`0`, the writing reader (layout `lR`) elsewhere. -/
def takePureSpec (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := lW) mpWriter fun _ _ => True
  | _ + 1 => RelPureSpec.ofProgram (layout := lR) takeReader fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states.** -/
theorem takePureSpec_init (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] {f d : BitVec 64} (hfd : f ≠ d) {sW sR : isa.State}
    (hW : StartW (layout := lW) f d sW) (hR : StartT (layout := lR) f d sR) :
    ∀ tid s, [sW, sR][tid]? = some s → (takePureSpec lW lR (mpGhost (ghostParams f d)).rel tid).Holds s := by
  have hd : ∀ v, Pred.Pure ((mpGhost (ghostParams f d)).rel ⟨d, 4⟩) v := fun v => by
    rw [show (⟨d, 4⟩ : Loc) = (ghostParams f d).Dt from rfl,
      mpGhost_rel_ne (Ne.symm (ghostParams_mpLocs hfd).fl_dt)]
    exact Pred.emp_pure v
  intro tid s hs
  match tid, hs with
  | 0, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hW
    letI : CodeEnv := ⟨lW mpWriter⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lW)
      (mpWriter_relPure (layout := lW) _ f d hd).partial rfl he hds hend hpc ⟨hx0, hx1, hdf, hdd⟩
  | 1, hs =>
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hdf, hdd⟩ := hR
    letI : CodeEnv := ⟨lR takeReader⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := lR) (takeReader_relPure (layout := lR) _ f d hd).uncount
      rfl he hds hend hpc ⟨0, hx0, hx1, hdf, hdd⟩
  | _ + 2, hs => cases hs

/-- **Message passing with a writing reader, for AArch64 under `Arch.armv8`**:
the writer `mpWriter` (thread `0`, layout `lW`) and the reader `takeReader`
(thread `1`, layout `lR`), started with `X0 = f`, `X1 = d` from an initial
memory with the flag at `0`: at every reachable final configuration the
reader's `W4` is `43` and the data word's final value is `43`. The reader
takes all of the data at its acquire load (the take route,
`npSafeP_of_safelyEnvGT`) and then writes it. -/
theorem takeMp_envG {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR takeReader)] (f d : BitVec 64) (hfd : f ≠ d) {sW sR : isa.State}
    {initMem : List (Loc × Val)} (hW : StartW (layout := lW) f d sW) (hR : StartT (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 43#128 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := TPost (ghostParams f d) 1)
    (Φ := fun c => (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨d, 4⟩ = 43#128)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_mpInit _ _ hF0) pend_mpGhost
    (takePureSpec lW lR _) (takePureSpec_init lW lR hfd hW hR) (takeMp_npSafe lW lR hfd hW hR) hc hf
    fun _ _ E' _ hsize hB => takeMp_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.TakeMp

#print axioms Kraken.Promising.SLR.EnvG.TakeMp.takeMp_envG
#print axioms Kraken.Promising.SLR.EnvG.TakeMp.takeRuleR_noFault
