/-
**Whole image, part 2: the AArch64 SPSC ring with
both threads running the whole `.kl` image** (`spsc_queue.kl` under
`Arch.armv8`). Additive: `a64_spsc_envG`
(`EnvG/A64SpscPublic.lean`) is unchanged.

**`a64_spsc_envG_whole`**: `a64_spsc_envG`'s conclusion (at every reachable
final configuration the consumer has `W10 = 1`, `W11 = 2`, `W12 = 3`), with
both threads' executable the whole `code` block `spscImageA` under one
layout, the producer from `prod` to `pdone`, the consumer from `cons` to
`cdone` (as `Kraken.Litmus.AArch64.prepareProgram` sets them up). This
resolves `a64_spsc_envG`'s per-thread-image deviation.

- **Producer**: `ThreadRuleRXGS.ofSafelyEnvGTUM` (`EnvG/A64MaskLink.lean`)
  over the mask `spscImageP` (the dead `NOP` behind `pdone:` and the
  consumer's code masked): the shape `spscImageP_phase1` and the halt
  `prodP_stuck` of the mask, the static check and fault-freedom of the
  image.
- **Consumer**: the same link at the trivial mask (`MaskOf.refl`): its exit
  `cdone` ends the image (`consA_stuck`).
- **Final argument, ghost and purity specification shape**: the AArch64 SPSC proof's
  (`spsc_final`, `spscRes`, `spscGhost`, `erase_spscInit`, `PR_init`,
  `CE_init`, `hB_P`/`hB_C`'s proofs); the purity runs are
  `spscProdW_relPure`/`spscConsW_relPure` in the image.
-/
import Kraken.Promising.SLR.EnvG.A64SpscWholeVCGen
import Kraken.Promising.SLR.EnvG.A64SpscPublic
import Kraken.Promising.SLR.EnvG.A64MaskHelpers

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

set_option linter.unusedSimpArgs false

/-! ## The image's static facts -/

/-- Every cell of the image is phase-1 (`dirs_phase1`'s script, for every
ambient executable). -/
theorem spscImageA_dirsPhase1 : ∀ d ∈ spscImageA, ∀ (e : _root_.Executable) z, DirPhase1 Arch.armv8 e d z := by
  dirs_phase1_any spscImageA
  all_goals (by_cases hz : s.status.z = true <;> simp [hz, DetAccess, SingleAccessS, toEv])

/-- A label cell is phase-1 (`label_dirPhase1_any`). -/
theorem label_dirPhase1 (l : Label) (e : _root_.Executable) (z : Nat) : DirPhase1 Arch.armv8 e (.label l) z :=
  label_dirPhase1_any Arch.armv8 l e z

/-- A data cell is phase-1 (its tree is a fault; `byteArray_dirPhase1_any`). -/
theorem byteArray_dirPhase1 (b : ByteArray) (e : _root_.Executable) (z : Nat) :
    DirPhase1 Arch.armv8 e (.byteArray b) z :=
  byteArray_dirPhase1_any Arch.armv8 b e z

section Static

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)]

omit [Executable.ValidLayout (layout spscImageA)] in
theorem spscImageA_rmwLive : (layout spscImageA).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

/-- The image is phase-1 (both roles' code). -/
theorem spscImageA_phase1 : Phase1Tree Arch.armv8 (layout spscImageA) :=
  phase1Tree_of_dirs (dirsPhase1_layout spscImageA_dirsPhase1)

/-- The producer's mask is phase-1. -/
theorem spscImageP_phase1 : Phase1Tree Arch.armv8 (layout spscImageP) :=
  haveI := spscImageP_valid (layout := layout)
  phase1Tree_of_dirs (dirsPhase1_layout (mem_maskKeep_range (Φd := fun d => ∀ e z, DirPhase1 Arch.armv8 e d z)
    (fun d hd => spscImageA_dirsPhase1 d (List.mem_of_mem_drop (List.mem_of_mem_take hd)))
    (fun l => label_dirPhase1 l) (byteArray_dirPhase1 _)))

omit [Executable.ValidLayout (layout spscImageA)] in
theorem spscImageA_noFault : DirsNoFault (layout spscImageA) := by dirs_no_fault' spscImageA

/-! ## The halts -/

set_option maxRecDepth 8192 in
/-- `pdone`'s address is the producer's mask's cell `18` (the masked
`NOP`). -/
theorem labA_pdone : labA "pdone" = (layout spscImageP).addrOf 18 := by
  have hd : labA "pdone" = (layout spscImageA).addrOf 17 :=
    Program.label_addrOf_drop spscImageA_wf.nodup (by decide) (by decide)
  have h17 : (layout spscImageA).2[17]? = some (Directive.label "pdone", Kraken.Layout.size Directive 17) := by
    simp [Layout.apply_snd, Layout.frag, spscImageA]
  rw [addrOf_mask spscImageP_mask, Executable.addrOf_succ _ h17,
    Executable.ValidLayout.label_size 17 "pdone" _ h17, hd]
  simp

/-- **No step of the producer's mask at its exit label `pdone`** (the
guarded exit: the image has the `NOP` there). -/
theorem prodP_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labA "pdone" → ¬ (layout spscImageP).instrStepEnv env x R := by
  haveI := spscImageP_valid (layout := layout)
  rw [labA_pdone]
  exact not_instrStepEnv_of_byteArray (i := 18) (b := .mk #[]) env spscImageP_18

set_option maxRecDepth 8192 in
/-- `cdone`'s address is the end of the image. -/
theorem labA_cdone : labA "cdone" = (layout spscImageA).addrOf spscImageA.length := by
  have hd : labA "cdone" = (layout spscImageA).addrOf 47 :=
    Program.label_addrOf_drop spscImageA_wf.nodup (by decide) (by decide)
  have h47 : (layout spscImageA).2[47]? = some (Directive.label "cdone", Kraken.Layout.size Directive 47) := by
    simp [Layout.apply_snd, Layout.frag, spscImageA]
  rw [show spscImageA.length = 47 + 1 from rfl, Executable.addrOf_succ _ h47,
    Executable.ValidLayout.label_size 47 "cdone" _ h47, hd]
  simp

/-- **No step of the image at the consumer's exit label `cdone`.** -/
theorem consA_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labA "cdone" → ¬ (layout spscImageA).instrStepEnv env x R := by
  rw [labA_cdone]
  exact not_instrStepEnv_of_end_labels env 1

end Static

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)]

/-- The producer's postcondition: its exit label and all of `T` (the
counter projected away). -/
abbrev postPW (P : SP) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labA "pdone" ∧ (x.2.r.wr P.T).q = 1) ∨ False

omit [Executable.ValidLayout (layout spscImageA)] in
theorem postPW_end (P : SP) : ∀ y, postPW P y → y.1.2 = labA "pdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout spscImageA)] in
/-- **`hB` for the whole-image producer** (`hB_P`'s proof). -/
theorem hB_PW (P : SP) (tid : Nat) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postPW P (t.st.st, σ) → t.prom = [] → EnvRel tid (prodPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hq⟩ := hpost.resolve_right id
  obtain rfl : r = σ.r := by
    rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
    · rfl
    · rw [hp] at hts; cases hts
  exact .inl (by rw [hq]; decide)

/-- **The whole-image producer's rule** (cumulative take route, over its
mask). -/
def prodRuleW (P : SP) (hL : SpscLocs P) (tid : Nat) : ThreadRuleRXGS G₀ Arch.armv8 (SpscPost P) tid :=
  ThreadRuleRXGS.ofSafelyEnvGTUM (post := postPW P) spscImageP_mask (prodPlan_valid hL) spscImageA_rmwLive
    spscImageP_phase1 (postPW_end P) (prodP_stuck _) (hB_PW P tid)

/-- **The whole-image producer's no-fault rule**, unconditional in the
thread's promises. -/
theorem prodRuleW_noFault (P : SP) (hL : SpscLocs P) (tid : Nat) : NoFaultRuleS (prodRuleW P hL tid) :=
  noFaultRule_ofSafelyEnvGTUM _ _ _ _ _ _ _ spscImageA_noFault

/-- The consumer's postcondition: its exit label and, under the clean flag,
`1, 2, 3`. -/
abbrev postCW : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labA "cdone" ∧ (x.2.cl → x.1.1.regs.X10.toBitVec.setWidth 32 = 1 ∧
    x.1.1.regs.X11.toBitVec.setWidth 32 = 2 ∧ x.1.1.regs.X12.toBitVec.setWidth 32 = 3)) ∨ False

omit [Executable.ValidLayout (layout spscImageA)] in
theorem postCW_end : ∀ y, postCW y → y.1.2 = labA "cdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout spscImageA)] in
/-- **`hB` for the whole-image consumer** (`hB_C`'s proof). -/
theorem hB_CW (P : SP) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postCW (t.st.st, σ) → t.prom = [] → EnvRel 1 (consPlan P) σ c t r g cl → cl → SpscPost P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ - hrel hcl
  obtain ⟨-, hx⟩ := hpost.resolve_right id
  obtain ⟨h10, h11, h12⟩ := hx (hrel.cl hcl)
  exact .inr ⟨t, hrel.ht, h10, h11, h12⟩

/-- **The whole-image consumer's rule** (cumulative take route, the image
itself as its mask, thread `1`). -/
def consRuleW (P : SP) (hL : SpscLocs P) : ThreadRuleRXGS G₀ Arch.armv8 (SpscPost P) 1 :=
  ThreadRuleRXGS.ofSafelyEnvGTUM (post := postCW) (MaskOf.refl _) (consPlan_valid hL) spscImageA_rmwLive
    spscImageA_phase1 postCW_end (consA_stuck _) (hB_CW P)

/-- **The whole-image consumer's no-fault rule.** -/
theorem consRuleW_noFault (P : SP) (hL : SpscLocs P) : NoFaultRuleS (consRuleW P hL) :=
  noFaultRule_ofSafelyEnvGTUM _ _ _ _ _ _ _ spscImageA_noFault

end Rules

/-! ## The start -/

/-- **The producer at its start in the whole image**, as the runner sets it
up: the image, no declarations, pc at `prod`, end at `pdone`, and
`a64_spsc_envG`'s frame (`X0 = buf`, `X1 = head`, `X2 = tail`, no private
byte at the four shared words). -/
structure StartPW [layout : _root_.Layout] (P : SP) (s : isa.State) : Prop where
  exe : s.exe = layout spscImageA
  decls : s.decls = {}
  pc : s.st.2 = labA "prod"
  endPc : s.endPc = labA "pdone"
  frame : FrameP P s.st.1

/-- **The consumer at its start in the whole image**: pc at `cons`, end at
`cdone`. -/
structure StartCW [layout : _root_.Layout] (P : SP) (s : isa.State) : Prop where
  exe : s.exe = layout spscImageA
  decls : s.decls = {}
  pc : s.st.2 = labA "cons"
  endPc : s.endPc = labA "cdone"
  frame : FrameC P s.st.1

section Inv

variable [layout : _root_.Layout] [Executable.ValidLayout (layout spscImageA)] {P : SP} {sP sC : isa.State}
  {initMem : List (Loc × Val)}

/-- **`NPSafeP` for the whole-image producer** (thread `0`). -/
theorem prodW_npSafeP (hL : SpscLocs P) (hP : StartPW P sP)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 0 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 0) (spscGhost P) := by
  obtain ⟨he, hds, hpc, hend, hfr⟩ := hP
  refine npSafeP_of_safelyEnvGTUM (post := postPW P) spscImageP_mask (prodPlan_valid hL) spscImageA_rmwLive
    spscImageP_phase1 (postPW_end P) (prodP_stuck _) (hB_PW P 0) n m
    (invGTUM_init (s := sP) rfl rfl ⟨he, hds, hend, ?_⟩)
  rw [show sP.st = (sP.st.1, labA "prod") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscProdW_envGTU P hL 0 _ (_, 0) ⟨hfr, PR_init hL hH0⟩)

/-- **`NPSafeP` for the whole-image consumer** (thread `1`). -/
theorem consW_npSafeP (hL : SpscLocs P) (hC : StartCW P sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0) (n m : Nat) :
    NPSafeP (model isa) Arch.armv8 (SpscPost P) 1 G₀ (K2Scope (model isa) AllocIds) n m True
      (Config.init [sP, sC] initMem) (spscRes (Config.init [sP, sC] initMem).mem P 1) (spscGhost P) := by
  obtain ⟨he, hds, hpc, hend, hfr⟩ := hC
  refine npSafeP_of_safelyEnvGTUM (post := postCW) (MaskOf.refl _) (consPlan_valid hL) spscImageA_rmwLive
    spscImageA_phase1 postCW_end (consA_stuck _) (hB_CW P) n m
    (invGTUM_init (s := sC) rfl rfl ⟨he, hds, hend, ?_⟩)
  rw [show sC.st = (sC.st.1, labA "cons") from Prod.ext rfl hpc]
  exact Safely.uncountA (spscConsW_envGTU P hL 1 _ (_, 0) ⟨hfr, CE_init hL hT0⟩)

end Inv

/-- **The `NPSafeP` side, whole image.** -/
theorem a64_spsc_whole_npSafe (l : _root_.Layout) [Executable.ValidLayout (l spscImageA)] {P : SP}
    (hL : SpscLocs P) {sP sC : isa.State} {initMem : List (Loc × Val)} (hP : StartPW (layout := l) P sP)
    (hC : StartCW (layout := l) P sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal P.T = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal P.H = 0) :
    ∀ tid, tid < [sP, sC].length → ∀ n m, NPSafeP (model isa) Arch.armv8 (SpscPost P) tid G₀
      (K2Scope (model isa) AllocIds) n m True (Config.init [sP, sC] initMem)
      (spscRes (Config.init [sP, sC] initMem).mem P tid) (spscGhost P) := by
  intro tid htid n m
  rcases tid with _ | _ | k
  · exact prodW_npSafeP (layout := l) hL hP hH0 n m
  · exact consW_npSafeP (layout := l) hL hC hT0 n m
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Purity -/

/-- The threads' purity specifications in the whole image: the producer's
run to `pdone` at thread `0`, the consumer's to `cdone` elsewhere. -/
def spscPureSpecW (l : _root_.Layout) [hv : Executable.ValidLayout (l spscImageA)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => { e := l spscImageA, valid := hv, endPc := labA (layout := l) "pdone",
           post := fun x => ∃ _ : Nat, (x.1.2 = labA (layout := l) "pdone" ∧ True) ∨ False,
           post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }
  | _ + 1 => { e := l spscImageA, valid := hv, endPc := labA (layout := l) "cdone",
               post := fun x => ∃ _ : Nat, (x.1.2 = labA (layout := l) "cdone" ∧ True) ∨ False,
               post_end := fun _ ⟨_, h⟩ => h.elim And.left False.elim }

/-- **The purity specifications hold at the start states.** -/
theorem spscPureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l spscImageA)] {P : SP}
    (hL : SpscLocs P) {sP sC : isa.State} (hP : StartPW (layout := l) P sP) (hC : StartCW (layout := l) P sC) :
    ∀ tid s, [sP, sC][tid]? = some s → (spscPureSpecW l (spscGhost P).rel tid).Holds s := by
  intro tid s hs
  match tid, hs with
  | 0, hs =>
    cases hs
    obtain ⟨he, hds, hpc, hend, hfr⟩ := hP
    refine ⟨he, hend, hds, ?_⟩
    rw [show sP.st = (sP.st.1, labA (layout := l) "prod") from Prod.ext rfl hpc]
    exact Safely.uncountA (spscProdW_relPure (layout := l) P _
      (fun v => by rw [spscGhost_rel, relS_B0 hL]; exact Pred.emp_pure v)
      (fun v => by rw [spscGhost_rel, relS_B1 hL]; exact Pred.emp_pure v) _ ((), 0) hfr)
  | 1, hs =>
    cases hs
    obtain ⟨he, hds, hpc, hend, hfr⟩ := hC
    refine ⟨he, hend, hds, ?_⟩
    rw [show sC.st = (sC.st.1, labA (layout := l) "cons") from Prod.ext rfl hpc]
    exact Safely.uncountA (spscConsW_relPure (layout := l) P _ _ ((), 0) hfr)
  | _ + 2, hs => cases hs

/-! ## The theorem -/

/-- **The AArch64 SPSC ring under `Arch.armv8`, both threads running the
whole `.kl` image** (`Examples/LockFree/AArch64/spsc_queue.kl`,
`forall (1:X10=1 /\ 1:X11=2 /\ 1:X12=3)`, on the low 32 bits).

For a valid layout `l` of the `.kl`'s `code` block `spscImageA` and
addresses `b` (`buf`; slot `1` is `b ^^^ 8`), `h` (`head`), `t` (`tail`)
whose four words are distinct (`SpscLocs`): if thread `0` runs the image
from `prod` to `pdone` and thread `1` from `cons` to `cdone`, each with no
declarations, `X0 = b`, `X1 = h`, `X2 = t` and no private byte at the four
shared words (`StartPW`, `StartCW`), and the initial memory has `tail` and
`head` at `0`, then every configuration `Reachable` under `Arch.armv8` that
is final has the consumer's `W10 = 1`, `W11 = 2`, `W12 = 3`.

This is `a64_spsc_envG` with the runner's executable: the per-thread-image
deviation of `a64_spsc_envG` is resolved here (the dead `NOP` at `pdone`,
which broke the halt, is handled by the producer's mask:
`EnvG/A64MaskLink.lean`). As there, only final configurations are
constrained (no fairness), faults are covered by the per-thread no-fault
facts (`prodRuleW_noFault`, `consRuleW_noFault`), and the threads have no
declarations (the runner sets `decls` from the init block). -/
theorem a64_spsc_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l spscImageA)]
    (b h t : BitVec 64) (hL : SpscLocs ⟨b, h, t⟩) {sP sC : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPW (layout := l) ⟨b, h, t⟩ sP) (hC : StartCW (layout := l) ⟨b, h, t⟩ sC)
    (hT0 : (Config.init [sP, sC] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hH0 : (Config.init [sP, sC] initMem).mem.initVal ⟨h, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sP, sC] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ BitVec.setWidth 32 th.st.st.1.regs.X10.toBitVec = 1 ∧
      BitVec.setWidth 32 th.st.st.1.regs.X11.toBitVec = 2 ∧ BitVec.setWidth 32 th.st.st.1.regs.X12.toBitVec = 3 :=
  final_of_relPureSafelyS Arch.armv8 fuel (B := SpscPost ⟨b, h, t⟩) (Φ := ConsDone)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_spscInit hL _ hT0 hH0) pend_spscGhost
    (spscPureSpecW l _) (spscPureSpecW_init l hL hP hC) (a64_spsc_whole_npSafe l hL hP hC hT0 hH0) hc hf
    fun _ _ E' _ hsize hB => spsc_final E' hf hsize hB

end Kraken.Promising.SLR.EnvG.SpscA

#print axioms Kraken.Promising.SLR.EnvG.SpscA.a64_spsc_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.SpscA.prodRuleW_noFault
#print axioms Kraken.Promising.SLR.EnvG.SpscA.consRuleW_noFault
