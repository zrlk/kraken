/-
**`msqueue2.kl` with both threads running the
whole `.kl` image.** Additive: `MsQueue.msqueue2_envG`
(`EnvG/MsQueue2Public.lean`) is unchanged.

As `EnvG/A64WholeMsQueue1.lean`, for the two-node queue: the runner's
executable is the whole `code` block `msq2Image` (`enq:`, `enq2Prog`, the
dead `NOP` behind `pdone:`, `deq1:`, `deq2Prog`, the `NOP` behind `ddone1:`;
`msq2Image_eq`) under one layout, each thread from its entry label (`enq`,
`deq1`) to its exit label (`pdone`, `ddone1`).

- **Both roles are masked**: the enqueuer runs over `msq2ImageE` (cells
  `0 … 42` kept), the dequeuer over `msq2ImageD` (cells `44 … 84`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdjM` (`EnvG/A64MaskAdj.lean`).
- **Runs**: the MS queue proof's scripts, unchanged and not repeated: `enq2_envGCAdj_at`,
  `deq2_envGCAdj_at` (in the masks) and `enq2_relPure_at`, `deq2_relPure_at`
  (purity, in the image).
- **Final argument, ghost and resources**: the MS queue proof's (`MB2`,
  `MsQueue2Final`, `tRes2`, `ghost2`, `start1_init`, `comD2_init`,
  `erase_init2`, `final_values2`, `tokE_pair_false`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Public
import Kraken.Promising.SLR.EnvG.A64MaskAdj
import Kraken.Promising.SLR.EnvG.A64MaskHelpers
import Kraken.Promising.SLR.EnvG.A64MaskRunAt

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The image and the masks -/

/-- **The `code` block of `msqueue2.kl`, verbatim**: the runner's
executable, shared by both threads (`P0: enq pdone; P1: deq1 ddone1`). -/
def msq2Image : Program := parseAArch64("
enq:
enq1:
  MOV X2,X12
  MOV W9,#1
  STR W9,[X2]
enq1_loop:
  LDAR X3,[X1]
  ADD X8,X3,#8
  LDAR X4,[X8]
  CBNZ X4,enq1_fix
  MOV X5,#0
  CASAL X5,X2,[X8]
  CBNZ X5,enq1_loop
  MOV X5,X3
  CASAL X5,X2,[X1]
  B enq1_end
enq1_fix:
  MOV X5,X3
  CASAL X5,X4,[X1]
  B enq1_loop
enq1_end:
enq2:
  MOV X2,X13
  MOV W9,#2
  STR W9,[X2]
enq2_loop:
  LDAR X3,[X1]
  ADD X8,X3,#8
  LDAR X4,[X8]
  CBNZ X4,enq2_fix
  MOV X5,#0
  CASAL X5,X2,[X8]
  CBNZ X5,enq2_loop
  MOV X5,X3
  CASAL X5,X2,[X1]
  B enq2_end
enq2_fix:
  MOV X5,X3
  CASAL X5,X4,[X1]
  B enq2_loop
enq2_end:
  B pdone
pdone:
  NOP
deq1:
deq1a:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq1a_ne
  CBZ X5,deq1a
  MOV X6,X3
  CASAL X6,X5,[X1]
  B deq1a
deq1a_ne:
  CBZ X5,deq1a
  LDR W7,[X5]
  MOV X6,X3
  CASAL X6,X5,[X0]
  CMP X6,X3
  B.NE deq1a
  MOV W10,W7
deq1b:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq1b_ne
  CBZ X5,deq1b
  MOV X6,X3
  CASAL X6,X5,[X1]
  B deq1b
deq1b_ne:
  CBZ X5,deq1b
  LDR W7,[X5]
  MOV X6,X3
  CASAL X6,X5,[X0]
  CMP X6,X3
  B.NE deq1b
  MOV W11,W7
  B ddone1
ddone1:
  NOP
")

/-- info: (86, 42, 40) -/
#guard_msgs in
#eval (msq2Image.length, enq2Prog.length, deq2Prog.length)

/-- The image is the per-thread texts behind their entry labels, each
followed by a `NOP`. -/
theorem msq2Image_eq : msq2Image[0]? = some (.label "enq") ∧ (msq2Image.drop 1).take 42 = enq2Prog ∧
    msq2Image[44]? = some (.label "deq1") ∧ (msq2Image.drop 45).take 40 = deq2Prog := by decide

/-- **The enqueuer's mask**: cells `0 … 42` (`enq:` to `pdone:`) kept. -/
abbrev msq2ImageE : Program := msq2Image.maskKeep (keepRange 0 43)

/-- **The dequeuer's mask**: cells `44 … 84` (`deq1:` to `ddone1:`) kept. -/
abbrev msq2ImageD : Program := msq2Image.maskKeep (keepRange 44 85)

/-- Every cell of the image is phase-1 with failing release RMWs. -/
theorem msq2Image_dirs : ∀ d ∈ msq2Image, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any msq2Image

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labQ2 (x : Label) : Int64 := (_root_.Executable.labels (layout msq2Image)).label x

theorem msq2Image_rmwLive : (layout msq2Image).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem msq2Image_noFault : DirsNoFault (layout msq2Image) := by dirs_no_fault' msq2Image

variable [Executable.ValidLayout (layout msq2Image)]

set_option maxRecDepth 8192 in
theorem labQ2_enq : labQ2 "enq" = labQ2 "enq1" :=
  label_addrOf_succ_label (i := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
theorem labQ2_deq1 : labQ2 "deq1" = labQ2 "deq1a" :=
  label_addrOf_succ_label (i := 44) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- **No step of the enqueuer's mask at `pdone`** (the masked `NOP`). -/
theorem enqQ2_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ2 "pdone" → ¬ (layout msq2ImageE).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 43) msq2Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq2ImageE) (i := 43) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 0 43) (i := 42) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the dequeuer's mask at `ddone1`** (the masked `NOP`). -/
theorem deqQ2_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ2 "ddone1" → ¬ (layout msq2ImageD).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 44 85) msq2Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq2ImageD) (i := 85) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 44 85) (i := 84) (by decide) (by decide) (by decide) (by decide)))

/-! ## The runs (the MS queue proof's scripts, at the masks and the image) -/

/-- The enqueuer's run over its mask, at the image's labels. -/
theorem enqQ2_envGCAdj (P : Params2) (hL : QLocs2 P) : ∀ s g, enqTable2 P "enq1" s g →
    Safely ((layout msq2ImageE).instrStepEnv (SharedEnv.counted (EE2 P)))
      (fun x => (x.1.2 = labQ2 "pdone" ∧ ComE2 P x.2.1) ∨ False) ((s, labQ2 "enq1"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 43) msq2Image)
  letI : CodeEnv := ⟨layout msq2ImageE⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (enq2_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq2ImageE) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) s g hsg)

/-- The dequeuer's run over its mask, at the image's labels. -/
theorem deqQ2_envGCAdj (P : Params2) (hL : QLocs2 P) : ∀ s g, deqTable2 P "deq1a" s g →
    Safely ((layout msq2ImageD).instrStepEnv (SharedEnv.counted (ED2 P)))
      (fun x => (x.1.2 = labQ2 "ddone1" ∧ Dn2 P x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2.1) ∨ False)
      ((s, labQ2 "deq1a"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 44 85) msq2Image)
  letI : CodeEnv := ⟨layout msq2ImageD⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (deq2_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq2ImageD) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) s g hsg)

/-- The image as the ambient code (the purity runs). -/
local instance msq2Image.env : CodeEnv := ⟨layout msq2Image⟩

theorem msq2Image_placed : Program.Placed msq2Image "enq" := Program.placed_of_layout (by decide) rfl (by decide)

end Lay

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq2Image)]

/-- The whole-image enqueuer's postcondition. -/
abbrev postEQ2 (P : Params2) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ2 "pdone" ∧ ComE2 P x.2) ∨ False

/-- The whole-image dequeuer's postcondition. -/
abbrev postDQ2 (P : Params2) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ2 "ddone1" ∧ Dn2 P x.1.1.regs.X10.toBitVec x.1.1.regs.X11.toBitVec x.2) ∨ False

omit [Executable.ValidLayout (layout msq2Image)] in
/-- **`hB` for the whole-image enqueuer** (`hB_E2`'s proof). -/
theorem hB_EQ2 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postEQ2 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE2 P) σ c t r g cl → cl → MB2 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2.1
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout msq2Image)] in
/-- **`hB` for the whole-image dequeuer** (`hB_D2`'s proof). -/
theorem hB_DQ2 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDQ2 P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MB2 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The whole-image enqueuer's rule** (thread `0`, over its mask). -/
noncomputable def enqRuleQ2 (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postEQ2 P) (maskOf_layout _ _) (planE2_valid P) msq2Image_rmwLive
    (phase1TreeF_maskKeep_range msq2Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (enqQ2_stuck _)
    (hB_EQ2 P)

/-- **The whole-image enqueuer's rule excludes faults.** -/
theorem enqRuleQ2_noFault (P : Params2) : NoFaultRuleF (enqRuleQ2 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq2Image_noFault

/-- **The whole-image dequeuer's rule** (thread `1`, over its mask). -/
noncomputable def deqRuleQ2 (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB2 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postDQ2 P) (maskOf_layout _ _) (planD2_valid P) msq2Image_rmwLive
    (phase1TreeF_maskKeep_range msq2Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqQ2_stuck _)
    (hB_DQ2 P)

/-- **The whole-image dequeuer's rule excludes faults.** -/
theorem deqRuleQ2_noFault (P : Params2) : NoFaultRuleF (deqRuleQ2 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq2Image_noFault

end Rules

/-! ## The start -/

/-- **The enqueuer at its start in the whole image**, as the runner sets it
up (`0:X1=tail; 0:X12=n1; 0:X13=n2`): the image, no declarations, pc at
`enq`, end at `pdone`, `x1 = t`, `x12 = n1`, `x13 = n2`, and no private copy
of any 8- or 4-byte word. -/
structure StartEQ2 [layout : _root_.Layout] (t n1 n2 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq2Image
  decls : s.decls = {}
  pc : s.st.2 = labQ2 "enq"
  endPc : s.endPc = labQ2 "pdone"
  x1 : s.st.1.regs.X1.toBitVec = t
  x12 : s.st.1.regs.X12.toBitVec = n1
  x13 : s.st.1.regs.X13.toBitVec = n2
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **The dequeuer at its start in the whole image** (`1:X0=head;
1:X1=tail`): pc at `deq1`, end at `ddone1`. -/
structure StartDQ2 [layout : _root_.Layout] (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq2Image
  decls : s.decls = {}
  pc : s.st.2 = labQ2 "deq1"
  endPc : s.endPc = labQ2 "ddone1"
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq2Image)] {s0 s1 : isa.State}
  {initMem : List (Loc × Val)}

theorem invEQ2_init {P : Params2} (hL : QLocs2 P) (hS : StartEQ2 P.t P.n1 P.n2 s0) :
    (enqRuleQ2 P).Inv True (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem).mem P 0)
      (ghost2 P) := by
  refine invGFCAdjM_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s0.st = (s0.st.1, labQ2 "enq1") from Prod.ext rfl (hS.pc.trans labQ2_enq)]
  exact Safely.uncountA (enqQ2_envGCAdj P hL _ (_, 0)
    ⟨hS.x1, hS.d8, hS.d4, hS.x13, .inl ⟨rfl, hS.x12, start1_init P _⟩⟩)

theorem invDQ2_init {P : Params2} (hL : QLocs2 P) (hS : StartDQ2 P.h P.t s1)
    (hi : InitV2 (Config.init [s0, s1] initMem).mem P) :
    (deqRuleQ2 P).Inv True (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem).mem P 1)
      (ghost2 P) := by
  refine invGFCAdjM_init (s := s1) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s1.st = (s1.st.1, labQ2 "deq1a") from Prod.ext rfl (hS.pc.trans labQ2_deq1)]
  exact Safely.uncountA (deqQ2_envGCAdj P hL _ (_, 0)
    ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comD2_init P _ hi, trivial⟩⟩)

end Start

/-- **The `NPSafeF` side, whole image.** -/
theorem msqueue2_whole_npSafeF (l : _root_.Layout) [Executable.ValidLayout (l msq2Image)] {P : Params2}
    (hL : QLocs2 P) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEQ2 (layout := l) P.t P.n1 P.n2 s0) (h1 : StartDQ2 (layout := l) P.h P.t s1)
    (hi : InitV2 (Config.init [s0, s1] initMem).mem P) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB2 P) tid k j True
      (Config.init [s0, s1] initMem) (tRes2 (Config.init [s0, s1] initMem).mem P tid) (ghost2 P) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEQ2_init (layout := l) hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDQ2_init (layout := l) hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Purity -/

/-- The threads' purity specifications in the whole image: the enqueuer's
run to `pdone` at thread `0`, the dequeuer's to `ddone1` elsewhere. -/
def msq2PureSpecW (l : _root_.Layout) [Executable.ValidLayout (l msq2Image)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.toEnd (l msq2Image) (labQ2 (layout := l) "pdone")
  | _ + 1 => RelPureSpec.toEnd (l msq2Image) (labQ2 (layout := l) "ddone1")

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data words `[n1]`, `[n2]`. -/
theorem msq2PureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l msq2Image)] {rel : Loc → Pred}
    {h t n1 n2 : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) {s0 s1 : isa.State}
    (h0 : StartEQ2 (layout := l) t n1 n2 s0) (h1 : StartDQ2 (layout := l) h t s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msq2PureSpecW l rel tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, ?_⟩
    rw [show s0.st = (s0.st.1, labQ2 (layout := l) "enq1") from Prod.ext rfl (h0.pc.trans labQ2_enq)]
    letI : CodeEnv := ⟨l msq2Image⟩
    exact Safely.uncountA (enq2_relPure_at rel n1 n2 hd hd2
      (Program.PlacedIn.of_placedE (msq2Image_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "pdone") (by decide)) _ ((), 0) ⟨h0.d8, h0.d4, h0.x13, .inl ⟨rfl, h0.x12⟩⟩)
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, ?_⟩
    rw [show s1.st = (s1.st.1, labQ2 (layout := l) "deq1a") from Prod.ext rfl (h1.pc.trans labQ2_deq1)]
    letI : CodeEnv := ⟨l msq2Image⟩
    exact Safely.uncountA (deq2_relPure_at rel
      (Program.PlacedIn.of_placedE (msq2Image_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "ddone1") (by decide)) _ ((), 0) ⟨h1.d8, h1.d4, .inl rfl⟩)
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **The two-node Michael–Scott queue `msqueue2.kl` for AArch64 under
`Arch.armv8`, both threads running the whole `.kl` image** (on `EnvGCAdj`;
`forall (1:X10=1 /\ 1:X11=2)`).

For a valid layout `l` of the `.kl`'s `code` block `msq2Image` and all
addresses with `msqueue2_envG`'s inequalities: if thread `0` runs the image
from `enq` to `pdone` with `x1 = t`, `x12 = n1`, `x13 = n2` and thread `1`
from `deq1` to `ddone1` with `x0 = h`, `x1 = t`, each with no declarations
and an empty private memory (`StartEQ2`, `StartDQ2`), and the initial memory
has `head = tail = d` and the three links `0` (`InitV2`), then every final
configuration reachable under `Arch.armv8` has `1:X10 = 1 ∧ 1:X11 = 2`.

This is `msqueue2_envG` with the runner's executable (its per-thread-image
deviation resolved). -/
theorem msqueue2_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l msq2Image)]
    (h t d n1 n2 : BitVec 64) (hht : h ≠ t) (hhd : h ≠ d + 8)
    (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8) (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8)
    (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0) (hn2 : n2 ≠ 0) {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : StartEQ2 (layout := l) t n1 n2 s0) (h1 : StartDQ2 (layout := l) h t s1)
    (hi : InitV2 (Config.init [s0, s1] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
      th1.st.st.1.regs.X11.toBitVec = 2 := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB2 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue2Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init2 hL _) (ghost2_pend _) (msq2PureSpecW l _)
    (msq2PureSpecW_init l (fun v => ?_) (fun v => ?_) h0 h1) (msqueue2_whole_npSafeF l hL h0 h1 hi) hc hf
    fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
    rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v
  exact msqueue2_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue2_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.enqRuleQ2_noFault
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.deqRuleQ2_noFault
