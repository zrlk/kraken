/-
**`msqueue3.kl` with all three threads running the
whole `.kl` image.** Additive: `MsQueue.msqueue3_envG`
(`EnvG/MsQueue3Public.lean`) is unchanged.

As `EnvG/A64WholeMsQueue1.lean`, for the queue with two competing
dequeuers: the runner's executable is the whole `code` block `msq3Image`
(`enq:`, `enq2Prog`, `NOP`, `deq1:`, `deqProg`, `NOP`, `deq2:`, `deqBProg`,
`NOP`; `msq3Image_eq`) under one layout, each thread from its entry label
(`enq`, `deq1`, `deq2`) to its exit label (`pdone`, `ddone1`, `ddone2`).

- **All three roles are masked**: the enqueuer runs over `msq3ImageE`
  (cells `0 … 42` kept), the first dequeuer over `msq3ImageA` (cells
  `44 … 65`), the second over `msq3ImageB` (cells `67 … 88`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdjM` (`EnvG/A64MaskAdj.lean`).
- **Runs**: the MS queue proof's scripts, unchanged and not repeated: `enq2_envGCAdj_at`,
  `deqA3_envGCAdj_at`, `deqB3_envGCAdj_at` (in the masks) and
  `enq2_relPure_at`, `deq_relPure_at`, `deqB_relPure_at` (purity, in the
  image).
- **Final argument, ghost and resources**: the three-thread MS queue proof's (`MB3`,
  `MsQueue3Final`, `tRes3`, `ghost2`, `start1_init3`, `comDa3_init`,
  `comDb3_init`, `erase_init3`, `pigeon3`, `final_values3`).
-/
import Kraken.Promising.SLR.EnvG.MsQueue3Public
import Kraken.Promising.SLR.EnvG.A64MaskAdj
import Kraken.Promising.SLR.EnvG.A64MaskHelpers
import Kraken.Promising.SLR.EnvG.A64MaskRunAt

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The image and the masks -/

/-- **The `code` block of `msqueue3.kl`, verbatim**: the runner's
executable, shared by the three threads (`P0: enq pdone; P1: deq1 ddone1;
P2: deq2 ddone2`). -/
def msq3Image : Program := parseAArch64("
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
  B ddone1
ddone1:
  NOP
deq2:
deq2a:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq2a_ne
  CBZ X5,deq2a
  MOV X6,X3
  CASAL X6,X5,[X1]
  B deq2a
deq2a_ne:
  CBZ X5,deq2a
  LDR W7,[X5]
  MOV X6,X3
  CASAL X6,X5,[X0]
  CMP X6,X3
  B.NE deq2a
  MOV W10,W7
  B ddone2
ddone2:
  NOP
")

/-- info: (90, 42, 21, 21) -/
#guard_msgs in
#eval (msq3Image.length, enq2Prog.length, deqProg.length, deqBProg.length)

/-- The image is the per-thread texts behind their entry labels, each
followed by a `NOP`. -/
theorem msq3Image_eq : msq3Image[0]? = some (.label "enq") ∧ (msq3Image.drop 1).take 42 = enq2Prog ∧
    msq3Image[44]? = some (.label "deq1") ∧ (msq3Image.drop 45).take 21 = deqProg ∧
    msq3Image[67]? = some (.label "deq2") ∧ (msq3Image.drop 68).take 21 = deqBProg := by decide

/-- **The enqueuer's mask**: cells `0 … 42` (`enq:` to `pdone:`) kept. -/
abbrev msq3ImageE : Program := msq3Image.maskKeep (keepRange 0 43)

/-- **The first dequeuer's mask**: cells `44 … 65` (`deq1:` to `ddone1:`) kept. -/
abbrev msq3ImageA : Program := msq3Image.maskKeep (keepRange 44 66)

/-- **The second dequeuer's mask**: cells `67 … 88` (`deq2:` to `ddone2:`) kept. -/
abbrev msq3ImageB : Program := msq3Image.maskKeep (keepRange 67 89)

/-- Every cell of the image is phase-1 with failing release RMWs. -/
theorem msq3Image_dirs : ∀ d ∈ msq3Image, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any msq3Image

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labQ3 (x : Label) : Int64 := (_root_.Executable.labels (layout msq3Image)).label x

theorem msq3Image_rmwLive : (layout msq3Image).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem msq3Image_noFault : DirsNoFault (layout msq3Image) := by dirs_no_fault' msq3Image

variable [Executable.ValidLayout (layout msq3Image)]

set_option maxRecDepth 8192 in
theorem labQ3_enq : labQ3 "enq" = labQ3 "enq1" :=
  label_addrOf_succ_label (i := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
theorem labQ3_deq1 : labQ3 "deq1" = labQ3 "deq1a" :=
  label_addrOf_succ_label (i := 44) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
theorem labQ3_deq2 : labQ3 "deq2" = labQ3 "deq2a" :=
  label_addrOf_succ_label (i := 67) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- **No step of the enqueuer's mask at `pdone`** (the masked `NOP`). -/
theorem enqQ3_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ3 "pdone" → ¬ (layout msq3ImageE).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 43) msq3Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq3ImageE) (i := 43) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 0 43) (i := 42) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the first dequeuer's mask at `ddone1`** (the masked `NOP`). -/
theorem deqAQ3_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ3 "ddone1" → ¬ (layout msq3ImageA).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 44 66) msq3Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq3ImageA) (i := 66) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 44 66) (i := 65) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the second dequeuer's mask at `ddone2`** (the masked `NOP`). -/
theorem deqBQ3_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ3 "ddone2" → ¬ (layout msq3ImageB).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 67 89) msq3Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq3ImageB) (i := 89) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 67 89) (i := 88) (by decide) (by decide) (by decide) (by decide)))

/-! ## The runs (the MS queue proof's scripts, at the masks and the image) -/

/-- The enqueuer's run over its mask, at the image's labels. -/
theorem enqQ3_envGCAdj (P : Params2) (hL : QLocs2 P) : ∀ s g, enqTable2 P "enq1" s g →
    Safely ((layout msq3ImageE).instrStepEnv (SharedEnv.counted (EE2 P)))
      (fun x => (x.1.2 = labQ3 "pdone" ∧ ComE2 P x.2.1) ∨ False) ((s, labQ3 "enq1"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 43) msq3Image)
  letI : CodeEnv := ⟨layout msq3ImageE⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (enq2_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq3ImageE) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) s g hsg)

/-- The first dequeuer's run over its mask, at the image's labels. -/
theorem deqAQ3_envGCAdj (P : Params2) (hL : QLocs2 P) :
    ∀ s g, deqTable3 P 1 "deq1a" "deq1a_ne" "ddone1" "deq1a" s g →
    Safely ((layout msq3ImageA).instrStepEnv (SharedEnv.counted (ED3 P 1)))
      (fun x => (x.1.2 = labQ3 "ddone1" ∧ Dn3 P 1 x.1.1.regs.X10.toBitVec x.2.1) ∨ False) ((s, labQ3 "deq1a"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 44 66) msq3Image)
  letI : CodeEnv := ⟨layout msq3ImageA⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (deqA3_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq3ImageA) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) s g hsg)

/-- The second dequeuer's run over its mask, at the image's labels. -/
theorem deqBQ3_envGCAdj (P : Params2) (hL : QLocs2 P) :
    ∀ s g, deqTable3 P 2 "deq2a" "deq2a_ne" "ddone2" "deq2a" s g →
    Safely ((layout msq3ImageB).instrStepEnv (SharedEnv.counted (ED3 P 2)))
      (fun x => (x.1.2 = labQ3 "ddone2" ∧ Dn3 P 2 x.1.1.regs.X10.toBitVec x.2.1) ∨ False) ((s, labQ3 "deq2a"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 67 89) msq3Image)
  letI : CodeEnv := ⟨layout msq3ImageB⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (deqB3_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq3ImageB) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone2") (by decide)) s g hsg)

/-- The image as the ambient code (the purity runs). -/
local instance msq3Image.env : CodeEnv := ⟨layout msq3Image⟩

theorem msq3Image_placed : Program.Placed msq3Image "enq" := Program.placed_of_layout (by decide) rfl (by decide)

end Lay

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3Image)]

/-- The whole-image enqueuer's postcondition. -/
abbrev postEQ3 (P : Params2) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ3 "pdone" ∧ ComE2 P x.2) ∨ False

/-- The whole-image first dequeuer's postcondition. -/
abbrev postDAQ3 (P : Params2) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ3 "ddone1" ∧ Dn3 P 1 x.1.1.regs.X10.toBitVec x.2) ∨ False

/-- The whole-image second dequeuer's postcondition. -/
abbrev postDBQ3 (P : Params2) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ3 "ddone2" ∧ Dn3 P 2 x.1.1.regs.X10.toBitVec x.2) ∨ False

omit [Executable.ValidLayout (layout msq3Image)] in
/-- **`hB` for the whole-image enqueuer** (`hB_E3`'s proof). -/
theorem hB_EQ3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postEQ3 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inr hcom.2.2.1)
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout msq3Image)] in
/-- **`hB` for the whole-image first dequeuer** (`hB_DA3`'s proof). -/
theorem hB_DAQ3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDAQ3 P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1.1 rfl⟩
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout msq3Image)] in
/-- **`hB` for the whole-image second dequeuer** (`hB_DB3`'s proof). -/
theorem hB_DBQ3 (P : Params2) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDBQ3 P (t.st.st, σ) → t.prom = [] → EnvRel 2 (planD2 P) σ c t r g cl → cl → MB3 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr (.inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.1.2 rfl⟩)
  · rw [hp] at hts; cases hts

/-- **The whole-image enqueuer's rule** (thread `0`, over its mask). -/
noncomputable def enqRuleQ3 (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postEQ3 P) (maskOf_layout _ _) (planE2_valid P) msq3Image_rmwLive
    (phase1TreeF_maskKeep_range msq3Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (enqQ3_stuck _)
    (hB_EQ3 P)

/-- **The whole-image enqueuer's rule excludes faults.** -/
theorem enqRuleQ3_noFault (P : Params2) : NoFaultRuleF (enqRuleQ3 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq3Image_noFault

/-- **The whole-image first dequeuer's rule** (thread `1`, over its mask). -/
noncomputable def deqARuleQ3 (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postDAQ3 P) (maskOf_layout _ _) (planD2_valid P) msq3Image_rmwLive
    (phase1TreeF_maskKeep_range msq3Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqAQ3_stuck _)
    (hB_DAQ3 P)

/-- **The whole-image first dequeuer's rule excludes faults.** -/
theorem deqARuleQ3_noFault (P : Params2) : NoFaultRuleF (deqARuleQ3 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq3Image_noFault

/-- **The whole-image second dequeuer's rule** (thread `2`, over its mask). -/
noncomputable def deqBRuleQ3 (P : Params2) : ThreadRuleRXF (I := isa) Arch.armv8 (MB3 P) 2 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postDBQ3 P) (maskOf_layout _ _) (planD2_valid P) msq3Image_rmwLive
    (phase1TreeF_maskKeep_range msq3Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqBQ3_stuck _)
    (hB_DBQ3 P)

/-- **The whole-image second dequeuer's rule excludes faults.** -/
theorem deqBRuleQ3_noFault (P : Params2) : NoFaultRuleF (deqBRuleQ3 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq3Image_noFault

end Rules

/-! ## The start -/

/-- **The enqueuer at its start in the whole image**, as the runner sets it
up (`0:X1=tail; 0:X12=n1; 0:X13=n2`): the image, no declarations, pc at
`enq`, end at `pdone`, `x1 = t`, `x12 = n1`, `x13 = n2`, and no private copy
of any 8- or 4-byte word. -/
structure StartEQ3 [layout : _root_.Layout] (t n1 n2 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq3Image
  decls : s.decls = {}
  pc : s.st.2 = labQ3 "enq"
  endPc : s.endPc = labQ3 "pdone"
  x1 : s.st.1.regs.X1.toBitVec = t
  x12 : s.st.1.regs.X12.toBitVec = n1
  x13 : s.st.1.regs.X13.toBitVec = n2
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **A dequeuer at its start in the whole image** (`X0=head; X1=tail`): pc
at the entry label `le`, end at the exit label `lx` (`deq1`/`ddone1` for
thread `1`, `deq2`/`ddone2` for thread `2`). -/
structure StartDQ3 [layout : _root_.Layout] (le lx : Label) (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq3Image
  decls : s.decls = {}
  pc : s.st.2 = labQ3 le
  endPc : s.endPc = labQ3 lx
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq3Image)] {s0 s1 s2 : isa.State}
  {initMem : List (Loc × Val)}

theorem invEQ3_init {P : Params2} (hL : QLocs2 P) (hS : StartEQ3 P.t P.n1 P.n2 s0) :
    (enqRuleQ3 P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 0) (ghost2 P) := by
  refine invGFCAdjM_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s0.st = (s0.st.1, labQ3 "enq1") from Prod.ext rfl (hS.pc.trans labQ3_enq)]
  exact Safely.uncountA (enqQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x1, hS.d8, hS.d4, hS.x13, .inl ⟨rfl, hS.x12, start1_init3 hL _⟩⟩)

theorem invDAQ3_init {P : Params2} (hL : QLocs2 P) (hS : StartDQ3 "deq1" "ddone1" P.h P.t s1)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqARuleQ3 P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 1) (ghost2 P) := by
  refine invGFCAdjM_init (s := s1) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s1.st = (s1.st.1, labQ3 "deq1a") from Prod.ext rfl (hS.pc.trans labQ3_deq1)]
  exact Safely.uncountA (deqAQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comDa3_init P _ hi⟩⟩)

theorem invDBQ3_init {P : Params2} (hL : QLocs2 P) (hS : StartDQ3 "deq2" "ddone2" P.h P.t s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    (deqBRuleQ3 P).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem P 2) (ghost2 P) := by
  refine invGFCAdjM_init (s := s2) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s2.st = (s2.st.1, labQ3 "deq2a") from Prod.ext rfl (hS.pc.trans labQ3_deq2)]
  exact Safely.uncountA (deqBQ3_envGCAdj P hL _ (_, 0)
    ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comDb3_init P _ hi⟩⟩)

end Start

/-- **The `NPSafeF` side, whole image.** -/
theorem msqueue3_whole_npSafeF (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)] {P : Params2}
    (hL : QLocs2 P) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEQ3 (layout := l) P.t P.n1 P.n2 s0) (h1 : StartDQ3 (layout := l) "deq1" "ddone1" P.h P.t s1)
    (h2 : StartDQ3 (layout := l) "deq2" "ddone2" P.h P.t s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem P) :
    ∀ tid, tid < [s0, s1, s2].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB3 P) tid k j True
      (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem).mem P tid) (ghost2 P) := by
  intro tid htid k j
  rcases tid with _ | _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEQ3_init (layout := l) hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDAQ3_init (layout := l) hL h1 hi)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDBQ3_init (layout := l) hL h2 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Purity -/

/-- The threads' purity specifications in the whole image: the enqueuer's
run to `pdone` at thread `0`, the first dequeuer's to `ddone1` at thread
`1`, the second's to `ddone2` elsewhere. -/
def msq3PureSpecW (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.toEnd (l msq3Image) (labQ3 (layout := l) "pdone")
  | 1 => RelPureSpec.toEnd (l msq3Image) (labQ3 (layout := l) "ddone1")
  | _ + 2 => RelPureSpec.toEnd (l msq3Image) (labQ3 (layout := l) "ddone2")

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data words `[n1]`, `[n2]`. -/
theorem msq3PureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)] {rel : Loc → Pred}
    {h t n1 n2 : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v)
    (hd2 : ∀ v : Val, Pred.Pure (rel ⟨n2, 4⟩) v) {s0 s1 s2 : isa.State}
    (h0 : StartEQ3 (layout := l) t n1 n2 s0) (h1 : StartDQ3 (layout := l) "deq1" "ddone1" h t s1)
    (h2 : StartDQ3 (layout := l) "deq2" "ddone2" h t s2) :
    ∀ tid s, [s0, s1, s2][tid]? = some s → (msq3PureSpecW l rel tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, ?_⟩
    rw [show s0.st = (s0.st.1, labQ3 (layout := l) "enq1") from Prod.ext rfl (h0.pc.trans labQ3_enq)]
    letI : CodeEnv := ⟨l msq3Image⟩
    exact Safely.uncountA (enq2_relPure_at rel n1 n2 hd hd2
      (Program.PlacedIn.of_placedE (msq3Image_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "pdone") (by decide)) _ ((), 0) ⟨h0.d8, h0.d4, h0.x13, .inl ⟨rfl, h0.x12⟩⟩)
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, ?_⟩
    rw [show s1.st = (s1.st.1, labQ3 (layout := l) "deq1a") from Prod.ext rfl (h1.pc.trans labQ3_deq1)]
    letI : CodeEnv := ⟨l msq3Image⟩
    exact Safely.uncountA (deq_relPure_at rel
      (Program.PlacedIn.of_placedE (msq3Image_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "ddone1") (by decide)) _ ((), 0) ⟨h1.d8, h1.d4, .inl rfl⟩)
  | 2, s, hs => by
    cases hs
    refine ⟨h2.exe, h2.endPc, h2.decls, ?_⟩
    rw [show s2.st = (s2.st.1, labQ3 (layout := l) "deq2a") from Prod.ext rfl (h2.pc.trans labQ3_deq2)]
    letI : CodeEnv := ⟨l msq3Image⟩
    exact Safely.uncountA (deqB_relPure_at rel
      (Program.PlacedIn.of_placedE (msq3Image_placed (layout := l)) (by decide))
      (Program.last_of_check (lx := "ddone2") (by decide)) _ ((), 0) ⟨h2.d8, h2.d4, .inl rfl⟩)
  | _ + 3, _, hs => by cases hs

/-! ## The theorem -/

/-- **The Michael–Scott queue with two competing dequeuers `msqueue3.kl` for
AArch64 under `Arch.armv8`, all three threads running the whole `.kl` image**
(on `EnvGCAdj`; `forall ((1:X10=1 /\ 2:X10=2) \/ (1:X10=2 /\ 2:X10=1))`).

For a valid layout `l` of the `.kl`'s `code` block `msq3Image` and all
addresses with `msqueue3_envG`'s inequalities: if thread `0` runs the image
from `enq` to `pdone` with `x1 = t`, `x12 = n1`, `x13 = n2`, thread `1` from
`deq1` to `ddone1` and thread `2` from `deq2` to `ddone2`, both with
`x0 = h`, `x1 = t`, all with no declarations and an empty private memory
(`StartEQ3`, `StartDQ3`), and the initial memory has `head = tail = d` and
the three links `0` (`InitV2`), then every final configuration reachable
under `Arch.armv8` has `(1:X10 = 1 ∧ 2:X10 = 2) ∨ (1:X10 = 2 ∧ 2:X10 = 1)`.

This is `msqueue3_envG` with the runner's executable (its per-thread-image
deviation resolved). -/
theorem msqueue3_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l msq3Image)]
    (h t d n1 n2 : BitVec 64)
    (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (hhn2 : h ≠ n2 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (htn2 : t ≠ n2 + 8) (hdn : d ≠ n1) (hdn2 : d ≠ n2) (hn12 : n1 ≠ n2) (hn1 : n1 ≠ 0)
    (hn2 : n2 ≠ 0) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEQ3 (layout := l) t n1 n2 s0) (h1 : StartDQ3 (layout := l) "deq1" "ddone1" h t s1)
    (h2 : StartDQ3 (layout := l) "deq2" "ddone2" h t s2)
    (hi : InitV2 (Config.init [s0, s1, s2] initMem).mem ⟨⟨h, t, d, n1⟩, n2⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1 th2, cfg.threads[1]? = some th1 ∧ cfg.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) := by
  have hL : QLocs2 ⟨⟨h, t, d, n1⟩, n2⟩ := ⟨⟨hht, hhd, hhn, htd, htn, hdn⟩, hhn2, htn2, hdn2, hn12, hn1, hn2⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB3 ⟨⟨h, t, d, n1⟩, n2⟩) (Φ := MsQueue3Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init3 hL _) (ghost2_pend _) (msq3PureSpecW l _)
    (msq3PureSpecW_init l (fun v => ?_) (fun v => ?_) h0 h1 h2) (msqueue3_whole_npSafeF l hL h0 h1 h2 hi)
    hc hf fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost2_rel_ne (not_isW_dat _)]; exact Pred.emp_pure v
  · show Pred.Pure ((ghost2 ⟨⟨h, t, d, n1⟩, n2⟩).rel (Params2.dat2 ⟨⟨h, t, d, n1⟩, n2⟩)) v
    rw [ghost2_rel_ne (not_isW_dat2 _)]; exact Pred.emp_pure v
  exact msqueue3_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.enqRuleQ3_noFault
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.deqARuleQ3_noFault
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.deqBRuleQ3_noFault
