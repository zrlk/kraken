/-
**`msqueue1.kl` with both threads running the
whole `.kl` image.** Additive: `MsQueue.msqueue1_envG`
(`EnvG/MsQueuePublic.lean`) is unchanged.

`msqueue1_envG` runs each thread over its own text (`enqProg`, `deqProg`),
each with its own layout. The runner's executable is the whole `code` block
`msq1Image` (`enq:`, `enqProg`, the dead `NOP` behind `pdone:`, `deq1:`,
`deqProg`, the `NOP` behind `ddone1:`; `msq1Image_eq`) under one layout, each
thread from its entry label (`enq`, `deq1`) to its exit label (`pdone`,
`ddone1`), as `Kraken.Litmus.AArch64.prepareProgram` sets them up.

- **Both roles are masked**, since both exit labels are followed by a
  `NOP`: the enqueuer runs over `msq1ImageE` (cells `0 … 22` kept), the
  dequeuer over `msq1ImageD` (cells `24 … 45`); the other cells are data
  cells, so the halt at the exit label is read off the mask
  (`label_addrOf_succ_maskKeep`, `not_instrStepEnv_of_byteArray`).
- **Rules**: `ThreadRuleRXF.ofSafelyEnvGFCAdjM` (`EnvG/A64MaskAdj.lean`).
- **Runs**: the MS queue proof's scripts, unchanged and not repeated: `enq_envGCAdj_at`,
  `deq_envGCAdj_at` (in the masks) and `enq_relPure_at`, `deq_relPure_at`
  (purity, in the image) (`EnvG/A64MaskRunAt.lean`). The entry labels share
  their address with the texts' first labels (`labQ1_enq`, `labQ1_deq1`).
- **Final argument, ghost and resources**: the MS queue proof's (`MB`, `MsQueue1Final`,
  `tRes`, `ghost₀`, `e0_init`, `comD_init`, `erase_init`, `final_value`,
  `tokE_pair_false`).
-/
import Kraken.Promising.SLR.EnvG.MsQueuePublic
import Kraken.Promising.SLR.EnvG.A64MaskAdj
import Kraken.Promising.SLR.EnvG.A64MaskHelpers
import Kraken.Promising.SLR.EnvG.A64MaskRunAt

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-! ## The image and the masks -/

/-- **The `code` block of `msqueue1.kl`, verbatim**: the runner's
executable, shared by both threads (`P0: enq pdone; P1: deq1 ddone1`). -/
def msq1Image : Program := parseAArch64("
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
")

/-- info: (47, 22, 21) -/
#guard_msgs in
#eval (msq1Image.length, enqProg.length, deqProg.length)

/-- The image is the per-thread texts behind their entry labels, each
followed by a `NOP`. -/
theorem msq1Image_eq : msq1Image[0]? = some (.label "enq") ∧ (msq1Image.drop 1).take 22 = enqProg ∧
    msq1Image[24]? = some (.label "deq1") ∧ (msq1Image.drop 25).take 21 = deqProg := by decide

/-- **The enqueuer's mask**: cells `0 … 22` (`enq:` to `pdone:`) kept. -/
abbrev msq1ImageE : Program := msq1Image.maskKeep (keepRange 0 23)

/-- **The dequeuer's mask**: cells `24 … 45` (`deq1:` to `ddone1:`) kept. -/
abbrev msq1ImageD : Program := msq1Image.maskKeep (keepRange 24 46)

/-- Every cell of the image is phase-1 with failing release RMWs. -/
theorem msq1Image_dirs : ∀ d ∈ msq1Image, ∀ (e : _root_.Executable) z, DirPhase1F e d z := by
  dirs_phase1F_any msq1Image

section Lay

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labQ1 (x : Label) : Int64 := (_root_.Executable.labels (layout msq1Image)).label x

theorem msq1Image_rmwLive : (layout msq1Image).rmwLive = true := by rw [Layout.apply_rmwLive]; decide

theorem msq1Image_noFault : DirsNoFault (layout msq1Image) := by dirs_no_fault' msq1Image

variable [Executable.ValidLayout (layout msq1Image)]

set_option maxRecDepth 8192 in
theorem labQ1_enq : labQ1 "enq" = labQ1 "enq1" :=
  label_addrOf_succ_label (i := 0) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
theorem labQ1_deq1 : labQ1 "deq1" = labQ1 "deq1a" :=
  label_addrOf_succ_label (i := 24) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxRecDepth 8192 in
/-- **No step of the enqueuer's mask at `pdone`** (the masked `NOP`). -/
theorem enqQ1_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ1 "pdone" → ¬ (layout msq1ImageE).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 23) msq1Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq1ImageE) (i := 23) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 0 23) (i := 22) (by decide) (by decide) (by decide) (by decide)))

set_option maxRecDepth 8192 in
/-- **No step of the dequeuer's mask at `ddone1`** (the masked `NOP`). -/
theorem deqQ1_stuck (env : SharedEnv) : ∀ x R, x.1.2 = labQ1 "ddone1" → ¬ (layout msq1ImageD).instrStepEnv env x R := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 24 46) msq1Image)
  intro x R hx
  exact not_instrStepEnv_of_byteArray (q := msq1ImageD) (i := 46) (b := .mk #[]) env (by decide) x R
    (hx.trans (label_addrOf_succ_maskKeep (keepRange 24 46) (i := 45) (by decide) (by decide) (by decide) (by decide)))

/-! ## The runs (the MS queue proof's scripts, at the masks and the image) -/

/-- The enqueuer's run over its mask, at the image's labels. -/
theorem enqQ1_envGCAdj (P : Params) (hL : QLocs P) : ∀ s g, enqTable P "enq1" s g →
    Safely ((layout msq1ImageE).instrStepEnv (SharedEnv.counted (EE P)))
      (fun x => (x.1.2 = labQ1 "pdone" ∧ ComE P x.2.1) ∨ False) ((s, labQ1 "enq1"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 0 23) msq1Image)
  letI : CodeEnv := ⟨layout msq1ImageE⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (enq_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq1ImageE) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "pdone") (by decide)) s g hsg)

/-- The dequeuer's run over its mask, at the image's labels. -/
theorem deqQ1_envGCAdj (P : Params) (hL : QLocs P) : ∀ s g, deqTable P "deq1a" s g →
    Safely ((layout msq1ImageD).instrStepEnv (SharedEnv.counted (ED P)))
      (fun x => (x.1.2 = labQ1 "ddone1" ∧ Dn P x.1.1.regs.X10.toBitVec x.2.1) ∨ False) ((s, labQ1 "deq1a"), g) := by
  haveI := ValidLayout.of_mask (maskOf_layout (layout := layout) (keepRange 24 46) msq1Image)
  letI : CodeEnv := ⟨layout msq1ImageD⟩
  intro s g hsg
  exact Safely.atImageLabels (maskOf_layout _ _) (deq_envGCAdj_at P hL (Program.PlacedIn.of_placedE
    (Program.placed_of_layout (p := msq1ImageD) (by decide) rfl (by decide)) (by decide))
    (Program.last_of_check (lx := "ddone1") (by decide)) s g hsg)

/-- The image as the ambient code (the purity runs). -/
local instance msq1Image.env : CodeEnv := ⟨layout msq1Image⟩

theorem msq1Image_placed : Program.Placed msq1Image "enq" := Program.placed_of_layout (by decide) rfl (by decide)

end Lay

/-! ## The rules -/

section Rules

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq1Image)]

/-- The whole-image enqueuer's postcondition. -/
abbrev postEQ1 (P : Params) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ1 "pdone" ∧ ComE P x.2) ∨ False

/-- The whole-image dequeuer's postcondition. -/
abbrev postDQ1 (P : Params) : MachineState × EStateA → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labQ1 "ddone1" ∧ Dn P x.1.1.regs.X10.toBitVec x.2) ∨ False

omit [Executable.ValidLayout (layout msq1Image)] in
/-- **`hB` for the whole-image enqueuer** (`hB_E`'s proof). -/
theorem hB_EQ1 (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postEQ1 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MB P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

omit [Executable.ValidLayout (layout msq1Image)] in
/-- **`hB` for the whole-image dequeuer** (`hB_D`'s proof). -/
theorem hB_DQ1 (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postDQ1 P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD P) σ c t r g cl → cl → MB P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The whole-image enqueuer's rule** (thread `0`, over its mask). -/
noncomputable def enqRuleQ1 (P : Params) : ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postEQ1 P) (maskOf_layout _ _) (planE_valid P) msq1Image_rmwLive
    (phase1TreeF_maskKeep_range msq1Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (enqQ1_stuck _)
    (hB_EQ1 P)

/-- **The whole-image enqueuer's rule excludes faults.** -/
theorem enqRuleQ1_noFault (P : Params) : NoFaultRuleF (enqRuleQ1 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq1Image_noFault

/-- **The whole-image dequeuer's rule** (thread `1`, over its mask). -/
noncomputable def deqRuleQ1 (P : Params) : ThreadRuleRXF (I := isa) Arch.armv8 (MB P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjM (post := postDQ1 P) (maskOf_layout _ _) (planD_valid P) msq1Image_rmwLive
    (phase1TreeF_maskKeep_range msq1Image_dirs) (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (deqQ1_stuck _)
    (hB_DQ1 P)

/-- **The whole-image dequeuer's rule excludes faults.** -/
theorem deqRuleQ1_noFault (P : Params) : NoFaultRuleF (deqRuleQ1 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjM _ _ _ _ _ _ _ msq1Image_noFault

end Rules

/-! ## The start -/

/-- **The enqueuer at its start in the whole image**, as the runner sets it
up (`0:X1=tail; 0:X12=n1`): the image, no declarations, pc at `enq`, end at
`pdone`, `x1 = t`, `x12 = n1`, and no private copy of any 8- or 4-byte
word. -/
structure StartEQ1 [layout : _root_.Layout] (t n1 : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq1Image
  decls : s.decls = {}
  pc : s.st.2 = labQ1 "enq"
  endPc : s.endPc = labQ1 "pdone"
  x1 : s.st.1.regs.X1.toBitVec = t
  x12 : s.st.1.regs.X12.toBitVec = n1
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

/-- **The dequeuer at its start in the whole image** (`1:X0=head;
1:X1=tail`): pc at `deq1`, end at `ddone1`. -/
structure StartDQ1 [layout : _root_.Layout] (h t : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout msq1Image
  decls : s.decls = {}
  pc : s.st.2 = labQ1 "deq1"
  endPc : s.endPc = labQ1 "ddone1"
  x0 : s.st.1.regs.X0.toBitVec = h
  x1 : s.st.1.regs.X1.toBitVec = t
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none
  d4 : ∀ a, Mem.loadInt s.st.1.dmem a 4 = none

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout msq1Image)] {s0 s1 : isa.State}
  {initMem : List (Loc × Val)}

theorem invEQ1_init {P : Params} (hL : QLocs P) (hS : StartEQ1 P.t P.n1 s0) :
    (enqRuleQ1 P).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P 0)
      (ghost₀ P) := by
  refine invGFCAdjM_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s0.st = (s0.st.1, labQ1 "enq1") from Prod.ext rfl (hS.pc.trans labQ1_enq)]
  exact Safely.uncountA (enqQ1_envGCAdj P hL _ (_, 0) ⟨hS.x1, hS.d8, hS.d4, .inl ⟨rfl, hS.x12, e0_init P _⟩⟩)

theorem invDQ1_init {P : Params} (hL : QLocs P) (hS : StartDQ1 P.h P.t s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    (deqRuleQ1 P).Inv True (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P 1)
      (ghost₀ P) := by
  refine invGFCAdjM_init (s := s1) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, ?_⟩
  rw [show s1.st = (s1.st.1, labQ1 "deq1a") from Prod.ext rfl (hS.pc.trans labQ1_deq1)]
  exact Safely.uncountA (deqQ1_envGCAdj P hL _ (_, 0) ⟨hS.x0, hS.x1, hS.d8, hS.d4, .inl ⟨rfl, comD_init P _ hi⟩⟩)

end Start

/-- **The `NPSafeF` side, whole image.** -/
theorem msqueue1_whole_npSafeF (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)] {P : Params}
    (hL : QLocs P) {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartEQ1 (layout := l) P.t P.n1 s0)
    (h1 : StartDQ1 (layout := l) P.h P.t s1) (hi : InitV (Config.init [s0, s1] initMem).mem P) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.armv8 (MB P) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem P tid) (ghost₀ P) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEQ1_init (layout := l) hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDQ1_init (layout := l) hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-! ## Purity -/

/-- The threads' purity specifications in the whole image: the enqueuer's
run to `pdone` at thread `0`, the dequeuer's to `ddone1` elsewhere. -/
def msq1PureSpecW (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)] (rel : Loc → Pred) :
    Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.toEnd (l msq1Image) (labQ1 (layout := l) "pdone")
  | _ + 1 => RelPureSpec.toEnd (l msq1Image) (labQ1 (layout := l) "ddone1")

/-- **The purity specifications hold at the start states**, for release
predicates pure at the data word `[n1]`. -/
theorem msq1PureSpecW_init (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)] {rel : Loc → Pred}
    {h t n1 : BitVec 64} (hd : ∀ v : Val, Pred.Pure (rel ⟨n1, 4⟩) v) {s0 s1 : isa.State}
    (h0 : StartEQ1 (layout := l) t n1 s0) (h1 : StartDQ1 (layout := l) h t s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msq1PureSpecW l rel tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, ?_⟩
    rw [show s0.st = (s0.st.1, labQ1 (layout := l) "enq1") from Prod.ext rfl (h0.pc.trans labQ1_enq)]
    letI : CodeEnv := ⟨l msq1Image⟩
    exact Safely.uncountA (enq_relPure_at rel n1 hd
      (Program.PlacedIn.of_placedE (msq1Image_placed (layout := l)) (by decide)) (Program.last_of_check (lx := "pdone") (by decide))
      _ ((), 0) ⟨h0.d8, h0.d4, .inl ⟨rfl, h0.x12⟩⟩)
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, ?_⟩
    rw [show s1.st = (s1.st.1, labQ1 (layout := l) "deq1a") from Prod.ext rfl (h1.pc.trans labQ1_deq1)]
    letI : CodeEnv := ⟨l msq1Image⟩
    exact Safely.uncountA (deq_relPure_at rel
      (Program.PlacedIn.of_placedE (msq1Image_placed (layout := l)) (by decide)) (Program.last_of_check (lx := "ddone1") (by decide))
      _ ((), 0) ⟨h1.d8, h1.d4, .inl rfl⟩)
  | _ + 2, _, hs => by cases hs

/-! ## The theorem -/

/-- **The one-node Michael–Scott queue `msqueue1.kl` for AArch64 under
`Arch.armv8`, both threads running the whole `.kl` image** (on `EnvGCAdj`;
`forall (1:X10=1)`).

For a valid layout `l` of the `.kl`'s `code` block `msq1Image`, all
addresses `h` of `head`, `t` of `tail` (8 bytes), `d` of the dummy node and
`n1` of the enqueued node (data `[n]`, 4 bytes; link `[n + 8]`, 8 bytes)
with `msqueue1_envG`'s inequalities: if thread `0` runs the image from `enq`
to `pdone` with `x1 = t`, `x12 = n1` and thread `1` from `deq1` to `ddone1`
with `x0 = h`, `x1 = t`, each with no declarations and an empty private
memory (`StartEQ1`, `StartDQ1`), and the initial memory has
`head = tail = d` and both links `0` (`InitV`), then every final
configuration reachable under `Arch.armv8` has `1:X10 = 1`.

This is `msqueue1_envG` with the runner's executable (its per-thread-image
deviation resolved). As there, only the addresses' `Loc`s are
distinguished, faults are covered by `enqRuleQ1_noFault`/`deqRuleQ1_noFault`,
and the threads have no declarations. -/
theorem msqueue1_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l msq1Image)]
    (h t d n1 : BitVec 64) (hht : h ≠ t) (hhd : h ≠ d + 8) (hhn : h ≠ n1 + 8) (htd : t ≠ d + 8)
    (htn : t ≠ n1 + 8) (hdn : d ≠ n1) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEQ1 (layout := l) t n1 s0) (h1 : StartDQ1 (layout := l) h t s1)
    (hi : InitV (Config.init [s0, s1] initMem).mem ⟨h, t, d, n1⟩)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 := by
  have hL : QLocs ⟨h, t, d, n1⟩ := ⟨hht, hhd, hhn, htd, htn, hdn⟩
  refine final_of_relPureSafelyF Arch.armv8 fuel (B := MB ⟨h, t, d, n1⟩) (Φ := MsQueue1Final)
    (fun _ hc' => Config.ntFree_armv8 hc') (erase_init hL _) (ghost₀_pend _) (msq1PureSpecW l _)
    (msq1PureSpecW_init l (fun v => ?_) h0 h1) (msqueue1_whole_npSafeF l hL h0 h1 hi) hc hf
    fun rF' g' E' hle hsize hB => ?_
  · show Pred.Pure ((ghost₀ ⟨h, t, d, n1⟩).rel (Params.dat ⟨h, t, d, n1⟩)) v
    rw [ghost₀_rel_ne (not_isQ_dat _)]; exact Pred.emp_pure v
  exact msqueue1_final_of_hB hL hf E' hle hsize hB

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_whole
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.enqRuleQ1_noFault
#print axioms Kraken.Promising.SLR.EnvG.MsQueue.deqRuleQ1_noFault
