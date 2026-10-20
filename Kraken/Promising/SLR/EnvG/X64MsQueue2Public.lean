/-
**The x64 two-node Michael–Scott queue
`msqueue2.kl`, verbatim, end to end** (on the adjacency environment
`EnvGCAdjX`): `x64_msqueue2_envG_verbatim`, the `.kl`'s property
`1:r12=n1 ∧ 1:r13=n2` at every final configuration reachable under
`Arch.tso`, for the `.kl`'s `code` block as written, run by both threads in
the runner's image `msq2ImageV` (the code, then the data trailer `s`, `n1`,
`n2`, `head`, `tail`), over every valid layout of the image.

- **Parameters** (`paramsV`): the five symbols' addresses. `QLocs` from the
  symbols' distinctness and the nodes' non-nullness (`qLocs_paramsV`; the
  concrete instance discharges them by `decide`).
- **Enqueuer** (thread `0`, entry `enqueuer`, exit `edone`): its exit label
  is followed by code (the dequeuer). The rule is
  `ThreadRuleRXF.ofSafelyEnvGFCAdjXM` (`EnvG/X64MsQueueMaskAdj.lean`) over
  the mask `msq2ImageM` (the cells from `dequeuer:` on are data cells): the
  halt at `edone` is the mask's (`enqM_stuck`), the mask is phase-1
  (`msq2ImageM_phase1FX`).
- **Dequeuer** (thread `1`, entry `dequeuer`, exit `ddone`): its exit is
  followed by the data trailer, so `ThreadRuleRXF.ofSafelyEnvGFCAdjX` at the
  whole image applies (`deqV_stuck`, `msq2ImageV_phase1FX`).
- **Shared postcondition** (`MQX`): the dequeuer done (`DoneD2` of its
  `r12`, `r13`), the initial values and the acquire id `0` of every queue
  word on the resource; or the enqueuer's own token `tokH` whole (`ComE`).
- **Assembly**: `CmpxPublic.final_of_relPureSafelyQX_tsoF'`, purity from
  `enqV_noNT`/`deqV_noNT` (the image, unmasked), initial erasure
  `erase_init`; `tokH_pair_false` excludes both threads holding the token,
  and `final_values` (`EnvG/X64MsQueue2Final.lean`) gives the values.

Start predicates fix only what the runner sets: the image, no declarations,
the entry and exit labels, an empty private memory, the dequeuer's `r12 = 0`
(the runner zeroes the registers the `.kl` does not set), and the `.kl`'s
initial memory (`head = tail = s`, the three links `0`: `InitV`). Not
covered (as for `x64_treiber2_envG_verbatim`): the runner's declarations
(`decls = {}`), final configurations only.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue2VCGen
import Kraken.Promising.SLR.EnvG.X64MsQueueMaskAdj
import Kraken.Promising.SLR.EnvG.X64Treiber2Public

namespace Kraken.Promising.X64.EnvG.MsQueueX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

/-! ## The shared postcondition -/

/-- **The shared postcondition of `msqueue2.kl`**: the dequeuer (thread `1`)
done with its values, the initial values and the acquire id `0` of every
queue word; or the enqueuer's token whole. -/
def MQX (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  (∃ th, c.threads[1]? = some th ∧
    DoneD2 c.mem P (th.st.st.1.regs.get64 .r12) (th.st.st.1.regs.get64 .r13) ∧ InitV c.mem P ∧
    ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨ 1 ≤ (r.wr P.tokH).q

/-- **The `.kl`'s property**: the dequeuer got `n1`, then `n2`. -/
def MsQueue2FinalX (n1 n2 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = n1 ∧ th1.st.st.1.regs.get64 .r13 = n2

/-- **Two threads cannot both hold the enqueuer's token whole.** -/
theorem tokH_pair_false {P : Params} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa}
    (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (h1 : 1 ≤ ((rF i).wr P.tokH).q) (h2 : 1 ≤ ((rF j).wr P.tokH).q) : False := by
  have := E.q_add_le_one hi hj hij P.tokH
  grind

/-! ## The start of each role -/

/-- **`E0` at the start**: the enqueuer's resource `resE` (half of
`head`/`tail`, every other location whole), no forwarding item. -/
theorem e0_init (P : Params) (c : Config isa) : E0 P P.n1 (σInitX c (resE c.mem P) (ghost₀ P)) := by
  have hq : ∀ x, ((σInitX c (resE c.mem P) (ghost₀ P)).r.wr x).q = fracE P x := fun _ => rfl
  have hne : ∀ (a : BitVec 64) (b : Nat), b ≠ 8 → ¬((⟨a, b⟩ : Loc) = P.head ∨ (⟨a, b⟩ : Loc) = P.tail) := by
    rintro a b hb (h | h) <;> (simp only [Params.head, Params.tail, Loc.mk.injEq] at h; omega)
  refine ⟨⟨ghost₀_gw P, fun a => ?_, ?_⟩, .inl ⟨rfl, ?_, ?_⟩⟩
  · rw [hq]; unfold fracE; split <;> grind
  · unfold TokFrozen; rw [hq]; simp [fracE, Params.tokH, hne _ 2 (by decide)]
  · unfold TokFrozen; rw [hq]; simp [fracE, Params.tok1, hne _ 1 (by decide)]
  · unfold TokFrozen; rw [hq]; simp [fracE, Params.tok2, hne _ 1 (by decide)]

/-- **`ComD` at the start**: the dequeuer's resource `resD` (half of
`head`/`tail`, the acquire id `0` of every queue word), the initial values,
no forwarding item. -/
theorem comD_init (P : Params) (c : Config isa) (hi : InitV c.mem P) :
    ComD P (σInitX c (resD c.mem P) (ghost₀ P)) := by
  have hq : ∀ x, ((σInitX c (resD c.mem P) (ghost₀ P)).r.wr x).q = fracD P x := fun _ => rfl
  refine ⟨ghost₀_gw P, ?_, ?_, fun x hx => ?_, hi, ?_⟩
  · rw [hq]; simp [fracD]; grind
  · rw [hq]; simp [fracD]; grind
  · show 1 ≤ (if P.IsW x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx]
  · intro l f hf; simp [σInitX, Views.getFwd] at hf

variable [layout : _root_.Layout]

theorem qLocs_paramsV (hht : symV "head" ≠ symV "tail") (hhs : symV "head" ≠ symV "s")
    (hh1 : symV "head" ≠ symV "n1") (hh2 : symV "head" ≠ symV "n2") (hts : symV "tail" ≠ symV "s")
    (ht1 : symV "tail" ≠ symV "n1") (ht2 : symV "tail" ≠ symV "n2") (hs1 : symV "s" ≠ symV "n1")
    (hs2 : symV "s" ≠ symV "n2") (h12 : symV "n1" ≠ symV "n2") (hn1 : symV "n1" ≠ 0) (hn2 : symV "n2" ≠ 0) :
    QLocs paramsV :=
  ⟨hht, hhs, hh1, hh2, hts, ht1, ht2, hs1, hs2, h12, hn1, hn2⟩

variable [Executable.ValidLayout (layout msq2ImageV)]

/-! ## Shapes and fault-freedom of the image and the mask -/

omit layout [Executable.ValidLayout (layout msq2ImageV)] in
/-- The image's cells are phase-1 (the x64 Treiber proof's popper script). -/
theorem msq2ImageV_dirsPhase1FX : ∀ d ∈ msq2ImageV, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [msq2ImageV, msq2CodeV, msq2DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1FX

/-- **The whole image is phase-1.** -/
theorem msq2ImageV_phase1FX : Phase1TreeFX (layout msq2ImageV) :=
  phase1TreeFX_of_dirs (dirsPhase1FX_layout msq2ImageV_dirsPhase1FX)

/-- **The enqueuer's mask is phase-1** (its kept cells are the image's). -/
theorem msq2ImageM_phase1FX : Phase1TreeFX (layout msq2ImageM) :=
  phase1TreeFX_maskKeep_range fun d hd => msq2ImageV_dirsPhase1FX d (List.mem_of_mem_drop (List.mem_of_mem_take hd))

omit [Executable.ValidLayout (layout msq2ImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem msq2ImageV_noFaultCode : DirsNoFaultCode (layout msq2ImageV) := by
  dirs_no_fault_code msq2ImageV msq2CodeV msq2DataV

/-! ## The rules -/

/-- The enqueuer's postcondition: the exit label and `ComE`. -/
abbrev postEV (P : Params) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labV "edone" ∧ ComE P x.2) ∨ False

omit [Executable.ValidLayout (layout msq2ImageV)] in
theorem postEV_end (P : Params) : ∀ y, postEV P y → y.1.2 = labV "edone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout msq2ImageV)] in
/-- **`hB` for the enqueuer**: its token, whole. -/
theorem hB_EV (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postEV P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MQX P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hcom.2.2
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 enqueuer's rule** (thread `0`, layout `sAll`), over
the mask `msq2ImageM`. -/
noncomputable def enqRuleV (P : Params) : ThreadRuleRXF (I := isa) Arch.tso (MQX P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXM (S := sAll) (post := postEV P) msq2ImageM_mask (planE_valid P) sAll_le16
    msq2ImageM_phase1FX (postEV_end P) (enqM_stuck _) (hB_EV P)

/-- **The verbatim enqueuer's rule excludes faults.** -/
theorem enqRuleV_noFault (P : Params) : NoFaultRuleF (enqRuleV P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjXM _ _ _ _ _ _ _ msq2ImageV_noFaultCode

/-- The dequeuer's postcondition: the exit label and `Dn`. -/
abbrev postDV (P : Params) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labV "ddone" ∧ Dn P (x.1.1.regs.get64 .r12) (x.1.1.regs.get64 .r13) x.2) ∨ False

omit [Executable.ValidLayout (layout msq2ImageV)] in
theorem postDV_end (P : Params) : ∀ y, postDV P y → y.1.2 = labV "ddone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout msq2ImageV)] in
/-- **`hB` for the dequeuer**: `Dn` at the anchor gives `DoneD2` at the
configuration. -/
theorem hB_DV (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postDV P (t.st.st, σ) → t.prom = [] → EnvRel 1 (planD P) σ c t r g cl → cl → MQX P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl ⟨t, hrel.ht, hd.mono hpre, hcom.2.2.2.2.1.of_init hrel.snap.init, hcom.2.2.2.1⟩
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 dequeuer's rule** (thread `1`, layout `sAll`, the
whole image). -/
noncomputable def deqRuleV (P : Params) : ThreadRuleRXF (I := isa) Arch.tso (MQX P) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjX (S := sAll) (post := postDV P) (planD_valid P) sAll_le16
    msq2ImageV_phase1FX (postDV_end P) (deqV_stuck _) (hB_DV P)

/-- **The verbatim dequeuer's rule excludes faults** (unconditional in
promises). -/
theorem deqRuleV_noFault (P : Params) : NoFaultRuleF (deqRuleV P) := by
  unfold deqRuleV ThreadRuleRXF.ofSafelyEnvGFCAdjX
  exact noFaultRuleF_ofEnvGFCAdj_struct _ _
    (Treiber2X.noFault_QX64CAdjCode msq2ImageV_noFaultCode (postDV_end P))

/-! ## The start -/

/-- **The verbatim enqueuer at its start**, as the runner sets it up: the
image, no declarations, pc at `enqueuer`, end at `edone`, an empty private
memory. -/
structure StartEV (s : State) : Prop where
  exe : s.exe = layout msq2ImageV
  decls : s.decls = {}
  pc : s.st.2 = labV "enqueuer"
  endPc : s.endPc = labV "edone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **The verbatim dequeuer at its start**: the image, no declarations, pc at
`dequeuer`, end at `ddone`, `r12 = 0` (the runner's zeroed registers), an
empty private memory. -/
structure StartDV (s : State) : Prop where
  exe : s.exe = layout msq2ImageV
  decls : s.decls = {}
  pc : s.st.2 = labV "dequeuer"
  endPc : s.endPc = labV "ddone"
  r12 : s.st.1.regs.get64 .r12 = 0
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit layout [Executable.ValidLayout (layout msq2ImageV)] in
theorem d8_of_dmem {s : State} (h : ∀ k, s.st.1.dmem.get? k = none) : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none :=
  fun a => (split_sAll h).loadInt_none (mem_sAll8 a) (by decide) (by decide)

section Start

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim enqueuer's initial invariant.** -/
theorem invEV_init (hL : QLocs paramsV) (hS : StartEV s0) :
    (enqRuleV paramsV).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem paramsV 0) (ghost₀ paramsV) := by
  have hst : s0.st = (s0.st.1, labV "enqueuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXM_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (enqM_envGCAdj paramsV hL rfl rfl rfl rfl s0.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, e0_init paramsV _⟩)

/-- **The verbatim dequeuer's initial invariant.** -/
theorem invDV_init (hL : QLocs paramsV) (hS : StartDV s1) (hi : InitV (Config.init [s0, s1] initMem).mem paramsV) :
    (deqRuleV paramsV).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem paramsV 1) (ghost₀ paramsV) := by
  have hst : s1.st = (s1.st.1, labV "dequeuer") := Prod.ext rfl hS.pc
  refine invGFCAdjX_init (s := s1) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (deqV_envGCAdj' paramsV hL rfl rfl rfl s1.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, comD_init paramsV _ hi, hS.r12⟩)

end Start

/-! ## Purity -/

/-- The threads' all-release specifications (the image, unmasked). -/
noncomputable def msq2NoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := sAll
      le16 := sAll_le16
      e := layout msq2ImageV
      valid := inferInstance
      endPc := labV "edone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV "edone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := sAll
      le16 := sAll_le16
      e := layout msq2ImageV
      valid := inferInstance
      endPc := labV "ddone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV "ddone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem msq2NoNTSpecV_init {s0 s1 : State} (h0 : StartEV s0) (h1 : StartDV s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (msq2NoNTSpecV tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, split_sAll h0.dmem, ?_⟩
    rw [show s0.st = (s0.st.1, labV "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enqV_noNT _ ((), 0) (d8_of_dmem h0.dmem))
  | 1, s, hs => by
    cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, split_sAll h1.dmem, ?_⟩
    rw [show s1.st = (s1.st.1, labV "dequeuer") from Prod.ext rfl h1.pc]
    exact TreiberAbs.Safely.uncountT (deqV_noNT _ ((), 0) (d8_of_dmem h1.dmem))
  | _ + 2, s, hs => by simp at hs

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for the verbatim `msqueue2`.** -/
theorem msq2V_npSafeF (hL : QLocs paramsV) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV s0) (h1 : StartDV s1) (hi : InitV (Config.init [s0, s1] initMem).mem paramsV) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.tso (MQX paramsV) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem paramsV tid) (ghost₀ paramsV) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEV_init hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV_init hL h1 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The two-node Michael–Scott queue `LockFree/X64/msqueue2.kl` for x64
under `Arch.tso`, the `.kl`'s code verbatim**: for every valid layout of the
image `msq2ImageV` (the `code` block, then the runner's data trailer placing
`s`, `n1`, `n2`, `head`, `tail`) in which the five symbols have distinct
addresses and the nodes are non-null, if thread `0` starts at `enqueuer`
with end `edone` and an empty private memory (`StartEV`), thread `1` at
`dequeuer` with end `ddone`, `r12 = 0` and an empty private memory
(`StartDV`), and the initial memory is the `.kl`'s (`head = tail = s`, the
links of `s`, `n1`, `n2` zero: `InitV`), then every final configuration
reachable under `Arch.tso` has `r12 = n1` and `r13 = n2` in the dequeuer
(the `.kl`'s `forall (1:r12=n1 /\ 1:r13=n2)`). -/
theorem x64_msqueue2_envG_verbatim {fuel : Nat} (hht : symV "head" ≠ symV "tail")
    (hhs : symV "head" ≠ symV "s") (hh1 : symV "head" ≠ symV "n1") (hh2 : symV "head" ≠ symV "n2")
    (hts : symV "tail" ≠ symV "s") (ht1 : symV "tail" ≠ symV "n1") (ht2 : symV "tail" ≠ symV "n2")
    (hs1 : symV "s" ≠ symV "n1") (hs2 : symV "s" ≠ symV "n2") (h12 : symV "n1" ≠ symV "n2")
    (hn1 : symV "n1" ≠ 0) (hn2 : symV "n2" ≠ 0) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV s0) (h1 : StartDV s1) (hi : InitV (Config.init [s0, s1] initMem).mem paramsV)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th1, cfg.threads[1]? = some th1 ∧ th1.st.st.1.regs.get64 .r12 = symV "n1" ∧
      th1.st.st.1.regs.get64 .r13 = symV "n2" := by
  have hL := qLocs_paramsV hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' (B := MQX paramsV)
    (Φ := MsQueue2FinalX (symV "n1") (symV "n2"))
    (erase_init hL _) (ghost₀_pend _) msq2NoNTSpecV (msq2NoNTSpecV_init h0 h1)
    (msq2V_npSafeF hL h0 h1 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw paramsV).mono hle
  have fin : ∀ i, i < cfg.threads.size → (∃ th, cfg.threads[1]? = some th ∧
      DoneD2 cfg.mem paramsV (th.st.st.1.regs.get64 .r12) (th.st.st.1.regs.get64 .r13) ∧
      InitV cfg.mem paramsV ∧ ∀ x, paramsV.IsW x → 1 ≤ (rF' i).acq x 0) →
      MsQueue2FinalX (symV "n1") (symV "n2") cfg := by
    rintro i hi ⟨th, hth, hd, hiv, hacq⟩
    exact ⟨th, hth, final_values E' hW hL hiv
      (fun x hx => TreiberCommon.total_acq_of_ge E' hi (hacq x hx)) hd⟩
  rcases hB 0 (Config.final_done hf hi0) with hd0 | hq0
  · exact fin 0 hi0 hd0
  rcases hB 1 (Config.final_done hf hi1) with hd1 | hq1
  · exact fin 1 hi1 hd1
  exact (tokH_pair_false E' hi0 hi1 (by decide) hq0 hq1).elim

end Kraken.Promising.X64.EnvG.MsQueueX

#print axioms Kraken.Promising.X64.EnvG.MsQueueX.x64_msqueue2_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.MsQueueX.enqRuleV_noFault
#print axioms Kraken.Promising.X64.EnvG.MsQueueX.deqRuleV_noFault
