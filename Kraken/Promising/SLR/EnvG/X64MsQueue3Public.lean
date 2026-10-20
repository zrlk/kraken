/-
**Msqueue3 part 5: the x64 Michael–Scott
queue `msqueue3.kl` (one enqueuer, two try-once dequeuers), verbatim, end to
end** (on the adjacency environment `EnvGCAdjX`): `x64_msqueue3_envG_verbatim`,
the `.kl`'s five outcomes of `(1:r12, 2:r12)` — `(n1,n2)`, `(n2,n1)`,
`(n1,0)`, `(0,n1)`, `(0,0)` — at every final configuration reachable under
`Arch.tso`, for the `.kl`'s `code` block as written, run by the three threads
in the runner's image `msq3ImageV` (the code, then the data trailer `s`, `n1`,
`n2`, `head`, `tail`), over every valid layout of the image.

- **Parameters** (`params3V`): the five symbols' addresses, tracking the
  `head` swings (`trk = true`: a `head` write carries its writer's pop token).
- **Enqueuer** (thread `0`, `enqueuer` to `edone`): `msqueue2`'s enqueuer
  over the mask `msq3ImageM` (`ThreadRuleRXF.ofSafelyEnvGFCAdjXM`).
- **Dequeuers** (threads `1`, `2`, `dequeuer` to `ddone`): one rule generic
  in the thread (`deqRule3`, `ThreadRuleRXF.ofSafelyEnvGFCAdjX` over the
  whole image).
- **Shared postcondition** (`MQ3`): each thread holds its own mark whole (the
  enqueuer's is `tokH`); a dequeuer also has its record `DoneD3` and the
  initial values, dequeuer `1` the acquire id `0` of every queue word.
- **Assembly**: `CmpxPublic.final_of_relPureSafelyQX_tsoF'`, purity from
  `enq3V_noNT`/`deq3V_noNT`, initial erasure `erase_init3`. The three marks
  are in three different threads (`mark_pair_false`), so the dequeuers'
  disjuncts both occur, and `final_values3` gives the outcomes.

Start predicates fix only what the runner sets: the image, no declarations,
the entry and exit labels, an empty private memory, and the `.kl`'s initial
memory (`InitV`). Not covered (as for `x64_msqueue2_envG_verbatim`): the
runner's declarations (`decls = {}`), final configurations only.
-/
import Kraken.Promising.SLR.EnvG.X64MsQueue3VCGen
import Kraken.Promising.SLR.EnvG.X64MsQueue2Public

namespace Kraken.Promising.X64.EnvG.MsQueue3X

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.X64.EnvG.MsQueueX
open Kraken.Promising.X64.EnvG.TreiberX (sAll sAll_le16 mem_sAll8 split_sAll)

/-! ## The shared postcondition -/

/-- **The shared postcondition of `msqueue3.kl`**: the enqueuer's mark
whole; or dequeuer `w`'s mark whole, its record, the initial values, and
(dequeuer `1`) the acquire id `0` of every queue word. -/
def MQ3 (P : Params) (c : Config isa) (r : Res) (_ : Ghost) : Prop :=
  TokFrozen (markT P 0) r ∨
    (TokFrozen (markT P 1) r ∧ ∃ th, c.threads[1]? = some th ∧
      DoneD3 c.mem P 1 r (th.st.st.1.regs.get64 .r12) ∧ InitV c.mem P ∧ ∀ x, P.IsW x → 1 ≤ r.acq x 0) ∨
    (TokFrozen (markT P 2) r ∧ ∃ th, c.threads[2]? = some th ∧
      DoneD3 c.mem P 2 r (th.st.st.1.regs.get64 .r12) ∧ InitV c.mem P)

/-- **The `.kl`'s property**: the five outcomes of the two dequeuers. -/
def MsQueue3FinalX (n1 n2 : BitVec 64) (c : Config isa) : Prop :=
  ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
    let x1 := th1.st.st.1.regs.get64 .r12
    let x2 := th2.st.st.1.regs.get64 .r12
    (x1 = n1 ∧ x2 = n2) ∨ (x1 = n2 ∧ x2 = n1) ∨ (x1 = n1 ∧ x2 = 0) ∨ (x1 = 0 ∧ x2 = n1) ∨ (x1 = 0 ∧ x2 = 0)

/-- **Two threads cannot both hold a mark whole.** -/
theorem mark_pair_false {P : Params} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config isa}
    (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    {w : Nat} (h1 : TokFrozen (markT P w) (rF i)) (h2 : TokFrozen (markT P w) (rF j)) : False := by
  have := E.q_add_le_one hi hj hij (markT P w)
  unfold TokFrozen at h1 h2
  grind

/-! ## The start of each role -/

/-- **`E0` at the start**: the enqueuer's resource `resE3`. -/
theorem e0_init3 (P : Params) (c : Config isa) : E0 P P.n1 (σInitX c (resE3 c.mem P) (ghost₀ P)) := by
  have hq : ∀ x, ((σInitX c (resE3 c.mem P) (ghost₀ P)).r.wr x).q = fracE3 P x := fun _ => rfl
  have hne : ∀ (a : BitVec 64) (b : Nat), b ≠ 8 → ¬((⟨a, b⟩ : Loc) = P.head ∨ (⟨a, b⟩ : Loc) = P.tail) := by
    rintro a b hb (h | h) <;> (simp only [Params.head, Params.tail, Loc.mk.injEq] at h; omega)
  have hnd : ∀ (a : BitVec 64) (b : Nat), b ≤ 8 → b ≠ 3 → b ≠ 4 → ¬ DOwn P ⟨a, b⟩ := by
    rintro a b hb h3 h4 (h | h | h | h) <;>
      (simp only [markT, Params.popTok, Loc.mk.injEq] at h; omega)
  refine ⟨⟨ghost₀_gw P, fun a => ?_, ?_⟩, .inl ⟨rfl, ?_, ?_⟩⟩
  · rw [hq]; unfold fracE3; split
    · grind
    · simp only [hnd a 8 (by decide) (by decide) (by decide), ite_false]; grind
  · unfold TokFrozen; rw [hq]
    simp [fracE3, Params.tokH, hne _ 2 (by decide), hnd _ 2 (by decide) (by decide) (by decide)]
  · unfold TokFrozen; rw [hq]
    simp [fracE3, Params.tok1, hne _ 1 (by decide), hnd _ 1 (by decide) (by decide) (by decide)]
  · unfold TokFrozen; rw [hq]
    simp [fracE3, Params.tok2, hne _ 1 (by decide), hnd _ 1 (by decide) (by decide) (by decide)]

/-- **`L0` at the start**: dequeuer `w`'s resource `resD3`, the initial
values, no forwarding item. -/
theorem l0_init3 (P : Params) (w : Nat) (hw : w ≤ 2) (c : Config isa) (hi : InitV c.mem P) :
    L0 P w (σInitX c (resD3 c.mem P w) (ghost₀ P)) := by
  have hq : ∀ x, ((σInitX c (resD3 c.mem P w) (ghost₀ P)).r.wr x).q = fracD3 P w x := fun _ => rfl
  have hm : ¬ (markT P w = P.head ∨ markT P w = P.tail) := by
    rintro (h | h) <;> exact markT_ne_8 P w hw _ h
  have hp : ¬ (P.popTok w = P.head ∨ P.popTok w = P.tail) := by
    rintro (h | h) <;> exact popTok_ne_8 P w _ h
  refine ⟨⟨ghost₀_gw P, ?_, ?_, fun hw1 x hx => ?_, hi, ?_, ?_⟩, ?_⟩
  · rw [hq]; simp [fracD3]; grind
  · rw [hq]; simp [fracD3]; grind
  · show 1 ≤ (if w = 1 ∧ P.IsW x ∧ (0 : PredId) = 0 then 1 else 0); simp [hx, hw1]
  · intro l f hf; simp [σInitX, Views.getFwd] at hf
  · unfold TokFrozen; rw [hq]; simp [fracD3, hm]
  · unfold TokFrozen; rw [hq]; simp [fracD3, hp]

variable [layout : _root_.Layout]

theorem qLocs_params3V (hht : symV3 "head" ≠ symV3 "tail") (hhs : symV3 "head" ≠ symV3 "s")
    (hh1 : symV3 "head" ≠ symV3 "n1") (hh2 : symV3 "head" ≠ symV3 "n2") (hts : symV3 "tail" ≠ symV3 "s")
    (ht1 : symV3 "tail" ≠ symV3 "n1") (ht2 : symV3 "tail" ≠ symV3 "n2") (hs1 : symV3 "s" ≠ symV3 "n1")
    (hs2 : symV3 "s" ≠ symV3 "n2") (h12 : symV3 "n1" ≠ symV3 "n2") (hn1 : symV3 "n1" ≠ 0)
    (hn2 : symV3 "n2" ≠ 0) : QLocs params3V :=
  ⟨hht, hhs, hh1, hh2, hts, ht1, ht2, hs1, hs2, h12, hn1, hn2⟩

variable [Executable.ValidLayout (layout msq3ImageV)]

/-! ## Shapes and fault-freedom of the image and the mask -/

omit layout [Executable.ValidLayout (layout msq3ImageV)] in
/-- The image's cells are phase-1 (the x64 Treiber proof's popper script). -/
theorem msq3ImageV_dirsPhase1FX : ∀ d ∈ msq3ImageV, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [msq3ImageV, msq3CodeV, msq2DataV, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1FX

/-- **The whole image is phase-1.** -/
theorem msq3ImageV_phase1FX : Phase1TreeFX (layout msq3ImageV) :=
  phase1TreeFX_of_dirs (dirsPhase1FX_layout msq3ImageV_dirsPhase1FX)

/-- **The enqueuer's mask is phase-1** (its kept cells are the image's). -/
theorem msq3ImageM_phase1FX : Phase1TreeFX (layout msq3ImageM) :=
  phase1TreeFX_maskKeep_range fun d hd => msq3ImageV_dirsPhase1FX d (List.mem_of_mem_drop (List.mem_of_mem_take hd))

omit [Executable.ValidLayout (layout msq3ImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem msq3ImageV_noFaultCode : DirsNoFaultCode (layout msq3ImageV) := by
  dirs_no_fault_code msq3ImageV msq3CodeV msq2DataV

/-! ## The rules -/

/-- The enqueuer's postcondition: the exit label and `ComE`. -/
abbrev postEV3 (P : Params) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labV3 "edone" ∧ ComE P x.2) ∨ False

omit [Executable.ValidLayout (layout msq3ImageV)] in
theorem postEV3_end (P : Params) : ∀ y, postEV3 P y → y.1.2 = labV3 "edone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout msq3ImageV)] in
/-- **`hB` for the enqueuer**: its mark (`tokH`), whole. -/
theorem hB_EV3 (P : Params) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postEV3 P (t.st.st, σ) → t.prom = [] → EnvRel 0 (planE P) σ c t r g cl → cl → MQ3 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inl hcom.2.2
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 enqueuer's rule** (thread `0`, layout `sAll`), over
the mask `msq3ImageM`. -/
noncomputable def enqRule3 (P : Params) : ThreadRuleRXF (I := isa) Arch.tso (MQ3 P) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjXM (S := sAll) (post := postEV3 P) msq3ImageM_mask (planE_valid P) sAll_le16
    msq3ImageM_phase1FX (postEV3_end P) (enq3M_stuck _) (hB_EV3 P)

/-- **The verbatim enqueuer's rule excludes faults.** -/
theorem enqRule3_noFault (P : Params) : NoFaultRuleF (enqRule3 P) :=
  noFaultRuleF_ofSafelyEnvGFCAdjXM _ _ _ _ _ _ _ msq3ImageV_noFaultCode

/-- Dequeuer `w`'s postcondition: the exit label and `Dn3`. -/
abbrev postDV3 (P : Params) (w : Nat) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labV3 "ddone" ∧ Dn3 P w (x.1.1.regs.get64 .r12) x.2) ∨ False

omit [Executable.ValidLayout (layout msq3ImageV)] in
theorem postDV3_end (P : Params) (w : Nat) : ∀ y, postDV3 P w y → y.1.2 = labV3 "ddone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout msq3ImageV)] in
/-- **`hB` for dequeuer `w`**: `Dn3` at the anchor gives its `MQ3` disjunct
at the configuration. -/
theorem hB_DV3 (P : Params) {w : Nat} (hw : w = 1 ∨ w = 2) : ∀ (c : Config isa) (t : Thread isa) r g cl
    (σ : EStateX), postDV3 P w (t.st.st, σ) → t.prom = [] → EnvRel w (planD3 P w) σ c t r g cl → cl →
      MQ3 P c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hcom, hd⟩ := hpost.resolve_right id
  have hpre : σ.snap.mem.Prefix c.mem := ⟨hrel.snap.init, hrel.snap.msgs⟩
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · have hiv := hcom.2.2.2.2.1.of_init hrel.snap.init
    rcases hw with rfl | rfl
    · exact .inr (.inl ⟨hcom.2.2.2.2.2.2, t, hrel.ht, hd.mono hpre, hiv, hcom.2.2.2.1 rfl⟩)
    · exact .inr (.inr ⟨hcom.2.2.2.2.2.2, t, hrel.ht, hd.mono hpre, hiv⟩)
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 dequeuers' rule** (thread `w ∈ {1, 2}`, layout
`sAll`, the whole image). -/
noncomputable def deqRule3 (P : Params) (w : Nat) (hw : w = 1 ∨ w = 2) :
    ThreadRuleRXF (I := isa) Arch.tso (MQ3 P) w :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjX (S := sAll) (post := postDV3 P w) (planD3_valid P w) sAll_le16
    msq3ImageV_phase1FX (postDV3_end P w) (deq3V_stuck _) (hB_DV3 P hw)

/-- **The verbatim dequeuers' rule excludes faults** (unconditional in
promises). -/
theorem deqRule3_noFault (P : Params) (w : Nat) (hw : w = 1 ∨ w = 2) : NoFaultRuleF (deqRule3 P w hw) := by
  unfold deqRule3 ThreadRuleRXF.ofSafelyEnvGFCAdjX
  exact noFaultRuleF_ofEnvGFCAdj_struct _ _
    (Treiber2X.noFault_QX64CAdjCode msq3ImageV_noFaultCode (postDV3_end P w))

/-! ## The start -/

/-- **The verbatim enqueuer at its start**, as the runner sets it up: the
image, no declarations, pc at `enqueuer`, end at `edone`, an empty private
memory. -/
structure StartEV3 (s : State) : Prop where
  exe : s.exe = layout msq3ImageV
  decls : s.decls = {}
  pc : s.st.2 = labV3 "enqueuer"
  endPc : s.endPc = labV3 "edone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

/-- **A verbatim dequeuer at its start**: the image, no declarations, pc at
`dequeuer`, end at `ddone`, an empty private memory. -/
structure StartDV3 (s : State) : Prop where
  exe : s.exe = layout msq3ImageV
  decls : s.decls = {}
  pc : s.st.2 = labV3 "dequeuer"
  endPc : s.endPc = labV3 "ddone"
  dmem : ∀ k, s.st.1.dmem.get? k = none

section Start

variable {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim enqueuer's initial invariant.** -/
theorem invEV3_init (hL : QLocs params3V) (hS : StartEV3 s0) :
    (enqRule3 params3V).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V 0) (ghost₀ params3V) := by
  have hst : s0.st = (s0.st.1, labV3 "enqueuer") := Prod.ext rfl hS.pc
  refine invGFCAdjXM_init (s := s0) rfl rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (enq3M_envGCAdj params3V hL rfl rfl rfl rfl s0.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, e0_init3 params3V _⟩)

/-- **A verbatim dequeuer's initial invariant.** -/
theorem invDV3_init (hL : QLocs params3V) {w : Nat} (hw : w = 1 ∨ w = 2) {s : isa.State}
    (hs : [s0, s1, s2][w]? = some s) (hS : StartDV3 s)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V) :
    (deqRule3 params3V w hw).Inv True (Config.init [s0, s1, s2] initMem)
      (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V w) (ghost₀ params3V) := by
  have htr : tRes3 (Config.init [s0, s1, s2] initMem).mem params3V w =
      resD3 (Config.init [s0, s1, s2] initMem).mem params3V w := by
    rcases hw with rfl | rfl <;> rfl
  rw [htr]
  have hst : s.st = (s.st.1, labV3 "dequeuer") := Prod.ext rfl hS.pc
  refine invGFCAdjX_init (s := s) hs rfl ⟨hS.exe, hS.decls, hS.endPc, split_sAll hS.dmem, ?_⟩
  rw [hst]
  exact TreiberAbs.Safely.uncountT (deq3V_envGCAdj' params3V hL hw rfl rfl s.st.1 (_, 0)
    ⟨d8_of_dmem hS.dmem, l0_init3 params3V w (by omega) _ hi⟩)

end Start

/-! ## Purity -/

/-- The threads' all-release specifications (the image, unmasked). -/
noncomputable def msq3NoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := sAll
      le16 := sAll_le16
      e := layout msq3ImageV
      valid := inferInstance
      endPc := labV3 "edone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV3 "edone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := sAll
      le16 := sAll_le16
      e := layout msq3ImageV
      valid := inferInstance
      endPc := labV3 "ddone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labV3 "ddone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

/-- **The all-release specifications hold at the start states.** -/
theorem msq3NoNTSpecV_init {s0 s1 s2 : State} (h0 : StartEV3 s0) (h1 : StartDV3 s1) (h2 : StartDV3 s2) :
    ∀ tid s, [s0, s1, s2][tid]? = some s → (msq3NoNTSpecV tid).Holds s := by
  have H : ∀ {s : State}, StartDV3 s → ∀ i, (msq3NoNTSpecV (i + 1)).Holds s := fun {s} hS i => by
    refine ⟨hS.exe, hS.endPc, hS.decls, split_sAll hS.dmem, ?_⟩
    rw [show s.st = (s.st.1, labV3 "dequeuer") from Prod.ext rfl hS.pc]
    exact TreiberAbs.Safely.uncountT (deq3V_noNT _ ((), 0) (d8_of_dmem hS.dmem))
  intro tid s hs
  rcases tid with _ | _ | _ | i
  · cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, split_sAll h0.dmem, ?_⟩
    rw [show s0.st = (s0.st.1, labV3 "enqueuer") from Prod.ext rfl h0.pc]
    exact TreiberAbs.Safely.uncountT (enq3V_noNT _ ((), 0) (d8_of_dmem h0.dmem))
  · cases hs; exact H h1 0
  · cases hs; exact H h2 1
  · simp at hs

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for the verbatim `msqueue3`.** -/
theorem msq3V_npSafeF (hL : QLocs params3V) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV3 s0) (h1 : StartDV3 s1) (h2 : StartDV3 s2)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V) :
    ∀ tid, tid < [s0, s1, s2].length → ∀ k j, NPSafeF (model isa) Arch.tso (MQ3 params3V) tid k j True
      (Config.init [s0, s1, s2] initMem) (tRes3 (Config.init [s0, s1, s2] initMem).mem params3V tid)
      (ghost₀ params3V) := by
  intro tid htid k j
  rcases tid with _ | _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invEV3_init hL h0)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV3_init hL (.inl rfl) rfl h1 hi)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invDV3_init hL (.inr rfl) rfl h2 hi)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Michael–Scott queue `LockFree/X64/msqueue3.kl` for x64 under
`Arch.tso`, the `.kl`'s code verbatim**: for every valid layout of the image
`msq3ImageV` (the `code` block, then the runner's data trailer placing `s`,
`n1`, `n2`, `head`, `tail`) in which the five symbols have distinct
addresses and the nodes are non-null, if thread `0` starts at `enqueuer`
with end `edone` (`StartEV3`), threads `1` and `2` at `dequeuer` with end
`ddone` (`StartDV3`), all with an empty private memory, and the initial
memory is the `.kl`'s (`head = tail = s`, the links of `s`, `n1`, `n2` zero:
`InitV`), then every final configuration reachable under `Arch.tso` has
`(1:r12, 2:r12)` among `(n1,n2)`, `(n2,n1)`, `(n1,0)`, `(0,n1)`, `(0,0)`
(the `.kl`'s `forall`). -/
theorem x64_msqueue3_envG_verbatim {fuel : Nat} (hht : symV3 "head" ≠ symV3 "tail")
    (hhs : symV3 "head" ≠ symV3 "s") (hh1 : symV3 "head" ≠ symV3 "n1") (hh2 : symV3 "head" ≠ symV3 "n2")
    (hts : symV3 "tail" ≠ symV3 "s") (ht1 : symV3 "tail" ≠ symV3 "n1") (ht2 : symV3 "tail" ≠ symV3 "n2")
    (hs1 : symV3 "s" ≠ symV3 "n1") (hs2 : symV3 "s" ≠ symV3 "n2") (h12 : symV3 "n1" ≠ symV3 "n2")
    (hn1 : symV3 "n1" ≠ 0) (hn2 : symV3 "n2" ≠ 0) {s0 s1 s2 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartEV3 s0) (h1 : StartDV3 s1) (h2 : StartDV3 s2)
    (hi : InitV (Config.init [s0, s1, s2] initMem).mem params3V)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1, s2] initMem) cfg)
    (hf : cfg.final = true) :
    MsQueue3FinalX (symV3 "n1") (symV3 "n2") cfg := by
  have hL := qLocs_params3V hht hhs hh1 hh2 hts ht1 ht2 hs1 hs2 h12 hn1 hn2
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' (B := MQ3 params3V)
    (Φ := MsQueue3FinalX (symV3 "n1") (symV3 "n2"))
    (erase_init3 hL _) (ghost₀_pend _) msq3NoNTSpecV (msq3NoNTSpecV_init h0 h1 h2)
    (msq3V_npSafeF hL h0 h1 h2 hi) hc hf fun rF' g' E' hle hsize hB => ?_
  have hi0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hi2 : (2 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have hW := (ghost₀_gw params3V).mono hle
  -- the two dequeuers' disjuncts, in threads `k1`, `k2`
  have fin : ∀ k1 k2, k1 < cfg.threads.size → k2 < cfg.threads.size →
      (∃ th, cfg.threads[1]? = some th ∧ DoneD3 cfg.mem params3V 1 (rF' k1) (th.st.st.1.regs.get64 .r12) ∧
        InitV cfg.mem params3V ∧ ∀ x, params3V.IsW x → 1 ≤ (rF' k1).acq x 0) →
      (∃ th, cfg.threads[2]? = some th ∧ DoneD3 cfg.mem params3V 2 (rF' k2) (th.st.st.1.regs.get64 .r12) ∧
        InitV cfg.mem params3V) →
      MsQueue3FinalX (symV3 "n1") (symV3 "n2") cfg := by
    rintro k1 k2 hk1 hk2 ⟨th1, hth1, hd1, hiv, hacq⟩ ⟨th2, hth2, hd2, -⟩
    exact ⟨th1, th2, hth1, hth2, final_values3 E' hW hL hiv
      (fun x hx => TreiberCommon.total_acq_of_ge E' hk1 (hacq x hx)) rfl hk1 hk2 hd1 hd2⟩
  have hb0 := hB 0 (Config.final_done hf hi0)
  have hb1 := hB 1 (Config.final_done hf hi1)
  have hb2 := hB 2 (Config.final_done hf hi2)
  rcases hb0 with m0 | ⟨m0, d0⟩ | ⟨m0, d0⟩ <;> rcases hb1 with m1 | ⟨m1, d1⟩ | ⟨m1, d1⟩ <;>
    rcases hb2 with m2 | ⟨m2, d2⟩ | ⟨m2, d2⟩
  all_goals first
    | exact (mark_pair_false E' hi0 hi1 (by decide) m0 m1).elim
    | exact (mark_pair_false E' hi0 hi2 (by decide) m0 m2).elim
    | exact (mark_pair_false E' hi1 hi2 (by decide) m1 m2).elim
    | exact fin _ _ hi0 hi1 d0 d1
    | exact fin _ _ hi0 hi2 d0 d2
    | exact fin _ _ hi1 hi0 d1 d0
    | exact fin _ _ hi1 hi2 d1 d2
    | exact fin _ _ hi2 hi0 d2 d0
    | exact fin _ _ hi2 hi1 d2 d1

end Kraken.Promising.X64.EnvG.MsQueue3X

#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.x64_msqueue3_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.enqRule3_noFault
#print axioms Kraken.Promising.X64.EnvG.MsQueue3X.deqRule3_noFault
