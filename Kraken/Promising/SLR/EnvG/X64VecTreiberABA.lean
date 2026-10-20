/-
**`treiber_aba_tagged.kl` verbatim, end to end** (on
the adjacency environment `EnvGCAdj`, with declarations):
`x64_treiber_aba_tagged_never`, the `.kl`'s `~exists` clause: no final
configuration reachable under `Arch.tso` has
`0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B`, for the `.kl`'s `code` block as written,
run by both threads in the runner's image `abaImageV` (the code, then the
data trailer `head`, `A`, `B`), over every valid layout of the image.

- **Parameters** `abaP`: `head`, `A`, `B` at their symbols.
- **Rules** (`rule0`, `rule1`): `ThreadRuleRXF.ofSafelyEnvGFCAdjVecD` at the
  whole image with the threads' declarations `ds` (strict and sized,
  `Decls.Sized`): the image is piece-free and phase-1
  (`X64VecTreiberABAImage.lean`), `done` is followed by the data trailer
  (`abaV_stuck`); the postconditions are `Done0` / `Done1` and `hB` is
  `hB0` / `hB1` (`X64VecTreiberABAFinal.lean`).
- **Start**: thread `0` at `p0`, thread `1` at `p1` (mid-program: the rule's
  invariant is built from the run directly, not from a whole-program
  triple), each on its private stack (`StartV`); the stack range of a thread
  is the domain of its initial private memory (`domS`).
- **Purity**: `specV` from `p0V_noNT` / `p1V_noNT`.
- **Assembly**: `final_of_relPureSafelyVecD_tsoF`, initial erasure
  `erase_init`, the final argument `final_never`.

Start predicates fix only what the runner sets: the image, the
declarations, the entry and exit labels, the private stack (its 16-byte slot
at `-16(%rsp)` mapped and 16-aligned; `head`, and the nodes the thread
dereferences, not in it), `head` 16-aligned, the initial values
`head = {A, 0}`, `A.next = B`, `B.next = 0` (`IV`), and the symbols'
distinctness and non-nullness.

**Not covered: fault-freedom.** The rules are `ThreadRuleRXF`s without a
no-fault part. With typed declarations (`head` is a 16-byte location, `A`
and `B` 8-byte ones), an access whose footprint straddles or splits a
declared location faults (mixed-size), and the node load `movq (%rax),%rbx`
and the push's store `movq %rax,(%r12)` go through pointers read from
`head`. That those pointers are always `0`, `A` or `B` is the stack's
history invariant, which the runs here do not carry (their tables only
attribute messages, `X64VecTreiberABARec.lean`), so mixed-size faults are
not excluded (`X64_KNOWN_GAPS.md`).
-/
import Kraken.Promising.SLR.EnvG.X64VecTreiberABAFinal
import Kraken.Promising.SLR.EnvG.X64VecTreiberABAImage

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG

namespace Kraken.Promising.X64.EnvG.VecABA

/-! ## The initial thread states -/

section Init

variable {P : Params} {m : Memory}

theorem thrRes_q (m : Memory) (P : Params) (w : Nat) (x : Loc) : ((thrRes m P w).wr x).q = frac P w x := rfl

theorem thrRes_X (m : Memory) (P : Params) (w : Nat) (x : Loc) (p : Val × Time) :
    ((thrRes m P w).wr x).X p ↔ 0 < frac P w x ∧ p = (m.initVal x, 0) := Iff.rfl

theorem fr_init0 : Fr P 0 (thrRes m P 0) := by
  unfold Fr
  simp only [↓reduceIte, thrRes_q]
  exact ⟨by simp [frac], by simp [frac, Ne.symm (hd_ne_tok0 P)]⟩

theorem fr_init1 : Fr P 1 (thrRes m P 1) := by
  unfold Fr
  simp only [Nat.one_ne_zero, ↓reduceIte, thrRes_q]
  refine ⟨by simp [frac], by simp [frac, Ne.symm (hd_ne_tok1 P)], fun x hx => ?_⟩
  have h1 : x ≠ P.hd := fun h => by rw [h] at hx; simp at hx
  have h2 : x ≠ P.tok1 := fun h => by rw [h] at hx; simp at hx
  simp [frac, h1, h2, hx]

theorem com_init {w : Nat} {c : Config isa} (hfr : Fr P w (thrRes c.mem P w)) (hiv : IV P c.mem) :
    Com P w (σInitX c (thrRes c.mem P w) ghost₀) := by
  refine ⟨rfl, hfr, hiv, ?_, ?_⟩
  · intro x f hf; simp [σInitX, Views.getFwd] at hf
  · intro f hf; simp [σInitX, Views.getFwd] at hf

theorem exH_init {w : Nat} : ExH P (thrRes m P w) (fun _ => False) := fun _ p hp =>
  .inl (by rw [((thrRes_X _ _ _ _ _).mp hp).2])

theorem exN_init {w : Nat} : ExN (thrRes m P w) (fun _ _ => False) := fun _ _ _ p hp =>
  .inl (by rw [((thrRes_X _ _ _ _ _).mp hp).2])

/-- **Thread `0` at its start**: `A0`. -/
theorem a0_init {c : Config isa} (hiv : IV P c.mem) : A0 P (σInitX c (thrRes c.mem P 0) ghost₀) :=
  ⟨com_init fr_init0 hiv, exH_init⟩

/-- **Thread `1` at its start**: `A1`. -/
theorem a1_init {c : Config isa} (hiv : IV P c.mem) : A1 P (σInitX c (thrRes c.mem P 1) ghost₀) :=
  ⟨com_init fr_init1 hiv, exH_init, exN_init⟩

end Init

variable [layout : _root_.Layout] [Executable.ValidLayout (layout abaImageV)]

local instance abaImageV.envT : CodeEnv := ⟨layout abaImageV⟩

/-! ## The start -/

/-- **A thread at its start**, as the runner sets it up: the image, the
declarations `ds`, pc at `lab`, end at `done`, and its private stack: the
16-byte slot at `-16(%rsp)` mapped and 16-aligned, `head` unmapped. -/
structure StartV (ds : Decls) (lab : Label) (s : State) : Prop where
  exe : s.exe = layout abaImageV
  decls : s.decls = ds
  pc : s.st.2 = labV lab
  endPc : s.endPc = labV "done"
  slot : (Mem.loadInt s.st.1.dmem (s.st.1.regs.get64 .rsp + (-16 : Int64).toBitVec) 16).isSome = true
  slotAl : isAligned 16 (s.st.1.regs.get64 .rsp + (-16 : Int64).toBitVec) = true
  hdFree : s.st.1.dmem.get? (symV "head") = none

/-- A thread's private stack range: the domain of its initial private
memory. -/
def domS (s : State) : BitVec 64 → Prop := fun k => (s.st.1.dmem.get? k).isSome = true

omit [Executable.ValidLayout (layout abaImageV)] in
theorem StartV.stk {ds : Decls} {lab : Label} {s : State} (h : StartV ds lab s) :
    Stk (domS s) (symV "head") s.st.1 :=
  ⟨fun _ hk => hk, h.slot, h.slotAl, fun h' => by unfold domS at h'; rw [h.hdFree] at h'; cases h'⟩

/-! ## The rules -/

/-- Thread `0`'s postcondition: `done` and `Done0`. -/
abbrev post0 (S : BitVec 64 → Prop) : MachineState × EStateX → Prop :=
  fun y => ∃ _ : Nat, (y.1.2 = labV "done" ∧ Done0 abaP S y.2 (y.1.1.regs.get64 .r12) (y.1.1.regs.get64 .r13)) ∨
    False

/-- Thread `1`'s postcondition: `done` and `Done1`. -/
abbrev post1 (S : BitVec 64 → Prop) : MachineState × EStateX → Prop :=
  fun y => ∃ _ : Nat, (y.1.2 = labV "done" ∧ Done1 abaP S y.2 (y.1.1.regs.get64 .r12) (y.1.1.regs.get64 .r13)) ∨
    False

/-- **Thread `0`'s rule.** -/
noncomputable def rule0 (S0 S1 : BitVec 64 → Prop) (ds : Decls) (hsz : ds.Sized) :
    ThreadRuleRXF (I := isa) Arch.tso (BV abaP S0 S1) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjVecD (pl := plan0) (ds := ds) (e := layout abaImageV) (endPc := labV "done")
    (post := post0 S0) plan0_valid hsz abaImageV_noPieces abaImageV_phase1FX
    (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (abaV_stuck _)
    (hB0 fun _ ⟨_, h⟩ => (h.resolve_right id).2)

/-- **Thread `1`'s rule.** -/
noncomputable def rule1 (S0 S1 : BitVec 64 → Prop) (ds : Decls) (hsz : ds.Sized) :
    ThreadRuleRXF (I := isa) Arch.tso (BV abaP S0 S1) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCAdjVecD (pl := plan0) (ds := ds) (e := layout abaImageV) (endPc := labV "done")
    (post := post1 S1) plan0_valid hsz abaImageV_noPieces abaImageV_phase1FX
    (fun _ ⟨_, h⟩ => h.elim And.left False.elim) (abaV_stuck _)
    (hB1 fun _ ⟨_, h⟩ => (h.resolve_right id).2)

section Start

variable {s0 s1 : isa.State} {initMem : List (Loc × Val)} {ds : Decls}

/-- **Thread `0`'s initial invariant.** -/
theorem inv0_init (hsz : ds.Sized) (hal : isAligned 16 (symV "head") = true) (h0 : StartV ds "p0" s0)
    (hiv : IV abaP (Config.init [s0, s1] initMem).mem) :
    (rule0 (domS s0) (domS s1) ds hsz).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem abaP 0) ghost₀ := by
  refine invGFCAdjVecD_init (s := s0) rfl rfl ⟨h0.exe, h0.decls, h0.endPc, ?_⟩
  rw [show s0.st = (s0.st.1, labV "p0") from Prod.ext rfl h0.pc]
  exact Safely.uncountEnv (p0V_envGCAdj (domS s0) hal s0.st.1 (_, 0) ⟨h0.stk, a0_init hiv⟩)

/-- **Thread `1`'s initial invariant.** -/
theorem inv1_init (hsz : ds.Sized) (hal : isAligned 16 (symV "head") = true) (h1 : StartV ds "p1" s1)
    (hiv : IV abaP (Config.init [s0, s1] initMem).mem) :
    (rule1 (domS s0) (domS s1) ds hsz).Inv True (Config.init [s0, s1] initMem)
      (tRes (Config.init [s0, s1] initMem).mem abaP 1) ghost₀ := by
  refine invGFCAdjVecD_init (s := s1) rfl rfl ⟨h1.exe, h1.decls, h1.endPc, ?_⟩
  rw [show s1.st = (s1.st.1, labV "p1") from Prod.ext rfl h1.pc]
  exact Safely.uncountEnv (p1V_envGCAdj (domS s1) hal s1.st.1 (_, 0) ⟨h1.stk, a1_init hiv⟩)

/-- **The `NPSafeF` side of Theorem 1′.** -/
theorem abaV_npSafeF (hsz : ds.Sized) (hal : isAligned 16 (symV "head") = true) (h0 : StartV ds "p0" s0)
    (h1 : StartV ds "p1" s1) (hiv : IV abaP (Config.init [s0, s1] initMem).mem) :
    ∀ tid, tid < [s0, s1].length → ∀ k j, NPSafeF (model isa) Arch.tso (BV abaP (domS s0) (domS s1)) tid k j True
      (Config.init [s0, s1] initMem) (tRes (Config.init [s0, s1] initMem).mem abaP tid) ghost₀ := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (inv0_init hsz hal h0 hiv)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (inv1_init hsz hal h1 hiv)
  · simp only [List.length_cons, List.length_nil] at htid; omega

end Start

/-! ## Purity -/

/-- The threads' all-release specifications (the image, declarations `ds`). -/
noncomputable def specV (ds : Decls) (hsz : ds.Sized) : Nat → RelPureSpecVecD := fun _ =>
  { e := layout abaImageV
    valid := inferInstance
    endPc := labV "done"
    post := fun x => ∃ _ : Nat, (x.1.2 = labV "done" ∧ True) ∨ False
    post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim
    ds := ds
    sized := hsz
    noPieces := abaImageV_noPieces }

theorem specV_init {ds : Decls} (hsz : ds.Sized) (hal : isAligned 16 (symV "head") = true) {s0 s1 : State}
    (h0 : StartV ds "p0" s0) (h1 : StartV ds "p1" s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (specV ds hsz tid).Holds Arch.tso (fun _ _ => False) s := by
  intro tid s hs
  rcases tid with _ | _ | i
  · cases hs
    refine ⟨h0.exe, h0.endPc, h0.decls, ?_⟩
    rw [show s0.st = (s0.st.1, labV "p0") from Prod.ext rfl h0.pc]
    exact Safely.uncountEnv (p0V_noNT (domS s0) hal s0.st.1 ((), 0) h0.stk)
  · cases hs
    refine ⟨h1.exe, h1.endPc, h1.decls, ?_⟩
    rw [show s1.st = (s1.st.1, labV "p1") from Prod.ext rfl h1.pc]
    exact Safely.uncountEnv (p1V_noNT (domS s1) hal s1.st.1 ((), 0) h1.stk)
  · simp at hs

/-! ## The theorem -/

/-- **The tagged-pointer Treiber stack `LockFree/X64/treiber_aba_tagged.kl`
for x64 under `Arch.tso`, the `.kl`'s code verbatim: the ABA outcome is
impossible.** For every valid layout of the image `abaImageV` (the `code`
block, then the runner's data trailer placing `head`, `A`, `B`) in which
`head` is 16-aligned and `A`, `B` are distinct and non-null, if both threads
run the image with strict sized declarations `ds`, thread `0` from `p0` and
thread `1` from `p1` to `done`, each on its private stack (`StartV`), `A`
not on thread `0`'s stack and `A`, `B` not on thread `1`'s, and the initial
memory has `head = {A, 0}`, `A.next = B`, `B.next = 0`, then no final
configuration reachable under `Arch.tso` has
`0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B` (the `.kl`'s `~exists`). -/
theorem x64_treiber_aba_tagged_never {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hal : isAligned 16 (symV "head") = true) (hA : symV "A" ≠ 0) (hB : symV "B" ≠ 0) (hAB : symV "A" ≠ symV "B")
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartV ds "p0" s0) (h1 : StartV ds "p1" s1)
    (hA0 : s0.st.1.dmem.get? (symV "A") = none) (hA1 : s1.st.1.dmem.get? (symV "A") = none)
    (hB1 : s1.st.1.dmem.get? (symV "B") = none) (hiv : IV abaP (Config.init [s0, s1] initMem).mem)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg) (hf : cfg.final = true) :
    ¬ ∃ t0 t1, cfg.threads[0]? = some t0 ∧ cfg.threads[1]? = some t1 ∧
      t0.st.st.1.regs.get64 .r12 = symV "A" ∧ t0.st.st.1.regs.get64 .r13 = symV "B" ∧
      t1.st.st.1.regs.get64 .r13 = symV "B" :=
  final_of_relPureSafelyVecD_tsoF
    (Φ := fun c => ¬ ∃ t0 t1, c.threads[0]? = some t0 ∧ c.threads[1]? = some t1 ∧
      t0.st.st.1.regs.get64 .r12 = symV "A" ∧ t0.st.st.1.regs.get64 .r13 = symV "B" ∧
      t1.st.st.1.regs.get64 .r13 = symV "B") (B := BV abaP (domS s0) (domS s1)) (erase_init abaP _) ghost₀_pend
    (specV ds hsz) (specV_init hsz hal h0 h1) (abaV_npSafeF hsz hal h0 h1 hiv) hc hf
    fun _ _ E _ hsize hBV => final_never (P := abaP) E hf hsize hBV hA hB hAB (fun h' => by unfold domS at h'; rw [hA0] at h'; cases h')
      (fun h' => by unfold domS at h'; rw [hA1] at h'; cases h') (fun h' => by unfold domS at h'; rw [hB1] at h'; cases h')

end Kraken.Promising.X64.EnvG.VecABA

#print axioms Kraken.Promising.X64.EnvG.VecABA.x64_treiber_aba_tagged_never
