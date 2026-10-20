/-
**The x64 Treiber stack `treiber_pp.kl`, verbatim: the public theorem**
`x64_treiber_pp_envG_verbatim`, the `.kl`'s property
`1:r10=n1 ∧ 1:r11=1` at every final configuration reachable under
`Arch.tso`, for the `.kl`'s `code` block as written, run by both threads in
the runner's image `treiberImageV` (the code, then the data trailer). The
statement of the x64 Treiber proof's `TreiberX.x64_treiber_pp_envG` (which proves the
per-thread texts `treiberPusherX`/`treiberPopperX`, each laid out alone; it
stays unchanged), over every valid layout of the image, with `top` and `n1`
the symbols' addresses `symT "top"`, `symT "n1"`.

- **Pusher** (thread `0`, entry `pusher`, exit `pdone`): its exit label is
  followed by code (`pdone: nop`, then the popper). The rule is
  `ThreadRuleRXF.ofSafelyEnvGFCXM` (`EnvG/X64MaskLink.lean`) over the mask
  `treiberImageM` (`EnvG/X64TreiberAbsMask.lean`: the cells from the `nop`
  on are data cells): the halt at `pdone` and the phase-1 shape are the
  mask's (`pusherM_stuck`, `treiberImageM_phase1FX`).
- **Popper** (thread `1`, entry `popper`, exit `qdone`): its exit is followed
  by the data trailer, so the existing `ThreadRuleRXF.ofSafelyEnvGFCX` at the
  whole image applies (`popperV_stuck` from the trailer's first data cell;
  the whole image is phase-1: `treiberImageV_phase1FX`).
- The runs are the x64 absolute-address proofs' `popperV_envGC` and this iteration's
  `pusherM_envGC`; the all-release specifications the x64 absolute-address proofs' `pusherV_noNT`,
  `popperV_noNT` (the image, unmasked: no halt is needed there).
- **Assembly**: the x64 Treiber proof's (`CmpxPublic.final_of_relPureSafelyQX_tsoF'`,
  `erase_init`, `ghost₀`, the ownership argument on `top`).

Start predicates fix only what the runner sets: the image, no declarations,
the entry and exit labels, the registers the `.kl` sets (`0:rdi=top;
0:rbx=n1; 1:rdi=top`), and the private memory (the runner's is empty; the
pusher's is only asked not to hold `top` or the node's words). Not covered
(as for `x64_treiber_pp_envG`): the runner's declarations (`decls = {}`),
final configurations only, `t ≠ n + 8` for the model's mixed-size gap.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberAbsMask
import Kraken.Promising.SLR.EnvG.X64TreiberPublic

namespace Kraken.Promising.X64.EnvG.TreiberAbs

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX

/-! ## Forgetting the access counter -/

/-- A `Safely` judgment in `SharedEnv.counted env` is one in `env` (a copy of
`SpinAbs.Safely.uncountV`, `EnvG/X64SpinAbsPublic.lean`). -/
theorem Safely.uncountT {e : Kraken.Executable Directive} {env : SharedEnv}
    {post : MachineState × (SharedEnv.counted env).State → Prop} {x : MachineState}
    {g : (SharedEnv.counted env).State} (h : Safely (e.instrStepEnv (SharedEnv.counted env)) post (x, g)) :
    Safely (e.instrStepEnv env) (fun y => ∃ n : Nat, post (y.1, (y.2, n))) (x, g.1) :=
  _root_.Safely.uncountEnv h

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiberImageV)]

/-! ## Shapes, halts and fault-freedom of the image -/

omit layout [Executable.ValidLayout (layout treiberImageV)] in
/-- The pusher's cells are phase-1 (the x64 Treiber proof's script). -/
theorem pusherX_dirsPhase1FX : ∀ d ∈ treiberPusherX, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [treiberPusherX, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1FX

omit layout [Executable.ValidLayout (layout treiberImageV)] in
/-- The popper's cells are phase-1 (the x64 Treiber proof's script). -/
theorem popperX_dirsPhase1FX : ∀ d ∈ treiberPopperX, ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [treiberPopperX, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  cells_phase1FX

omit layout [Executable.ValidLayout (layout treiberImageV)] in
/-- Labels, `nop` and data cells are phase-1. -/
theorem other_dirsPhase1FX : ∀ d ∈ ([.instr (.regular .W64 .W64 (.nop 1))] ++ treiberDataV : Program),
    ∀ (e : _root_.Executable) z, DirPhase1FX e d z := by
  intro d hd e z s pc
  simp only [treiberDataV, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hd
  repeat' (rcases hd with rfl | hd)
  all_goals simp [_root_.Directive.interp, _root_.Instr.interp, _root_.Operation.interp,
    Kraken.Promising.X64.toEv, Phase1ShapeF, DetAccess, SingleAccessS2, AccessFree]

omit layout [Executable.ValidLayout (layout treiberImageV)] in
/-- The image is the pusher, `pdone`'s `nop`, the popper and the trailer. -/
theorem treiberImageV_split : treiberImageV =
    treiberPusherX ++ ([.instr (.regular .W64 .W64 (.nop 1))] ++ treiberPopperX ++ treiberDataV) := by
  decide

/-- **The pusher's mask is phase-1** (its kept cells are the pusher's). -/
theorem treiberImageM_phase1FX : Phase1TreeFX (layout treiberImageM) :=
  phase1TreeFX_maskKeep_range (by
    rw [show (treiberImageV.drop 0).take (9 - 0) = treiberPusherX by decide]
    exact pusherX_dirsPhase1FX)

/-- **The whole image is phase-1** (both roles' cells, the trailer). -/
theorem treiberImageV_phase1FX : Phase1TreeFX (layout treiberImageV) := by
  refine phase1TreeFX_of_dirs (dirsPhase1FX_layout ?_)
  rw [treiberImageV_split]
  intro d hd
  simp only [List.mem_append] at hd
  rcases hd with hd | (hd | hd) | hd
  · exact pusherX_dirsPhase1FX d hd
  · exact other_dirsPhase1FX d (List.mem_append_left _ hd)
  · exact popperX_dirsPhase1FX d hd
  · exact other_dirsPhase1FX d (List.mem_append_right _ hd)

omit [Executable.ValidLayout (layout treiberImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem treiberImageV_noFaultCode : DirsNoFaultCode (layout treiberImageV) := by
  dirs_no_fault_code treiberImageV treiberCodeV treiberDataV

/-- `qdone`'s address is the trailer's first data cell. -/
theorem labT_qdone : labT "qdone" = (layout treiberImageV).addrOf 21 := by
  have hd : labT "qdone" = (layout treiberImageV).addrOf 20 :=
    Program.label_addrOf_drop treiberImageV_wf.nodup (by decide) (by decide)
  have h20 : (layout treiberImageV).2[20]? = some (Directive.label "qdone", Kraken.Layout.size Directive 20) := by
    simp [Layout.apply_snd, Layout.frag, treiberImageV, treiberCodeV, treiberDataV]
  rw [Executable.addrOf_succ _ h20, Executable.ValidLayout.label_size 20 "qdone" _ h20, hd]
  simp

/-- **No instruction steps at the popper's exit label `qdone`.** -/
theorem popperV_stuck (env : SharedEnv) :
    ∀ x R, x.1.2 = labT "qdone" → ¬ (layout treiberImageV).instrStepEnv env x R := by
  rw [labT_qdone]
  exact not_instrStepEnv_of_byteArray (i := 21) (b := .mk #[]) env (by decide)

/-! ## The rules -/

/-- The pusher's postcondition: the exit label and `Pd`. -/
abbrev postPushV (P : Params) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labT "pdone" ∧ Pd P x.2) ∨ False

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem postPushV_end (P : Params) : ∀ y, postPushV P y → y.1.2 = labT "pdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiberImageV)] in
/-- **`hB` for the verbatim pusher** (`hB_pushX`). -/
theorem hB_pushV (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPushV P (t.st.st, σ) → t.prom = [] → EnvRel 0 (pushPlan P) σ c t r g cl → cl → TBX P n c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ hp hrel -
  obtain ⟨-, hPd⟩ := hpost.resolve_right id
  rcases hrel.res with ⟨rfl, -⟩ | ⟨ts, -, -, hts, -⟩
  · exact .inr hPd.2
  · rw [hp] at hts; cases hts

/-- **The verbatim x64 pusher's rule** (thread `0`, layout `pushS t n`), over
the mask `treiberImageM`. -/
noncomputable def pushRuleV (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 0 :=
  ThreadRuleRXF.ofSafelyEnvGFCXM (S := pushS t n) (post := postPushV (tPX t n)) treiberImageM_mask
    (pushPlan_valid hL) (pushS_le16 t n) treiberImageM_phase1FX (postPushV_end _) (pusherM_stuck _) (hB_pushV _ n)

/-- **The verbatim pusher's rule excludes faults.** -/
theorem pushRuleV_noFault (t n : BitVec 64) (hL : TLocs (tPX t n)) : NoFaultRuleF (pushRuleV t n hL) :=
  noFaultRuleF_ofSafelyEnvGFCXM _ _ _ _ _ _ _ treiberImageV_noFaultCode

/-- The popper's postcondition: the exit label and, under the clean flag,
its registers. -/
abbrev postPopV (n : BitVec 64) : MachineState × EStateX → Prop :=
  fun x => ∃ _ : Nat, (x.1.2 = labT "qdone" ∧ PopPostX n x.1.1 x.2.cl) ∨ False

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem postPopV_end (n : BitVec 64) : ∀ y, postPopV n y → y.1.2 = labT "qdone" :=
  fun _ ⟨_, h⟩ => h.elim And.left False.elim

omit [Executable.ValidLayout (layout treiberImageV)] in
/-- **`hB` for the verbatim popper** (`hB_popX`). -/
theorem hB_popV (P : Params) (n : BitVec 64) : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateX),
    postPopV n (t.st.st, σ) → t.prom = [] → EnvRel 1 (popPlan P) σ c t r g cl → cl → TBX P n c r g := by
  rintro c t r g cl σ ⟨_, hpost⟩ - hrel hcl
  obtain ⟨-, hq⟩ := hpost.resolve_right id
  obtain ⟨h10, h11⟩ := hq (hrel.cl hcl)
  exact .inl ⟨t, hrel.ht, h10, h11⟩

/-- **The verbatim x64 popper's rule** (thread `1`, layout `sAll`), at the
whole image. -/
noncomputable def popRuleV (t n : BitVec 64) (hL : TLocs (tPX t n)) :
    ThreadRuleRXF (I := isa) Arch.tso (TBX (tPX t n) n) 1 :=
  ThreadRuleRXF.ofSafelyEnvGFCX (S := sAll) (post := postPopV n) (popPlan_valid hL) sAll_le16
    treiberImageV_phase1FX (postPopV_end n) (popperV_stuck _) (hB_popV _ n)

/-- **The verbatim popper's rule excludes faults** (`QX64C` is `QX64M` at
the unmasked image). -/
theorem popRuleV_noFault (t n : BitVec 64) (hL : TLocs (tPX t n)) : NoFaultRuleF (popRuleV t n hL) := by
  unfold popRuleV ThreadRuleRXF.ofSafelyEnvGFCX
  exact noFaultRuleF_ofEnvGFC_struct _ _
    (noFault_QX64M (E := Kraken.Promising.SLR.EnvGC isa Arch.tso 1 (popPlan (tPX t n))) (S := sAll)
      (MaskOf.refl _) treiberImageV_noFaultCode (postPopV_end n))

/-! ## The start -/

/-- **The verbatim pusher at its start**, as the runner sets it up: the
image, no declarations, pc at `pusher`, end at `pdone`, the `.kl`'s
`0:rdi=top; 0:rbx=n1`, and neither `top` nor the node's words in the private
memory. -/
structure StartPushV (s : State) : Prop where
  exe : s.exe = layout treiberImageV
  decls : s.decls = {}
  pc : s.st.2 = labT "pusher"
  endPc : s.endPc = labT "pdone"
  rdi : s.st.1.regs.get64 .rdi = symT "top"
  rbx : s.st.1.regs.get64 .rbx = symT "n1"
  split : Split (pushS (symT "top") (symT "n1")) s.st.1.dmem

/-- **The verbatim popper at its start**: the image, no declarations, pc at
`popper`, end at `qdone`, the `.kl`'s `1:rdi=top`, and an empty private
memory. -/
structure StartPopV (s : State) : Prop where
  exe : s.exe = layout treiberImageV
  decls : s.decls = {}
  pc : s.st.2 = labT "popper"
  endPc : s.endPc = labT "qdone"
  rdi : s.st.1.regs.get64 .rdi = symT "top"
  dmem : ∀ k, s.st.1.dmem.get? k = none

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem StartPushV.frame {s : State} (h : StartPushV s) : PFrameX (symT "top") (symT "n1") s.st.1 :=
  ⟨h.rdi, h.rbx, h.split.loadInt_none (by simp) (by decide) (by decide),
    h.split.loadInt_none (by simp) (by decide) (by decide), h.split.loadInt_none (by simp) (by decide) (by decide)⟩

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem StartPopV.frame {s : State} (h : StartPopV s) : QFrameX (symT "top") s.st.1 :=
  ⟨h.rdi, fun a => (split_sAll h.dmem).loadInt_none (mem_sAll8 a) (by decide) (by decide),
    fun a => (split_sAll h.dmem).loadInt_none (mem_sAll4 a) (by decide) (by decide)⟩

section Start

variable {t n : BitVec 64} {sP sQ : isa.State} {initMem : List (Loc × Val)}

/-- **The verbatim pusher's initial invariant.** -/
theorem invPushV_init (htn : symT "top" ≠ symT "n1" + 8) (hP : StartPushV sP) :
    (pushRuleV (symT "top") (symT "n1") (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) 0)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  have hL := tLocs_tPX htn
  have hst : sP.st = (sP.st.1, labT "pusher") := Prod.ext rfl hP.pc
  refine invGFCXM_init (s := sP) rfl rfl ⟨hP.exe, hP.decls, hP.endPc, hP.split, ?_⟩
  rw [hst]
  refine Safely.uncountT (pusherM_envGC _ _ ⟨symT "top", 1⟩ hL sP.st.1 (_, 0) ⟨hP.frame, ghost₀_gw _, ?_⟩)
  have htd := hL.top_d; have htn' := hL.top_n; have hdn := hL.d_n
  simp only [σInitX, tRes, ↓reduceIte, pushRes, Res.initOf, Perm.init, pushFrac]
  simp only [Ne.symm htd, Ne.symm htn', ↓reduceIte, true_or, or_true, true_and]
  refine ⟨by grind, fun p hp => by rw [hp.2]⟩

/-- **The verbatim popper's initial invariant.** -/
theorem invPopV_init (htn : symT "top" ≠ symT "n1" + 8) (hQ : StartPopV sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0) :
    (popRuleV (symT "top") (symT "n1") (tLocs_tPX htn)).Inv True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) 1)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  have hL := tLocs_tPX htn
  have hst : sQ.st = (sQ.st.1, labT "popper") := Prod.ext rfl hQ.pc
  refine invGFCX_init (s := sQ) rfl rfl ⟨hQ.exe, hQ.decls, hQ.endPc, split_sAll hQ.dmem, ?_⟩
  rw [hst]
  refine Safely.uncountT (popperV_envGC _ _ ⟨symT "top", 1⟩ hL sQ.st.1 (_, 0) ⟨hQ.frame, ghost₀_gw _, ?_⟩)
  have htt := hL.top_t
  simp only [σInitX, tRes, popRes, Res.initOf, Perm.init, popFrac]
  simp [Ne.symm htt, Views.getFwd]
  exact ⟨by grind, hT0⟩

end Start

/-! ## Purity -/

/-- The verbatim threads' all-release specifications (the image, unmasked). -/
noncomputable def treiberNoNTSpecV : Nat → RelPureSpecQX Arch.tso fun _ _ => False
  | 0 =>
    { S := pushS (symT "top") (symT "n1")
      le16 := pushS_le16 _ _
      e := layout treiberImageV
      valid := inferInstance
      endPc := labT "pdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labT "pdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }
  | _ + 1 =>
    { S := sAll
      le16 := sAll_le16
      e := layout treiberImageV
      valid := inferInstance
      endPc := labT "qdone"
      post := fun x => ∃ _ : Nat, (x.1.2 = labT "qdone" ∧ True) ∨ False
      post_end := fun _ h => h.elim fun _ h => h.elim And.left False.elim }

set_option maxRecDepth 8000 in
/-- **The all-release specifications hold at the start states.** -/
theorem treiberNoNTSpecV_init {sP sQ : State} (hP : StartPushV sP) (hQ : StartPopV sQ) :
    ∀ tid s, [sP, sQ][tid]? = some s → (treiberNoNTSpecV tid).Holds s
  | 0, s, hs => by
    cases hs
    refine ⟨hP.exe, hP.endPc, hP.decls, hP.split, ?_⟩
    rw [show sP.st = (sP.st.1, labT "pusher") from Prod.ext rfl hP.pc]
    exact Safely.uncountT (pusherV_noNT _ _ sP.st.1 ((), 0) hP.frame)
  | 1, s, hs => by
    cases hs
    refine ⟨hQ.exe, hQ.endPc, hQ.decls, split_sAll hQ.dmem, ?_⟩
    rw [show sQ.st = (sQ.st.1, labT "popper") from Prod.ext rfl hQ.pc]
    exact Safely.uncountT (popperV_noNT _ sQ.st.1 ((), 0) hQ.frame)

/-! ## `NPSafeF` and the theorem -/

/-- **The `NPSafeF` side of Theorem 1′ for the verbatim `treiber_pp`.** -/
theorem treiberV_npSafeF (htn : symT "top" ≠ symT "n1" + 8) {sP sQ : isa.State} {initMem : List (Loc × Val)}
    (hP : StartPushV sP) (hQ : StartPopV sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0) :
    ∀ tid, tid < [sP, sQ].length → ∀ k j, NPSafeF (model isa) Arch.tso (TBX (tPX (symT "top") (symT "n1")) (symT "n1"))
      tid k j True (Config.init [sP, sQ] initMem)
      (tRes (Config.init [sP, sQ] initMem).mem (tPX (symT "top") (symT "n1")) tid)
      (ghost₀ (tPX (symT "top") (symT "n1"))) := by
  intro tid htid k j
  rcases tid with _ | _ | i
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPushV_init htn hP)
  · exact NPSafeF.of_ruleRXF _ k j _ _ _ _ (invPopV_init htn hQ hT0)
  · simp only [List.length_cons, List.length_nil] at htid; omega

/-- **The Treiber stack `LockFree/X64/treiber_pp.kl` for x64 under
`Arch.tso`, the `.kl`'s code verbatim**: for every valid layout of the image
`treiberImageV` (the `code` block, then the runner's data trailer placing
`top` and `n1`), if the symbols' `Loc`s are distinct as in
`x64_treiber_pp_envG` (`top ≠ n1 + 8`), thread `0` starts at `pusher` with
end `pdone`, `%rdi = top`, `%rbx = n1` and neither `top` nor the node's words
in its private memory (`StartPushV`), thread `1` starts at `popper` with end
`qdone`, `%rdi = top` and an empty private memory (`StartPopV`), and `top`
is initially `0`, then every final configuration reachable under `Arch.tso`
has the popper's `r10 = n1` and `r11d = 1` (the `.kl`'s
`forall (1:r10=n1 /\ 1:r11=1)`). -/
theorem x64_treiber_pp_envG_verbatim {fuel : Nat} (htn : symT "top" ≠ symT "n1" + 8) {sP sQ : isa.State}
    {initMem : List (Loc × Val)} (hP : StartPushV sP) (hQ : StartPopV sQ)
    (hT0 : (Config.init [sP, sQ] initMem).mem.initVal ⟨symT "top", 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init [sP, sQ] initMem) cfg)
    (hf : cfg.final = true) :
    ∃ th, cfg.threads[1]? = some th ∧ th.st.st.1.regs.get64 .r10 = symT "n1" ∧
      BitVec.setWidth 32 (th.st.st.1.regs.get64 .r11) = 1 := by
  have hL := tLocs_tPX htn
  refine CmpxPublic.final_of_relPureSafelyQX_tsoF' (B := TBX (tPX (symT "top") (symT "n1")) (symT "n1"))
    (Φ := PopperFinalX (symT "n1"))
    (erase_init hL _) (ghost₀_pend _) treiberNoNTSpecV (treiberNoNTSpecV_init hP hQ)
    (treiberV_npSafeF htn hP hQ hT0) hc hf fun rF' g' E' _ hsize hB => ?_
  have h0 : (0 : Nat) < cfg.threads.size := by rw [hsize]; simp
  have h1 : (1 : Nat) < cfg.threads.size := by rw [hsize]; simp
  rcases hB 1 (Config.final_done hf h1) with hfin | hq1
  · exact hfin
  rcases hB 0 (Config.final_done hf h0) with hfin | hq0
  · exact hfin
  have := E'.q_add_le_one h0 h1 (by decide) (tPX (symT "top") (symT "n1")).top
  exfalso
  grind

end Kraken.Promising.X64.EnvG.TreiberAbs

#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.x64_treiber_pp_envG_verbatim
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.pushRuleV_noFault
#print axioms Kraken.Promising.X64.EnvG.TreiberAbs.popRuleV_noFault
