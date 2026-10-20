/-
**The x64 Treiber stack of `treiber_pp.kl`, the `.kl` code verbatim, on
`EnvGCX` by `vcgen`**: the `code` block of
`Kraken/Examples/LockFree/X64/treiber_pp.kl` as written (`treiberCodeV`: the
pusher, `pdone: nop`, the popper, `qdone:`), run by both threads in its image
`treiberImageV` (the code, then the `.kl` runner's data trailer
`treiberDataV`). The x64 Treiber proof's theorem proves the per-thread texts
`treiberPusherX` and `treiberPopperX` laid out on their own; this file proves
the threads as the runner runs them: thread `0` from the entry label
`pusher` to the exit label `pdone`, thread `1` from `popper` to `qdone`.

The fragments are the x64 Treiber proof's texts: their blocks are the image's
(`Program.subBlocksOfE`, by `decide`; the pusher's exit block `pdone:` is
empty, the image's `pdone` block, `nop`, is never run). The tables, VCs and
scripts are the x64 Treiber proof's (`EnvG/X64TreiberVCGen.lean`,
`EnvG/X64TreiberRelPure.lean`), unchanged; only the placement is
`cfgEnv_partial_at` (`Kraken/EnvCfgAbs.lean`).

- `pusherV_envGC`, `popperV_envGC`: the runs in the counted `EnvGCX`;
- `pusherV_noNT`, `popperV_noNT`: the runs in the all-release environment.
-/
import Kraken.Promising.SLR.EnvG.X64TreiberVCGen
import Kraken.Promising.SLR.EnvG.X64TreiberRelPure
import Kraken.EnvCfgAbs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Treiber Kraken.Promising.SLR.EnvG.TreiberCommon
open Kraken.Promising.X64.EnvG.TreiberX
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.TreiberAbs

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The program and its image -/

/-- **The `code` block of `treiber_pp.kl`, verbatim.** -/
def treiberCodeV : Program := parse("
pusher:
  movl $1,(%rbx)
push:
  movq (%rdi),%rax
  movq %rax,8(%rbx)
  lock cmpxchgq %rbx,(%rdi)
  jne push
  jmp pdone
pdone:
  nop
popper:
  movq (%rdi),%rax
  testq %rax,%rax
  je popper
  movq 8(%rax),%rcx
  lock cmpxchgq %rcx,(%rdi)
  jne popper
  movq %rax,%r10
  movl (%rax),%r11d
  jmp qdone
qdone:
")

/-- The `.kl` runner's data trailer of `treiber_pp.kl`: each symbol a label
behind a padding cell, in the order of first mention (`top`, `n1`). -/
def treiberDataV : Program := [.byteArray (.mk #[]), .label "top", .byteArray (.mk #[]), .label "n1"]

/-- The image: the code, then the data trailer. -/
def treiberImageV : Program := treiberCodeV ++ treiberDataV

/-- info: 21 -/
#guard_msgs in
#eval treiberCodeV.length

theorem treiberImageV_wf : Program.WF treiberImageV := by decide

theorem pusherFragV_sub : Program.subBlocksOfE treiberPusherX treiberImageV = true := by decide

theorem popperFragV_sub : Program.subBlocksOfE treiberPopperX treiberImageV = true := by decide

/-! ## The pusher in any code environment

The pusher's run does not depend on where its fragment sits: any code
environment that places `treiberPusherX` (`Program.PlacedIn`) runs it from
`pusher` to `pdone`. The image (`pusherV_envGC`) and the pusher's mask
(`pusherM_envGC'`, `EnvG/X64TreiberAbsMask.lean`) are its instances (the script
is the x64 absolute-address proofs', unchanged). -/

section AnyEnv

variable [CodeEnv]

/-- The pusher fragment's exit block (`pdone:`, empty) ends at `pdone`, in
any code environment. -/
theorem pusherFrag_last : ∀ l blk, Program.blockAt treiberPusherX l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body =
      (_root_.Executable.labels cenv).label "pdone" := by
  intro l blk hb hn
  have hm := Program.blockAt_mem_labels hb
  have hls : Program.labels treiberPusherX = ["pusher", "push", "pdone"] := by decide
  rw [hls] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · have hw : (Program.blockAt treiberPusherX "pusher").map (·.next) = some (some "push") := by decide
    rw [hb] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    rw [hn] at hw; cases hw
  · have hw : (Program.blockAt treiberPusherX "push").map (·.next) = some (some "pdone") := by decide
    rw [hb] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    rw [hn] at hw; cases hw
  · have hd : (Program.blockAt treiberPusherX "pdone").map (·.body) = some [] := by decide
    rw [hb] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    rw [hd]; rfl

/-- **The verbatim x64 pusher on `EnvGCX` in any code environment placing
`treiberPusherX`** (counted, partial), at that environment's labels. -/
theorem pusher_envGC_of (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok))
    (hpl : Program.PlacedIn treiberPusherX) :
    ∀ s g, PFrameX t n s ∧ Pu0 (tParamsX t n tok) g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EPX t n tok)))
        (fun x => (x.1.2 = (_root_.Executable.labels cenv).label "pdone" ∧ Pd (tParamsX t n tok) x.2.1) ∨ False)
        ((s, (_root_.Executable.labels cenv).label "pusher"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EPX t n tok))
    (Q := fun _ σ => Pd (tParamsX t n tok) σ.1) (E := fun _ _ _ => False) (pushTableX t n tok) ?_ rfl
    (by decide) hpl pusherFrag_last s g (by simpa [pushTableX] using hsg)
  cfg_cases_env [treiberPusherX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hx1, hdt, hdd, hdn⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  -- cut `pusher`: `movl $1, (%rbx)`
  case vc1 => simp [hx1, hdd]
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    exact vc_push_str_d_ok_at hL _ hT (by simp [hx1]) (by decide)
  case vc3 =>
    rename_i b σ1 hst _
    exact ⟨⟨by simp [hx0], by simp [hx1], hdt, hdd, hdn⟩,
      .inr (.inl ⟨rfl, vc_push_str_d_at hL _ hT (by simp [hx1]) (by decide) b σ1.1 hst.1⟩)⟩
  -- cut `push`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    exact trivial
  case vc2 =>
    rename_i v σ1 hld hnone _
    have hP : Pu (tParamsX t n tok) σ1.1 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · exact vc_push_load_at _ hT w σ1.1 hst.1
    simp only [SharedEnv.counted_ok]
    exact vc_push_str_n_ok_at hL _ hP _ (by simp [hx1])
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc4 =>
    rename_i v σ1 hld dm σ2 hst _
    have hP : Pu (tParamsX t n tok) σ1.1 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · exact vc_push_load_at _ hT w σ1.1 hst.1
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP _ (by simp [hx1]) _ σ2.1 h
    simp only [SharedEnv.counted_ok]
    exact vc_push_cas_ok_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64])
  case vc5 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf1 σ5 hf2 _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    rcases hc with ⟨hne, -⟩ | ⟨-, hPd⟩
    · exact absurd heq hne
    · exact Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdt,
        by simpa using hdd, by simpa using hdn⟩, .inr (.inr ⟨rfl, Pd.fence (Pd.fence hPd hf1.1) hf2.1⟩)⟩,
        .inl (by decide)⟩
  case vc7 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simp [hx1], by simpa using hdt,
        by simpa using hdd, by simpa using hdn⟩, .inr (.inl ⟨rfl, Pu.fence hPu hf.1⟩)⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have h4 := hf.2
      omega
    · exact absurd heq' heq
  case vc8 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz σ4 hf1 σ5 hf2 _
    have hP : Pu (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_push_load_at _ hT w σ1.1 hst.1, by omega⟩
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, hso, hst2⟩ := hst
    subst hdm
    have hP2 : Pu (tParamsX t n tok) σ2.1 := by
      rcases hso with h | h <;> exact vc_push_str_n_at hL _ hP.1 _ (by simp [hx1]) _ σ2.1 h
    have hc := vc_push_cas_at hL _ hP2 v (by simp [hx0]) (by simp [hx1, cmpxOp64]) old σ3.1 hcas.1
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by bv_omega) heq
  -- cut `pdone`
  case vc1 => exact hT

end AnyEnv

/-! ## The symbols -/

variable [layout : _root_.Layout]

/-- A label's address in the image. -/
abbrev labT (x : Label) : Int64 := (_root_.Executable.labels (layout treiberImageV)).label x

/-- A symbol's address in the image. -/
abbrev symT (x : Label) : BitVec 64 := (labT x).toBitVec

variable [Executable.ValidLayout (layout treiberImageV)]

local instance treiberImageV.env : CodeEnv := ⟨layout treiberImageV⟩

theorem pusherFragV_placedIn : Program.PlacedIn treiberPusherX :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageV) treiberImageV_wf rfl (by decide))
    pusherFragV_sub

theorem popperFragV_placedIn : Program.PlacedIn treiberPopperX :=
  Program.PlacedIn.of_placedE (Program.placed_of_layout (p := treiberImageV) treiberImageV_wf rfl (by decide))
    popperFragV_sub

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem pusherFragV_last : ∀ l blk, Program.blockAt treiberPusherX l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labT "pdone" :=
  pusherFrag_last

omit [Executable.ValidLayout (layout treiberImageV)] in
theorem popperFragV_last : ∀ l blk, Program.blockAt treiberPopperX l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labT "qdone" :=
  Program.after_last_of (by decide)

/-! ## The pusher -/

/-- **The verbatim x64 pusher on `EnvGCX`** (counted, partial;
`TreiberX.pusherX_envGC` in the image). -/
theorem pusherV_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    ∀ s g, PFrameX t n s ∧ Pu0 (tParamsX t n tok) g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EPX t n tok)))
        (fun x => (x.1.2 = labT "pdone" ∧ Pd (tParamsX t n tok) x.2.1) ∨ False) ((s, labT "pusher"), g) :=
  pusher_envGC_of t n tok hL pusherFragV_placedIn

/-! ## The popper -/

/-- **The verbatim x64 popper on `EnvGCX`** (counted, partial;
`TreiberX.popperX_envGC` in the image). -/
theorem popperV_envGC (t n : BitVec 64) (tok : Loc) (hL : TLocs (tParamsX t n tok)) :
    ∀ s g, QFrameX t s ∧ Pp (tParamsX t n tok) g.1 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EQX t n tok)))
        (fun x => (x.1.2 = labT "qdone" ∧ PopPostX n x.1.1 x.2.1.cl) ∨ False) ((s, labT "popper"), g) := by
  intro s g hsg
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EQX t n tok))
    (Q := fun s σ => PopPostX n s σ.1.cl) (E := fun _ _ _ => False) (popTableX t n tok) ?_ rfl
    (by decide) popperFragV_placedIn popperFragV_last s g (by simpa [popTableX] using hsg)
  cfg_cases_env [treiberPopperX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨⟨hx0, hd8, hd4⟩, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [Reg64s.get64] at hx0
  -- cut `popper`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    -- `je popper` taken
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl ⟨rfl, hP3⟩⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have := hf1.2
    have := hf2.2
    omega
  case vc3 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll8 _⟩
  case vc4 => simp [hd8]
  case vc5 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    simp only [SharedEnv.counted_ok]
    exact vc_pop_cas_ok_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64])
  case vc6 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz2
  case vc7 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll4 _⟩
  case vc8 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 σ7 hf4 w σ8 hld3 σ9 hf5 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf3 hf4 hf5
    rcases hc with ⟨hne, -⟩ | ⟨-, hPc⟩
    · exact absurd heq hne
    have hPc7 := (hPc.fence hf3.1).fence hf4.1
    rcases hld3 with ⟨w', hw, -, -⟩ | ⟨-, w', hlo, hv⟩
    · simp [hd4] at hw
    have hfin := vc_pop_ldr_at _ v hPc7 (by simp) w' σ8.1 hlo.1
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr ⟨rfl, fun hcl => ?_⟩⟩, .inl (by decide)⟩
    obtain ⟨h1, h2⟩ := hfin (hf5.1.cl ▸ hcl)
    subst hv
    simp
    exact ⟨h1.symm, h2⟩
  case vc9 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf3
    rcases hc with ⟨-, hPp⟩ | ⟨heq', -⟩
    · refine Table.ofLabelsEnv_at ⟨by decide, ⟨⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl ⟨rfl, hPp.fence hf3.1⟩⟩,
        .inr fun ⟨_, hg⟩ => ?_⟩
      subst hg
      have := hf1.2
      have := hf2.2
      have := hf3.2
      omega
    · exact absurd heq' heq
  case vc10 =>
    simp only [SharedEnv.counted_ok]
    exact ⟨trivial, mem_sAll4 _⟩
  case vc11 =>
    rename_i σ v σ1 hld af σ2 hf1 hz σ3 hf2 v4 σ4 hld2 old σ5 hcas heq hz2 σ6 hf3 σ7 hf4 w σ8 hld3 σ9 hf5 _
    simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCX] at hf1 hf2
    have hP1 : Pp (tParamsX t n tok) σ1.1 ∧ σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hT w σ1.1 hst.1, by omega⟩
    have hP3 : Pp (tParamsX t n tok) σ3.1 := (hP1.1.fence hf1.1).fence hf2.1
    simp [CondCode.interp, StatusFlags.from_result] at hz
    have hP4 : Pp (tParamsX t n tok) σ4.1 ∧ σ3.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        exact ⟨vc_pop_load_at _ hP3 w σ4.1 hst.1, by omega⟩
    have hc := vc_pop_cas_at hL _ hP4.1 v v4 hz (by simp [hx0]) (by simp [cmpxOp64]) old σ5.1 hcas.1
    have h5 := hcas.2
    simp only [SharedAccess.tick] at h5
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz2
    exact absurd (by bv_omega) heq
  -- cut `qdone`
  case vc1 => exact hT ‹_›

/-! ## Only release writes -/

/-- **The verbatim pusher makes only release writes** (counted, partial). -/
theorem pusherV_noNT (t n : BitVec 64) :
    ∀ s g, PFrameX t n s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT (pushS t n))))
        (fun x => (x.1.2 = labT "pdone" ∧ True) ∨ False) ((s, labT "pusher"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT (pushS t n))) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT (pushS t n))).State) =>
      PFrameX t n s) ?_ rfl (by decide) pusherFragV_placedIn pusherFragV_last s g hs
  cfg_cases_env [treiberPusherX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hdt, hdd, hdn⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0 hx1
  all_goals have hdn' : Mem.loadInt _ (n + 8#64) 8 = none := hdn
  -- cut `pusher`
  case vc1 => simp [hx1, hdd]
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc3 => exact ⟨by simp [hx0], by simp [hx1], hdt, hdd, hdn⟩
  -- cut `push`
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc2 =>
    simp only [SharedEnv.counted_ok]
    simp [hx1]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc3 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp [hx0, hdt]
  case vc4 =>
    rename_i v σ1 hld dm σ2 hst _
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -⟩ := hst
    subst hdm
    simp only [SharedEnv.counted_ok]
    simp [hx0]
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc5 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by rw [heq]; exact BitVec.sub_self _) hz
  case vc6 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inl (by decide)⟩
  case vc7 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hdt, by simpa using hdd, by simpa using hdn⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc8 =>
    rename_i σ v σ1 hld dm σ2 hst old σ3 hcas heq hz _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hx0, hdt] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    simp [hx1, hdn'] at hst
    obtain ⟨hdm, -, hst2⟩ := hst
    subst hdm
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result] at hz
    exact absurd (by bv_omega) heq

/-- **The verbatim popper makes only release writes** (counted, partial). -/
theorem popperV_noNT (t : BitVec 64) :
    ∀ s g, QFrameX t s →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labT "qdone" ∧ True) ∨ False) ((s, labT "popper"), g) := by
  intro s g hs
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun (_ : Label) s (_ : (SharedEnv.counted (EnvRT sAll)).State) =>
      QFrameX t s) ?_ rfl (by decide) popperFragV_placedIn popperFragV_last s g hs
  cfg_cases_env [treiberPopperX]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
  all_goals simp only [Reg64s.get64] at hx0
  case vc1 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc2 =>
    rename_i σ v σ1 hld af hz _
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
    · simp [hd8] at hm
    · have h1 := hst.2
      simp only [SharedAccess.tick] at h1
      omega
  case vc3 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc4 => simp [hd8]
  case vc5 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc6 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h2 : σ1.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc7 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc8 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i σ v σ1 hld af hz v4 σ4 hld2 old σ5 hcas heq hz2 _
    have h1 : σ.2 < σ1.2 := by
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h2 : σ1.2 ≤ σ4.2 := by
      rcases hld2 with ⟨w, hm, -, -⟩ | ⟨-, w, hst, -⟩
      · simp [hd8] at hm
      · have h1 := hst.2
        simp only [SharedAccess.tick] at h1
        omega
    have h3 := hcas.2
    simp only [SharedAccess.tick] at h3
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    omega
  case vc10 =>
    simp only [SharedEnv.counted_ok]
    refine ⟨?_, by first | exact mem_sAll8 _ | exact mem_sAll4 _⟩
    simp
    first | trivial | exact fun h => absurd rfl h | exact fun h => h rfl | (simp [SharedEnv.relPureQ]; done)
  case vc11 => exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd8, by simpa using hd4⟩, .inl (by decide)⟩

end Kraken.Promising.X64.EnvG.TreiberAbs
