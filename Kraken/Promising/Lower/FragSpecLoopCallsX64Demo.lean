/-
**Demo: a retry loop around a register-link call,
x64.** ISA: x64; environment: the all-release
environment on the whole layout, counted (`RPX = counted (EnvRT sAll)`, the
environment of the x64 register-link pilot's purity twin `pilotXR_pure`); machine: the executable
machine's per-thread environment semantics (`Executable.instrStepEnv`),
partial correctness, as `FragSpecEnvL` (`Lower/FragSpecCallsX64.lean`), built
by `FragSpecEnvL.of_cfgP` (`Lower/FragSpecLoopCallsX64.lean`).

`popw` is "pop until non-empty": it calls the x64 register-link pilot's `pop` (`popFragXR`, the
text as is) in a loop until `pop` returns a non-null node.

    popw:      movq %r11, %rbp            // the return address, kept over the calls
    popw_loop: movq %rbx, %rdi            // `top`, kept in callee-saved rbx
               leaq popw_ret(%rip), %r11
               jmp pop
    popw_ret:  testq %rax, %rax
               je popw_loop               // empty: retry
               jmp *%rbp

**`pop`'s spec.** the x64 register-link pilot's `pop_specXR` cannot be used as is: it is a
`FunSpecPartialEnv` in `pilotXR`'s layout (not a `FragSpecEnv`), and its post
is the protocol's `Dn`, which is not retryable (an empty result records a
finished pop, so `pop`'s `Po` precondition fails on the second iteration; as on
AArch64). The x64 register-link pilot's purity twin `pilotXR_pure` is a
whole-program run with no function specs. So `popFragXR_pure` here is a new
placement-independent purity spec of `popFragXR` (`FragSpecEnv.of_cfg`, the
VCs of `pilotXR_pure`'s `pop` blocks): link `r11 = ra`, `dmem` maps no word
(`D8`); post the x64 pilot's callee-saved `Saved` and `D8`.

The loop block is `PartialWpEnvS.call_triples`: the call block and the
return block `popw_ret` together, stepping, so the `je popw_loop` back edge
needs no `EdgeSafe`; `popw_ret`'s own table entry is `False` (entered only
from `pop`'s return). The entry block is a plain `vcgen` block
(`PartialWpEnv.of_triple`). The post adds what the loop establishes:
`rax ≠ 0`.
-/
import Kraken.Promising.Lower.FragSpecLoopCallsX64
import Kraken.Promising.Lower.PilotXRPure

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.LoopCallsX

open Kraken.Promising.X64.EnvG.TreiberX (sAll mem_sAll8 EnvRT)
open Kraken.Promising.X64.EnvG.Treiber2X (ldN)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.Promising.Lower.PilotXR (D8 popFragXR ofBitVec_reg)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The environment: all-release on the whole layout, counted. -/
abbrev RPX : SharedEnv := SharedEnv.counted (EnvRT sAll)

/-! ## `pop`, pure -/

/-- `pop`'s purity precondition: the link `r11 = ra`, `dmem` maps no word. -/
def PopPreP (ra : Int64) (t : MachineData) (_ : RPX.State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ D8 t.dmem

/-- `pop`'s purity postcondition: the callee-saved frame, `dmem` empty. -/
def PopPostP (_ : Int64) (t : MachineData) (_ : RPX.State) (s : MachineData) (_ : RPX.State) : Prop :=
  Saved t s ∧ D8 s.dmem

/-- **`pop` is pure** (placement-independent): the x64 register-link pilot's `popFragXR` makes
only release writes and returns to its link with the callee-saved frame. -/
theorem popFragXR_pure : FragSpecEnv RPX popFragXR "pop" PopPreP PopPostP := by
  refine FragSpecEnv.of_cfg (fun ra t _ lb s _ => s.regs.get64 .r11 = ra.toBitVec ∧ Saved t s ∧ D8 s.dmem ∧
      (lb = "pop" ∨ lb = "pop_nz")) rfl (by decide)
    (fun ra t g ⟨h1, h2⟩ => ⟨h1, Saved.refl t, h2, .inl rfl⟩) ?_
  intro _ ra t g _
  cfg_cases_env [popFragXR]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨h11, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step,
    SharedEnv.within_ok_load, SharedEnv.within_ok_rmw, SharedEnv.tick_load, SharedEnv.tick_rmw] at *
  all_goals first
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | exact hd8 _
    | skip
  -- `pop`: to `pop_nz` (forward), or the empty return
  case vc2 =>
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8, .inr rfl⟩,
      .inl (by decide)⟩)
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc3 =>
    refine .inr ⟨by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact ofBitVec_reg h11,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  -- `pop_nz`
  case vc4 =>
    rename_i u σ1 old σ2 heq hz hld hcas _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc5 =>
    refine .inr ⟨by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact ofBitVec_reg h11,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc6 =>
    rename_i u σ1 old σ2 hne hz hld hcas _
    have h1 := ldN hd8 hld; have h3 := hcas.2
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩)
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc7 =>
    rename_i u σ1 old σ2 hne hz hld hcas _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

/-! ## `popw`: a retry loop around the call -/

/-- `popw`'s text. -/
def popwFragX : Program := parse("
popw:
    movq %r11, %rbp
popw_loop:
    movq %rbx, %rdi
    leaq popw_ret(%rip), %r11
    jmp pop
popw_ret:
    testq %rax, %rax
    je popw_loop
    jmp *%rbp
")

/-- The loop block's prefix: `top` into `rdi`. -/
def popwAX : Program := parse("
    movq %rbx, %rdi
")

/-- The return block's body: retry on empty, else return through `rbp`. -/
def popwBX : Program := parse("
    testq %rax, %rax
    je popw_loop
    jmp *%rbp
")

theorem blockAt_popwRet : Program.blockAt popwFragX "popw_ret" = some ⟨"popw_ret", popwBX, none⟩ := by
  decide

/-- `popw`'s precondition: the link `r11 = ra`, `dmem` maps no word. -/
def PopwPreX (ra : Int64) (t : MachineData) (_ : RPX.State) : Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ D8 t.dmem

/-- `popw`'s postcondition: `rbx` kept, `dmem` empty, a non-null node in
`rax`. -/
def PopwPostX (_ : Int64) (t : MachineData) (_ : RPX.State) (t' : MachineData) (_ : RPX.State) : Prop :=
  t'.regs.get64 .rbx = t.regs.get64 .rbx ∧ D8 t'.dmem ∧ t'.regs.get64 .rax ≠ 0

/-- `popw`'s loop table: `rbx` kept, `dmem` empty, and the return address in
`r11` (entry) or `rbp` (the loop); `popw_ret` is entered only from `pop`'s
return (inside the loop block's `PartialWpEnvS`), so its entry is `False`. -/
def popwTableX (ra : Int64) (t : MachineData) (_ : RPX.State) (l : Label) (s : MachineData) (_ : RPX.State) :
    Prop :=
  s.regs.get64 .rbx = t.regs.get64 .rbx ∧ D8 s.dmem ∧
    ((l = "popw" ∧ s.regs.get64 .r11 = ra.toBitVec) ∨ (l = "popw_loop" ∧ s.regs.get64 .rbp = ra.toBitVec))

/-- **`popw`'s spec** ("pop until non-empty", x64), from `pop`'s purity spec,
by `FragSpecEnvL.of_cfgP`: a register-link call inside a retry loop. -/
theorem popwX_spec : FragSpecEnvL RPX [popwFragX, popFragXR] "popw" PopwPreX PopwPostX := by
  refine FragSpecEnvL.of_cfgP popwTableX rfl (by decide)
    (fun ra t g ⟨h11, hd⟩ => ⟨rfl, hd, .inl ⟨rfl, h11⟩⟩) ?_
  intro _ hpl ra t g _
  have hpop := popFragXR_pure.toL.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  have hplF := hpl popwFragX List.mem_cons_self
  cfg_cases_env [popwFragX]
  · -- the entry block: a plain `vcgen` block, falling into the loop
    intro s₀ g₀ hT
    refine .inl (PartialWpEnv.of_triple (P := fun s g' => popwTableX ra t g "popw" s g' ∧ s = s₀ ∧ g' = g₀)
      ?_ ⟨hT, rfl, rfl⟩)
    vcgen
    obtain ⟨⟨hbx, hd, h11⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp (config := { decide := true }) only [true_and, false_and, or_false] at h11
    refine ⟨?_, hd, .inr ⟨rfl, ?_⟩⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  · -- the loop block with the return block: stepping
    intro s₀ g₀ hT
    refine .inr (PartialWpEnvS.call_triples (A := popwAX) hplF blockAt_popwRet hpop
      (P := fun s g' => popwTableX ra t g "popw_loop" s g' ∧ s = s₀ ∧ g' = g₀)
      (Mid1 := fun s _ => s.regs.get64 .rbp = ra.toBitVec ∧ s.regs.get64 .rbx = t.regs.get64 .rbx ∧ D8 s.dmem)
      (Mid2 := fun s _ => s.regs.get64 .rbp = ra.toBitVec ∧ s.regs.get64 .rbx = t.regs.get64 .rbx ∧ D8 s.dmem)
      ?_ ⟨hT, rfl, rfl⟩ ?_ ?_)
    · unfold popwAX
      vcgen
      obtain ⟨⟨hbx, hd, h⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      simp (config := { decide := true }) only [false_and, false_or, true_and] at h
      refine ⟨?_, ?_, hd⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals assumption
    · rintro s σ ⟨hbp, hbx, hd⟩
      refine ⟨⟨by simp only [Reg64s.get64_set64, ↓reduceIte], hd⟩, ?_⟩
      rintro s' σ' ⟨⟨f1, f2, -, -, -, -, -⟩, hd'⟩
      refine ⟨?_, ?_, hd'⟩
      · rw [f2]; simpa only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] using hbp
      · rw [f1]; simpa only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] using hbx
    · intro s₁ g₁
      dsimp only
      unfold popwBX
      vcgen
      all_goals obtain ⟨⟨hbp, hbx, hd⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      · exact .inl (Table.ofLabelsEnv_at ⟨by decide, hbx, hd, .inr ⟨rfl, hbp⟩⟩)
      · rename_i hnz _
        refine .inr ⟨ofBitVec_reg hbp, hbx, hd, ?_⟩
        simpa [CondCode.interp, StatusFlags.from_result] using hnz
  · -- the return block: entered only from `pop`'s return
    intro s₀ g₀ hT
    simp (config := { decide := true }) [popwTableX] at hT

/-! ## Instantiation at a program -/

/-- `pop` and `popw` laid out in one text (`pop` first: `popw`'s spec is
placed by its own fragments, in any order). -/
def loopDemoX : Program := popFragXR ++ popwFragX

section Prog

variable [layout : _root_.Layout] [Executable.ValidLayout (layout loopDemoX)]

local instance loopDemoX.env : CodeEnv := ⟨layout loopDemoX⟩

omit layout [Executable.ValidLayout (layout loopDemoX)] in
theorem loopDemoX_wf : Program.WF loopDemoX := by decide

/-- Where `loopDemoX`'s blocks sit. -/
theorem loopDemoX_placed : Program.Placed loopDemoX "pop" :=
  Program.placed_of_layout loopDemoX_wf rfl (by decide)

/-- **`popw`'s spec in `loopDemoX`.** -/
theorem popwX_spec_at :
    FunSpecPartialEnv RPX ((_root_.Executable.labels cenv).label "popw") PopwPreX PopwPostX :=
  popwX_spec.of_placed loopDemoX_placed (by decide)

end Prog

end Kraken.Promising.Lower.LoopCallsX

#print axioms Kraken.Promising.Lower.LoopCallsX.popwX_spec_at
#print axioms Kraken.Promising.Lower.LoopCallsX.popFragXR_pure
#print axioms MachineWP.FragSpecEnvL.of_cfgP
#print axioms MachineWP.PartialWpEnvS.call_triples
