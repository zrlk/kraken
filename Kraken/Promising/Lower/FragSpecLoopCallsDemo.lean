/-
**Demo: a retry loop around a call.** ISA: AArch64; machine: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness, as
`FragSpecEnvL` (`Lower/FragSpecCalls.lean`), built by
`FragSpecEnvL.of_cfgP` (`Lower/FragSpecLoopCalls.lean`).

`popw` is "pop until non-empty": it calls `pop` in a loop until `pop` returns
a non-null node.

    popw:      mov x19, x30        // the return address, kept over the calls
    popw_loop: mov x0, x20         // `top`, kept in callee-saved x20
               bl pop
               cbz x0, popw_loop   // empty: retry
               mov x30, x19
               ret

`pop`'s `FragSpecEnv` is the one-spec-per-fragment layer's purity twin `Uni.popFrag_pureU`
(`Lower/FragSpecUni.lean`), used as is (never re-proved). The loop's back edge
follows a call, so its block is a stepping `PartialWpEnvS`
(`PartialWpEnvS.call_triples`) and needs no `EdgeSafe` (`pop`'s spec does not
say the state changed). The entry block is a plain `vcgen` block
(`PartialWpEnv.of_triple`). The post adds what the loop establishes:
`x0 ≠ 0`.

The protocol spec `Uni.popFrag_specU` is not retried here: its empty result
gives `DnD` (the pop is done) rather than `Po` back, so `pop`'s precondition
fails on the second iteration. A retryable protocol post would have to give
`pop`'s precondition back in the empty case (`x0 = 0 → Po P w σ'`: an empty
read that leaves the thread's protocol state as it was, instead of recording
a finished pop). The loop rule itself puts no condition on the callee.

The spec is placed by `[popwFrag, popFrag]` and transported to the laid-out
program `loopDemo` (`pop` first, `popw` behind it) in one line.
-/
import Kraken.Promising.Lower.FragSpecLoopCalls
import Kraken.Promising.Lower.FragSpecCallsDemo

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.LoopCalls

open Kraken.Promising.Lower.Uni (popFrag_pureU)
open Kraken.Promising.Lower.Pilot (CalleeSaved RP popFrag)
open Kraken.Promising.Lower.Pilot2 (Saved2)
open Kraken.Promising.Lower.Calls
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

theorem SavedX19.refl (t : MachineData) : SavedX19 t t := by
  simp [SavedX19]

/-- `popw`'s text. -/
def popwFrag : Program := parseAArch64("
popw:
    mov x19, x30
popw_loop:
    mov x0, x20
    bl pop
    cbz x0, popw_loop
    mov x30, x19
    ret
")

/-- The loop block's prefix: `top` into `x0`. -/
def popwA : Program := parseAArch64("
    mov x0, x20
")

/-- The loop block's suffix: retry on empty, else restore `x30`, return. -/
def popwB : Program := parseAArch64("
    cbz x0, popw_loop
    mov x30, x19
    ret
")

/-- `popw`'s precondition: `x20 = top`, the frame `F`. -/
def PopwPre (tp : BitVec 64) (F : Mem 64 → Prop) {rel : Loc → Pred} (ra : Int64) (t : MachineData)
    (_ : (RP rel).State) : Prop :=
  t.lr = ra ∧ t.regs.X20.toBitVec = tp ∧ F t.dmem

/-- `popw`'s postcondition: `SavedX19`, the frame, a non-null node in `x0`. -/
def PopwPost (F : Mem 64 → Prop) {rel : Loc → Pred} (_ : Int64) (t : MachineData) (_ : (RP rel).State)
    (t' : MachineData) (_ : (RP rel).State) : Prop :=
  SavedX19 t t' ∧ F t'.dmem ∧ t'.regs.X0.toBitVec ≠ 0

/-- `popw`'s loop table: the frame so far, and the return address in `x30`
(entry) or `x19` (the loop). -/
def popwTable (F : Mem 64 → Prop) {rel : Loc → Pred} (ra : Int64) (t : MachineData) (_ : (RP rel).State)
    (l : Label) (s : MachineData) (_ : (RP rel).State) : Prop :=
  SavedX19 t s ∧ F s.dmem ∧
    ((l = "popw" ∧ s.lr = ra) ∨ (l = "popw_loop" ∧ Int64.ofBitVec s.regs.X19.toBitVec = ra))

/-- **`popw`'s spec** ("pop until non-empty"), from `pop`'s, by
`FragSpecEnvL.of_cfgP`: a call inside a retry loop. -/
theorem popw_spec (rel : Loc → Pred) (tp : BitVec 64) (F : Mem 64 → Prop)
    (hF : ∀ d, F d → Mem.loadInt d tp 8 = none) :
    FragSpecEnvL (RP rel) [popwFrag, popFrag] "popw" (PopwPre tp F) (PopwPost F) := by
  refine FragSpecEnvL.of_cfgP (popwTable F) rfl (by decide)
    (fun ra t g ⟨hlr, _, hd⟩ => ⟨SavedX19.refl t, hd, .inl ⟨rfl, hlr⟩⟩) ?_
  intro _ hpl ra t g hpre
  have hpop := (popFrag_pureU rel tp F hF).toL.at_sub hpl fun p hp => List.mem_cons_of_mem _ hp
  cfg_cases_env [popwFrag]
  · -- the entry block: a plain `vcgen` block, falling into the loop
    intro s₀ g₀ hT
    refine .inl (PartialWpEnv.of_triple (P := fun s g' => popwTable F ra t g "popw" s g' ∧ s = s₀ ∧ g' = g₀)
      ?_ ⟨hT, rfl, rfl⟩)
    vcgen
    obtain ⟨⟨hfr, hd, hlr⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
    simp (config := { decide := true }) only [true_and, false_and, or_false] at hlr
    simp only [MachineData.lr] at hlr
    simp_all [popwTable, SavedX19]
  · -- the loop block: `mov x0, x20; bl pop; cbz x0, popw_loop; …`, stepping
    intro s₀ g₀ hT
    refine .inr (PartialWpEnvS.call_triples (A := popwA) (B := popwB) hpop
      (P := fun s g' => popwTable F ra t g "popw_loop" s g' ∧ s = s₀ ∧ g' = g₀)
      (Mid1 := fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ s.regs.X0.toBitVec = tp ∧
        SavedX19 t s ∧ F s.dmem)
      (Mid2 := fun s _ => Int64.ofBitVec s.regs.X19.toBitVec = ra ∧ SavedX19 t s ∧ F s.dmem)
      ?_ ⟨hT, rfl, rfl⟩ ?_ ?_)
    · unfold popwA
      vcgen
      obtain ⟨⟨hfr, hd, h19⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      simp (config := { decide := true }) only [false_and, false_or, true_and] at h19
      obtain ⟨-, h20, -⟩ := hpre
      rw [← hfr.1] at h20
      simp_all [SavedX19]
    · rintro s σ ⟨h19, hx0, hfr, hd⟩ ra'
      refine ⟨⟨by simp [MachineData.lr, MachineData.setLr], by simpa [MachineData.setLr] using hx0,
        by simpa [MachineData.setLr] using hd⟩, ?_⟩
      rintro s' σ' ⟨hs, hd'⟩
      refine ⟨?_, hfr.trans ?_, hd'⟩
      · rw [hs.1.1]; simpa [MachineData.setLr] using h19
      · simpa [SavedX19, MachineData.setLr, Reg64s.setXReg] using Saved2.savedX19 hs
    · intro s₁ g₁
      unfold popwB
      vcgen
      all_goals obtain ⟨⟨h19, hfr, hd⟩, rfl, rfl⟩ := ‹_ ∧ _ = _ ∧ _ = _›
      · exact .inl (Table.ofLabelsEnv_at ⟨by decide, hfr, hd, .inr ⟨rfl, h19⟩⟩)
      · rename_i hnz _
        refine .inr ⟨by simpa using h19, ?_⟩
        simp_all [PopwPost, SavedX19]

/-! ## Instantiation at a program -/

/-- `pop` and `popw` laid out in one text (`pop` first: `popw`'s spec is
placed by its own fragments, in any order). -/
def loopDemo : Program := popFrag ++ popwFrag

section Prog

variable [layout : _root_.Layout] [Executable.ValidLayout (layout loopDemo)]

local instance loopDemo.env : CodeEnv := ⟨layout loopDemo⟩

omit layout [Executable.ValidLayout (layout loopDemo)] in
theorem loopDemo_wf : Program.WF loopDemo := by decide

/-- Where `loopDemo`'s blocks sit. -/
theorem loopDemo_placed : Program.Placed loopDemo "pop" :=
  Program.placed_of_layout loopDemo_wf rfl (by decide)

/-- **`popw`'s spec in `loopDemo`.** -/
theorem popw_spec_at (rel : Loc → Pred) (tp : BitVec 64) (F : Mem 64 → Prop)
    (hF : ∀ d, F d → Mem.loadInt d tp 8 = none) :
    FunSpecPartialEnv (RP rel) ((_root_.Executable.labels cenv).label "popw") (PopwPre tp F) (PopwPost F) :=
  (popw_spec rel tp F hF).of_placed loopDemo_placed (by decide)

end Prog

end Kraken.Promising.Lower.LoopCalls
