/-
**The relPure twin of `pilotXR`.** ISA: x64; environment: the all-release environment on the whole
layout, `EnvRT sAll = (relPureQ Arch.tso ⊥).within sAll`, counted (the
kit's `LowerCoreX.pure`).

With `dmem` empty every access of the thread is a shared `sAll`-access, and
under `Arch.tso` every plain store and every `lock cmpxchgq` is a release:
the twin needs no function specifications, only where the links point.
It is one `cfgEnv_partial_at` over the whole text, its table the link
registers (`twinT`): `r11` the return address in `main` (the end of the
text), in `push` (`ret_push`) and in `pop`/`pop_nz` (`ret_pop`), `rbp`
`main`'s link from `main`'s first instruction on; at `main`, the bump
check's room (`ja oom` not taken; `oom`'s self-loop is not in the table). Each `jmp *%r` exits to a
label of the table (`ofBitVec_reg`).

**Zero-step guard.** `cfgEnv_partial_at` lets an edge go back in the text
only if the state changed (`Program.EdgeSafe`). The two returns
`jmp *%r11` are such backward edges (`push` → `ret_push`, `pop_nz`/`pop` →
`ret_pop`); in the counted environment every shared access counts one, so
each return sits in a block with a shared access (`pilotXR`'s `pop` returns
on empty from its first block, behind the load). The function specs
(`FunSpecPartialEnv.of_cfg`) do not need this: their return is an exit, not
an edge.
-/
import Kraken.Promising.Lower.PilotXRMain

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.PilotXR

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (sAll mem_sAll8 EnvRT)
open Kraken.X64.Parser
open MachineWP (ja_not_taken)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The twin's table**: `dmem` empty, and where the links point (`rM`
`main`'s return address, `rp`/`rq` the return labels of `push`/`pop`). -/
def twinT (rM rp rq : BitVec 64) (lb : Label) (s : MachineData) : Prop :=
  D8 s.dmem ∧
    if lb = "main" then s.regs.get64 .r11 = rM ∧ s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15
    else if lb = "ret_push" ∨ lb = "ret_pop" then s.regs.get64 .rbp = rM
    else if lb = "push" then s.regs.get64 .r11 = rp ∧ s.regs.get64 .rbp = rM
    else if lb = "pop" ∨ lb = "pop_nz" then s.regs.get64 .r11 = rq ∧ s.regs.get64 .rbp = rM
    else lb = "done"

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotXR)]

local instance pilotXR.envP : CodeEnv := ⟨layout pilotXR⟩

omit [Executable.ValidLayout (layout pilotXR)] in
theorem pilotXR_last : ∀ l blk, Program.blockAt pilotXR l = some blk → blk.next = none →
    cenv.after ((_root_.Executable.labels cenv).label l) blk.body = labXR "done" :=
  Program.after_last_of (by decide)

/-- **`pilotXR` makes only release writes** (counted, partial): from `main`
with `dmem` empty, the link `r11` at `done` and room for a node, every run
that stops is at `done`. -/
theorem pilotXR_pure :
    ∀ s g, D8 s.dmem ∧ s.regs.get64 .r11 = (labXR "done").toBitVec ∧
      s.regs.get64 .r14 + 16 ≤ s.regs.get64 .r15 →
      Safely (cenv.instrStepEnv (SharedEnv.counted (EnvRT sAll)))
        (fun x => (x.1.2 = labXR "done" ∧ True) ∨ False) ((s, labXR "main"), g) := by
  rintro s g ⟨hd8, h11, h15⟩
  refine MachineWP.cfgEnv_partial_at (env := SharedEnv.counted (EnvRT sAll)) (Q := fun _ _ => True)
    (E := fun _ _ _ => False) (fun lb s _ => twinT (labXR "done").toBitVec (labXR "ret_push").toBitVec
      (labXR "ret_pop").toBitVec lb s) ?_ rfl pilotXR_wf pilotXR_placed.toPlacedIn pilotXR_last s g
    ⟨hd8, by simpa [twinT] using ⟨h11, h15⟩⟩
  cfg_cases_env [pilotXR]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [↓reduceIte] at hT
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step,
    SharedEnv.within_ok_load, SharedEnv.within_ok_store, SharedEnv.within_ok_rmw, SharedEnv.tick_load,
    SharedEnv.tick_rmw, SharedEnv.tick_store] at *
  -- `main`
  case vc1 =>
    rename_i hz _
    obtain ⟨-, h15⟩ := hT
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte] at hz
    have e16 : BitVec.setWidth 64 (Int64.toBitVec 16) = 16 := by decide
    rw [e16, BitVec.add_comm, ja_not_taken h15] at hz
    exact absurd hz Bool.false_ne_true
  case vc2 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT.1]⟩, .inl (by decide)⟩
  -- `ret_push`
  case vc1 =>
    have hT' := hT; simp only [Reg64s.get64] at hT'
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩, .inl (by decide)⟩
  -- `ret_pop`
  case vc1 =>
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [ofBitVec_reg hT]
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true })⟩, .inl (by decide)⟩
  -- the functions: `ok` of each access, `dmem` empty
  all_goals first
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]; done)
    | (refine ⟨?_, mem_sAll8 _⟩; simp [SharedEnv.relPureQ]
       first | rfl | trivial | exact fun h => absurd rfl h | exact fun h => h rfl)
    | exact hd8 _
    | (rename_i hld hst _; obtain ⟨rfl, -⟩ := stN hd8 hst; exact hd8 _)
    | skip
  all_goals have hT' := hT; simp only [Reg64s.get64] at hT'
  -- `push`
  case vc5 =>
    rename_i v σ1 dm σ2 old σ3 heq hz hld hst hcas _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc6 =>
    rename_i v σ1 dm σ2 old σ3 heq hz hld hst hcas _
    obtain ⟨rfl, h2⟩ := stN hd8 hst
    have h1 := ldN hd8 hld; have h3 := hcas.2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [ofBitVec_reg hT.1]
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc7 =>
    rename_i v σ1 dm σ2 old σ3 hne hz hld hst hcas _
    obtain ⟨rfl, h2⟩ := stN hd8 hst
    have h1 := ldN hd8 hld; have h3 := hcas.2
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc8 =>
    rename_i v σ1 dm σ2 old σ3 hne hz hld hst hcas _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne
  -- `pop`
  case vc2 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inl (by decide)⟩
  case vc3 =>
    rename_i v σ1 af hz hld _
    have h1 := ldN hd8 hld
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [ofBitVec_reg hT.1]
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  -- `pop_nz`
  case vc4 =>
    rename_i u σ1 old σ2 heq hz hld hcas _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc5 =>
    rename_i u σ1 old σ2 heq hz hld hcas _
    have h1 := ldN hd8 hld; have h3 := hcas.2
    simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    rw [ofBitVec_reg hT.1]
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc6 =>
    rename_i u σ1 old σ2 hne hz hld hcas _
    have h1 := ldN hd8 hld; have h3 := hcas.2
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨hd8, by simp (config := { decide := true }) [hT']⟩,
      .inr fun ⟨_, hg⟩ => by subst hg; omega⟩
  case vc7 =>
    rename_i u σ1 old σ2 hne hz hld hcas _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

end Kraken.Promising.Lower.PilotXR
