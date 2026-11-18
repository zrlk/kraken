import Kraken.X64.Parser
import Kraken.MachineWP
import Kraken.Rules.ScalarFloat
import Kraken.X64.Examples.Sbr.SessionBin.WitEnvDefs

/-!
# The witness stand-ins: the straight-line ones

The contracts of the stand-ins of `WitEnvDefs` that run straight through: `av_log`,
`avpriv_request_sample`, `ff_psdsp_init`, `ff_ps_apply`, the transform `tx_stub` (each `ret`),
`powf` and `log2f` (`1.0f` in `xmm0`), and `av_tx_init` (succeeds, handing out `tx_stub` with
an empty context). Each holds of any ambient code where its text is placed. The proofs are
`ProcSpec.of_cfg_post` on texts of one or a few blocks, the shape of `Dsp/NegOdd64.lean`'s
exit block.
-/

open Kraken.X64.Parser Kraken Kraken.SysV Std.WP Mem MachineWP

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.WitEnv

/-- The caller's side of memory behind the footprint. -/
def Rest (need : Nat) (R : Mem 64 → Prop) (ra : Int64) (t₀ : MachineData) : Mem 64 → Prop :=
  RetCell ra (t₀.regs.get64 .rsp) ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ R)

/-- The entry assertion of a one-block leaf at `l₀` with footprint `F`. -/
abbrev table (l₀ : Label) (F : MachineData → Mem 64 → Prop) (need : Nat) (R : Mem 64 → Prop)
    (ra : Int64) (t₀ : MachineData) (l : Label) (s : MachineData) : Prop :=
  l = l₀ ∧ s = t₀ ∧ (t₀.dmem =⋆ F t₀ ⋆ Rest need R ra t₀)

/-- What the `ret` leaves: `CallPost` with the footprint in front, and `Q`. -/
abbrev Post' (Q : MachineData → MachineData → Prop) (F : MachineData → Mem 64 → Prop)
    (need : Nat) (R : Mem 64 → Prop) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rsp = t₀.regs.get64 .rsp + 8
  ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
  ∧ (s.dmem =⋆ F t₀ ⋆ (8 ?@ (t₀.regs.get64 .rsp) ⋆ (Reserve need (t₀.regs.get64 .rsp) ⋆ R)))
  ∧ Q t₀ s

theorem pre_of_call {F : MachineData → Mem 64 → Prop} {need : Nat} {R : Mem 64 → Prop}
    {ra : Int64} {t : MachineData} (h : CallPre need (F t ⋆ R) ra t) :
    t.dmem =⋆ F t ⋆ Rest need R ra t := by
  simp only [Rest, CallPre] at h ⊢
  rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (RetCell _ _)] at h
  exact h

theorem post_of_ret {F : MachineData → Mem 64 → Prop} {need : Nat} {R : Mem 64 → Prop}
    {Q : MachineData → MachineData → Prop} {ra : Int64} {t₀ s : MachineData}
    (h : Post' Q F need R ra t₀ s) : LeafPost need F R ra t₀ s ∧ Q t₀ s := by
  obtain ⟨h1, h2, h3, hm, hq⟩ := h
  refine ⟨⟨h1, h2, h3, ?_⟩, hq⟩
  show (_ ⋆ (_ ⋆ (F t₀ ⋆ R))) s.dmem
  rw [Std.ExtHashMap.sep_comm_l (Reserve _ _), Std.ExtHashMap.sep_comm_l (Block _ _)]
  exact hm

set_option hygiene false in
/-- The one block of a straight-line stand-in that ends in `ret`. -/
macro "leaf_block" : tactic => `(tactic| (
  vcgen
  all_goals simp only [Rest] at *
  all_goals call_simp
  all_goals (try simp only [RegZmms.get_set_xmm_same] at *)
  all_goals grind_cells))

variable [CodeEnv]

theorem avLog_spec (Ext : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn avLogT) :
    AvLogSpec Ext need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := avLogT) (table "av_log" (fun _ => Ext) need)
    (Post' (fun _ _ => True) (fun _ => Ext) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := fun _ => Ext) h.1⟩)
    (hpost := fun _ _ _ _ h => (post_of_ret h).1)
  intro R ra t₀
  cfg_cases [avLogT]
  · leaf_block

theorem powf_spec (Ext : Mem 64 → Prop) (lg : BitVec 32 → BitVec 32) (need : Nat)
    (hpl : Program.PlacedIn powfT) :
    Reset.PowfSpec ⟨Ext, fun _ _ => Reset.f1, lg⟩ need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := powfT) (table "powf" (fun _ => Ext) need)
    (Post' (fun _ s => Reset.lo32 s .mm0 = Reset.f1) (fun _ => Ext) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := fun _ => Ext) h.1⟩)
    (hpost := fun _ _ _ _ h => post_of_ret h)
  intro R ra t₀
  cfg_cases [powfT]
  · leaf_block

theorem log2f_spec (Ext : Mem 64 → Prop) (pw : BitVec 32 → BitVec 32 → BitVec 32) (need : Nat)
    (hpl : Program.PlacedIn log2fT) :
    Reset.Log2fSpec ⟨Ext, pw, fun _ => Reset.f1⟩ need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := log2fT) (table "log2f" (fun _ => Ext) need)
    (Post' (fun _ s => Reset.lo32 s .mm0 = Reset.f1) (fun _ => Ext) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := fun _ => Ext) h.1⟩)
    (hpost := fun _ _ _ _ h => post_of_ret h)
  intro R ra t₀
  cfg_cases [log2fT]
  · leaf_block

/-- The footprint of `av_tx_init` at entry. -/
abbrev TxInF (TxTab X : Mem 64 → Prop) (t : MachineData) : Mem 64 → Prop :=
  8 ?@ arg0 t ⋆ (8 ?@ arg1 t ⋆ Init.TxIn TxTab X t)

theorem avReq_spec (Ext : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn avReqT) :
    DecExt.AvReqSpec Ext need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := avReqT)
    (table "avpriv_request_sample" (fun _ => Ext) need)
    (Post' (fun _ _ => True) (fun _ => Ext) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := fun _ => Ext) h.1⟩)
    (hpost := fun _ _ _ _ h => (post_of_ret h).1)
  intro R ra t₀
  cfg_cases [avReqT]
  · leaf_block

theorem psdsp_spec (X : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn psdspT) :
    Init.PsDspInitSpec X need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := psdspT)
    (table "ff_psdsp_init" (fun t => 64 ?@ arg0 t ⋆ X) need)
    (Post' (fun _ _ => True) (fun t => 64 ?@ arg0 t ⋆ X) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := fun t => 64 ?@ arg0 t ⋆ X) h.1⟩)
    (hpost := fun _ _ _ _ h => (post_of_ret h).1)
  intro R ra t₀
  cfg_cases [psdspT]
  · leaf_block

theorem txFn_spec (Ctx : BitVec 64 → Mem 64 → Prop) (TxTab : Mem 64 → Prop) (need : Nat)
    (hpl : Program.PlacedIn txFnT) : TxSpec Ctx TxTab need (entry "tx_stub") := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := txFnT)
    (table "tx_stub" (TxF Ctx TxTab) need)
    (Post' (fun _ _ => True) (TxF Ctx TxTab) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, rfl, pre_of_call (F := TxF Ctx TxTab) h.1⟩)
    (hpost := fun _ _ _ _ h => (post_of_ret h).1)
  intro R ra t₀
  cfg_cases [txFnT]
  · leaf_block

/-- `ff_ps_apply`'s entry assertion: the footprint at the logical variables `x`. -/
abbrev psTable (PsTab : Mem 64 → Prop) (need : Nat) (x : PsArgs) (ra : Int64)
    (t₀ : MachineData) (l : Label) (s : MachineData) : Prop :=
  l = "ff_ps_apply" ∧ s = t₀ ∧ PsApplyC x t₀
    ∧ (t₀.dmem =⋆ PsApplyF PsTab x t₀ ⋆ Rest need x.R ra t₀)

theorem psApply_spec (PsTab : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn psApplyT) :
    PsApplySpec PsTab need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := psApplyT) (psTable PsTab need)
    (fun x ra t₀ s => PsApplyC x t₀ ∧ Post' (fun _ _ => True) (PsApplyF PsTab x) need x.R ra t₀ s)
    (hblocks := ?_)
    (hpre := fun x _ _ h => ⟨rfl, rfl, h.2, pre_of_call (F := PsApplyF PsTab x) (R := x.R) h.1⟩)
    (hpost := ?_)
  · intro x ra t₀
    cfg_cases [psApplyT]
    · vcgen
      all_goals simp only [Rest] at *
      all_goals call_simp
      all_goals grind_cells
  · intro x ra t₀ s ⟨hc, h⟩
    obtain ⟨⟨h1, h2, h3, hm⟩, -⟩ := post_of_ret h
    refine ⟨h1, h2, h3, ?_⟩
    have hw := hc.2.2.1.2.2.2.2.2.2.2.2.1
    have hl : x.psh.length = 68 := hc.2.2.1.2.1
    obtain ⟨a₁, a₂, ad, ae, ha₁, a₃, a₄, bd, be, hb₁, c₁, c₂, cd, ce, hc₁, hc₂⟩ := hm
    exact ⟨a₁, a₂, ad, ae, ha₁, a₃, a₄, bd, be, hb₁, c₁, c₂, cd, ce, ⟨x.psh, hl, hw, hc₁⟩, hc₂⟩

/-- What the succeeding `av_tx_init` leaves: `*ctx = 0`, `*tx = tx_stub`, the inputs. -/
abbrev TxOkF (TxTab X : Mem 64 → Prop) (t : MachineData) : Mem 64 → Prop :=
  Apply.c8 (arg0 t) 0#64 ⋆ (FnCell (arg1 t) (entry "tx_stub") ⋆ Init.TxIn TxTab X t)

/-- The entry assertion of `txInitT`. -/
abbrev txOkTable (TxTab X : Mem 64 → Prop) (need : Nat) (R : Mem 64 → Prop) (ra : Int64)
    (t₀ : MachineData) : Label → MachineData → Prop
  | "av_tx_init", s => s = t₀ ∧ (t₀.dmem =⋆ TxInF TxTab X t₀ ⋆ Rest need R ra t₀)
  | "av_tx_init.ctx", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s
      ∧ s.regs.get64 .rdi = arg0 t₀
      ∧ (s.dmem =⋆ (8 ?@ arg0 t₀ ⋆ (FnCell (arg1 t₀) (entry "tx_stub") ⋆ Init.TxIn TxTab X t₀))
          ⋆ Rest need R ra t₀)
  | "av_tx_init.done", s => s.regs.get64 .rsp = t₀.regs.get64 .rsp
      ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp ∧ SavedRegs t₀ s ∧ s.regs.get64 .rax = 0#64
      ∧ (s.dmem =⋆ TxOkF TxTab X t₀ ⋆ Rest need R ra t₀)
  | _, _ => False

/-- With the transform contexts owning nothing (`Ctx = emp`), the succeeding stand-in meets
`av_tx_init`'s contract, given that `tx_stub` is placed. -/
theorem txInit_spec (TxTab X : Mem 64 → Prop) (need : Nat) (hpl : Program.PlacedIn txInitT)
    (hstub : Program.PlacedIn txFnT) :
    Init.AvTxInitSpec (fun _ => Std.ExtHashMap.emp) TxTab X need := by
  refine Kraken.Executable.ProcSpec.of_cfg_post (p := txInitT) (txOkTable TxTab X need)
    (Post' (fun _ s => s.regs.get64 .rax = 0#64) (TxOkF TxTab X) need) (hblocks := ?_)
    (hpre := fun _ _ _ h => ⟨rfl, pre_of_call (F := TxInF TxTab X) h⟩) (hpost := ?_)
  · intro R ra t₀
    cfg_cases [txInitT]
    · vcgen
      all_goals (try simp only [txOkTable.match_1.eq_1] at *)
      all_goals (try obtain ⟨⟨rfl, _⟩, _⟩ := ‹_ ∧ _›)
      all_goals grind_cells
    · vcgen
      all_goals grind_cells
    · leaf_block
  · intro R ra t₀ s h
    obtain ⟨⟨h1, h2, h3, hm⟩, hr⟩ := post_of_ret h
    refine ⟨0#64, entry "tx_stub", fun _ => txFn_spec _ TxTab need hstub, h1, h2, h3, ?_⟩
    have hpos : 0 ≤ ((s.regs.get64 .rax).setWidth 32).toInt := by rw [hr]; decide
    simp only [Init.TxOut, hpos, ite_true, Std.ExtHashMap.sep_emp]
    simpa only [TxOkF, Std.ExtHashMap.sep_assoc] using hm

end Kraken.Examples.Sbr.WitEnv
