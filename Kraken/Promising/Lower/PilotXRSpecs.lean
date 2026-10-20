/-
**The function specifications of `push` and
`pop` under the register-link convention, x64.** ISA:
x64; environment: the x64 treiber2 ownership environment on the whole layout,
`EWX P w = EnvGCAdjX Arch.tso w (plan P w) sAll`, counted (the environment
of the verbatim `treiber2.kl` worker, `EnvG/X64Treiber2VCGen.lean`).

Each spec is a `FunSpecPartialEnv` (`X64/EnvCallsPartial.lean`) at the
function's label in the laid-out `pilotXR`, by `FunSpecPartialEnv.of_cfg`
with one `vcgen` call per function and the VCs of `EnvG/X64Treiber2VC.lean`.
The return address `ra` is the link register's value (`r11 = ra`), and the
return is `jmp *%r11`, the exit at `ra`. The callee-saved frame is the x64 pilot's
`Saved` (`rbx rbp r12 r13 r14 r15`, `dmem`). With `dmem` empty (`D8`: no
8-byte word mapped), every access is the shared event (`ldS`/`stS`), and
`within sAll` admits every access (`mem_sAll8`): no heap or frame side
conditions.

`pop` returns `0` on empty: the `Dn` of its postcondition is then the
`DoneCbz` disjunct (`Pl.dn_empty`), which the final reading excludes.
-/
import Kraken.Promising.Lower.PilotXRProg
import Kraken.Promising.Lower.PilotX64Specs

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.PilotXR

open Kraken.Promising.X64.EnvG.Treiber2X
open Kraken.Promising.X64.EnvG.TreiberX (cmpxOp64 sAll mem_sAll8)
open Kraken.Promising.Lower.PilotX (Saved Saved.refl)
open Kraken.X64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `dmem` maps no 8-byte word. -/
abbrev D8 (d : DataMem) : Prop := ∀ a, Mem.loadInt d a 8 = none

/-- **The empty-stack return** (`testq` read `0`): `Dn` of any result, by
its `DoneCbz` disjunct (the pop token held, `top` read `0` at or after the
push). -/
theorem Pl.dn_empty {P : Params} {w : Nat} {y0 : Val} {σ : EStateX} (h : Pl P w y0 σ)
    (hz : BitVec.setWidth 64 y0 = 0) (x : BitVec 64) : Dn P w x σ := by
  obtain ⟨hcom, Pw, tr0, ⟨h1, -, -, h4⟩, hle, hrd, -⟩ := h
  exact ⟨hcom, .inr ⟨h4, Pw, tr0, y0, h1, hle, hrd, hz⟩⟩

/-- The exit of `jmp *%r` at a register holding `a`'s bits is `a`. -/
theorem ofBitVec_reg {s : MachineData} {r : Reg64} {a : Int64} (h : s.regs.get64 r = a.toBitVec) :
    Int64.ofBitVec (s.regs.get64 r) = a := by
  rw [h, Int64.ofBitVec_toBitVec]

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilotXR)]

local instance pilotXR.env : CodeEnv := ⟨layout pilotXR⟩

omit layout [Executable.ValidLayout (layout pilotXR)] in
theorem pilotXR_wf : Program.WF pilotXR := by decide

/-- Where `pilotXR`'s blocks sit. -/
theorem pilotXR_placed : Program.Placed pilotXR "main" :=
  Program.placed_of_layout pilotXR_wf rfl (by decide)

/-! ## `push` -/

/-- `push`'s text, as a fragment of `pilotXR`. -/
def pushFragXR : Program := parse("
push:
    movq (%rdi), %rax
    movq %rax, (%rsi)
    lock cmpxchgq %rsi, (%rdi)
    jne push
    jmp *%r11
")

/-- `push`'s precondition: the link `r11 = ra`, `rdi = &top`, `rsi` the
node, `dmem` empty, before the push (`Pu`). -/
def PushPreR (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EWX P w)).State) :
    Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.t ∧ t.regs.get64 .rsi = P.n w ∧ D8 t.dmem ∧
    Pu P w σ.1

/-- `push`'s postcondition: the frame kept, pushed (`Po`). -/
def PushPostR (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWX P w)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EWX P w)).State) : Prop :=
  Saved t s ∧ Po P w σ.1

/-- `push`'s loop table. -/
abbrev pushTableR (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWX P w)).State) :
    Label → MachineData → (SharedEnv.counted (EWX P w)).State → Prop :=
  fun lb s σ => lb = "push" ∧ s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.t ∧
    s.regs.get64 .rsi = P.n w ∧ Saved t s ∧ D8 s.dmem ∧ Pu P w σ.1

/-- **`push`'s specification**, once, for every caller. -/
theorem push_specXR (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWX P w)) ((_root_.Executable.labels cenv).label "push")
      (PushPreR P w) (PushPostR P w) := by
  refine FunSpecPartialEnv.of_cfg (p := pushFragXR) (pushTableR P w) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotXR_placed (by decide))
    (fun ra t g ⟨h1, h2, h3, h4, h5⟩ => ⟨rfl, h1, h2, h3, Saved.refl t, h4, h5⟩) ?_
  rintro ra t g -
  have ea : ∀ s : MachineData, s.regs.get64 .rdi = P.t → s.regs.get64 .rdi + Int64.toBitVec 0 = P.t :=
    fun s h => by simp [h]
  cfg_cases_env [pushFragXR]
  intro s₀ g₀
  vcgen
  all_goals obtain ⟨⟨-, h11, hdi, hsi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_store, SharedEnv.within_ok_rmw] at *
  all_goals have hdi' := hdi; have hsi' := hsi; simp only [Reg64s.get64] at hdi' hsi'
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    rename_i v σ1 _ hld _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    have h := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).1
    exact ⟨by simpa [hsi, hsi', Params.nd] using h, mem_sAll8 _⟩
  case vc3 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨rfl, -, -⟩ := stS hd8 hst
    exact hd8 _
  case vc4 =>
    rename_i v σ1 dm σ2 hld hst _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi', Params.nd]) (by simp))
    have h := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).1
    exact ⟨okR h (by simp [hdi', Params.top]) (by simp [hsi', cmpxOp64]), mem_sAll8 _⟩
  case vc5 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 hld hst hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc6 =>
    rename_i v σ1 dm σ2 old σ3 heq hz σ4 σ5 hld hst hcas hf1 hf2 _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, -⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1 (by simp [hdi', Params.top]) (by simp [hsi', cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd heq hne
    refine .inr ⟨by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact ofBitVec_reg h11, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, (hPo.fence hf1.1).fence hf2.1⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc7 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 hld hst hcas hf _
    obtain ⟨v, hs, l1, rfl⟩ := ldS hd8 hld
    have hP := vc_push_load _ hT v σ1.1 hs
    obtain ⟨rfl, ⟨ok, hso⟩, l2⟩ := stS hd8 hst
    have hP2 := (vc_push_str hL hw _ hP (BitVec.setWidth 128 (BitVec.setWidth 64 v))).2 ok σ2.1
      (stepS hso (by simp [hsi', Params.nd]) (by simp))
    have hc := (vc_push_cas hL hw _ hP2 (BitVec.setWidth 64 v) (by simp)).2 old σ3.1
      (stepR hcas.1 (by simp [hdi', Params.top]) (by simp [hsi', cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPu⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨rfl, ?_, ?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
        Pu.fence hPu.pu hf.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      rotate_left 9
      · subst hg
        have h3 := hcas.2; have h4 := hf.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals assumption
    · exact absurd heq' hne
  case vc8 =>
    rename_i v σ1 dm σ2 old σ3 hne hz σ4 σ5 hld hst hcas hf1 hf2 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

/-! ## `pop` -/

/-- `pop`'s text, as a fragment of `pilotXR`. -/
def popFragXR : Program := parse("
pop:
    movq (%rdi), %rax
    testq %rax, %rax
    jne pop_nz
    jmp *%r11
pop_nz:
    movq (%rax), %rcx
    lock cmpxchgq %rcx, (%rdi)
    jne pop
    jmp *%r11
")

/-- `pop`'s precondition: the link `r11 = ra`, `rdi = &top`, `dmem` empty,
pushed (`Po`). -/
def PopPreR (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EWX P w)).State) :
    Prop :=
  t.regs.get64 .r11 = ra.toBitVec ∧ t.regs.get64 .rdi = P.t ∧ D8 t.dmem ∧ Po P w σ.1

/-- `pop`'s postcondition: the frame kept, `Dn` of the result `rax` (the
popped node, or `0` on empty by `DoneCbz`). -/
def PopPostR (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWX P w)).State)
    (s : MachineData) (σ : (SharedEnv.counted (EWX P w)).State) : Prop :=
  Saved t s ∧ Dn P w (s.regs.get64 .rax) σ.1

/-- `pop`'s table: `Po` at `pop`; at `pop_nz`, `Pl` of the non-null value
read, in `rax`. -/
abbrev popTableR (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (_ : (SharedEnv.counted (EWX P w)).State) :
    Label → MachineData → (SharedEnv.counted (EWX P w)).State → Prop :=
  fun lb s σ => s.regs.get64 .r11 = ra.toBitVec ∧ s.regs.get64 .rdi = P.t ∧ Saved t s ∧ D8 s.dmem ∧
    ((lb = "pop" ∧ Po P w σ.1) ∨
      (lb = "pop_nz" ∧ ∃ y0, s.regs.get64 .rax = BitVec.setWidth 64 y0 ∧ BitVec.setWidth 64 y0 ≠ 0 ∧
        Pl P w y0 σ.1))

/-- **`pop`'s specification**, once, for every caller. -/
theorem pop_specXR (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EWX P w)) ((_root_.Executable.labels cenv).label "pop")
      (PopPreR P w) (PopPostR P w) := by
  refine FunSpecPartialEnv.of_cfg (p := popFragXR) (popTableR P w) rfl (by decide)
    (Program.PlacedIn.of_placedE pilotXR_placed (by decide))
    (fun ra t g ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, Saved.refl t, h3, .inl ⟨rfl, h4⟩⟩) ?_
  rintro ra t g -
  cfg_cases_env [popFragXR]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨h11, hdi, ⟨f1, f2, f3, f4, f5, f6, fdm⟩, hd8, hT⟩, rfl, rfl⟩ :=
    ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMonoX_le_counted, fenceMonoX_le_within, fenceMonoX_le_envGCAdjX,
    SharedEnv.counted_step, SharedEnv.counted_ok, SharedEnv.within_step, SharedEnv.within_ok_load,
    SharedEnv.within_ok_rmw] at *
  all_goals have hdi' := hdi; simp only [Reg64s.get64] at hdi'
  -- `pop`
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 =>
    rename_i v σ1 af σ2 hz σ3 hld hf1 hf2 _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v ≠ 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
      .inr ⟨rfl, v, ?_, hz', hPl⟩⟩, .inl (by decide)⟩)
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc3 =>
    rename_i v σ1 af σ2 hz σ3 σ4 hld hf1 hf2 hf3 _
    obtain ⟨v, hs, -, rfl⟩ := ldS hd8 hld
    have hPl := ((vc_pop_ldar (xcl := false) _ hT v σ1.1 (stepL hs (by simp [hdi', Params.top]))).fence
      hf1.1).fence hf2.1
    have hz' : BitVec.setWidth 64 v = 0 := by simpa [CondCode.interp, StatusFlags.from_result] using hz
    refine .inr ⟨by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact ofBitVec_reg h11,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, (Pl.dn_empty hPl hz' _).fence hf3.1⟩
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  -- `pop_nz`
  case vc1 => exact ⟨trivial, mem_sAll8 _⟩
  case vc2 => exact hd8 _
  case vc3 =>
    rename_i u σ1 hld _
    obtain ⟨y0, hrax, hnz, hPl⟩ := hT
    have hrax' := hrax; simp only [Reg64s.get64] at hrax'
    obtain ⟨u, hs2, -, rfl⟩ := ldS hd8 hld
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ1.1 (stepL hs2 (by simp [hrax]))
    have h := (vc_pop_cas hw _ hPr hnz).1
    exact ⟨okR h (by simp [hdi', Params.top]) (by simp [hrax', cmpxOp64]), mem_sAll8 _⟩
  case vc4 =>
    rename_i u σ1 old σ2 heq hz σ3 hld hcas hf _
    simp at heq
    simp [CondCode.interp, StatusFlags.from_result, heq] at hz
  case vc5 =>
    rename_i u σ1 old σ2 heq hz σ3 σ4 hld hcas hf1 hf2 _
    obtain ⟨y0, hrax, hnz, hPl⟩ := hT
    have hrax' := hrax; simp only [Reg64s.get64] at hrax'
    obtain ⟨u, hs2, -, rfl⟩ := ldS hd8 hld
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ1.1 (stepL hs2 (by simp [hrax]))
    have hc := (vc_pop_cas hw _ hPr hnz).2 old σ2.1
      (stepR hcas.1 (by simp [hdi', Params.top]) (by simp [hrax', cmpxOp64]))
    simp at heq
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (heq.trans (by simp [hrax'])) hne
    refine .inr ⟨by simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]; exact ofBitVec_reg h11,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, ?_⟩
    rotate_left 6
    · simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hrax]
      exact ((hDn.fence hf1.1).fence hf2.1).dn
    all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
    all_goals assumption
  case vc6 =>
    rename_i u σ1 old σ2 hne hz σ3 hld hcas hf _
    obtain ⟨y0, hrax, hnz, hPl⟩ := hT
    have hrax' := hrax; simp only [Reg64s.get64] at hrax'
    obtain ⟨u, hs2, l2, rfl⟩ := ldS hd8 hld
    have hPr := vc_pop_ldr (xcl := false) _ hPl u σ1.1 (stepL hs2 (by simp [hrax]))
    have hc := (vc_pop_cas hw _ hPr hnz).2 old σ2.1
      (stepR hcas.1 (by simp [hdi', Params.top]) (by simp [hrax', cmpxOp64]))
    simp at hne
    rcases hc with ⟨-, hPo⟩ | ⟨heq', -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, fdm⟩, hd8,
        .inl ⟨rfl, hPo.fence hf.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      rotate_left 8
      · subst hg
        have := hf.2; have h3 := hcas.2
        simp only [SharedAccess.tick] at h3
        omega
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte]
      all_goals assumption
    · exact absurd (heq'.trans (by simp [hrax'])) hne
  case vc7 =>
    rename_i u σ1 old σ2 hne hz σ3 σ4 hld hcas hf1 hf2 _
    simp at hne
    simp [CondCode.interp, StatusFlags.from_result] at hz
    first
      | exact absurd (Kraken.Promising.SLR.EnvG.TreiberCommon.bv64_eq_of_sub_eq_zero hz).symm hne
      | exact absurd hz.symm hne
      | exact absurd hz hne

end Kraken.Promising.Lower.PilotXR
