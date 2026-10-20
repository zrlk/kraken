/-
**The function specifications of `push` and
`pop`, once each.** ISA: AArch64; environment: the
`treiber2` ownership environment `EW P w = EnvGCAdj isa Arch.armv8 w (plan P w)`
(`EnvG/Treiber2VC.lean`), counted (the zero-step guard of the retry loops).

Each spec is a `FunSpecPartialEnv` (`AArch64/EnvCallsPartial.lean`) at the function's label
in the laid-out `pilot`, proved by `cfgEnv_partial_fun` with one `vcgen` call
per block and the VCs of `EnvG/Treiber2VC.lean` (the same VCs as the inlined
`treiber2` worker). The specs mention the caller only through the draft
convention's registers: arguments `x0` (`&top`), `x1` (the node, `push` only), the result
`x0` (`pop`), the return address `ra` (`X30` on entry), and the callee-saved
frame `CalleeSaved` (`x19`–`x28` and `dmem` unchanged).

- `push_spec`: from `Pu` (before the push) to `Po` (pushed; before the pop).
- `pop_spec`: from `Po` to either an empty stack (`x0 = 0`, `DnD` for every
  `x10`, `x11`) or a successful pop of `x0` (`DnB`, the `ldar` read below
  `vrNew`, which the caller's payload load needs).

`dmem` maps no 8- or 4-byte word (`NoDmem`): the link load `ldr x4, [x2, #8]`
reads at an address loaded from `top`, which no thread-local fact bounds.
-/
import Kraken.Promising.Lower.PilotProg
import Kraken.AArch64.EnvCallsPartial
import Kraken.Promising.SLR.EnvG.Treiber2DataVCGen

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Pilot

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The fragments and the frame -/

/-- `push`'s text, as a fragment of `pilot`. -/
def pushFrag : Program := parseAArch64("
push:
    ldar x2, [x0]
    str x2, [x1, #8]
    mov x3, x2
    casal x3, x1, [x0]
    cmp x3, x2
    b.ne push
    ret
")

/-- `pop`'s text, as a fragment of `pilot`. -/
def popFrag : Program := parseAArch64("
pop:
    ldar x2, [x0]
    cbz x2, pop_done
    ldr x4, [x2, #8]
    mov x3, x2
    casal x3, x4, [x0]
    cmp x3, x2
    b.ne pop
pop_done:
    mov x0, x2
    ret
")

/-- **The callee-saved frame** of the draft calling convention: `x19`–`x28` (`x27`/`x28`
the allocator's bump and limit) and the private memory unchanged. -/
def CalleeSaved (t s : MachineData) : Prop :=
  s.regs.X19 = t.regs.X19 ∧ s.regs.X20 = t.regs.X20 ∧ s.regs.X21 = t.regs.X21 ∧ s.regs.X22 = t.regs.X22 ∧
    s.regs.X23 = t.regs.X23 ∧ s.regs.X24 = t.regs.X24 ∧ s.regs.X25 = t.regs.X25 ∧
    s.regs.X26 = t.regs.X26 ∧ s.regs.X27 = t.regs.X27 ∧ s.regs.X28 = t.regs.X28 ∧ s.dmem = t.dmem

/-- `dmem` maps no 8- or 4-byte word. -/
def NoDmem (s : MachineData) : Prop := (∀ a, Mem.loadInt s.dmem a 8 = none) ∧ ∀ a, Mem.loadInt s.dmem a 4 = none

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot)]

local instance pilot.env : CodeEnv := ⟨layout pilot⟩

omit layout [Executable.ValidLayout (layout pilot)] in
theorem pilot_wf : Program.WF pilot := by decide

/-- Where `pilot`'s blocks sit. -/
theorem pilot_placed : Program.Placed pilot "main" :=
  Program.placed_of_layout pilot_wf rfl (by decide)

/-! ## `push` -/

/-- `push`'s precondition: `X30 = ra`, `x0 = &top`, `x1` the node, before
the push (`Pu`). -/
def PushPre (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EW P w)).State) :
    Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ t.regs.X1.toBitVec = P.n w ∧ NoDmem t ∧ Pu P w σ.1

/-- `push`'s postcondition: the frame kept, pushed (`Po`). -/
def PushPost (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EW P w)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (EW P w)).State) : Prop :=
  CalleeSaved t t' ∧ Po P w σ'.1

/-- `push`'s loop table. -/
abbrev pushTable (P : Params) (w : Nat) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t s ∧ lb = "push" ∧ Pu P w σ.1

/-- **`push`'s specification**, once, for every caller. -/
theorem push_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) := by
  rintro ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hPu⟩
  refine cfgEnv_partial_fun (p := pushFrag) (pushTable P w ra t) (E := fun a s σ => a = ra ∧ PushPost P w ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) t g
    ⟨hx0, hx1, hd8, hd4, hlr, by simp [CalleeSaved], rfl, hPu⟩
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hlr, hfr, -, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8, hd4]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8, hd4]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have h := (vc_push_cas hL hw _ (hP2.fence hf.1) (BitVec.setWidth 64 v) (by simp)).1
    simp [hx0, hx1]
    simpa [casOp64, Params.top] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    have hs2 : σ1.2 ≤ σ2.2 := by omega
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
        by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, rfl,
        Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 σ7 hld hst hf1 hcas hf2 hf3 hf4 _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8, hd4] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
        Po.fence (Po.fence (Po.fence hPo hf2.1) hf3.1) hf4.1⟩
  all_goals done


/-! ## `pop` -/

/-- What `pop` returns in `x`: the empty stack (`x = 0`, then `DnD` for every
`x10`, `x11`), or a successful pop of `x ≠ 0` (`DnB`). -/
def PopRes (P : Params) (w : Nat) (x : BitVec 64) (σ : State isa) : Prop :=
  (x = 0 ∧ ∀ a b, DnD P w a b σ) ∨ (x ≠ 0 ∧ DnB P w x σ)

omit layout [Executable.ValidLayout (layout pilot)] in
theorem PopRes.fence {P : Params} {w : Nat} {x : BitVec 64} {σ σ' : State isa} (h : PopRes P w x σ)
    (hf : FenceLe σ σ') : PopRes P w x σ' :=
  h.imp (fun ⟨h0, hd⟩ => ⟨h0, fun a b => (hd a b).fence hf⟩) fun ⟨h0, hd⟩ => ⟨h0, hd.fence hf⟩

/-- `pop`'s precondition: `X30 = ra`, `x0 = &top`, pushed (`Po`). -/
def PopPre (P : Params) (w : Nat) (ra : Int64) (t : MachineData) (σ : (SharedEnv.counted (EW P w)).State) :
    Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ NoDmem t ∧ Po P w σ.1

/-- `pop`'s postcondition: the frame kept, the result in `x0`. -/
def PopPost (P : Params) (w : Nat) (_ : Int64) (t : MachineData) (_ : (SharedEnv.counted (EW P w)).State)
    (t' : MachineData) (σ' : (SharedEnv.counted (EW P w)).State) : Prop :=
  CalleeSaved t t' ∧ PopRes P w t'.regs.X0.toBitVec σ'.1

/-- `pop`'s table. -/
abbrev popTable (P : Params) (w : Nat) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EW P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ s.lr = ra ∧ CalleeSaved t s ∧
    ((lb = "pop" ∧ Po P w σ.1) ∨ (lb = "pop_done" ∧ PopRes P w s.regs.X2.toBitVec σ.1))

/-- **`pop`'s specification**, once, for every caller. -/
theorem pop_spec (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) := by
  rintro ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hPo⟩
  refine cfgEnv_partial_fun (p := popFrag) (popTable P w ra t)
    (E := fun a s σ => a = ra ∧ PopPost P w ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot_placed (by decide)) t g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hPo⟩⟩
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step,
    SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hd8, hd4]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
      by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, .inr ⟨rfl, .inl ⟨by simpa using hz,
        fun a b => DnD.fence (vc_pop_cbz_d _ (vc_pop_ldar (xcl := false) _ hT v σ1.1
          (by simpa [hx0, Params.top] using hld.1)) hz a b) hf.1⟩⟩⟩, .inl (by decide)⟩)
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have h := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.top] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPo⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hd8], by simp [hd4],
        by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr,
        .inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc11 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp [hd8] at hnz hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    refine ⟨by simp [hx0], by simp [hd8], by simp [hd4], by simpa [MachineData.lr] using hlr,
      by simpa [CalleeSaved] using hfr, .inr ⟨trivial, .inr ⟨by simpa using hnz, ?_⟩⟩⟩
    simpa using (hDn.fence hf3.1).fence hf4.1
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [CalleeSaved] using hfr, ?_⟩
    simpa using (hT.fence hf1.1).fence hf2.1
  all_goals done

end Kraken.Promising.Lower.Pilot

