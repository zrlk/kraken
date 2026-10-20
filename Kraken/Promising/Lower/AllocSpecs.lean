/-
**The function specifications** in the laid-out
`allocP`.
- `alloc_spec`, **for every environment** (`alloc` makes no memory access):
  from `x27 = n` with room below `x28`, returns `x0 = n`, `x27 = n + 16`, the
  frame `AllocSaved` (the draft convention's callee-saved set except `x27`), any
  fence-stable `R` kept.
- `push_spec`, `pop_spec`: the first lowering pilot's pre/posts and tables at `allocP`.
- `pu_of_pu2`: after `str xzr, [x0, #8]` the node is back in `Pu`.
-/
import Kraken.Promising.Lower.AllocProg
import Kraken.Promising.Lower.PilotPure

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Alloc

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem pushFrag popFrag PushPre PushPost pushTable PopRes PopPre
  PopPost popTable)
open Kraken.AArch64.Parser

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- `alloc`'s text, as a fragment of `allocP`. -/
def allocFrag : Program := parseAArch64("
alloc:
    mov x0, x27
    add x27, x27, #16
    cmp x27, x28
    b.hi alloc_oom
    ret
alloc_oom:
    b alloc_oom
")

/-- **The allocator's frame**: `CalleeSaved` except `x27`. -/
def AllocSaved (t s : MachineData) : Prop :=
  s.regs.X19 = t.regs.X19 ∧ s.regs.X20 = t.regs.X20 ∧ s.regs.X21 = t.regs.X21 ∧ s.regs.X22 = t.regs.X22 ∧
    s.regs.X23 = t.regs.X23 ∧ s.regs.X24 = t.regs.X24 ∧ s.regs.X25 = t.regs.X25 ∧
    s.regs.X26 = t.regs.X26 ∧ s.regs.X28 = t.regs.X28 ∧ s.dmem = t.dmem

/-- After the initial link store the node is again in `push`'s state. -/
theorem pu_of_pu2 {P : Params} {w : Nat} {y : Val} {σ : State isa} (h : Pu2 P w y σ) : Pu P w σ := by
  obtain ⟨h1, h2, h3, ⟨t, -, h4, -, h5⟩, h6, h7⟩ := h
  exact ⟨h1, h2, h3, fun p hp => Nat.le_trans (h4 p hp) h5, h6, h7⟩

variable [layout : _root_.Layout] [Executable.ValidLayout (layout allocP)]

local instance allocP.env : CodeEnv := ⟨layout allocP⟩

omit layout [Executable.ValidLayout (layout allocP)] in
theorem allocP_wf : Program.WF allocP := by decide

theorem allocP_placed : Program.Placed allocP "main" :=
  Program.placed_of_layout allocP_wf rfl (by decide)

/-! ## `alloc` -/

/-- `alloc`'s precondition: `X30 = ra`, `x27 = n` with room, `R`. -/
def AllocPre (env : SharedEnv) (R : env.State → Prop) (n : BitVec 64) (ra : Int64) (t : MachineData)
    (g : env.State) : Prop :=
  t.lr = ra ∧ t.regs.X27.toBitVec = n ∧ t.regs.X27.toBitVec + 16 ≤ t.regs.X28.toBitVec ∧ R g

/-- `alloc`'s postcondition: `x0 = n`, `x27 = n + 16`, the frame, `R`. -/
def AllocPost (env : SharedEnv) (R : env.State → Prop) (n : BitVec 64) (_ : Int64) (t : MachineData)
    (_ : env.State) (t' : MachineData) (g' : env.State) : Prop :=
  t'.regs.X0.toBitVec = n ∧ t'.regs.X27.toBitVec = n + 16 ∧ AllocSaved t t' ∧ R g'

/-- **`alloc`'s specification**, in every environment. -/
theorem alloc_spec (env : SharedEnv) [env.FenceMono] (R : env.State → Prop)
    (hR : ∀ g g', R g → SharedEnv.FenceMono.le g g' → R g') (n : BitVec 64) :
    FunSpecPartialEnv env ((_root_.Executable.labels cenv).label "alloc") (AllocPre env R n)
      (AllocPost env R n) := by
  rintro ra t g ⟨hlr, h27, hlim, hg⟩
  refine cfgEnv_partial_fun (p := allocFrag)
    (fun lb s σ => lb = "alloc" ∧ s = t ∧ R σ) (E := fun a s σ => a = ra ∧ AllocPost env R n ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE allocP_placed (by decide)) t g ⟨rfl, rfl, hg⟩
  cfg_cases_env [allocFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨-, rfl, hR0⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp [AllocPost, AllocSaved, MachineData.lr] at *
  case vc1 =>
    rename_i hhi _
    simp only [← UInt64.toNat_toBitVec] at hhi
    bv_omega
  case vc2 =>
    refine .inr ?_
    repeat (first | exact hR0 | refine hR _ _ ?_ (by assumption))

/-! ## `push` and `pop`: the first lowering pilot's specifications at `allocP` -/

/-- **`push`'s specification**, once, for every caller. -/
theorem push_spec (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "push") (PushPre P w)
      (PushPost P w) := by
  rintro ra t g ⟨hlr, hx0, hx1, ⟨hd8, hd4⟩, hPu⟩
  refine cfgEnv_partial_fun (p := pushFrag) (pushTable P w ra t) (E := fun a s σ => a = ra ∧ PushPost P w ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE allocP_placed (by decide)) t g
    ⟨hx0, hx1, hd8, hd4, hlr, by simp [CalleeSaved], rfl, hPu⟩
  cfg_cases_env [pushFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hlr, hfr, -, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, hd8]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hd8] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1
    simp [hx1, hd8] at hst
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
    simp [hx1, hd8] at hst
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
    simp [hx1, hd8] at hst
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

/-- **`pop`'s specification**, once, for every caller. -/
theorem pop_spec (P : Params) (w : Nat) (hw : w < 2) :
    FunSpecPartialEnv (SharedEnv.counted (EW P w)) ((_root_.Executable.labels cenv).label "pop") (PopPre P w)
      (PopPost P w) := by
  rintro ra t g ⟨hlr, hx0, ⟨hd8, hd4⟩, hPo⟩
  refine cfgEnv_partial_fun (p := popFrag) (popTable P w ra t)
    (E := fun a s σ => a = ra ∧ PopPost P w ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE allocP_placed (by decide)) t g
    ⟨hx0, hd8, hd4, hlr, by simp [CalleeSaved], .inl ⟨rfl, hPo⟩⟩
  cfg_cases_env [popFrag]
  all_goals (intro s₀ g₀; vcgen)
  all_goals obtain ⟨⟨hx0, hd8, hd4, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_envGCAdj, SharedEnv.counted_step, SharedEnv.counted_ok] at *
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

end Kraken.Promising.Lower.Alloc
