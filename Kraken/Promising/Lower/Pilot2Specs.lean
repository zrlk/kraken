/-
**Part 3: `push` and `pop` beside a `dmem` stack.**
ISA: AArch64; environment: `counted (EWV P w)`, the
treiber2 ownership environment `EW P w` with load answers at `top` and the
links restricted to `0`/`n0`/`n1` (`Lower/Pilot2Bridge.lean`).

`Pilot.push_spec`/`pop_spec` with `Pilot.NoDmem` (no private word at all)
replaced by the private-stack interface:
- `StackOK P lo n d`: the heap (`top` and both nodes' words, `HP P`) is off the
  private memory (the private-stack layer's `HeapOff`), and the caller's stack region
  `[lo, lo + n)` is mapped (`StackFull`), in `Pre` and `Post`;
- `Saved2`: the draft convention's callee-saved set, `x19`–`x28`, `dmem` (so the caller's frame
  is preserved) and `sp`.
`push` and `pop` are leaves: they keep `x30` and touch no stack slot.

The shared accesses at fixed addresses (`top`, the own node's link) are
unmapped by `HeapOff.loadInt_none_of_mem`. `pop`'s `ldr x4, [x2, #8]` reads
through the pointer `x2` loaded from `top`: the `EWV` answer gives
`treiber2GA` of it, so `PtrsInHeap` (`treiber2_ptrsInHeap`) names a node and the
link address is in the heap. In plain `EW` that fact is missing; see the
bridge file. `pop` returns that fact with its result (`PopRes2`), for
`main`'s payload load.
-/
import Kraken.Promising.Lower.Pilot2Prog
import Kraken.Promising.Lower.Pilot2Bridge
import Kraken.Promising.Lower.PilotSpecs
import Kraken.Promising.Lower.DStackTreiber2A64

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Pilot2

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved PopRes pushFrag popFrag)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The environment and the stack interface -/

/-- The value condition: `top` and both links hold `0`, `n0` or `n1`. -/
abbrev GV (P : Params) : Loc → Val → Prop := treiber2GA P.t (P.n 0) (P.n 1)

/-- Thread `w`'s environment: `EW P w` with value-restricted load answers. -/
noncomputable abbrev EWV (P : Params) (w : Nat) : SharedEnv := EnvGCAdjV Arch.armv8 w (plan P w) (GV P)

/-- The shared layout: `top`, each node's data word and link. -/
abbrev SLay (P : Params) : SharedEnv.Layout := treiber2SA P.t (P.n 0) (P.n 1)

/-- The heap: the bytes of the shared layout. -/
abbrev HP (P : Params) : BitVec 64 → Prop := SharedLayout.Covers (SLay P)

/-- **The stack interface**: the heap off the private memory, the stack
region `[lo, lo + n)` mapped. -/
def StackOK (P : Params) (lo : BitVec 64) (n : Nat) (d : Mem 64) : Prop := HeapOff (HP P) d ∧ StackFull lo n d

/-- **The draft convention's callee-saved set**: `x19`–`x28`, `dmem`, and `sp`. -/
def Saved2 (t s : MachineData) : Prop := CalleeSaved t s ∧ s.regs.SP = t.regs.SP

theorem Saved2.refl (t : MachineData) : Saved2 t t := ⟨by simp [CalleeSaved], rfl⟩

/-- A `PtrsInHeap` node's link and data word are heap addresses. -/
theorem hp_link {P : Params} {p : BitVec 64} (h : p = P.n 0 ∨ p = P.n 1) : HP P (p + 8#64) :=
  covers_self (n := 8) (by rcases h with rfl | rfl <;> simp) (by decide)

theorem hp_data {P : Params} {p : BitVec 64} (h : p = P.n 0 ∨ p = P.n 1) : HP P p :=
  covers_self (n := 4) (by rcases h with rfl | rfl <;> simp) (by decide)

theorem hp_top (P : Params) : HP P P.t := covers_self (n := 8) (by simp) (by decide)

theorem pn_cases {P : Params} {w : Nat} (hw : w < 2) : P.n w = P.n 0 ∨ P.n w = P.n 1 := by
  match w, hw with
  | 0, _ => exact .inl rfl
  | 1, _ => exact .inr rfl

variable [layout : _root_.Layout] [Executable.ValidLayout (layout pilot2)]

local instance pilot2.env : CodeEnv := ⟨layout pilot2⟩

omit layout [Executable.ValidLayout (layout pilot2)] in
theorem pilot2_wf : Program.WF pilot2 := by decide

/-- Where `pilot2`'s blocks sit. -/
theorem pilot2_placed : Program.Placed pilot2 "main" :=
  Program.placed_of_layout pilot2_wf rfl (by decide)

/-! ## `push` -/

/-- `push`'s precondition: `X30 = ra`, `x0 = &top`, `x1` the node, the stack
interface, before the push (`Pu`). -/
def PushPre2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ t.regs.X1.toBitVec = P.n w ∧ StackOK P lo n t.dmem ∧ Pu P w σ.1

/-- `push`'s postcondition: the callee-saved set and the stack interface kept,
pushed (`Po`). -/
def PushPost2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWV P w)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EWV P w)).State) :
    Prop :=
  Saved2 t t' ∧ StackOK P lo n t'.dmem ∧ Po P w σ'.1

/-- `push`'s loop table. -/
abbrev pushTable2 (P : Params) (w : Nat) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EWV P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧
    Saved2 t s ∧ lb = "push" ∧ Pu P w σ.1

/-- **`push`'s specification beside a `dmem` stack**, once, for every caller. -/
theorem push_spec2 (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "push")
      (PushPre2 P w lo n) (PushPost2 P w lo n) := by
  rintro ra t g ⟨hlr, hx0, hx1, ⟨hH, hF⟩, hPu⟩
  have hw' := pn_cases (P := P) hw
  refine cfgEnv_partial_fun (p := pushFrag) (pushTable2 P w ra t)
    (E := fun a s σ => a = ra ∧ PushPost2 P w lo n ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t g
    ⟨hx0, hx1, hH, hlr, Saved2.refl t, rfl, hPu⟩
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd, hlr, hfr, -, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals have hn8 := hd.loadInt_none (hp_link hw') (n := 8) (by decide)
  all_goals simp only [fenceMono_le_counted, fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
    SharedEnv.counted_step, SharedEnv.counted_ok, and_true] at *
  all_goals try (simp [hx0, hx1, ht8]; done)
  case vc5 =>
    rename_i s σ0 v σ1 rng hnone hld _
    have hP := vc_push_load _ hT v σ1.1 hld.1.1
    simp [hx1]
    exact (vc_push_str hL hw _ hP _).1
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    simp [hx1, hn8] at hst
    obtain ⟨hdm, -, -⟩ := hst
    subst hdm
    simp [hx0, ht8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 hld hst hf _
    have hP := vc_push_load _ hT v σ1.1 hld.1.1
    simp [hx1, hn8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have h := (vc_push_cas hL hw _ (hP2.fence hf.1) (BitVec.setWidth 64 v) (by simp)).1
    simp [hx0, hx1]
    simpa [casOp64, Params.top] using h
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 hld hst hf1 hcas hf2 hf3 _
    have hP := vc_push_load _ hT v σ1.1 hld.1.1
    simp [hx1, hn8] at hst
    obtain ⟨hdm, hso, htk⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPu⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hd,
        by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, rfl,
        Pu.fence (Pu.fence hPu.pu hf2.1) hf3.1⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 σ3 old σ4 σ5 hbr σ6 σ7 hld hst hf1 hcas hf2 hf3 hf4 _
    have hP := vc_push_load _ hT v σ1.1 hld.1.1
    simp [hx1, hn8] at hst
    obtain ⟨hdm, hso, -⟩ := hst
    subst hdm
    have hP2 : Pu2 P w (BitVec.setWidth 128 (BitVec.setWidth 64 v)) σ2.1 := by
      rcases hso with h | h <;> exact (vc_push_str hL hw _ hP _).2 _ σ2.1 (by simpa [Params.nd] using h)
    have hc := (vc_push_cas hL hw _ (hP2.fence hf1.1) (BitVec.setWidth 64 v) (by simp)).2 old σ4.1
      (by simpa [hx0, hx1, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hPo⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    · have hSO : StackOK P lo n s.dmem := hfr.1.2.2.2.2.2.2.2.2.2.2 ▸ ⟨hH, hF⟩
      refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
        by simpa using hSO,
        Po.fence (Po.fence (Po.fence hPo hf2.1) hf3.1) hf4.1⟩
  all_goals done

/-! ## `pop` -/

/-- What `pop` returns in `x`: `Pilot.PopRes`, and a non-null result is a
node (the `PtrsInHeap` fact `main`'s payload load needs). -/
def PopRes2 (P : Params) (w : Nat) (x : BitVec 64) (σ : State isa) : Prop :=
  PopRes P w x σ ∧ (x ≠ 0 → x = P.n 0 ∨ x = P.n 1)

/-- `pop`'s precondition: `X30 = ra`, `x0 = &top`, the stack interface,
pushed (`Po`). -/
def PopPre2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EWV P w)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ StackOK P lo n t.dmem ∧ Po P w σ.1

/-- `pop`'s postcondition: the callee-saved set and the stack interface kept,
the result in `x0`. -/
def PopPost2 (P : Params) (w : Nat) (lo : BitVec 64) (n : Nat) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWV P w)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EWV P w)).State) :
    Prop :=
  Saved2 t t' ∧ StackOK P lo n t'.dmem ∧ PopRes2 P w t'.regs.X0.toBitVec σ'.1

/-- `pop`'s table. -/
abbrev popTable2 (P : Params) (w : Nat) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EWV P w)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ HeapOff (HP P) s.dmem ∧ s.lr = ra ∧ Saved2 t s ∧
    ((lb = "pop" ∧ Po P w σ.1) ∨ (lb = "pop_done" ∧ PopRes2 P w s.regs.X2.toBitVec σ.1))

omit layout [Executable.ValidLayout (layout pilot2)] in
/-- The value `pop`'s `ldar` read from `top` is null or a node: the `EWV`
answer (`GV`) and the source obligation `PtrsInHeap`. -/
theorem top_node {P : Params} {v : Val} (h : GV P ⟨P.t, 8⟩ v) (hnz : BitVec.setWidth 64 v ≠ 0) :
    BitVec.setWidth 64 v = P.n 0 ∨ BitVec.setWidth 64 v = P.n 1 :=
  (Treiber2A64.treiber2_ptrsInHeap P.t (P.n 0) (P.n 1) ⟨P.t, 8⟩ v (.inl rfl) h).resolve_left hnz

/-- **`pop`'s specification beside a `dmem` stack**, once, for every caller. -/
theorem pop_spec2 (P : Params) (w : Nat) (hw : w < 2) (lo : BitVec 64) (n : Nat) :
    FunSpecPartialEnv (SharedEnv.counted (EWV P w)) ((_root_.Executable.labels cenv).label "pop")
      (PopPre2 P w lo n) (PopPost2 P w lo n) := by
  rintro ra t g ⟨hlr, hx0, ⟨hH, hF⟩, hPo⟩
  refine cfgEnv_partial_fun (p := popFrag) (popTable2 P w ra t)
    (E := fun a s σ => a = ra ∧ PopPost2 P w lo n ra t g s σ) ?_
    rfl (by decide) (Program.PlacedIn.of_placedE pilot2_placed (by decide)) t g
    ⟨hx0, hH, hlr, Saved2.refl t, .inl ⟨rfl, hPo⟩⟩
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hd.loadInt_none (hp_top P) (n := 8) (by decide)
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
    SharedEnv.counted_step, SharedEnv.counted_ok, and_true] at *
  all_goals try (simp [hx0, ht8]; done)
  case vc4 =>
    rename_i s σ0 v σ1 hz σ2 hld hf _
    simp at hz
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inr ⟨rfl, ⟨.inl ⟨by simpa using hz,
        fun a b => DnD.fence (vc_pop_cbz_d _ (vc_pop_ldar (xcl := false) _ hT v σ1.1
          (by simpa [hx0, Params.top] using hld.1.1)) hz a b) hf.1⟩, by simp [hz]⟩⟩⟩, .inl (by decide)⟩)
  case vc9 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 hld hf1 hld2 hf2 _
    simp at hnz
    have hn := top_node (by simpa [hx0] using hld.1.2) hnz
    have hl8 := hd.loadInt_none (hp_link hn) (n := 8) (by decide)
    simp [hl8] at hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1.1
    have h := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).1
    simp [hx0]
    simpa [casOp64, Params.top] using h
  case vc10 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp at hnz
    have hn := top_node (by simpa [hx0] using hld.1.2) hnz
    have hl8 := hd.loadInt_none (hp_link hn) (n := 8) (by decide)
    simp [hl8] at hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨-, hPo⟩ | ⟨heq, -⟩
    · refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
        by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
        .inl ⟨rfl, Po.fence (Po.fence hPo hf3.1) hf4.1⟩⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
      subst hg
      have h1 := hld.2; have h2 := hcas.2; have h3 := hf1.2; have h4 := hf2.2; have h5 := hf3.2
      have h6 := hf4.2
      simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
      omega
    · exact absurd (by rw [heq]; exact BitVec.sub_self _) hbr
  case vc11 =>
    rename_i s σ0 v σ1 hnz σ2 rng v4 σ3 σ4 old σ5 σ6 hbr σ7 hld hf1 hld2 hf2 hcas hf3 hf4 _
    simp at hnz
    have hn := top_node (by simpa [hx0] using hld.1.2) hnz
    have hl8 := hd.loadInt_none (hp_link hn) (n := 8) (by decide)
    simp [hl8] at hld2
    have hP1 : Pl P w v σ2.1 :=
      (vc_pop_ldar (xcl := false) _ hT v σ1.1 (by simpa [hx0, Params.top] using hld.1.1)).fence hf1.1
    obtain ⟨u, h, rfl⟩ := hld2
    have hP3 := vc_pop_ldr _ hP1 u σ3.1 h.1.1
    have hc := (vc_pop_cas hw _ (hP3.fence hf2.1) hnz).2 old σ5.1
      (by simpa [hx0, casOp64, Params.top] using hcas.1)
    simp at hbr
    rcases hc with ⟨hne, -⟩ | ⟨-, hDn⟩
    · exact absurd (TreiberCommon.bv64_eq_of_sub_eq_zero hbr) hne
    refine ⟨by simp [hx0], by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [Saved2, CalleeSaved] using hfr, .inr ⟨trivial, ⟨.inr ⟨by simpa using hnz, ?_⟩, fun _ => by simpa using hn⟩⟩⟩
    simpa using (hDn.fence hf3.1).fence hf4.1
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    have hSO : StackOK P lo n s.dmem := hfr.1.2.2.2.2.2.2.2.2.2.2 ▸ ⟨hH, hF⟩
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
      by simpa using hSO, ?_⟩
    obtain ⟨hR, hN⟩ := hT
    exact ⟨by simpa using (hR.fence hf1.1).fence hf2.1, by simpa using hN⟩
  all_goals done

end Kraken.Promising.Lower.Pilot2
