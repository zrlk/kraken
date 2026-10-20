/-
**One most-general specification per Treiber
fragment.** ISA: AArch64; machine: the executable
machine's per-thread environment semantics (`Executable.instrStepEnv`),
partial correctness (`Safely`), as `FragSpecEnv` (`Lower/FragSpec.lean`).

Before this file the `push`/`pop` fragments (`Pilot.pushFrag`/`popFrag`) had
two incompatible specifications: the first lowering pilot/the allocation pilot's in `EW P w` with the frame
`NoDmem` and the post `CalleeSaved`, and the stack-frame pilot's in `EWV P w` with the frame
`StackOK` and the post `Saved2`. Here each fragment has **one** specification:

- **The environment** `EWG P w G`: `EnvGCAdj` with load answers restricted to
  `G` (the stack-frame pilot's `valsEnv`), for every `G`. The stack-frame pilot's `EWV P w` is `EWG P w (GV P)`
  (`rfl`); the first lowering pilot's `EW P w` is `EWG P w ⊤` up to the propositional equality
  `valsEnv E ⊤ = E` (`valsEnv_top`), which `FragSpecEnv.of_vals_top` transports.
- **The frame** `F : Mem 64 → Prop`, kept unchanged (`dmem` is not written),
  under `TFrameOK P w G F`: in an `F` memory the fragment's private-memory
  lookups at the heap words it touches are empty (`top`, the own node's link,
  and the link of every non-null `G`-value of `top`). `NoDmem` satisfies it for
  every `G` (`tFrameOK_noDmem`); a `HeapOff (HP P)` frame (e.g. `StackOK`)
  satisfies it at `G = GV P` (`tFrameOK_heapOff`). (`NoDmem` does not imply the
  byte-level `HeapOff`: it constrains 8- and 4-byte words only, so the frame
  condition is stated at the word level the proofs use.)
- **The post** `Saved2` (the draft convention's callee-saved set: `x19`–`x28`, `dmem`, `sp`;
  `CalleeSaved` is its first half), `F` of the exit memory, and the protocol
  post; `pop`'s result carries its `G`-value (`PopResU`), which is the stack-frame pilot's
  node fact at `GV P` and trivial at `⊤`.

Contents: `pushFrag_specU`, `popFrag_specU`, `pushFrag_pureU`, `popFrag_pureU`
(the purity twins, frame-parametric; `RP rel` needs no value restriction).
The clients' theorems are re-derived in `Lower/FragSpecUniClients.lean`.
-/
import Kraken.Promising.Lower.FragSpec
import Kraken.Promising.Lower.PilotPure
import Kraken.Promising.Lower.Pilot2Specs

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG
open Kraken.DStack

namespace Kraken.Promising.Lower.Uni

open Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.Promising.SLR.EnvG.Treiber (casOp64)
open Kraken.Promising.Lower.Pilot (CalleeSaved NoDmem PopRes RP pushFrag popFrag)
open Kraken.Promising.Lower.Pilot2 (valsEnv LoadVal EnvGCAdjV GV HP Saved2 hp_top hp_link pn_cases top_node)

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The common environment -/

/-- Thread `w`'s environment, value-restricted by `G`. -/
noncomputable abbrev EWG (P : Params) (w : Nat) (G : Loc → Val → Prop) : SharedEnv :=
  EnvGCAdjV Arch.armv8 w (plan P w) G

/-- **The trivial value restriction changes nothing** (propositionally: the
step relation gains a `True` conjunct). -/
theorem valsEnv_top (E : SharedEnv) : (valsEnv E fun _ _ => True).step = E.step := by
  funext a σ r σ'
  cases a <;> simp [LoadVal]

/-- **Transport from `valsEnv E ⊤` to `E`** (counted). -/
theorem FragSpecEnv.of_vals_top {E : SharedEnv} {frag : Program} {l : Label}
    {Pre : Int64 → MachineData → (SharedEnv.counted E).State → Prop}
    {Post : Int64 → MachineData → (SharedEnv.counted E).State → MachineData → (SharedEnv.counted E).State → Prop}
    (h : FragSpecEnv (SharedEnv.counted (valsEnv E fun _ _ => True)) frag l Pre Post) :
    FragSpecEnv (SharedEnv.counted E) frag l Pre Post := by
  have key : ∀ st : (a : SharedAccess) → E.State → a.Ret → E.State → Prop, st = E.step →
      FragSpecEnv (SharedEnv.counted ⟨E.State, E.ok, st⟩) frag l Pre Post →
      FragSpecEnv (SharedEnv.counted E) frag l Pre Post := by
    intro st hst H
    subst hst
    exact H
  exact key _ (valsEnv_top E) h

/-! ## The frame -/

/-- `dmem` maps no 8- or 4-byte word (`Pilot.NoDmem`, on the memory). -/
def NoDmemD (d : Mem 64) : Prop := (∀ a, Mem.loadInt d a 8 = none) ∧ ∀ a, Mem.loadInt d a 4 = none

/-- **The frame condition** of thread `w`'s `push`/`pop` at value restriction
`G`: an `F` memory maps no word at `top`, at the own node's link, or at the
link of a non-null `G`-value of `top`. -/
def TFrameOK (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) : Prop :=
  ∀ d, F d → Mem.loadInt d P.t 8 = none ∧ Mem.loadInt d (P.n w + 8#64) 8 = none ∧
    ∀ v : Val, G ⟨P.t, 8⟩ v → BitVec.setWidth 64 v ≠ 0 → Mem.loadInt d (BitVec.setWidth 64 v + 8#64) 8 = none

theorem tFrameOK_noDmem (P : Params) (w : Nat) (G : Loc → Val → Prop) : TFrameOK P w G NoDmemD :=
  fun _ hd => ⟨hd.1 _, hd.1 _, fun _ _ _ => hd.1 _⟩

theorem tFrameOK_heapOff {P : Params} {w : Nat} (hw : w < 2) {F : Mem 64 → Prop}
    (hF : ∀ d, F d → HeapOff (HP P) d) : TFrameOK P w (GV P) F := fun d hd =>
  ⟨(hF d hd).loadInt_none (hp_top P) (n := 8) (by decide),
    (hF d hd).loadInt_none (hp_link (pn_cases hw)) (n := 8) (by decide),
    fun _ hg hnz => (hF d hd).loadInt_none (hp_link (top_node hg hnz)) (n := 8) (by decide)⟩

/-! ## `push` -/

/-- `push`'s general precondition. -/
def PushPreU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EWG P w G)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ t.regs.X1.toBitVec = P.n w ∧ F t.dmem ∧ Pu P w σ.1

/-- `push`'s general postcondition. -/
def PushPostU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Saved2 t t' ∧ F t'.dmem ∧ Po P w σ'.1

/-- `push`'s loop table. -/
abbrev pushTableU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EWG P w G)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ s.regs.X1.toBitVec = P.n w ∧ F s.dmem ∧ s.lr = ra ∧
    Saved2 t s ∧ lb = "push" ∧ Pu P w σ.1

/-- **`push`'s most general specification.** -/
theorem pushFrag_specU (P : Params) (w : Nat) (hL : TLocs P) (hw : w < 2) (G : Loc → Val → Prop)
    (F : Mem 64 → Prop) (hF : TFrameOK P w G F) :
    FragSpecEnv (SharedEnv.counted (EWG P w G)) pushFrag "push" (PushPreU P w G F) (PushPostU P w G F) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => pushTableU P w G F ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hx1, hd, hPu⟩ => ⟨hx0, hx1, hd, hlr, Saved2.refl t, rfl, hPu⟩) ?_
  intro _ ra t g _
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd, hlr, hfr, -, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, hn8, -⟩ := hF _ hd
  all_goals simp only [fenceMono_le_counted, Pilot2.fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
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
    · refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
        by simpa using hd, Po.fence (Po.fence (Po.fence hPo hf2.1) hf3.1) hf4.1⟩
  all_goals done

/-! ## `pop` -/

/-- What `pop` returns in `x`: `Pilot.PopRes`, and a non-null result is a
`G`-value of `top` (the stack-frame pilot's node fact at `G = GV P`, `top_node`). -/
def PopResU (P : Params) (w : Nat) (G : Loc → Val → Prop) (x : BitVec 64) (σ : State isa) : Prop :=
  PopRes P w x σ ∧ (x ≠ 0 → ∃ v : Val, G ⟨P.t, 8⟩ v ∧ BitVec.setWidth 64 v = x)

/-- `pop`'s general precondition. -/
def PopPreU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ra : Int64) (t : MachineData)
    (σ : (SharedEnv.counted (EWG P w G)).State) : Prop :=
  t.lr = ra ∧ t.regs.X0.toBitVec = P.t ∧ F t.dmem ∧ Po P w σ.1

/-- `pop`'s general postcondition. -/
def PopPostU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (_ : Int64) (t : MachineData)
    (_ : (SharedEnv.counted (EWG P w G)).State) (t' : MachineData) (σ' : (SharedEnv.counted (EWG P w G)).State) :
    Prop :=
  Saved2 t t' ∧ F t'.dmem ∧ PopResU P w G t'.regs.X0.toBitVec σ'.1

/-- `pop`'s table. -/
abbrev popTableU (P : Params) (w : Nat) (G : Loc → Val → Prop) (F : Mem 64 → Prop) (ra : Int64) (t : MachineData) :
    Label → MachineData → (SharedEnv.counted (EWG P w G)).State → Prop :=
  fun lb s σ => s.regs.X0.toBitVec = P.t ∧ F s.dmem ∧ s.lr = ra ∧ Saved2 t s ∧
    ((lb = "pop" ∧ Po P w σ.1) ∨ (lb = "pop_done" ∧ PopResU P w G s.regs.X2.toBitVec σ.1))

/-- **`pop`'s most general specification.** -/
theorem popFrag_specU (P : Params) (w : Nat) (hw : w < 2) (G : Loc → Val → Prop) (F : Mem 64 → Prop)
    (hF : TFrameOK P w G F) :
    FragSpecEnv (SharedEnv.counted (EWG P w G)) popFrag "pop" (PopPreU P w G F) (PopPostU P w G F) := by
  refine FragSpecEnv.of_cfg (fun ra t _ => popTableU P w G F ra t) rfl (by decide)
    (fun ra t g ⟨hlr, hx0, hd, hPo⟩ => ⟨hx0, hd, hlr, Saved2.refl t, .inl ⟨rfl, hPo⟩⟩) ?_
  intro _ ra t g _
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd, hlr, hfr, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, -, hpv⟩ := hF _ hd
  all_goals simp (config := { decide := true }) only [true_and, false_and, or_false, false_or] at hT
  all_goals simp only [fenceMono_le_counted, Pilot2.fenceMono_le_valsEnv, fenceMono_le_envGCAdj,
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
    have hl8 := hpv v (by simpa [hx0] using hld.1.2) hnz
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
    have hl8 := hpv v (by simpa [hx0] using hld.1.2) hnz
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
    have hgv : G ⟨P.t, 8⟩ v := by simpa [hx0] using hld.1.2
    have hl8 := hpv v hgv hnz
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
      by simpa [Saved2, CalleeSaved] using hfr, .inr ⟨trivial, ⟨.inr ⟨by simpa using hnz, ?_⟩,
        fun _ => ⟨v, hgv, by simp⟩⟩⟩⟩
    simpa using (hDn.fence hf3.1).fence hf4.1
  case vc1 =>
    rename_i s σ0 σ1 σ2 hf1 hf2 _
    refine .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr,
      by simpa using hd, ?_⟩
    obtain ⟨hR, hN⟩ := hT
    exact ⟨by simpa using (hR.fence hf1.1).fence hf2.1, by simpa using hN⟩
  all_goals done

/-! ## The purity twins, frame-parametric -/

/-- `push`'s purity table. -/
abbrev pushPTableU (rel : Loc → Pred) (F : Mem 64 → Prop) (t n : BitVec 64) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ F s.dmem ∧ s.lr = ra ∧ Saved2 t0 s ∧ lb = "push"

/-- **`push` is pure, most generally**: any `top` `t`, node `n` and frame `F`
whose memories map no word at `t` or at the link `n + 8`. -/
theorem pushFrag_pureU (rel : Loc → Pred) (t n : BitVec 64) (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v)
    (F : Mem 64 → Prop) (hF : ∀ d, F d → Mem.loadInt d t 8 = none ∧ Mem.loadInt d (n + 8#64) 8 = none) :
    FragSpecEnv (RP rel) pushFrag "push"
      (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ F s.dmem)
      (fun _ s _ s' _ => Saved2 s s' ∧ F s'.dmem) := by
  have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  refine FragSpecEnv.of_cfg (fun ra t0 _ => pushPTableU rel F t n ra t0) rfl (by decide)
    (fun ra t0 g ⟨hlr, hx0, hx1, hd⟩ => ⟨hx0, hx1, hd, hlr, Saved2.refl t0, rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [pushFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals obtain ⟨ht8, hn8⟩ := hF _ hd
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, hx1, ht8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, ht8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, rfl⟩, .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, by simpa using hd⟩
  all_goals done

/-- `pop`'s purity table. -/
abbrev popPTableU (rel : Loc → Pred) (F : Mem 64 → Prop) (t : BitVec 64) (ra : Int64) (t0 : MachineData) :
    Label → MachineData → (RP rel).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ F s.dmem ∧ s.lr = ra ∧ Saved2 t0 s ∧ (lb = "pop" ∨ lb = "pop_done")

/-- **`pop` is pure, most generally**: any `top` `t` and frame `F` whose
memories map no word at `t`; the link load through `x2` may be private or
shared. -/
theorem popFrag_pureU (rel : Loc → Pred) (t : BitVec 64) (F : Mem 64 → Prop)
    (hF : ∀ d, F d → Mem.loadInt d t 8 = none) :
    FragSpecEnv (RP rel) popFrag "pop" (fun ra s _ => s.lr = ra ∧ s.regs.X0.toBitVec = t ∧ F s.dmem)
      (fun _ s _ s' _ => Saved2 s s' ∧ F s'.dmem) := by
  refine FragSpecEnv.of_cfg (fun ra t0 _ => popPTableU rel F t ra t0) rfl (by decide)
    (fun ra t0 g ⟨hlr, hx0, hd⟩ => ⟨hx0, hd, hlr, Saved2.refl t0, .inl rfl⟩) ?_
  intro _ ra t0 g _
  cfg_cases_env [popFrag]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hd, hlr, hfr, -⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hF _ hd
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp [hx0, ht8, SharedEnv.relPureQ]; done)
  case vc4 =>
    exact .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inr rfl⟩, .inl (by decide)⟩)
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hld2 with ⟨_, _, _, rfl⟩ | ⟨_, h, _⟩ <;> omega
    refine .inl (Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simpa using hd,
      by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩)
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    exact ⟨by simp [hx0], by simpa using hd, by simpa [MachineData.lr] using hlr,
      by simpa [Saved2, CalleeSaved] using hfr, .inr trivial⟩
  case vc1 =>
    exact .inr ⟨by simpa [MachineData.lr] using hlr, by simpa [Saved2, CalleeSaved] using hfr, by simpa using hd⟩
  all_goals done

end Kraken.Promising.Lower.Uni
