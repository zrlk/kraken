/-
Part 7: **the worker of `treiber2_nodes.kl` is
pure** (`TreiberRelPure.lean` for `treiber2Worker`): in
`SharedEnv.relPure Arch.armv8 rel` for any release predicates `rel` pure at
the node's link word `[n + 8]` (8 bytes). The worker's only non-release write
is the plain `str` of the link; both `casal`s are release RMWs
(unconstrained).

The purity half of `final_of_relPureSafelyF`: `StartW`, `treiber2PureSpec`
and `treiber2PureSpec_init`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.EnvG.Treiber2Smoke
import Kraken.AArch64.EnvCfg

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2

set_option mvcgen.warning false
set_option experimental.vcgen true

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2Worker)]

local instance treiber2Worker.env : CodeEnv := ⟨layout treiber2Worker⟩

/-- The worker's purity table: the frame everywhere. -/
abbrev workPureTable (t n : BitVec 64) (rel : Loc → Pred) :
    Label → MachineData → (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (lb = "push" ∨ lb = "pop" ∨ lb = "done")

/-- **The worker is pure** (counted, partial): its `str` writes the link,
pure there; the `casal`s are releases. -/
theorem treiber2Worker_relPure (rel : Loc → Pred) (t n : BitVec 64)
    (hn : ∀ v : Val, Pred.Pure (rel ⟨n + 8, 8⟩) v) :
    PartialTripleEnv (SharedEnv.counted (SharedEnv.relPure Arch.armv8 rel))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none))
      treiber2Worker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workPureTable t n rel) (hP := by funext s g; simp [workPureTable])
  cfg_cases_env [treiber2Worker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals have hn' : ∀ v : Val, Pred.Pure (rel ⟨n + 8#64, 8⟩) v := hn
  all_goals try (simp [hx0, hx1, hd8, SharedEnv.relPureQ, Arch.storeKind, hn',
    show Arch.armv8.plainStore = .plain from rfl]; done)
  case vc7 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hd8]
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    have h12 : σ1.2 ≤ σ2.2 := by omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inl rfl⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc10 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [hx0, hx1, hd8]
  case vc4 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr rfl)⟩,
      .inl (by decide)⟩
  case vc9 =>
    simp [hx0, SharedEnv.relPureQ]
    -- the `casal` is a release RMW: unconstrained
    exact fun h => (h (by decide)).elim
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
      omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inl rfl)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr rfl)⟩,
      .inl (by decide)⟩
  all_goals done

end Worker

/-! ## Start states and the purity specifications -/

section Start

variable [layout : _root_.Layout]

/-- **A worker's start state** (`i:X0=top; i:X1=n(i+1)`): at the start of
`treiber2Worker` with `x0 = t`, `x1 = n`; no private copy of any 8-byte word
(the link load's address is a loaded value). -/
structure StartW (t n : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout treiber2Worker
  decls : s.decls = {}
  endPc : s.endPc = (layout treiber2Worker).addrOf treiber2Worker.length
  pc : s.st.2 = (layout treiber2Worker).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = t
  x1 : s.st.1.regs.X1.toBitVec = n
  d8 : ∀ a, Mem.loadInt s.st.1.dmem a 8 = none

end Start

/-- The threads' purity specifications: the worker at layout `l0` at thread
`0`, at layout `l1` elsewhere. -/
def treiber2PureSpec (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2Worker)]
    [Executable.ValidLayout (l1 treiber2Worker)] (rel : Loc → Pred) : Nat → RelPureSpec Arch.armv8 rel
  | 0 => RelPureSpec.ofProgram (layout := l0) treiber2Worker fun _ _ => ∃ _ : Nat, True
  | _ + 1 => RelPureSpec.ofProgram (layout := l1) treiber2Worker fun _ _ => ∃ _ : Nat, True

/-- **The purity specifications hold at the start states**, for release
predicates pure at the nodes' links. -/
theorem treiber2PureSpec_init (l0 l1 : _root_.Layout) [Executable.ValidLayout (l0 treiber2Worker)]
    [Executable.ValidLayout (l1 treiber2Worker)] {rel : Loc → Pred} {t n0 n1 : BitVec 64}
    (hn0 : ∀ v : Val, Pred.Pure (rel ⟨n0 + 8, 8⟩) v) (hn1 : ∀ v : Val, Pred.Pure (rel ⟨n1 + 8, 8⟩) v)
    {s0 s1 : isa.State} (h0 : StartW (layout := l0) t n0 s0) (h1 : StartW (layout := l1) t n1 s1) :
    ∀ tid s, [s0, s1][tid]? = some s → (treiber2PureSpec l0 l1 rel tid).Holds s
  | 0, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hd8⟩ := h0
    letI : CodeEnv := ⟨l0 treiber2Worker⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l0)
      (treiber2Worker_relPure (layout := l0) rel t n0 hn0).uncount rfl he hds hend hpc ⟨0, hx0, hx1, hd8⟩
  | 1, s, hs => by
    cases hs
    obtain ⟨he, hds, hend, hpc, hx0, hx1, hd8⟩ := h1
    letI : CodeEnv := ⟨l1 treiber2Worker⟩
    exact RelPureSpec.holds_of_partialTripleEnv (layout := l1)
      (treiber2Worker_relPure (layout := l1) rel t n1 hn1).uncount rfl he hds hend hpc ⟨0, hx0, hx1, hd8⟩
  | _ + 2, _, hs => by cases hs

end Kraken.Promising.SLR.EnvG.Treiber2
