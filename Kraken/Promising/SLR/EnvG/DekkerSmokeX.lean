/-
**The x64 SB fragment by `vcgen`** — the
smoke test of the Dekker proof: Dekker's
`flag_i := 1; mfence; r := flag_j` on `EnvGX` (`Arch.tso`, empty plan) by one
`vcgen` call, ending in the `SBFact` of `EnvG/DekkerCore.lean`. It checks
that a program proof can carry the fence's exact effect: `vcgen` steps
`mfence` by `MachineWP.mfence_shared_spec` (priority 50, the env's own
`FenceOut`), not by the monotone `envMonoX_lift_spec` (`FenceLe` only).

- `sbFragX`: `movl $1, %ecx; movl %ecx, (%rsi); mfence; movl (%rdi), %eax`.
- `SB0`/`SB1`/`SB2`: before the store (a positive share of the own flag, the
  value `1` pure), before the fence (own message at `tw ≤ vwOld`), before the
  load (`tw ≤ vrNew`). All monotone under `FenceLe`.
- `sbFragX_envG`: the `TripleEnv` from `SB0` to `∃ v tw tr, SBFact …`.
-/
import Kraken.Promising.SLR.EnvG.DekkerCore
import Kraken.Promising.SLR.EnvG.X64VCGen
import Kraken.Promising.SLR.EnvG.X64Link
import Kraken.X64.Parser

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.Dekker
open Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.DekkerSmoke

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- Dekker's store-buffering fragment: raise the own flag at `(%rsi)`, full
fence, read the other flag at `(%rdi)`. -/
def sbFragX : Program := parse("
  movl $1, %ecx
  movl %ecx, (%rsi)
  mfence
  movl (%rdi), %eax
")

/-- The environment: `EnvG` under `Arch.tso` with the empty plan (no planned
release: every store pure), restricted to the two flags. -/
abbrev E (tid : Nat) (f l : BitVec 64) : SharedEnv := EnvGX Arch.tso tid ⟨[]⟩ [(f, 4), (l, 4)]

/-- Before the store: a positive share of the own flag, `1` pure for it. -/
def SB0 (f : BitVec 64) (σ : EStateX) : Prop := 0 < (σ.r.wr ⟨f, 4⟩).q ∧ Pred.Pure (σ.g.rel ⟨f, 4⟩) 1#128

/-- Before the fence: the own message at `tw ≤ vwOld`. -/
def SB1 (tid : Nat) (f : BitVec 64) (σ : EStateX) : Prop :=
  ∃ tw, σ.snap.mem.get? tw = some ⟨⟨f, 4⟩, 1#128, tid⟩ ∧ tw ≤ σ.vs.vwOld

/-- Before the load: the own message at `tw ≤ vrNew`. -/
def SB2 (tid : Nat) (f : BitVec 64) (σ : EStateX) : Prop :=
  ∃ tw, σ.snap.mem.get? tw = some ⟨⟨f, 4⟩, 1#128, tid⟩ ∧ tw ≤ σ.vs.vrNew

theorem SB0.fence {f : BitVec 64} {σ σ' : EStateX} (h : SB0 f σ) (hf : FenceLe σ σ') : SB0 f σ' := by
  unfold SB0; rw [hf.g, hf.r]; exact h

theorem SB1.fence {tid : Nat} {f : BitVec 64} {σ σ' : EStateX} (h : SB1 tid f σ) (hf : FenceLe σ σ') :
    SB1 tid f σ' := by
  unfold SB1; rw [hf.snap, hf.vwOld]; exact h

theorem SB2.fence {tid : Nat} {f : BitVec 64} {σ σ' : EStateX} (h : SB2 tid f σ) (hf : FenceLe σ σ') :
    SB2 tid f σ' := by
  obtain ⟨tw, h1, h2⟩ := h
  exact ⟨tw, by rw [hf.snap]; exact h1, Nat.le_trans h2 hf.vrNew⟩

/-! ## The VCs -/

theorem vc_store_ok {tid : Nat} {f l : BitVec 64} {σ : EStateX} (h : SB0 f σ) {a : BitVec 64} {v : Val}
    (ha : a = f) (hv : v = 1#128) : (E tid f l).ok (.store .plain false a 4 v) σ := by
  subst ha hv
  exact ⟨⟨rfl, h.1, fun _ => h.2, fun hr => by simp [Plan.rel, Plan.find?] at hr⟩, by simp [SharedEnv.AccessIn]⟩

theorem vc_store_step {tid : Nat} {f l : BitVec 64} {σ : EStateX} {a : BitVec 64} {v : Val}
    (ha : a = f) (hv : v = 1#128) :
    ∀ b (σ' : EStateX), (E tid f l).step (.store .plain false a 4 v) σ b σ' → SB1 tid f σ' := by
  subst ha hv
  intro b σ' hs
  obtain ⟨c, tw, -, hsnap, -, hwv, -⟩ := step_storeFacts hs
  exact ⟨tw, WriteSnap.get?_new' hsnap, hwv.vwOld (by decide)⟩

theorem vc_fence {tid : Nat} {f : BitVec 64} {σ σ' : EStateX} (h : SB1 tid f σ) (hfe : FenceOut σ σ' .sy) :
    SB2 tid f σ' := by
  obtain ⟨tw, h1, h2⟩ := h
  exact ⟨tw, by rw [show σ' = _ from hfe]; exact h1, Nat.le_trans h2 (vwOld_le_vrNew_of_fence hfe)⟩

theorem vc_load {tid : Nat} {f l : BitVec 64} {σ : EStateX} (h : SB2 tid f σ) {a : BitVec 64} (ha : a = l) :
    ∀ v (σ' : EStateX), (E tid f l).step (.load .plain false a 4) σ v σ' →
      ∃ tw tr, SBFact σ'.snap.mem tid ⟨f, 4⟩ 1#128 ⟨l, 4⟩ v tw tr := by
  subst ha
  intro v σ' hs
  obtain ⟨tw, h1, h2⟩ := h
  obtain ⟨tr, hf⟩ := sbFact_of_load h1 h2 (step_loadFacts (pl := ⟨[]⟩) hs)
  exact ⟨tw, tr, hf⟩

variable [layout : _root_.Layout]

local instance sbFragX.env : CodeEnv := ⟨layout sbFragX⟩

/-- **The SB fragment on `EnvG`, by `vcgen`**: from `SB0`, after
`flag := 1; mfence; r := other` the thread's snapshot carries the `SBFact`. -/
theorem sbFragX_envG (tid : Nat) (f l : BitVec 64) :
    TripleEnv (E tid f l)
      (fun s σ => s.regs.get64 .rsi = f ∧ s.regs.get64 .rdi = l ∧ Mem.loadInt s.dmem f 4 = none ∧
        Mem.loadInt s.dmem l 4 = none ∧ SB0 f σ)
      sbFragX (fun _ σ => ∃ v tw tr, SBFact σ.snap.mem tid ⟨f, 4⟩ 1#128 ⟨l, 4⟩ v tw tr)
      (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold sbFragX
  vcgen
  all_goals simp only [fenceMonoX_le_within, fenceMonoX_le_envG] at *
  case vc1 s σ0 hpre σ1 hdm hf =>
    obtain ⟨hx1, -, -, -, h0⟩ := hpre
    simp at hx1
    exact vc_store_ok (h0.fence hf) (by simp [hx1]) (by simp)
  case vc2 =>
    exact ⟨trivial, trivial⟩
  case vc3 s σ0 hpre σ1 dm σ2 hd σ3 hfe hdm hf =>
    obtain ⟨-, hx0, -, -, -⟩ := hpre
    simp at hx0
    exact ⟨trivial, by simp [hx0, SharedEnv.AccessIn]⟩
  case vc4 s σ0 hpre σ1 dm σ2 hd σ3 hfe y σ4 hld hf =>
    obtain ⟨hx1, hx0, hdf, hdl, -⟩ := hpre
    simp at hx0 hx1
    rcases hd with ⟨hsome, -, -⟩ | ⟨-, rfl, b, hst⟩
    · simp [hx1, hdf] at hsome
    · have h2 := vc_fence (vc_store_step (l := l) (by simp [hx1]) (by simp) b σ2 hst) hfe
      rcases hld with ⟨w, hm, -, -⟩ | ⟨-, v, hst2, -⟩
      · simp [hx0, hdl] at hm
      · obtain ⟨tw, tr, h⟩ := vc_load h2 (by simp [hx0]) v σ4 hst2
        exact ⟨v, tw, tr, h⟩

end Kraken.Promising.X64.EnvG.DekkerSmoke
