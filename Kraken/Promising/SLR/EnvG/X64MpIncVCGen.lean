/-
**x64 MP with an unlocked `incl` release, whole threads by `vcgen`**
.

- `mpIncWriterX_envG`: a `TripleEnv` in `EnvGLRX` (`EW`) from `W1I` to
  `W3I`, one `vcgen [inc32_shared_spec]` call; the `incl` goal is closed by
  `vc_incLoad`/`vc_incStore` at the loaded value plus one.
- `mpReaderIX_envGP`: `X64MpVCGen.mpReaderX_envGP` with the `WorldRI`
  table predicates (same proof).
-/
import Kraken.Promising.SLR.EnvG.X64MpInc
import Kraken.Promising.SLR.EnvG.X64MpVCGen

open Std.WP Kraken Kraken.Promising MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Mp
open Kraken.Promising.X64.EnvG.MpSmoke

namespace Kraken.Promising.X64.EnvG.MpInc

set_option mvcgen.warning false
set_option experimental.vcgen true

/-! ## The table predicates are monotone under fences -/

theorem W1I.fence {P : Params} {σ σ' : EStateX} (h : W1I P σ) (hf : FenceLe σ σ') : W1I P σ' := by
  unfold W1I WorldWI; rw [hf.g, hf.r]; exact h

theorem W2I.fence {P : Params} {σ σ' : EStateX} (h : W2I P σ) (hf : FenceLe σ σ') : W2I P σ' := by
  unfold W2I WorldWI Own1; rw [hf.g, hf.r, hf.vwOld]; exact h

theorem W3I.fence {P : Params} {σ σ' : EStateX} (h : W3I P σ) (hf : FenceLe σ σ') : W3I P σ' := by
  unfold W3I WorldWI; rw [hf.g, hf.r]; exact h

theorem R1I.fence {P : Params} {σ σ' : EStateX} (h : R1I P σ) (hf : FenceLe σ σ') : R1I P σ' :=
  R1G.fence (φ := φI P) h hf

theorem R3I.fence {P : Params} {σ σ' : EStateX} (h : R3I P σ) (hf : FenceLe σ σ') : R3I P σ' :=
  R3G.fence (φ := φI P) h hf

/-! ## The VCs at an address and value given by equations -/

theorem vc_w1I_ok {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1I P σ) {a : BitVec 64}
    {v : Val} (ha : a = P.d) (hv : v = dataVal) : (EW P tid).ok (.store .plain false a 4 v) σ := by
  subst ha hv; exact (vc_w1I hL tid σ h).1

theorem vc_w1I_step {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W1I P σ) {a : BitVec 64}
    {v : Val} (ha : a = P.d) (hv : v = dataVal) :
    ∀ b (σ' : EStateX), (EW P tid).step (.store .plain false a 4 v) σ b σ' → W2I P σ' := by
  subst ha hv; exact (vc_w1I hL tid σ h).2

theorem vc_incLoad_at {P : Params} (tid : Nat) (σ : EStateX) (h : W2I P σ) {a : BitVec 64} (ha : a = P.f) :
    ∀ v (σ' : EStateX), (EW P tid).step (.load .plain false a 4) σ v σ' → W2I P σ' := by
  subst ha; exact vc_incLoad tid σ h

theorem vc_incStore_at {P : Params} (hL : MpLocs P) (tid : Nat) (σ : EStateX) (h : W2I P σ) {a : BitVec 64}
    (ha : a = P.f) (v : Val) :
    (EW P tid).ok (.store .plain false a 4 v) σ ∧
      ∀ b (σ' : EStateX), (EW P tid).step (.store .plain false a 4 v) σ b σ' → W3I P σ' := by
  subst ha; exact vc_incStore hL tid σ h v

theorem vc_r1I_step {P : Params} (tid : Nat) (σ : EStateX) (h : R1I P σ) {a : BitVec 64} (ha : a = P.f) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' →
      R1I P σ' ∧ (BitVec.setWidth 32 v ≠ 0 → R3I P σ') :=
  vc_r1G_step (φ := φI P) tid σ h ha

theorem vc_r3I_step {P : Params} (tid : Nat) (σ : EStateX) (h : R3I P σ) {a : BitVec 64} (ha : a = P.d) :
    ∀ v (σ' : EStateX), (E P tid).step (.load .plain false a 4) σ v σ' → R4I P σ' ∧ (σ'.cl → v = dataVal) :=
  vc_r3G_step (flagPredI_law _) tid σ h ha

variable [layout : _root_.Layout]

/-! ## The writer -/

section Writer

local instance mpIncWriterX.env : CodeEnv := ⟨layout mpIncWriterX⟩

/-- **The x64 MP `incl` writer on `EnvGLRX`**: from `W1I` the writer ends in
`W3I`. -/
theorem mpIncWriterX_envG (P : Params) (hL : MpLocs P) (tid : Nat) :
    TripleEnv (EW P tid)
      (fun s σ => s.regs.get64 .rdi = P.f ∧ s.regs.get64 .rsi = P.d ∧ Mem.loadInt s.dmem P.f 4 = none ∧
        Mem.loadInt s.dmem P.d 4 = none ∧ W1I P σ)
      mpIncWriterX (fun _ σ => W3I P σ) (fun _ _ _ => False) := by
  apply TripleEnv.of_triple
  unfold mpIncWriterX
  vcgen [inc32_shared_spec]
  case vc1 s σ hpre =>
    obtain ⟨-, hx1, -, hdd, -⟩ := hpre
    simp [hx1, hdd]
  case vc2 s σ hpre =>
    obtain ⟨-, hx1, -, -, hW⟩ := hpre
    exact vc_w1I_ok hL tid σ hW (by simp [hx1]) (by decide)
  case vc3 s σ hpre _ _ _ =>
    obtain ⟨hx0, -, hdf, -, -⟩ := hpre
    simp [hx0, hdf]
  case vc4 s σ hpre _ _ _ =>
    obtain ⟨hx0, -, -, -, -⟩ := hpre
    exact ⟨trivial, by simp [SharedEnv.AccessIn, hx0]⟩
  case vc5 s σ hpre b σ1 hst v σ2 hld =>
    obtain ⟨hx0, hx1, -, -, hW⟩ := hpre
    have hW2 := vc_w1I_step hL tid σ hW (by simp [hx1]) (by decide) b σ1 hst
    have hW2' := vc_incLoad_at tid σ1 hW2 (by simp [hx0]) v σ2 hld
    have hS := vc_incStore_at hL tid σ2 hW2' (a := s.regs.get64 .rdi + Int64.toBitVec 0) (by simp [hx0])
      ((BitVec.setWidth 32 v + 1).setWidth 128)
    exact ⟨hS.1, fun _ g'' hs' _ _ _ => Eventually.done _ (Or.inl ⟨rfl, hS.2 _ g'' hs'⟩)⟩

end Writer

/-! ## The reader -/

section Reader

variable [Executable.ValidLayout (layout mpReaderX)]

local instance mpReaderIX.env : CodeEnv := ⟨layout mpReaderX⟩

/-- The reader's table: `R1` at `spin`; at `done_r`, `R4` and, under the
clean flag, `ebx = 42`. -/
abbrev readerTablePI (P : Params) (tid : Nat) :
    Label → MachineData → (SharedEnv.counted (E P tid)).State → Prop :=
  fun lb s σ => FrameRX P s ∧
    ((lb = "spin" ∧ R1I P σ.1) ∨
      (lb = "done_r" ∧ R4I P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42)))

/-- **The x64 MP reader on `EnvG` with `WorldRI`, with its end facts** (counted, partial;
`mpReaderX_envGP` with the `φI` world facts). -/
theorem mpReaderIX_envGP (P : Params) (tid : Nat) :
    PartialTripleEnv (SharedEnv.counted (E P tid))
      (fun s σ => FrameRX P s ∧ R1I P σ.1)
      mpReaderX (fun s σ => R4I P σ.1 ∧ (σ.1.cl → (s.regs.get64 .rbx).setWidth 32 = 42))
      (fun _ _ _ => False) :=
  mpReaderX_envGPG P (φI P) (flagPredI_law _) tid

end Reader

end Kraken.Promising.X64.EnvG.MpInc
