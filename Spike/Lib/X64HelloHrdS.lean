/-
**The pieces of hello.w's `wc_rodata` up to the allocator's return inside the start's level at the setup call's
frame** (x86-64; the twin of `Spike/Lib/A64HelloHrdS.lean`, the start's `hrd`): the facts by which
`X64HelloHrdRootX.hrd_WSHX` takes `RdWfSFX.rdPreW_WSHX` at `fs = [frH env]` (the root's `frM`), `wc_rodata`'s
entry invariant `mRdJ0 (rdJH lab R J) σC` (the source at `rodata`'s allocation `rdCN` after the setup's call) taken
also as the allocator's caller's (`J1 := J0`: the entry block's local run is the empty one).

The controls' facts are `RdCf.hcf_frH` at `rdCN`, the placement `RdPreS.rdPreW_frS` with the frame's `me` at
`scc_rt_main`'s spill of `%rdi` (slot `-16`, `frP_mNC`) whenever the invariant is inhabited (`rdPreW_frS'`; else
`rdPreW_void`). The memory side's and the arena's premises (`hmp`, `hmem`, `hno`, `hX0a`, `hctx`, `hctr` … `h64`)
are left to the root.

- `rdPreW_void`: `RdPreW` at uninhabited invariants, inside any predicate.
- `rdPreW_frS'`: `RdPreS.rdPreW_frS` with the frame's premises asked only at an inhabited invariant.
- `frP_mNC`: the frame's premises at a caller's state at `mNC`, `me` the entry's `%rdi`.

The statement (AArch64 `hrd_WSHF`, at `WSHF`) is at `ownGHXW` only: `X64HelloHrdRootX.hrd_WSHX`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- `me` is at `scc_rt_main`'s slot `-16`, where its prologue spilled `%rdi` (AArch64: slot `-80`, the saved `x0`),
  so `frP_mNC` asks `me`'s representation of `%rdi` (AArch64: `X0`).
- `mNC` and `rdJH` take the region `R`; the thread pointer is `fsBase` (AArch64 `TPIDR_EL0`).
- `call` pushes the return address: `8 ≤ R.hi` (AArch64 `0`); the base is 8-aligned (`hR8`; AArch64 `hal`, 16).
  The allocator's region is `aR (mR R)` with `CallerCells (mR R) (-48) (-160) 8` (AArch64 `0`), and its return
  label is `.Lwc_rodata.x0` (AArch64 `.L19_wc_rodata.sp0`).
- The prologue is x86-64's `XProW`, so `rdPreW_void` uses `WeS.proW_ofCtl` at it.
-/
import Spike.Lib.X64HelloRdPreS
import Spike.Lib.X64HelloWeS

namespace Spike.Lib.X64.HelloPh.HrdS

open CoreLang CoreTerm TermRun
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep)
open Spike.Lib.X64Consumer (Lbl Placed)
open Spike.Lib.X64ConsumerS (PlacedSE)
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Flow.HelloRd (rN RdPreW)
open Spike.Lib.X64.Flow.Hello1 (mNC mR mF)
open Spike.Lib.X64HelloRdCf (frH)
open Spike.Lib.X64.HelloPh.RdPlS (FrP)
open Spike.Lib (Frag Ctl Region)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## The placement at inhabited invariants -/

section Pl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {exe : _root_.Executable} {endPc : Int64} {ms : Spike.Lib.MemSide isa}
  {J0 J1 : FAS → Ctl → Prop}

/-- **`wc_rodata` up to the allocator's return at uninhabited invariants** is inside any predicate. -/
theorem rdPreW_void {P : Frag isa} {R : Region} {F : MachineData → Prop}
    (hn : ∀ σ c, ¬ J0 σ c ∧ ¬ J1 σ c) : RdPreW P (fun _ _ => False) exe endPc R F ms J0 J1 :=
  ⟨Spike.Lib.X64.HelloPh.WeS.proW_ofCtl fun σ c h => absurd h (hn σ c).1,
    fun _ _ c _ _ _ _ _ _ ⟨⟨σe, h, _⟩, _⟩ => absurd h (hn σe c).1,
    fun q _ _ => Spike.Lib.X64SetupPlaced.allocW_of_ctl fun _ hF _ _ _ _ => by
      obtain ⟨-, -, -, -, c', -, ⟨⟨σe, h, -⟩, -⟩, -⟩ := hF
      exact absurd h (hn σe c').2⟩

/-- **`RdPreS.rdPreW_frS` with the frame's premises asked only at an inhabited invariant** (`hP`). -/
theorem rdPreW_frS' {R : Region} {F : MachineData → Prop} {m0 : MachineData} {σC : FAS} {env : Env}
    (hP : (∃ σ c, J0 σ c ∨ J1 σ c) → FrP lbl R env σC) (hlo : R.lo ≤ -288)
    (hc : ∀ σ c, J0 σ c ∨ J1 σ c → ∀ s, Placed Λ lbl s c) :
    RdPreW (fun s c => PlacedSE Λ lbl s c [frH env]) (fun _ _ => False) exe endPc (mR R) (mF R F m0 σC) ms
      J0 J1 := by
  by_cases h : ∃ σ c, J0 σ c ∨ J1 σ c
  · exact Spike.Lib.X64.HelloPh.RdPreS.rdPreW_frS (hP h) hlo hc
  · exact rdPreW_void fun σ c => ⟨fun h0 => h ⟨σ, c, .inl h0⟩, fun h1 => h ⟨σ, c, .inr h1⟩⟩

/-- **The frame's premises at a caller's state at `mNC`** (`hJC`): `me`'s one word `w` (`hme`) is represented
by the entry's `%rdi` (`hX`), which `scc_rt_main` spilled at its slot `-16`. -/
theorem frP_mNC {lab : Label → Int64} {J : FAS → Ctl → Prop} {R : Region} {env : Env} {w : Word} {σC : FAS}
    (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hme : ∀ ty ws, lookupE env "me" = some (ty, ws) → ws = [w])
    (hX : ∀ σ c, J σ c → ValRep lbl w.val σ.regs.rdi.toBitVec.toNat) (hJC : ∃ c, (mNC lab R J).J σC c) :
    FrP lbl R env σC := by
  obtain ⟨c, σe, hJ, -, -, h16, -⟩ := hJC
  refine ⟨hR, hlo, hhi, -16, w, ⟨⟨by decide, by omega, by omega⟩, by decide⟩, hme, ?_⟩
  rw [h16]
  exact hX σe c hJ

end Pl

end Spike.Lib.X64.HelloPh.HrdS

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.HrdS.rdPreW_frS'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HrdS.rdPreW_frS'
