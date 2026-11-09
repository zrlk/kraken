/-
**hello.w on x86-64: the pieces of the state at `wc_rodata`'s entry after `call wc_rodata` inside the start's
level** (the twin of `Spike/Lib/A64HelloWeS.lean`): the facts by which `X64HelloWeSX` puts a state at
`Hello1.mNC` (`wc_rodata`'s entry, `scc_rt_main`'s frame at `-80` of the region `R`, the source still at the
start's control `c0`) inside the start's level.

The state is the first of `wc_rodata`'s prologue head in the callee's region `Hello1.mR R` (`at_enter`), so it is
the prologue's first block at its first instruction (`blkW_at0`) at the entry invariant `rdJe` (the caller's state
at `mNC` entered at `-80`), whose controls are `c0`, placed at every state (`proW_ofCtl`).

- `proW_ofCtl`: a prologue inside a predicate its invariant's controls satisfy at every state (`OfCtl.proW_ofCtl`).
- `blkW_at0`: a block node's state at its first instruction.
- `msT`: a memory side for the prologue's first block, which does not read it.
- `rdJe`: `wc_rodata`'s entry invariant at a caller's state at `mNC`.

The statements (AArch64 `hWe_W0SH`, `hWe_WS`, at `WSH`) are at `ownGHXW` only: `X64HelloWeSX`'s
`hWe_W0SHX`, `hWe_WSX`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- The prologue is x86-64's five-node `XProW` (`wc_rodata`'s frame of 32, `.Lwc_rodata.stk`), so `proW_ofCtl`
  takes its byte sizes and saved registers (AArch64: `ProW` with `XReg` pairs).
- A block's instructions are cells with sizes: `blkW_at0` is at `cellOff blk 0 = 0` (AArch64: `4 * 0`).
- `mNC` takes the region `R` (it records `%rbp = R.addr (-8)`); `call` pushes the return address, so the callee
  region is `R.callee (-80) (-208) 8` and `R.hi` is at least `8` (AArch64: `0`); there is no 16-alignment
  premise. The thread pointer is `fsBase` (AArch64: `TPIDR_EL0`).
-/
import Spike.Lib.X64HelloRdPreWI
import Spike.Lib.X64HelloAllocWSF
import Spike.Lib.X64HelloWcWf
import Spike.Lib.X64SetupPlaced
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloOfCtl

namespace Spike.Lib.X64.HelloPh.WeS

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (ND BlkW NodeW At)
open Spike.Lib.X64.Flow (XProW)
open Spike.Lib.X64.Flow.Hello1 (mNC)
open Spike.Lib (Frag Ctl Region)

/-- The abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.X64.AS

/-! ## Generic node facts -/

section Gen

variable {W : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A prologue is inside a predicate its invariant's controls satisfy at every state** (`h`), with no outside
moves; `OfCtl.proW_ofCtl`. -/
theorem proW_ofCtl {ms : Spike.Lib.MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : FAS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, W s c) :
    XProW W (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  Spike.Lib.X64.HelloPh.OfCtl.proW_ofCtl h

/-- **A block node's state at its first instruction is inside `W`** (`BlkW` at `0`, the block nonempty). -/
theorem blkW_at0 {K : State → State → Prop} {n : ND} {blk : List (Directive × Nat)}
    (hW : BlkW W K exe endPc R F n blk) (hl : 0 < blk.length) {s : State} {c : Ctl}
    (h : At exe endPc R F n s c) : W s c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  have := (hW s σ c he hn hd hpc hA hF hJ 0 hl s.st.1 hA (Spike.Lib.X64.DFrame.refl _ _)).1
  rw [show Spike.Lib.X64.cellOff blk 0 = 0 from rfl, Spike.Lib.X64.Flow.ofNat_zero', ← hpc] at this
  exact this

end Gen

/-- A memory side for the prologue's first block, which does not read it (`XProW.w0`). -/
def msT : Spike.Lib.MemSide isa :=
  { rd := fun _ => False, rt := fun _ => False, K := none, G := fun _ _ => False, heap := 0, ctr := 0,
    units := fun _ _ => 0, off := fun _ _ => 0, cells := 0 }

/-- **`wc_rodata`'s entry invariant at a caller's state at `mNC`**: the caller's state `σC` at `mNC` (region `R`,
invariant `J`) at the control `c`, entered at `-80` (`at_enter`'s node invariant). -/
def rdJe (lab : Label → Int64) (R : Region) (J : FAS → Ctl → Prop) (c : Ctl) (σC : FAS) (σ : FAS) (c' : Ctl) :
    Prop :=
  c' = c ∧ σ = Spike.Lib.X64.enter (-80) σC ∧ (mNC lab R J).J σC c

end Spike.Lib.X64.HelloPh.WeS
