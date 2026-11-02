/-
**hello.w's `wc_main` at the `clone`: the box's landing under `tpXa`, the region's base and `ClonePostH`** (x86-64;
the twin of `Spike/Lib/A64HelloWcHat.lean`, at hello's `wc_main`, frame 128). The pre-spawn segment's exit at the
clone's `syscall` (`wcNSH`) is `ClonePostH` once its region's base is known to be `%rsp + 128`; as on AArch64 no
region change is made here: hello's `ClonePostH` keeps `wcNSH` in `wc_main`'s region.

- `at_bXH_tpXa`: the box's landing at `ms` is at `tpXa ms t`;
- `wcNSH_base`: at the clone's `syscall` in a region reaching `-128`, its base is `%rsp + 128`;
- `clonePostH_of`: a state at `wcNSH` (at the second TCB `tH`, the stack top `kOf`) with that base, main's stack
  (`%rsp + 224` stack 0's top) and the thread pointer `t = pinA + 8` is `ClonePostH`.

## Differences from the AArch64 version

- `wc_main`'s frame is `%rbp`-based, `%rsp` at its offset `-128` (AArch64: the base `sp + 144`); `wcNSH_base` asks
  `R.lo ≤ -128` and reads `%rsp` (AArch64 `-144`, `SP`).
- `clonePostH_of` has no alignment premise beyond `ClonePostH`'s own (`R.base.toNat % 16 = 0`, kept as `hal`); the
  thread pointer is `fsBase` (`TP t s` is `fsBase = t`, which `ClonePostH` states directly).
- Only the live constants are twinned: the composites `hello_wc_mid_hat`, `hello_wc_mid_hatW` are not.
-/
import Spike.Lib.X64HelloWcMid
import Spike.Lib.X64HelloClonePreHOf
import Spike.Lib.X64WakeWcHat

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.HelloPh.WcSp6 (oWH wcNSH)
open Spike.Lib.X64.Flow.WakeWc (kOf okb_tpXa)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64HelloPreA (ClonePostH)

/-- **The box's landing under `tpXa`**: a state at `bXH` under `ms` is at `bXH` under `tpXa ms t`. -/
theorem at_bXH_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Ctl}
    (h : At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH (tpXa ms t) (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, h1, h2, h3⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_tpXa q.2⟩, h1, h2, h3⟩

/-- **At the clone's `syscall` the region's base is `%rsp + 128`**: `wcNSH`'s offsets put `%rsp` at `-128`, an
offset of `R` (`R.lo ≤ -128`, `0 ≤ R.hi`). -/
theorem wcNSH_base {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {c0 : Ctl}
    {t k : BitVec 64} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (h : At exe endPc R F (wcNSH (_root_.Executable.labels exe).label c0 t k sl me cA fr) s c) :
    (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 128 := by
  obtain ⟨-, -, -, -, σ, hA, -, -⟩ := h
  have hsp : σ.regs.get64 .rsp = R.addr (-128) := hA.so .rsp (-128) (by simp [SO.get, wcNSH])
  have := Region.addr_toNat_of hR hlo (by omega : (-128 : Int) < R.hi)
  rw [hA.regs, hsp]
  omega

/-- **The `clone` state is `ClonePostH`**: a state at `wcNSH` (the source `c` itself, the second TCB `tH`, the
child's stack top `kOf`) in the layout `L`, with `R`'s base 16-aligned and `%rsp + 128` (`hb`, `wcNSH_base`),
main's `%rsp` 224 below stack 0's top (`hsp`) and the thread pointer `pinA + 8` (`ht`). -/
theorem clonePostH_of {L : RuntimeLayout} {endPc : Int64} {R : Region} {F₂ : MachineData → Prop} {t : UInt64}
    {s : State} {c : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {me cA : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (hal : R.base.toNat % 16 = 0)
    (hA : At L.exe endPc R F₂ (wcNSH (_root_.Executable.labels L.exe).label c
      (tH (_root_.Executable.labels L.exe).label) (kOf (_root_.Executable.labels L.exe).label) sl me cA fr) s c)
    (hb : (R.base.toNat : Int) = (s.st.1.regs.get64 .rsp).toNat + 128) (htp : TP t s)
    (hsp : (s.st.1.regs.get64 .rsp).toNat + 224 = L.stacksA.toNat + 16384) (ht : t.toBitVec = L.pinA + 0#64 + 8#64) :
    ClonePostH L endPc t s c :=
  ⟨R, F₂, _, _, sl, me, cA, fr, hal, hA, hb, hsp, htp, ht⟩

end Spike.Lib.X64.Flow.HelloWc

/-- info: 'Spike.Lib.X64.Flow.HelloWc.at_bXH_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.at_bXH_tpXa

/-- info: 'Spike.Lib.X64.Flow.HelloWc.wcNSH_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.wcNSH_base

/-- info: 'Spike.Lib.X64.Flow.HelloWc.clonePostH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.clonePostH_of
