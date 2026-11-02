/-
**`hello.w`'s `scc_rt_main` on x86-64 up to `wc_main`** (the twin of `Spike/Lib/A64HelloMain.lean`'s live part):
the checks of `scc_rt_main`'s code in `helloCells` (`decide +kernel`), and `wc_main`'s region, frame condition and
entry invariant at `scc_rt_main`'s `call wc_main`.

hello.w's x86-64 `scc_rt_main` is hello1.w's, byte for byte (frame 64 under the saved `%rbp`, `%rdi` at
`-8(%rbp)`; `.entry`'s `call wc_rodata`; `.x2`'s copy of `wc_rodata`'s four results and the saved `%rdi` to
`%rdi`, `%rsi`, `%rdx`, `%rcx`, `%r8`, `call wc_main`), at the same labels: hello1's blocks, nodes and `mainIn`
(`X64Hello1Main`) are reused, decided again on `helloCells`.

- `hMainPro`, `hello_mainPro`, `hello_mainIn`: the checks.
- `wcR`, `wcF`, `wcJ0`, `wcR_ok`: `wc_main`'s region (`D` deep below the return address), frame condition and
  entry invariant at the call, from the caller's state `σC` at `Hello1.mWC`.

## Differences from the AArch64 version

- `call` pushes the return address, so `wc_main` is entered at `-80` of `scc_rt_main`'s region (the frame's base
  `-72`, the return address `.x3` at `-80`, `Hello1.mWC`), and its region `R.callee (-80) (-D) 8` reaches the
  return address's cell (AArch64: `R.callee (-80) (-D) 0`, `x30` holding it). There is no 16-aligned base
  (`wcR_ok` has no `hal`/`hD16`; `D % 8 = 0`).
- `MainPreW`, `MainPostW`, `hello_main_pre_segW`, `hello_main_post_segW`, `hello_main_xa_post` and
  `hello_main_hxa_of_post` are not twinned: nothing in hello's live closure reads them.
-/
import Spike.Lib.X64Hello1Main
import Spike.Lib.X64HelloRodata

namespace Spike.Lib.X64.Flow.HelloM

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Hello1 (mainIn)

/-! ## The checks -/

/-- `scc_rt_main`'s prologue: frame 64, `%rdi` (the thread pointer) at `-8(%rbp)`. -/
abbrev hMainPro : Bool := prologueIn SccCode.helloCells "scc_rt_main" ".Lscc_rt_main.chk" ".Lscc_rt_main.entry" 64 8
  ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)]

theorem hello_mainPro : hMainPro = true := by decide +kernel

/-- hello1's `scc_rt_main` blocks, at the same labels in `helloCells`. -/
theorem hello_mainIn : mainIn SccCode.helloCells = true := by decide +kernel

/-! ## `wc_main` at `scc_rt_main`'s call -/

/-- `wc_main`'s region at the call, `D` deep below the pushed return address. -/
abbrev wcR (R : Region) (D : Int) : Region := R.callee (-80) (-D) 8

/-- **`wc_main`'s frame condition at the call** from the caller's state `m0`, `σC` (`at_enter`). -/
def wcF (R : Region) (D : Int) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-80) (-D) 8 m0 m ∧ Abs R ⟨-80, []⟩ m0 σC

/-- `wc_main`'s entry invariant from the caller's state `σC` at the call node of invariant `Jc`. -/
def wcJ0 (Jc : AS → Ctl → Prop) (σC : AS) (σ : AS) (c : Ctl) : Prop := σ = enter (-80) σC ∧ Jc σC c

/-- `wc_main`'s region at the call is a region, its frame condition stable. -/
theorem wcR_ok {R : Region} {F : MachineData → Prop} {D : Int} (hD : 0 ≤ D) (hD8 : D % 8 = 0) (hR : R.OK)
    (hF : FStable R F) (hlo : R.lo ≤ -80 - D) (hhi : 0 ≤ R.hi) (m0 : MachineData) (σC : AS) :
    (wcR R D).OK ∧ FStable (wcR R D) (wcF R D F m0 σC) :=
  ⟨Region.callee_ok hR (by omega) (by omega) (by omega) (by omega),
    fstable_enter hR hF (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

end Spike.Lib.X64.Flow.HelloM

/-- info: 'Spike.Lib.X64.Flow.HelloM.hello_mainPro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.hello_mainPro

/-- info: 'Spike.Lib.X64.Flow.HelloM.hello_mainIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.hello_mainIn

/-- info: 'Spike.Lib.X64.Flow.HelloM.wcR_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.wcR_ok
