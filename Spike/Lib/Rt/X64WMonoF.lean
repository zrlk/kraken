/-
**The state obligations at a stronger frame condition** (x86-64): every
`NodeW`/`BlkW` obligation reads its frame condition `F` as a hypothesis on
the node's memory, so an obligation at `F` is one at any `F'` with
`F' → F`. Used to move the start's and `scc_rt_main`'s obligations, proved
at `swFSL`, to the extra frame `Fw ∧ swFSL` of `Spike/Lib/Rt/X64StartEF.lean`.

- `At.monoF`: a node's states at a stronger frame condition;
- `NodeW.monoF`, `BlkW.monoF`, `XExitW.monoF`, `XProW.monoF`,
  `MainSW.monoF`: the obligations at a stronger frame condition;
- `SwEW.toF`, `StartE1W.toF`, `StartEW.toF`: `SwEW`, `StartE1W`, `StartEW`
  are `SwEWF`, `StartE1WF`, `StartEWF` at any extra frame `Fw`.
-/
import Spike.Lib.Rt.X64StartEF
import Spike.Lib.Rt.X64MainS

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F' : MachineData → Prop}

/-- A node's states at a stronger frame condition are at the weaker one. -/
theorem At.monoF {n : ND} {s : State} {c : Ctl} (h : At exe endPc R F' n s c) (hF : ∀ m, F' m → F m) :
    At exe endPc R F n s c :=
  let ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  ⟨he, hn, hdc, hpc, σ, hA, hF _ hD, hJ⟩

/-- A node's obligation at a stronger frame condition. -/
theorem NodeW.monoF {n : ND} (h : NodeW W K exe endPc R F n) (hF : ∀ m, F' m → F m) :
    NodeW W K exe endPc R F' n :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => h s c ⟨he, hn, hdc, hpc, σ, hA, hF _ hD, hJ⟩

/-- A block's obligation at a stronger frame condition. -/
theorem BlkW.monoF {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hF : ∀ m, F' m → F m) : BlkW W K exe endPc R F' n blk :=
  fun s σ c he hn hdc hpc hA hD hJ => h s σ c he hn hdc hpc hA (hF _ hD) hJ

end Spike.Lib.X64

namespace Spike.Lib.X64.Flow

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F' : MachineData → Prop}

/-- The exit tail's obligations at a stronger frame condition. -/
theorem XExitW.monoF {n : ND} {sp b : Int} {k : Int64} {z0 z1 z2 : Nat}
    (h : XExitW W K exe endPc R F n sp b k z0 z1 z2) (hF : ∀ m, F' m → F m) :
    XExitW W K exe endPc R F' n sp b k z0 z1 z2 :=
  ⟨h.w0.monoF hF, h.w1.monoF hF⟩

/-- The prologue's obligations at a stronger frame condition. -/
theorem XProW.monoF {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    (h : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J) (hF : ∀ m, F' m → F m) :
    XProW W K exe endPc R F' ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨h.w0.monoF hF, h.w1.monoF hF, h.w2.monoF hF, h.w3.monoF hF, h.w4.monoF hF⟩

end Spike.Lib.X64.Flow

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F' : MachineData → Prop}

/-- `scc_rt_main`'s own obligations at a stronger frame condition. -/
theorem MainSW.monoF {ms : MemSide isa} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop}
    {Post : Ctl → BitVec 64 → Prop} {g : MainG} {x0 : BitVec 64}
    (h : MainSW W K exe endPc R F ms sc PostS Post g x0) (hF : ∀ m, F' m → F m) :
    MainSW W K exe endPc R F' ms sc PostS Post g x0 :=
  ⟨h.pro.monoF hF, h.call0.monoF hF, h.sp0.monoF hF, h.exit.monoF hF⟩

/-- `SwEW` is `SwEWF` at any extra frame. -/
theorem SwEW.toF {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    (h : SwEW W K exe endPc R F rS tcb top c0 L) (Fw : _root_.Mem 64 → Prop) :
    SwEWF W K exe endPc R F Fw rS tcb top c0 L :=
  ⟨h.sw, fun v => (h.xor v).monoF fun _ h => h.2, fun v => (h.blk v).monoF fun _ h => h.2⟩

/-- `StartE1W` is `StartE1WF` at any extra frame. -/
theorem StartE1W.toF {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int} {xr : Label}
    (h : StartE1W W K exe endPc R F rS n0 k0 c0 L xr) (Fw : _root_.Mem 64 → Prop) :
    StartE1WF W K exe endPc R F Fw rS n0 k0 c0 L xr :=
  ⟨h.s1, h.s2, h.s3.toF Fw⟩

/-- `StartEW` is `StartEWF` at any extra frame. -/
theorem StartEW.toF {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int} {xr : Label}
    (h : StartEW W K exe endPc R F rS n0 k0 c0 L xr) (Fw : _root_.Mem 64 → Prop) :
    StartEWF W K exe endPc R F Fw rS n0 k0 c0 L xr :=
  ⟨h.e, fun F' hS hK hF => (h.s F' hS hK hF).toF Fw⟩

end Spike.Lib.X64.Rt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.StartEW.toF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.StartEW.toF

/-- info: 'Spike.Lib.X64.Rt.MainSW.monoF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.MainSW.monoF
