/-
**The start's node obligations combined** (x86-64; X64-OwnW lift layer): each of the start's
obligation families (`TcbW`, `TakeW`,
`TiWAt`, `EntryW`, `XStartW`, `St0W`, `X0WAt`, `SwEW`, `StartE1W`,
`StartEW`) inside `W` from one inside `W1` (moved by `K`) and one inside
`W2` (not moved), where `W1 ∧ W2` gives `W` (`AllocG.NodeW.imp` /
`AllocG.BlkW.imp` node by node). Also the start's level at `ownGXW`
(`WSX`) and the per-state lift predicate `Lft`.

- `TcbW.imp`, `TakeW.imp`, `TiWAt.imp`, `EntryW.imp`, `XStartW.imp`,
  `St0W.imp`, `X0WAt.imp`, `SwEW.imp`, `StartE1W.imp`, `StartEW.imp`.
- `WSX`: `StartWf.WS` at `ownGXW`.
- `Lft`: a state of `WS` is one of `WSX`; `lft_of_cstOk` (`W0.liftX`);
  `StartEW.liftX` etc. are `imp` at `W2 := Lft`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnCstN
import Spike.Lib.X64WakeStartWfL

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (ND BlkW NodeW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Ret0 (TN TK TI TcbW TakeW)
open Spike.Lib.X64.AllocG (BlkW.imp NodeW.imp)

section Imp

variable {W W1 W2 : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

theorem TcbW.imp {q : Spike.Lib.X64.Flow.Ret0.TcbG} {i : TN} (h1 : TcbW W1 K exe endPc R F q i)
    (h2 : TcbW W2 (fun _ _ => False) exe endPc R F q i) (hw : ∀ s c, W1 s c → W2 s c → W s c) :
    TcbW W K exe endPc R F q i := by
  cases i <;> dsimp only [TcbW] at h1 h2 ⊢
  all_goals first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw

theorem TakeW.imp {M : MachineData → Prop} {q : Spike.Lib.X64.Flow.Ret0.TakeG} {i : TK}
    (h1 : TakeW W1 K exe endPc R F M q i) (h2 : TakeW W2 (fun _ _ => False) exe endPc R F M q i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : TakeW W K exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h1 h2 ⊢
  all_goals first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact fun s c hA => hw s c (h1 s c hA) (h2 s c hA)

theorem TiWAt.imp {M : MachineData → Prop} {q : Spike.Lib.X64.Flow.Ret0.TiG} {x : Label} {i : TI}
    (h1 : Spike.Lib.X64.Rt.TiWAt W1 K exe endPc R F M q x i)
    (h2 : Spike.Lib.X64.Rt.TiWAt W2 (fun _ _ => False) exe endPc R F M q x i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.TiWAt W K exe endPc R F M q x i := by
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TiWAt] at h1 h2 ⊢
  all_goals first
    | exact BlkW.imp h1 h2 hw
    | exact NodeW.imp h1 h2 hw
    | exact fun g hg j => TakeW.imp (h1 g hg j) (h2 g hg j) hw

theorem EntryW.imp {lab : Label → Int64} {c0 : Spike.Lib.Ctl}
    (h1 : Spike.Lib.X64.Rt.EntryW W1 K exe endPc R F lab c0)
    (h2 : Spike.Lib.X64.Rt.EntryW W2 (fun _ _ => False) exe endPc R F lab c0)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.EntryW W K exe endPc R F lab c0 :=
  ⟨NodeW.imp h1.xor h2.xor hw, NodeW.imp h1.and h2.and hw, BlkW.imp h1.call h2.call hw⟩

theorem XStartW.imp {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (h1 : Spike.Lib.X64.Flow.XStartW W1 K exe endPc R F J)
    (h2 : Spike.Lib.X64.Flow.XStartW W2 (fun _ _ => False) exe endPc R F J)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Flow.XStartW W K exe endPc R F J :=
  ⟨BlkW.imp h1.w0 h2.w0 hw, NodeW.imp h1.w1 h2.w1 hw, BlkW.imp h1.w2 h2.w2 hw, NodeW.imp h1.w3 h2.w3 hw⟩

theorem St0W.imp {n0 : BitVec 64} {c0 : Spike.Lib.Ctl}
    (h1 : Spike.Lib.X64.Flow.Ret0.St0W W1 K exe endPc R F n0 c0)
    (h2 : Spike.Lib.X64.Flow.Ret0.St0W W2 (fun _ _ => False) exe endPc R F n0 c0)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Flow.Ret0.St0W W K exe endPc R F n0 c0 :=
  ⟨XStartW.imp h1.start h2.start hw, BlkW.imp h1.blk h2.blk hw,
    fun g hg i => TcbW.imp (h1.tcb g hg i) (h2.tcb g hg i) hw⟩

theorem X0WAt.imp {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {x : Label}
    (h1 : Spike.Lib.X64.Rt.X0WAt W1 K exe endPc R F rS n0 k0 c0 x)
    (h2 : Spike.Lib.X64.Rt.X0WAt W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 x)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.X0WAt W K exe endPc R F rS n0 k0 c0 x :=
  ⟨BlkW.imp h1.b0 h2.b0 hw, fun g hg i => TiWAt.imp (h1.ti g hg i) (h2.ti g hg i) hw,
    BlkW.imp h1.fs h2.fs hw, NodeW.imp h1.sys h2.sys hw, BlkW.imp h1.sw h2.sw hw⟩

theorem SwEW.imp {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int}
    (h1 : Spike.Lib.X64.Rt.SwEW W1 K exe endPc R F rS tcb top c0 L)
    (h2 : Spike.Lib.X64.Rt.SwEW W2 (fun _ _ => False) exe endPc R F rS tcb top c0 L)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.SwEW W K exe endPc R F rS tcb top c0 L :=
  ⟨NodeW.imp h1.sw h2.sw hw, fun v => NodeW.imp (h1.xor v) (h2.xor v) hw,
    fun v => BlkW.imp (h1.blk v) (h2.blk v) hw⟩

theorem StartE1W.imp {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {xr : Label}
    (h1 : Spike.Lib.X64.Rt.StartE1W W1 K exe endPc R F rS n0 k0 c0 L xr)
    (h2 : Spike.Lib.X64.Rt.StartE1W W2 (fun _ _ => False) exe endPc R F rS n0 k0 c0 L xr)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.StartE1W W K exe endPc R F rS n0 k0 c0 L xr :=
  ⟨St0W.imp h1.s1 h2.s1 hw, X0WAt.imp h1.s2 h2.s2 hw, SwEW.imp h1.s3 h2.s3 hw⟩

/-- `StartEW` from two; the second's `scc_rt_start` part at every frame
condition `F'` of its region (no stability needed: `False` moves nothing). -/
theorem StartEW.imp {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Spike.Lib.Ctl} {L : Int} {xr : Label}
    (h1 : Spike.Lib.X64.Rt.StartEW W1 K exe endPc R F rS n0 k0 c0 L xr)
    (h2e : Spike.Lib.X64.Rt.EntryW W2 (fun _ _ => False) exe endPc R F (_root_.Executable.labels exe).label c0)
    (h2s : ∀ F' : MachineData → Prop, Spike.Lib.X64.FStable (R.callee (-8) (-296) 8) F' →
      Spike.Lib.X64.KStable K F' → (∀ m, F' m → F m) →
      Spike.Lib.X64.Rt.StartE1W W2 (fun _ _ => False) exe endPc (R.callee (-8) (-296) 8) F' rS n0 k0 c0 L xr)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.StartEW W K exe endPc R F rS n0 k0 c0 L xr :=
  ⟨EntryW.imp h1.e h2e hw, fun F' hFs hKs hF' => StartE1W.imp (h1.s F' hFs hKs hF') (h2s F' hFs hKs hF') hw⟩

end Imp

/-! ## The start's level at `ownGXW` -/

open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

/-- **The start's level at `ownGXW`**: `StartWf.WS` with main's and the
worker's TCB words appended. -/
abbrev WSX (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isa := fun s c =>
  W0 L.Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) ar p Dt (Spike.Lib.X64.WriteAb.Ab L.lab) Cl
    (Spike.Lib.X64.ThreadsAb.Ac L.lab Spike.Lib.X64.WakePh.StartWf.pfxM) Ctx lbl lsize frM X0 s c []

/-- **A state of `WS` is one of `WSX`.** -/
def Lft (L : RuntimeLayout) (a : BitVec 64) (ar : Arena) (p : Prog) (Dt Cl : State → Prop)
    (Ctx : FragS isa) (lbl : Lbl) (lsize : Lsize) (frM : TermRun.Frame) (X0 : State → Prop) :
    Spike.Lib.Frag isa := fun s c =>
  Spike.Lib.X64.WakePh.StartWf.WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c → WSX L a ar p Dt Cl Ctx lbl lsize frM X0 s c

variable {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}

/-- `Lft` where `CstOk` (`W0.liftX`). -/
theorem lft_of_cstOk {s : State} {c : Spike.Lib.Ctl} (h : CstOk (Spike.Lib.X64.PhRec.μ L) L a s) :
    Lft L a ar p Dt Cl Ctx lbl lsize frM X0 s c := fun hw => hw.liftX h

/-- The combination step: `WS ∧ Lft` is `WSX`. -/
theorem wsx_of {s : State} {c : Spike.Lib.Ctl} (h1 : Spike.Lib.X64.WakePh.StartWf.WS L a ar p Dt Cl Ctx lbl lsize frM X0 s c)
    (h2 : Lft L a ar p Dt Cl Ctx lbl lsize frM X0 s c) : WSX L a ar p Dt Cl Ctx lbl lsize frM X0 s c := h2 h1

/-- `Lft` at a block from `CstOk` there. -/
theorem BlkW.lft {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => CstOk (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hD hJ k hk m hA' hD' =>
    ⟨lft_of_cstOk (h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- `Lft` at a node from `CstOk` there. -/
theorem NodeW.lft {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {n : ND} (h : NodeW (fun s _ => CstOk (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨lft_of_cstOk (h s c hA).1, fun _ h => h⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.StartEW.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartEW.imp

/-- info: 'Spike.Lib.X64.WakePh.lft_of_cstOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.lft_of_cstOk
