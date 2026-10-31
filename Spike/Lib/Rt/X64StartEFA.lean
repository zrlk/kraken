/-
**The runtime's start up to `scc_rt_main`'s entry with the callees' own
words owned at their nodes' states and an extra frame `P` up to the take
site** (x86-64): `startEF_segW` (`Spike/Lib/Rt/X64StartEF.lean`) with
`TcbOkA`/`TakeOkA` for `TcbOk`/`TakeOk` and `P`. This is the x86-64 twin of
AArch64's `startEF_segWA` (`Spike/Lib/Rt/A64StartEF.lean`,
`Spike/Lib/Rt/A64StartEFP.lean`).

The frame `P` (`FStable R P`) is a fact of `_start`'s memory that holds up to
the take site of `scc_rt_stack_take`, where `TakeWP` asks the site's
obligation under it. The root uses `P := ¬ StackM rS0` to give `X0W`'s
`¬ StackM r0` at the site. `P` cannot be part of `F`, because the take must
keep `F` (`hFt`) and it breaks `P`.

- `XStartW.monoF`, `EntryW.monoF`, `St0W.monoF`: the obligations under a
  stronger frame condition;
- `StartE1WFP`, `StartEWFP`: `StartE1WF`, `StartEWF` with
  `scc_rt_thread_init`'s obligations `X0WAtP … P` (`.of_startEWF` at any
  `P`);
- `startEF_segWA`: the segment, from `_start` under `F ∧ P`.

**Unlike AArch64**: `_start` calls `scc_rt_start` (the callee's frame
condition `entryEF`, for every caller's state), so `P` is carried into the
callee's region (`FStable.callee`) beside `entryEF`. The counter's and the
take's ownership (`htcb`, `htk`) are asked in `scc_rt_alloc_tcb`'s and
`scc_rt_stack_take`'s regions below that callee's region.
-/
import Spike.Lib.Rt.X64StartEF
import Spike.Lib.Rt.X64SegsA

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The obligations under a stronger frame condition -/

section MonoF

variable {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F F' : MachineData → Prop}

/-- `XStartW` under a stronger frame condition. -/
theorem XStartW.monoF {J : AS → Ctl → Prop} (h : XStartW W K exe endPc R F J) (hFF : ∀ m, F' m → F m) :
    XStartW W K exe endPc R F' J :=
  ⟨blkW_mono h.w0 hFF, nodeW_mono h.w1 hFF, blkW_mono h.w2 hFF, nodeW_mono h.w3 hFF⟩

/-- `EntryW` under a stronger frame condition. -/
theorem EntryW.monoF {lab : Label → Int64} {c0 : Ctl} (h : EntryW W K exe endPc R F lab c0)
    (hFF : ∀ m, F' m → F m) : EntryW W K exe endPc R F' lab c0 :=
  ⟨nodeW_mono h.xor hFF, nodeW_mono h.and hFF, blkW_mono h.call hFF⟩

/-- `St0W` under a stronger frame condition. -/
theorem St0W.monoF {n0 : BitVec 64} {c0 : Ctl} (h : St0W W K exe endPc R F n0 c0) (hFF : ∀ m, F' m → F m) :
    St0W W K exe endPc R F' n0 c0 :=
  ⟨XStartW.monoF h.start hFF, blkW_mono h.blk hFF, fun g hg i => (h.tcb g hg i).mono hFF⟩

/-- `TcbOkA` under a stronger frame condition, both the facts' and the
nodes'. -/
theorem TcbOkA.mono2 {ms : MemSide isa} {q : TcbG} (h : TcbOkA ms F exe endPc R F q) (hFF : ∀ m, F' m → F m) :
    TcbOkA ms F' exe endPc R F' q :=
  ⟨h.next.mono hFF, (h.mono hFF).own⟩

/-- `TakeOkA` under a stronger frame condition, both the facts' and the
nodes'. -/
theorem TakeOkA.mono2 {ms : MemSide isa} {q : TakeG} (h : TakeOkA ms F exe endPc R F q)
    (hFF : ∀ m, F' m → F m) : TakeOkA ms F' exe endPc R F' q :=
  ⟨h.lock1.mono hFF, h.freeN.mono hFF, h.lock0.mono hFF, h.next.mono hFF, (h.mono hFF).ownLock,
    (h.mono hFF).ownFreeN, (h.mono hFF).ownNext⟩

end MonoF

/-! ## From `_start` to `scc_rt_main`'s entry, with `P` to the take site -/

section StartEFA

/-- **`StartE1WF` with the take site's frame condition also `P`**
(`X0WAtP`). -/
structure StartE1WFP (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (xr : Label) (P : MachineData → Prop) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0WAtP W K exe endPc R F rS n0 k0 c0 xr P
  s3 : SwEWF W K exe endPc R (fun m => F m ∧ StackM rS m) Fw rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L

/-- **`StartEWF` with the take site's frame condition also `P`**
(AArch64's `StartEWF … P`). -/
structure StartEWFP (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (xr : Label) (P : MachineData → Prop) : Prop where
  e : EntryW W K exe endPc R F (_root_.Executable.labels exe).label c0
  s : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' → KStable K F' → (∀ m, F' m → F m) →
    StartE1WFP W K exe endPc (R.callee (-8) (-296) 8) F' Fw rS n0 k0 c0 L xr P

/-- `StartEWF` gives `StartEWFP` at any `P`. -/
theorem StartEWFP.of_startEWF {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {Fw : _root_.Mem 64 → Prop} {rS : Scc.Sem.Range}
    {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int} {xr : Label} {P : MachineData → Prop}
    (h : StartEWF W K exe endPc R F Fw rS n0 k0 c0 L xr) : StartEWFP W K exe endPc R F Fw rS n0 k0 c0 L xr P :=
  ⟨h.e, fun F' hF hK hFF => ⟨(h.s F' hF hK hFF).s1, .of_x0WAt (h.s F' hF hK hFF).s2, (h.s F' hF hK hFF).s3⟩⟩

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **From `_start` to `scc_rt_main`'s entry, inside `W`, with the extra
frame `Fw` after the switch, the callees' own words owned at their nodes'
states (`htcb`, `htk`), and the extra frame `P` (`FStable R P`) from
`_start` to the take site** (`startEF_segW` by `startX0_segWA` and
`startX0Sw_segWAtA`; AArch64's `startEF_segWA`). -/
theorem startEF_segWA {W : Frag isa} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {xr : Label} (hc : RtCodeInTi cells xr) {L : Int}
    (hL : 8 ≤ L) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : ∀ g, TcbOkA ms F exe endPc ((R.callee (-8) (-296) 8).callee (-48 - 0) (-184) 8) F ⟨g, n0, c0⟩)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, TakeOkA ms F exe endPc
      (((R.callee (-8) (-296) 8).callee (-48 - 0) (-248) 8).callee (-48 - 0) (-200) 8) F ⟨g, k0, c0⟩)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧
      swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m)) {P : MachineData → Prop} (hP : FStable R P)
    (hW : StartEWFP W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F Fw rS n0 k0
      c0 L xr P) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R (fun m => F m ∧ P m) (entryN0 (_root_.Executable.labels exe).label c0))
      (MainEF exe endPc Fw rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L) := by
  have hlo1 : R.lo ≤ -8 + -296 := by omega
  have hhi1 : -8 + 8 ≤ R.hi := by omega
  have hkb : (-8 : Int) < R.hi := by omega
  have hFP : FStable R (fun m => F m ∧ P m) := fun m m' h hd => ⟨hF m m' h.1 hd, hP m m' h.2 hd⟩
  refine (entryE_segW hp hend hc.start0 hFP hR hal hlo1 hhi c0 (EntryW.monoF hW.e fun _ h => h.1)).seq
    (SegW.exists_pre fun m0 => SegW.exists_pre fun σC => ?_)
  have hR' : (R.callee (-8) (-296) 8).OK := Region.callee_ok hR hlo1 (by decide) hkb hhi1
  have hF' : FStable (R.callee (-8) (-296) 8) (entryEF R F m0 σC) :=
    fstable_enter hR hF hlo1 (by decide) hkb hhi1 (by decide) (by decide) (by decide)
  have hP' : FStable (R.callee (-8) (-296) 8) P := FStable.callee hR hlo1 (by decide) hkb hhi1 hP
  have hFP' : FStable (R.callee (-8) (-296) 8) (fun m => entryEF R F m0 σC m ∧ P m) := fun m m' h hd =>
    ⟨hF' m m' h.1 hd, hP' m m' h.2 hd⟩
  have hFt' : ∀ m pm, entryEF R F m0 σC m → entryEF R F m0 σC (takeMem pm rS m) := fun m pm h =>
    ⟨hFt m pm h.1, fun k hk hn => (loadInt_takeMem (hRS k hk)).trans (h.2.1 k hk hn), h.2.2⟩
  have hRS' : ∀ k, (R.callee (-8) (-296) 8).Off k → ∀ i < 8,
      (R.callee (-8) (-296) 8).addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS := fun k hk i hi => by
    rw [Region.callee_addr]
    exact hRS _ (Region.callee_off hlo1 hhi1 (by decide) hk) i hi
  have houtS' : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ (R.callee (-8) (-296) 8).base.toNat + (R.callee (-8) (-296) 8).lo ∨
        ((R.callee (-8) (-296) 8).base.toNat : Int) + (R.callee (-8) (-296) 8).hi ≤ a := by
    intro a h8 ha ha7
    have hb := Region.callee_base (hi' := 8) hR hlo1 (by decide) hkb
    have h := houtS a h8 ha ha7
    rw [hb]
    show (a : Int) + 8 ≤ R.base.toNat + -8 + -296 ∨ (R.base.toNat : Int) + -8 + 8 ≤ a
    omega
  have hs := hW.s _ hF' (TakeK.kstable hFt') fun _ h => h.1
  refine SegW.mono_pre (P := At exe endPc (R.callee (-8) (-296) 8) (fun m => entryEF R F m0 σC m ∧ P m)
    (startN0 (_root_.Executable.labels exe).label c0)) ?_
    fun s c ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hPm⟩, hKp, hAb⟩, hJ⟩ =>
      ⟨he, hn, hdc, hpc, σ, hA, ⟨⟨hD, hKp, hAb⟩, hPm⟩, hJ⟩
  exact (startX0_segWA hp hend hc.call hc.start hc.tcb hK hFP' hR' (by show (-296 : Int) ≤ -232; decide)
    (by show (0 : Int) ≤ 8; decide) n0 c0 hn (hhdr.mono fun _ h => h.1.1) (fun g => (htcb g).mono2 fun _ h => h.1.1)
    (St0W.monoF hs.s1 fun _ h => h.1)).seq
    ((startX0Sw_segWAtA hp hend hc.call2 hc.tail hc.ti hc.take hK hF' hR' (by show (-296 : Int) ≤ -296; decide)
      (by show (8 : Int) ≤ 8; decide) n0 k0 c0 hk (fun e he => (hfld e he).mono fun _ h => h.1)
      (fun g => (htk g).mono2 fun _ h => h.1) hP' hs.s2 hRS' hfitS houtS' hFt').seq
      (startSwitchEF_segW hp hend hc.tail _ _ c0 hL hok (fun _ h => h.2) hsub
        (fun m h => hun m h.1.1) (fun m h => hFw m h.1.1) hFwS hs.s3))

end StartEFA

end Spike.Lib.X64.Rt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.XStartW.monoF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.XStartW.monoF

/-- info: 'Spike.Lib.X64.Rt.EntryW.monoF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.EntryW.monoF

/-- info: 'Spike.Lib.X64.Rt.St0W.monoF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.St0W.monoF

/-- info: 'Spike.Lib.X64.Rt.TcbOkA.mono2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TcbOkA.mono2

/-- info: 'Spike.Lib.X64.Rt.TakeOkA.mono2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.TakeOkA.mono2

/-- info: 'Spike.Lib.X64.Rt.StartEWFP.of_startEWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.StartEWFP.of_startEWF

/-- info: 'Spike.Lib.X64.Rt.startEF_segWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.startEF_segWA
