/-
**The runtime's start up to `scc_rt_main`'s entry, with an extra frame
`Fw`** (AArch64): `SwEW`, `StartEW`, `MainE`, `startSwitchE_segW`,
`startE_segW` and `startE_segWS` (`Spike/Lib/Rt/A64StartE.lean`) with the
frame after the switch `Fw ∧ swFSL L rS top a v` in place of
`swFSL L rS top a v` (as `Spike/Lib/Rt/A64SegsF.lean` does for the bare
shape), so that a frame fact on the memory before the switch (`Fw` reads
`m.dmem` only, say `Spike.Lib.DmemPriv.WordsNone Λ`) reaches
`scc_rt_main`'s entry after a setup block.

- `SwEWF`, `StartEWF`: the structures, `Fw` an extra parameter;
- `MainEF`: `MainE` under `Fw ∧ swFSL …`;
- `startSwitchEF_segW`: from the switch to `MainEF`, given `Fw` of the frame
  before the switch (`hFw`; the switch writes no memory) and the new frame
  `FStable` in the new region (`hFwS`);
- `startEF_segW`, `startEF_segWS`: from `_start` (`entryN`) to `MainEF`.
-/
import Spike.Lib.Rt.A64StartE

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf)

set_option linter.unusedSimpArgs false

/-- **`SwEW` with the extra frame `Fw` after the switch**: the switch, and
the block after it in the new region under `Fw ∧ swFSL …`. -/
structure SwEWF (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Ctl) (L : Int) : Prop where
  sw : NodeW W K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0)
    (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain

/-- **`MainE` under the extra frame `Fw`**: at `scc_rt_main`'s entry after
the switch, in the new region of depth `L` under `Fw ∧ swFSL …`. -/
def MainEF (exe : _root_.Executable) (endPc : Int64) (rS : Scc.Sem.Range) (Fw : _root_.Mem 64 → Prop)
    (tcb top : BitVec 64) (c0 : Ctl) (L : Int) : Frag isaLSE2 := fun s c =>
  ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK ∧
    At exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
      (mainE0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩) s c

section SwitchEF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch to `scc_rt_main`'s entry, inside `W`, with the extra
frame `Fw`** (`startSwitchE_segW`): `Fw` holds after the switch since it
holds before (`hFw`) and the switch writes no memory; the new frame
`Fw ∧ swFSL …` is `FStable` in the new region (`hFwS`). -/
theorem startSwitchEF_segW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : startTailIn prog = true) {L : Int} (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec tcb)) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m))
    (hW : SwEWF W K exe endPc R F Fw rS tcb top c0 L) :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0))
      (MainEF exe endPc rS Fw tcb top c0 L) := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (UInt64.ofBitVec tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -L) (hi := 0) (F' := fun v m => Fw m.dmem ∧ swFSL L rS top a v m)
    (n' := startN6 lab tcb top c0)
    (sw_ndW rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨hFw m hD, ⟨rfl, hun m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, hsp.trans h9,
      htp'.trans htp, (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    refine (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (-L) 0) (hFwS v) hR hv (Int.le_refl _)
      (Int.le_refl _) (code_of hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
      (n := mainE0 lab g)).mono_post fun s c h => ⟨v, hv, hR, h⟩
    · dsimp only [startN6, mainE0, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainE0, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainE0, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, hx0⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

end SwitchEF

/-! ## From `_start` to `scc_rt_main`'s entry -/

section StartEF

/-- **`StartEW` with the extra frame `Fw` after the switch.** -/
structure StartEWF (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) : Prop where
  e : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB
  s1 : Sp0W W K exe endPc R F n0 c0
  s2 : Sp2W W K exe endPc R F rS n0 k0 c0
  s3 : SwEWF W K exe endPc R (fun m => F m ∧ StackM rS m) Fw rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From `_start` to `scc_rt_main`'s entry, inside `W`, with the extra
frame `Fw` after the switch** (`startE_segW`; the switch by
`startSwitchEF_segW`). -/
theorem startEF_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hc : RtCodeIn0 prog) {L : Int}
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEWF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F Fw rS n0 k0
      c0 L) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (entryN (_root_.Executable.labels exe).label c0))
      (MainEF exe endPc rS Fw (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L) :=
  (entry_segW' hp hend hc.entry hF hR hal (by omega) hhi c0 hW.e).seq
    ((startSp2_segW hp hend hc.call hc.start hc.tcb hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb hW.s1).seq
      ((startSp2Sw_segW hp hend hc.tail hc.ti hc.tiSp hc.take hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS
        hfitS houtS hFt).seq
        (startSwitchEF_segW hp hend hc.tail _ _ c0 h16 hok (fun _ h => h.2) hsub (fun m h => hun m h.1)
          (fun m h => hFw m h.1) hFwS hW.s3)))

/-- **`startEF_segW` at the empty frames** (`SegWS.liftS`). -/
theorem startEF_segWS {W : FragS isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hc : RtCodeIn0 prog) {L : Int}
    (hK : (ms []).K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0)
      (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F exe endPc (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
    (h16 : (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEWF (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe
      endPc R F Fw rS n0 k0 c0 L) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at [])
      ((MainEF exe endPc rS Fw (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L).at []) :=
  SegWS.liftS [] (startEF_segW hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk hfld htk h16 hok hsub
    hun hFw hFwS hRS hfitS houtS hFt hW) fun _ _ h => h

end StartEF

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.startSwitchEF_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startSwitchEF_segW

/-- info: 'Spike.Lib.A64.Rt.startEF_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms startEF_segWS

end Spike.Lib.A64.Rt
