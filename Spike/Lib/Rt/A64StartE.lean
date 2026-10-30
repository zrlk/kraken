/-
**The runtime's start up to `scc_rt_main`'s entry** (AArch64, any tail):
`startU_segW` (`Spike/Lib/Rt/A64Segs.lean`) stopped at `scc_rt_main`'s
entry, so that `scc_rt_main` itself is the program's segment (after a setup
block, `hello1.w`'s, not the bare shape `mainU_segW` proves). The code
checks are `RtCodeIn0` (`Spike/Lib/Rt/A64RtCodeSetup.lean`), which A11
gives on either tail.

- `SwEW`, `StartEW`: the states inside `W` from the switch to `bl
  scc_rt_main`, and from `_start` on (`StartAllUW` without `scc_rt_main`'s
  and the user function's).
- `MainE`: at `scc_rt_main`'s entry in the new region of depth `L` (for
  some new `sp` value), its ghosts the new stack's top, the thread pointer
  and the source control `c0`, `x0` the thread pointer (`mainE0`).
- `startSwitchE_segW`: from the switch to `MainE` (`startSwitchU_segW`'s
  first part).
- `startE_segW`: from `_start` (`entryN`) to `MainE`: `entry_segW'`,
  `startSp2_segW`, `startSp2Sw_segW`, `startSwitchE_segW`.
- `startE_segWS`: the same at the empty frames (`SegWS.liftS`).
-/
import Spike.Lib.Rt.A64Segs
import Spike.Lib.Rt.A64RtCodeSetup
import Spike.Lib.SegS

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf)

set_option linter.unusedSimpArgs false

/-- **From the switch to `bl scc_rt_main`: the states inside `W`**, none
moved by `K`: the switch, and the block after it in the new region of depth
`L` (for every value of the new `sp`). -/
structure SwEW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) :
    Prop where
  sw : NodeW W K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain

/-- **`scc_rt_main`'s entry with its argument**: `mainN0`'s ghosts and
`x0` the thread pointer (the start tail's `ldr x0, [sp, #16]`, the TCB). -/
def mainE0 (lab : Label → Int64) (g : MainG) : ND :=
  ⟨(mainN0 lab g).pc, (mainN0 lab g).o, fun σ c => (mainN0 lab g).J σ c ∧ σ.regs.X0.toBitVec = g.tp.toBitVec⟩

/-- **At `scc_rt_main`'s entry after the switch**: in the new region of
depth `L` based at some 16-aligned, non-wrapping `v`, under `swFSL`, the
entry's ghosts the new stack's top `top`, the thread pointer `tcb` and the
source control `c0`; `x0` the thread pointer (`mainE0`). -/
def MainE (exe : _root_.Executable) (endPc : Int64) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) :
    Frag isaLSE2 := fun s c => ∃ v : BitVec 64, v.toNat % 16 = 0 ∧ (swR v (-L) 0).OK ∧
  At exe endPc (swR v (-L) 0) (swFSL L rS top (limA (UInt64.ofBitVec tcb)) v)
    (mainE0 (_root_.Executable.labels exe).label ⟨top, UInt64.ofBitVec tcb, c0⟩) s c

section SwitchE

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch to `scc_rt_main`'s entry, inside `W`**: the switch
into the new region of depth `L`, then `movz x29, #0; bl scc_rt_main`
(`startSwitchU_segW` up to `mainU_segW`). The limit word is unmapped
(`hun`) and off the new region (`hfit`, `hout`); the new stack's cells hold
values (`hFS`, `hsub`). -/
theorem startSwitchE_segW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : startTailIn prog = true) {L : Int} (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec tcb)) 8 = none)
    (hW : SwEW W K exe endPc R F rS tcb top c0 L) :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0))
      (MainE exe endPc rS tcb top c0 L) := by
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
  refine sw_seqW (lo := -L) (hi := 0) (F' := swFSL L rS top a) (n' := startN6 lab tcb top c0)
    (sw_ndW rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨⟨rfl, hun m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, hsp.trans h9,
      htp'.trans htp, (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 : FStable (swR v (-L) 0) (swFSL L rS top a v) := fun m m' h hd =>
      ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    refine (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (-L) 0) hF2 hR hv (Int.le_refl _)
      (Int.le_refl _) (code_of hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
      (n := mainE0 lab g)).mono_post fun s c h => ⟨v, hv, hR, h⟩
    · dsimp only [startN6, mainE0, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainE0, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainE0, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, hx0⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

end SwitchE

/-! ## From `_start` to `scc_rt_main`'s entry -/

section StartE

/-- **The start's states inside `W` up to `scc_rt_main`'s entry**:
`_start`'s branch, up to `.sp2`, from `.sp2` to the switch, and from the
switch to `bl scc_rt_main` (with the stack range in private memory); the
thread init's take site at the extra frame `P` (`Sp2W`'s, `True` by default). -/
structure StartEW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (P : MachineData → Prop := fun _ => True) : Prop where
  e : BlkW W K exe endPc R F (entryN (_root_.Executable.labels exe).label c0) entryB
  s1 : Sp0W W K exe endPc R F n0 c0
  s2 : Sp2W W K exe endPc R F rS n0 k0 c0 P
  s3 : SwEW W K exe endPc R (fun m => F m ∧ StackM rS m) rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From `_start` to `scc_rt_main`'s entry, inside `W`, the take its
outside move**, in any valid layout of any program with the runtime's code
but `scc_rt_main`'s (`hc`): `entry_segW'`, `startSp2_segW`,
`startSp2Sw_segW`, `startSwitchE_segW`, with `startU_segW`'s premises but
`scc_rt_main`'s and its callee's. -/
theorem startE_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hc : RtCodeIn0 prog) {L : Int}
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
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0 L) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (entryN (_root_.Executable.labels exe).label c0))
      (MainE exe endPc rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L) :=
  (entry_segW' hp hend hc.entry hF hR hal (by omega) hhi c0 hW.e).seq
    ((startSp2_segW hp hend hc.call hc.start hc.tcb hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb hW.s1).seq
      ((startSp2Sw_segW hp hend hc.tail hc.ti hc.tiSp hc.take hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS
        hfitS houtS hFt).seq
        (startSwitchE_segW hp hend hc.tail _ _ c0 h16 hok (fun _ h => h.2) hfitS hsub hfit hout
          (fun m h => hun m h.1) hW.s3)))

/-- **`startE_segW` at the empty frames** (`SegWS.liftS`): the main
thread's source has no frame before `scc_rt_main`'s entry; its states
inside `W` at `[]`, under the memory side `ms []`. -/
theorem startE_segWS {W : FragS isaLSE2} {ms : List TermRun.Frame → MemSide isaLSE2} {rS : Scc.Sem.Range}
    {prog : List Directive} {kp : Nat}
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
    (hfit : (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 c0 L) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN (_root_.Executable.labels exe).label c0)).at [])
      ((MainE exe endPc rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L).at []) :=
  SegWS.liftS [] (startE_segW hp hend hc hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk hfld htk h16 hok hsub hfit
    hout hun hRS hfitS houtS hFt hW) fun _ _ h => h

end StartE

end Spike.Lib.A64.Rt
