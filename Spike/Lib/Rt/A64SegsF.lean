/-
**`scc_rt_start` from the switch on, with an extra frame `Fw`** (AArch64):
`SwUW`, `StartAllUW`, `startSwitchU_segW` and `startU_segW`
(`Spike/Lib/Rt/A64Segs.lean`) with the frame after the switch
`Fw ∧ swFSL L rS top a v` in place of `swFSL L rS top a v`, so a frame fact of
the segments before the switch on the memory (`Fw` reads `m.dmem` only, say
`Spike.Lib.DmemPriv.WordsNone Λ`) reaches
`scc_rt_main` and the user function.

- `SwUWF`, `StartAllUWF`: the structures, `Fw` an extra parameter;
- `swUWF_true_iff`, `startAllUWF_true_iff`: at `Fw := fun _ => True` they are
  `SwUW`, `StartAllUW`;
- `startSwitchUF_segW`, `startUF_segW`: the segments, given `Fw` of the frame
  before the switch (`hFw`; the switch writes no memory) and the new frame
  `FStable` in the new region (`hFwS`);
- `startSwitchU_segW'`: the original as a corollary.
-/
import Spike.Lib.Rt.A64Segs

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)

section SwitchUF

/-- **`SwUW` with the extra frame `Fw` after the switch**: the block after
the switch, `scc_rt_main`'s own states and the user function's segment in the
new region under `Fw ∧ swFSL …`. -/
structure SwUWF (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop)
    (ms : MemSide isaLSE2) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int)
    (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) : Prop where
  sw : NodeW W K exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
    (startN6 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW W K exe endPc (swR v (-L) 0)
    (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m) ms mc Post ⟨top, UInt64.ofBitVec tcb, c0⟩
  user : ∀ v, UserCallW W K p lbl ms exe endPc (swR v (-L) 0)
    (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m)
    mc.fn mc.Z D ZU Post ((_root_.Executable.labels exe).label mc.e0 + 4).toBitVec c0 (UInt64.ofBitVec tcb)

/-- The frame `True ∧ G` is `G`. -/
theorem true_and_fun (G : MachineData → Prop) :
    (fun m : MachineData => (fun _ : _root_.Mem 64 => True) m.dmem ∧ G m) = G :=
  funext fun _ => true_and _

/-- **`SwUWF` at the trivial extra frame is `SwUW`.** -/
theorem swUWF_true_iff {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int}
    {mc : MainCode} {D : Int} {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} :
    SwUWF W K p lbl exe endPc R F (fun _ => True) ms rS tcb top c0 L mc D ZU Post ↔
      SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post := by
  constructor
  · intro h
    refine ⟨h.sw, fun v => ?_, fun v => ?_, fun v => ?_⟩
    · have := h.blk v; rwa [true_and_fun] at this
    · have := h.main v; rwa [true_and_fun] at this
    · have := h.user v; rwa [true_and_fun] at this
  · intro h
    refine ⟨h.sw, fun v => ?_, fun v => ?_, fun v => ?_⟩
    · rw [true_and_fun]; exact h.blk v
    · rw [true_and_fun]; exact h.main v
    · rw [true_and_fun]; exact h.user v

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **From the switch on, inside `W`, with the extra frame `Fw`**
(`startSwitchU_segW`): `Fw` holds after the switch since it holds before
(`hFw`) and the switch writes no memory; the new frame `Fw ∧ swFSL …` is
`FStable` in the new region (`hFwS`). -/
theorem startSwitchUF_segW {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : startTailIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (UInt64.ofBitVec tcb)) v m))
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUWF W K p lbl exe endPc R F Fw ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q := by
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
  refine sw_seqW (lo := -L) (hi := 0) (F' := fun v m => Fw m.dmem ∧ swFSL L rS top a v m) (n' := startN6 lab tcb top c0)
    (sw_ndW rfl (code_of hp hend hin.1.2 rfl) (ofNat4_succ' _ 5).symm rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv hR => ?_
  · obtain ⟨rfl, h9, htp, hx0⟩ := hJ
    obtain ⟨hsp, hx, htp'⟩ := swStep (startN5 lab tcb top c).o ((startN5 lab tcb top c).pc + Int64.ofNat 4) σ
    rw [hsp, h9]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨h16, hok, ⟨hFw m hD, ⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl,
      hsp.trans h9, htp'.trans htp, (congrArg _ hx).trans hx0⟩
  · let g : MainG := ⟨top, UInt64.ofBitVec tcb, c0⟩
    have hF2 := hFwS v
    refine SegW.seq (Q := At exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a v m) (mainN0 lab g))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (-L) 0) hF2 hR hv (Int.le_refl _) (Int.le_refl _)
        (code_of hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (mainU_segW hp hend hmain hZ16 hZ hk hD0 hD8 hK hF2 hR hv (show -L ≤ -mc.Z.toInt - D by omega)
        (Int.le_refl _) g ⟨hlimM.rt, hlimM.mp, fun _ h => h.2.1.2, hlimM.room⟩
        ⟨hlimU.rt, hlimU.mp, fun _ h => h.2.1.2, hlimU.room⟩ (hW.user v)
        (fun s c x hP hAt => hexit _ _ s c x hP hAt) (hW.main v))
    · dsimp only [startN6, mainN0]; rw [startMain_run]
    · dsimp only [startN6, mainN0]; rw [startMain_run]; rfl
    · dsimp only [startN6, mainN0] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, -⟩ := hJ
      refine ⟨rfl, ?_, ?_⟩ <;> simp_all [setXReg_TPIDR, Reg64s.setXReg_SP] <;> rfl

/-- **`startSwitchU_segW` from `startSwitchUF_segW`** at `Fw := fun _ => True`. -/
theorem startSwitchU_segW' {W : Frag isaLSE2} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {prog : List Directive} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : startTailIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hk : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
    (hK : ms.K = some Scc.Sem.A64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (h16 : top.toNat % 16 = 0) (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (UInt64.ofBitVec tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (UInt64.ofBitVec tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨
      (top.toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec tcb)).toNat)
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA (UInt64.ofBitVec tcb)) (top - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (startN5 (_root_.Executable.labels exe).label tcb top c0)) Q :=
  startSwitchUF_segW hp hend hin hmain hZ16 hZ hk hD0 hD8 hL hK tcb top c0 h16 hok hFS hsub (fun _ _ => trivial)
    (fun _ m m' h hd => ⟨trivial, swF_stableL hfit hout m m' h.2.1 hd, stackOff_stable hfitS m m' h.2.2 hd⟩)
    hlimM hlimU hexit (swUWF_true_iff.mpr hW)

end SwitchUF

section StartUF

/-- **`StartAllUW` with the extra frame `Fw` after the switch.** -/
structure StartAllUWF (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (ms : MemSide isaLSE2) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) : Prop where
  s1 : Sp0W W K exe endPc R F n0 c0
  s2 : Sp2W W K exe endPc R F rS n0 k0 c0
  s3 : SwUWF W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) Fw ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post

/-- **`StartAllUWF` at the trivial extra frame is `StartAllUW`.** -/
theorem startAllUWF_true_iff {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isaLSE2} {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int}
    {mc : MainCode} {D : Int} {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} :
    StartAllUWF W K p lbl exe endPc R F (fun _ => True) ms rS n0 k0 c0 L mc D ZU Post ↔
      StartAllUW W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post :=
  ⟨fun h => ⟨h.s1, h.s2, swUWF_true_iff.mp h.s3⟩, fun h => ⟨h.s1, h.s2, swUWF_true_iff.mpr h.s3⟩⟩

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, inside `W`, with the extra frame `Fw`
after the switch** (`startU_segW`). -/
theorem startUF_segW {W : Frag isaLSE2} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hcall : startCallIn prog = true) (hstart : startIn prog = true)
    (hat : AllocTcb.allocTcbIn prog = true) (htail : startTailIn prog = true)
    (hti : ThreadInit.threadInitIn prog = true) (hsp : tiSpIn prog = true)
    (hst : StackTake.stackTakeIn prog = true)
    {mc : MainCode} (hmain : mainUIn prog mc = true) (hZ16 : mc.Z.toInt % 16 = 0) (hZ : 16 ≤ mc.Z.toInt)
    (hkm : Spike.Lib.offOk (-mc.Z.toInt) 0 (-mc.Z.toInt + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : mc.Z.toInt + D ≤ L)
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
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hlimM : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA (UInt64.ofBitVec (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - mc.Z.toBitVec - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + 4 + 4 + 4, ⟨-mc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUWF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F Fw ms
      rS n0 k0 c0 L mc D ZU Post)
    {Q : Frag isaLSE2} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (startSp2_segW hp hend hcall hstart hat hK hF hR hal (by omega) hhi n0 c0 hn hhdr htcb hW.s1).seq
    ((startSp2Sw_segW hp hend htail hti hsp hst hF hR hal hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS
      hFt).seq
      (startSwitchUF_segW hp hend htail hmain hZ16 hZ hkm hD0 hD8 hL hK _ _ c0 h16 hok (fun _ h => h.2) hsub
        (fun m h => hFw m h.1) hFwS (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit hW.s3))

end StartUF

end Spike.Lib.A64.Rt
