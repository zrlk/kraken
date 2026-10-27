/-
**`scc_rt_start` from the switch on, with an extra frame `Fw`** (x86-64):
`SwUW`, `StartAllUW`, `startSwitchU_segW` and `startU_segW`
(`Spike/Lib/Rt/X64Segs.lean`) with the frame after the switch
`Fw ∧ swFSL L rS top a v` (and `(Fw ∧ swFSL …) ∧ CallerCells …` in
`scc_rt_main`'s callee region) in place of `swFSL L rS top a v`, so a frame
fact on the memory of the segments before the switch (`Fw` reads `m.dmem`
only, say `Spike.Lib.DmemPriv.WordsNone Λ`) reaches `scc_rt_main` and the
user function.

- `SwUWF`, `StartAllUWF`: the structures, `Fw` an extra parameter;
- `swUWF_true_iff`, `startAllUWF_true_iff`: at `Fw := fun _ => True` they are
  `SwUW`, `StartAllUW`;
- `startSwitchUF_segW`, `startUF_segW`: the segments, given `Fw` of the frame
  before the switch (`hFw`; the switch writes no memory) and the new frame
  `FStable` in the new region (`hFwS`);
- `startSwitchU_segW'`: the original as a corollary.
-/
import Spike.Lib.Rt.X64Segs

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

section SwitchUF

/-- **`SwUW` with the extra frame `Fw` after the switch.** -/
structure SwUWF (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop)
    (ms : MemSide isa)
    (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) (mc : MainCode) (D : Int) (ZU : Int64)
    (Post : Ctl → BitVec 64 → Prop) : Prop where
  sw : NodeW W K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW W K exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain
  main : ∀ v, MainUW W K exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
    (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) ms mc Post
    ⟨top - 8#64, tpOf tcb, c0⟩
  user : ∀ v (F' : MachineData → Prop),
    (∀ m, F' m → (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) →
    UserCallW W K p lbl ms exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8) F' mc.fn mc.Z D ZU Post
      ((_root_.Executable.labels exe).label mc.sp0).toBitVec c0 (tpOf tcb)

/-- **`SwUWF` at the trivial extra frame is `SwUW`.** -/
theorem swUWF_true_iff {W : Frag isa} {K : State → State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ms : MemSide isa}
    {rS : Scc.Sem.Range} {tcb top : BitVec 64} {c0 : Ctl} {L : Int} {mc : MainCode} {D : Int} {ZU : Int64}
    {Post : Ctl → BitVec 64 → Prop} :
    SwUWF W K p lbl exe endPc R F (fun _ => True) ms rS tcb top c0 L mc D ZU Post ↔
      SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post :=
  ⟨fun h => ⟨h.sw, fun v => nodeW_mono (h.xor v) fun _ hm => ⟨trivial, hm⟩,
      fun v => blkW_mono (h.blk v) fun _ hm => ⟨trivial, hm⟩,
      fun v => (h.main v).mono fun _ hm => ⟨⟨trivial, hm.1⟩, hm.2⟩,
      fun v F' hF' => h.user v F' fun m hm => ⟨⟨trivial, (hF' m hm).1⟩, (hF' m hm).2⟩⟩,
    fun h => ⟨h.sw, fun v => nodeW_mono (h.xor v) fun _ hm => hm.2,
      fun v => blkW_mono (h.blk v) fun _ hm => hm.2,
      fun v => (h.main v).mono fun _ hm => ⟨hm.1.2, hm.2⟩,
      fun v F' hF' => h.user v F' fun m hm => ⟨(hF' m hm).1.2, (hF' m hm).2⟩⟩⟩

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **From the switch on, inside `W`, with the extra frame `Fw`**
(`startSwitchU_segW`): `Fw` holds after the switch since it holds before
(`hFw`) and the switch writes no memory; the new frame is `FStable` in the
new region (`hFwS`). -/
theorem startSwitchUF_segW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m))
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUWF W K p lbl exe endPc R F Fw ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [startTailIn, Bool.and_eq_true] at hin
  let a := limA (tpOf tcb)
  have hmap : ∀ m, F m → ∃ sl : Int → BitVec 64, ∀ k, (swR top (-L) 0).Off k →
      ∃ j, Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k := by
    intro m hD
    refine ⟨fun k => BitVec.ofInt 64 ((Mem.loadInt m.dmem ((swR top (-L) 0).addr k) 8).getD 0), fun k hk => ?_⟩
    obtain ⟨h8, ha, ha7⟩ := hsub k hk
    have h := hFS m hD _ h8 ha ha7
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact ⟨j, hj, by simp only [hj, Option.getD_some]⟩
  refine sw_seqW (lo := -L) (hi := 0) (F' := fun v m => Fw m.dmem ∧ swFSL L rS top a v m) (n' := startN7 lab tcb top c0)
    (sw_ndW rfl (code_field hp hend hin.1.1.2 rfl) (ofNat_add' _ 28 3) rfl hW.sw fun m σ c _ hD hJ => ?_)
    fun v hv => ?_
  · obtain ⟨rfl, hax, htp, hdi⟩ := hJ
    obtain ⟨hsp, htp'⟩ := swStep (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ
    have hdi' := (congrArg UInt64.toBitVec
      (swStep_rdi (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3) σ)).trans hdi
    have hsp2 : (AI.step (startN6 lab tcb top c).o ((startN6 lab tcb top c).pc + Int64.ofNat 3)
        (.reg .W64 (.mov (.reg (.low .rsp .W64)) (.regOrMem (.reg (.low .rax .W64))))) σ).regs.get64 .rsp = top := by
      show (UInt64.toBitVec _) = _; rw [hsp]; exact hax
    rw [hsp2]
    obtain ⟨sl, hsl⟩ := hmap m hD
    exact ⟨hok, ⟨hFw m hD, ⟨rfl, hlimM.unmapped m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl,
      by rw [hsp]; exact hax,
      htp'.trans htp, hdi'⟩
  · have hF2 := hFwS v
    let g : MainG := ⟨top - 8#64, tpOf tcb, c0⟩
    refine (SegW.seq (Q := At exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a v m)
      (startN8 lab tcb top c0))
      (seg_oneW (flag_ndW (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
        (code_field hp hend hin.1.2 rfl) (hW.xor v)
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
          show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
          by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
      (SegW.seq (Q := At exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a v m) (startNM lab tcb top c0))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL (by omega)) hF2 hv (Int.le_refl _) (Int.le_refl _)
        (code_field hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩))
      (call_nd_FWK (KC := False) (N := fun e : Empty => e.elim) (E := fun e : Empty => e.elim) (e0 := 0)
        (lo' := 8 - L) (hi' := 8) (M := fun _ => True)
        (Ne := fun _ : Unit => mainN0 lab g) (Ex := fun _ (e : Empty) => e.elim)
        hv hF2 (by show -L ≤ -8 - 0 + (8 - L); omega) (by omega) (by show (-8 : Int) - 0 < 0; decide)
        (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) (by omega) (by decide)
        (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
        (fun R' F' hR' hlo' hhi' hF' _ hFF hR'e hcc _ _ _ => by
          subst hR'e
          exact mainU_segW hp hend hmain hZ hZ8 hps hk hD0 hD8 hK hF' hR' (by omega) (by omega) g
            ⟨hlimM.rt, hlimM.mp, fun _ h => (hFF _ h).2.1.2, hlimM.room⟩
            ⟨hlimU.rt, hlimU.mp, fun _ h => (hFF _ h).2.1.2, hlimU.room⟩
            (hW.user v F' fun m h => ⟨hFF m h, hcc m h⟩)
            (fun s c x hP hAt => hexit _ _ s c x hP hAt)
            ((hW.main v).mono fun m h => ⟨hFF m h, hcc m h⟩))
        (fun _ => rfl) (fun σC c hJ => ⟨(), rfl, hJ.1, hJ.2.1, hJ.2.2.1⟩) fun _ x => x.elim))).mono_post
      fun _ _ h => h.elim (fun ⟨e, _⟩ => e.elim) fun ⟨e, _⟩ => e.elim
    · dsimp only [startN7, startN8] at hJ ⊢
      obtain ⟨rfl, hsp, htp, hdi⟩ := hJ
      exact ⟨rfl, hsp, htp, hdi⟩
    · dsimp only [startN8, startNM]; rw [startMain_run]
    · dsimp only [startN8, startNM]; rw [startMain_run]; rfl
    · dsimp only [startN8, startNM] at hJ ⊢; rw [startMain_run]
      obtain ⟨rfl, hsp, htp, hdi⟩ := hJ
      refine ⟨rfl, ?_, ?_, ?_⟩
      · simp [Reg64s.set64, Reg64s.get64, hsp]
      · simp [Reg64s.set64, htp]
      · simp [Reg64s.set64, hdi]

/-- **`startSwitchU_segW` from `startSwitchUF_segW`** at `Fw := fun _ => True`. -/
theorem startSwitchU_segW' {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hk : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (tcb top : BitVec 64) (c0 : Ctl)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hlimM : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf tcb)) (top - 8#64 - 8#64 - mc.Z.toBitVec - 8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : SwUW W K p lbl exe endPc R F ms rS tcb top c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)) Q :=
  startSwitchUF_segW hp hend hin hmain hZ hZ8 hps hk hD0 hD8 hL hL8 hK tcb top c0 hok hFS hsub (fun _ _ => trivial)
    (fun _ m m' h hd => ⟨trivial, swF_stableL hfit hout m m' h.2.1 hd, stackOff_stable hfitS m m' h.2.2 hd⟩)
    hlimM hlimU hexit (swUWF_true_iff.mpr hW)

end SwitchUF

section StartUF

/-- **`StartAllUW` with the extra frame `Fw` after the switch.** -/
structure StartAllUWF (W : Frag isa) (K : State → State → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop)
    (ms : MemSide isa) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (mc : MainCode) (D : Int) (ZU : Int64) (Post : Ctl → BitVec 64 → Prop) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0W W K exe endPc R F rS n0 k0 c0
  s3 : SwUWF W K p lbl exe endPc R (fun m => F m ∧ StackM rS m) Fw ms rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L mc D ZU Post

/-- **`StartAllUWF` at the trivial extra frame is `StartAllUW`.** -/
theorem startAllUWF_true_iff {W : Frag isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {ms : MemSide isa} {rS : Scc.Sem.Range} {n0 k0 : BitVec 64} {c0 : Ctl} {L : Int}
    {mc : MainCode} {D : Int} {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} :
    StartAllUWF W K p lbl exe endPc R F (fun _ => True) ms rS n0 k0 c0 L mc D ZU Post ↔
      StartAllUW W K p lbl exe endPc R F ms rS n0 k0 c0 L mc D ZU Post :=
  ⟨fun h => ⟨h.s1, h.s2, swUWF_true_iff.mp h.s3⟩, fun h => ⟨h.s1, h.s2, swUWF_true_iff.mpr h.s3⟩⟩

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start` never returns, inside `W`, with the extra frame `Fw`
after the switch** (`startU_segW`). -/
theorem startUF_segW {W : Frag isa} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hcall : startCallIn cells = true) (hstart : startIn cells = true)
    (hat : AllocTcb.allocTcbIn cells = true) (hcall2 : startCall2In cells = true)
    (htail : startTailIn cells = true) (hti : ThreadInit.threadInitIn cells = true)
    (hst : StackTake.stackTakeIn cells = true)
    {mc : MainCode} (hmain : mainUIn cells mc = true) (hZ : 0 ≤ mc.Z.toInt) (hZ8 : mc.Z.toInt % 8 = 0)
    (hps : ∀ q ∈ mc.ps, Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hkm : Spike.Lib.offOk (-8 - mc.Z.toInt) 0 (-8 + mc.k.toInt) = true)
    {D : Int} (hD0 : 0 ≤ D) (hD8 : D % 8 = 0) {ZU : Int64} {Post : Ctl → BitVec 64 → Prop} {L : Int}
    (hL : 8 + 8 + mc.Z.toInt + 8 + D ≤ L) (hL8 : L % 8 = 0)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -296) (hhi : 8 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl) (hn : n0.toNat + 80 ≤ 131072)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
    (hok : (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).OK)
    (hsub : ∀ k, (swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).Off k →
      ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) (-L) 0).addr k).toNat + 7))
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧
      swFSL L rS (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64)
      (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) v m))
    (hlimM : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec))
    (hlimU : LimOk ms F (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64)))
      (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64 - 8#64 - 8#64 - mc.Z.toBitVec -
        8#64 - 8#64 - ZU.toBitVec))
    (hexit : ∀ R' F' s c (v : BitVec 64), Post c v →
      At exe endPc R' F' ⟨(_root_.Executable.labels exe).label mc.sp0 + Int64.ofNat mc.ze0 + Int64.ofNat mc.ze1 +
        Int64.ofNat mc.ze2, ⟨-8 - mc.Z.toInt, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartAllUWF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl exe endPc R F Fw ms
      rS
      n0 k0 c0 L mc D ZU Post)
    {Q : Frag isa} :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (startN0 (_root_.Executable.labels exe).label c0)) Q :=
  (startX0_segW hp hend hcall hstart hat hK hF hR (by omega) (by omega) n0 c0 hn hhdr htcb hW.s1).seq
    ((startX0Sw_segW hp hend hcall2 htail hti hst hK hF hR hlo hhi n0 k0 c0 hk hfld htk hW.s2 hRS hfitS houtS
      hFt).seq
      (startSwitchUF_segW hp hend htail hmain hZ hZ8 hps hkm hD0 hD8 hL hL8 hK _ _ c0 hok (fun _ h => h.2)
        hsub (fun m h => hFw m h.1) hFwS (hlimM.mono fun _ h => h.1) (hlimU.mono fun _ h => h.1) hexit hW.s3))

end StartUF

end Spike.Lib.X64.Rt
