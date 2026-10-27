/-
**The runtime's start up to `scc_rt_main`'s entry with an extra frame `Fw`
after the switch** (x86-64): `SwEW`, `StartE1W`, `StartEW`, `MainE`,
`startSwitchE_segW`, `startE_segW` and `startE_segWS`
(`Spike/Lib/Rt/X64StartE.lean`) with the frame after the switch
`Fw ∧ swFSL L rS top a v` (and `(Fw ∧ swFSL …) ∧ CallerCells …` in
`scc_rt_main`'s callee region) in place of `swFSL L rS top a v`, so that a
frame fact on the memory of the segments before the switch (`Fw` reads
`m.dmem` only, say `Spike.Lib.DmemPriv.WordsNone Λ`) reaches `scc_rt_main`
and, through its calls, the setup block's and the user function's frame
conditions. As `Spike/Lib/Rt/X64SegsF.lean` is for the main-only start.

- `SwEWF`, `StartE1WF`, `StartEWF`: the structures, `Fw` an extra parameter;
- `MainEF`, `mainEF_ok`: `scc_rt_main`'s entry under the extra frame, and its
  callee region and frame condition (`FStable` from the new frame's, `hFwS`);
- `startSwitchEF_segW`, `startEF_segW`, `startEF_segWS`: the segments, given
  `Fw` of the frame before the switch (`hFw`; the switch writes no memory)
  and the new frame `FStable` in the new region (`hFwS`, at `WordsNone` by
  `wordsNone_swFSL_fstable`).
-/
import Spike.Lib.Rt.X64StartE

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- **`SwEW` with the extra frame `Fw` after the switch.** -/
structure SwEWF (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (tcb top : BitVec 64)
    (c0 : Ctl) (L : Int) : Prop where
  sw : NodeW W K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW W K exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain

/-- **`MainE` with the extra frame `Fw`**: at `scc_rt_main`'s entry after
the switch, in the callee's region of `call scc_rt_main`, under
`(Fw ∧ swFSL) ∧ CallerCells`. -/
def MainEF (exe : _root_.Executable) (endPc : Int64) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range)
    (tcb top : BitVec 64) (c0 : Ctl) (L : Int) : Frag isa := fun s c => ∃ v : BitVec 64, (swR v (-L) 0).OK ∧
  At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
    (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
      CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
    (mainE0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩) s c

/-- **`MainEF`'s region and frame condition** (`mainE_ok`): the callee's
region is a region, and no write inside it breaks the frame condition, when
the new frame is `FStable` in the new region (`hFwS`). -/
theorem mainEF_ok {Fw : _root_.Mem 64 → Prop} {rS : Scc.Sem.Range} {tcb top v : BitVec 64} {L : Int}
    (hL : 8 ≤ L) (hL8 : L % 8 = 0) (hv : (swR v (-L) 0).OK)
    (hFwS : FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m)) :
    ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8).OK ∧
      FStable ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => (Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m) ∧
          CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) := by
  have hlo : (swR v (-L) 0).lo ≤ -8 - 0 + (8 - L) := by show -L ≤ -8 - 0 + (8 - L); omega
  have hlo0 : 8 - L ≤ 0 := by omega
  have hkb : (-8 - 0 : Int) < (swR v (-L) 0).hi := by show (-8 : Int) - 0 < 0; decide
  have hhi : -8 - 0 + 8 ≤ (swR v (-L) 0).hi := by show (-8 : Int) - 0 + 8 ≤ 0; decide
  refine ⟨Region.callee_ok hv hlo hlo0 hkb hhi, fun m m' h hd =>
    ⟨FStable.callee hv hlo hlo0 hkb hhi hFwS m m' h.1 hd, fun k hk hn => ?_⟩⟩
  rw [hd _ (Region.addr_fit hv hk)
    (Region.callee_sep hv hlo hlo0 hkb (by decide) (by omega) (by decide) hk hn)]
  exact h.2 k hk hn

section SwitchEF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`startSwitchE_segW` with the extra frame `Fw` after the switch**:
`Fw` of the frame before it (`hFw`), the new frame `FStable` in the new
region (`hFwS`, in place of `hfit`, `hout`, `hfitS`). -/
theorem startSwitchEF_segW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {L : Int} (tcb top : BitVec 64) (c0 : Ctl) (hL : 8 ≤ L)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none)
    (hFw : ∀ m, F m → Fw m.dmem)
    (hFwS : ∀ v, FStable (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top (limA (tpOf tcb)) v m))
    (hW : SwEWF W K exe endPc R F Fw rS tcb top c0 L) :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0))
      (MainEF exe endPc Fw rS tcb top c0 L) := by
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
  refine sw_seqW (lo := -L) (hi := 0) (F' := fun v m => Fw m.dmem ∧ swFSL L rS top a v m)
    (n' := startN7 lab tcb top c0)
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
    exact ⟨hok, ⟨hFw m hD, ⟨rfl, hun m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, by rw [hsp]; exact hax,
      htp'.trans htp, hdi'⟩
  · have hF2 := hFwS v
    refine (SegW.seq (Q := At exe endPc (swR v (-L) 0) (fun m => Fw m.dmem ∧ swFSL L rS top a v m)
      (startN8 lab tcb top c0))
      (seg_oneW (flag_ndW (n := startN7 lab tcb top c0) (fi := .xor_rr32_self .rbp) rfl hF2
        (code_field hp hend hin.1.2 rfl) (hW.xor v)
        fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(),
          show lab x1L + Int64.ofNat 33 = lab x1L + Int64.ofNat 31 + Int64.ofNat 2 from ofNat_add' _ 31 2,
          by show SO.le SO.entry ((FI.xor_rr32_self .rbp).so SO.entry) = true; decide, ?_⟩⟩))
      (seg_oneW (seg_ndW (by simp [startMain]) (startMain_okL hL) hF2 hv (Int.le_refl _) (Int.le_refl _)
        (code_field hp hend hin.2 rfl) (hW.blk v) fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
        (n := startNM lab tcb top c0))).mono_post fun s c h => ?_
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
    · obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, ⟨hD, hK, hAC⟩, hc, hσ, hJ⟩ :=
        at_enter (e0 := 0) (lo' := 8 - L) (hi' := 8) (by show -L ≤ -8 - 0 + (8 - L); omega)
          (by show (-8 : Int) - 0 + 8 ≤ 0; decide) (by show ((-8 : Int) - 0) % 8 = 0; decide) h
      refine ⟨v, hv, he, hn, hdc, hpc, σ, hA, ⟨hD, fun k hk hn' => ?_⟩, ?_⟩
      · obtain ⟨j, hj, -⟩ := hAC.slot k hk
        rw [hK k hk hn', hj]; rfl
      · subst hσ; obtain ⟨hc', hsp, htp, hdi⟩ := hJ
        exact ⟨⟨hc', hsp, htp⟩, hdi.trans (by simp [tpOf])⟩

end SwitchEF

/-! ## From `_start` to `scc_rt_main`'s entry -/

section StartEF

/-- **`StartE1W` with the extra frame `Fw` after the switch.** -/
structure StartE1WF (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (xr : Label) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0WAt W K exe endPc R F rS n0 k0 c0 xr
  s3 : SwEWF W K exe endPc R (fun m => F m ∧ StackM rS m) Fw rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L

/-- **`StartEW` with the extra frame `Fw` after the switch.** -/
structure StartEWF (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (Fw : _root_.Mem 64 → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64)
    (c0 : Ctl) (L : Int) (xr : Label) : Prop where
  e : EntryW W K exe endPc R F (_root_.Executable.labels exe).label c0
  s : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' → KStable K F' → (∀ m, F' m → F m) →
    StartE1WF W K exe endPc (R.callee (-8) (-296) 8) F' Fw rS n0 k0 c0 L xr

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`startE_segW` with the extra frame `Fw` after the switch**: `Fw` of
`_start`'s frame (`hFw`), the new frame `FStable` in the new region
(`hFwS`, in place of `hfit`, `hout`). -/
theorem startEF_segW {W : Frag isa} {rS : Scc.Sem.Range} {Fw : _root_.Mem 64 → Prop} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {xr : Label} (hc : RtCodeInTi cells xr) {L : Int}
    (hL : 8 ≤ L) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk ms F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk ms F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk ms F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk ms F exe endPc k0)
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
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEWF W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F Fw rS n0 k0
      c0 L xr) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0))
      (MainEF exe endPc Fw rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L) := by
  have hlo1 : R.lo ≤ -8 + -296 := by omega
  have hhi1 : -8 + 8 ≤ R.hi := by omega
  have hkb : (-8 : Int) < R.hi := by omega
  refine (entryE_segW hp hend hc.start0 hF hR hal hlo1 hhi c0 hW.e).seq
    (SegW.exists_pre fun m0 => SegW.exists_pre fun σC => ?_)
  have hR' : (R.callee (-8) (-296) 8).OK := Region.callee_ok hR hlo1 (by decide) hkb hhi1
  have hF' : FStable (R.callee (-8) (-296) 8) (entryEF R F m0 σC) :=
    fstable_enter hR hF hlo1 (by decide) hkb hhi1 (by decide) (by decide) (by decide)
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
  exact (startX0_segW hp hend hc.call hc.start hc.tcb hK hF' hR' (by show (-296 : Int) ≤ -232; decide)
    (by show (0 : Int) ≤ 8; decide) n0 c0 hn (hhdr.mono fun _ h => h.1) (htcb.mono fun _ h => h.1) hs.s1).seq
    ((startX0Sw_segWAt hp hend hc.call2 hc.tail hc.ti hc.take hK hF' hR' (by show (-296 : Int) ≤ -296; decide)
      (by show (8 : Int) ≤ 8; decide) n0 k0 c0 hk (fun e he => (hfld e he).mono fun _ h => h.1)
      (htk.mono fun _ h => h.1) hs.s2 hRS' hfitS houtS' hFt').seq
      (startSwitchEF_segW hp hend hc.tail _ _ c0 hL hok (fun _ h => h.2) hsub
        (fun m h => hun m h.1.1) (fun m h => hFw m h.1.1) hFwS hs.s3))

/-- **`startEF_segW` at the empty frames** (`SegWS.liftS`, `startE_segWS`). -/
theorem startEF_segWS {W : FragS isa} {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range}
    {Fw : _root_.Mem 64 → Prop} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {xr : Label} (hc : RtCodeInTi cells xr) {L : Int}
    (hL : 8 ≤ L) (hK : (ms []).K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (n0 k0 : BitVec 64) (c0 : Ctl)
    (hn : n0.toNat + 80 ≤ 131072)
    (hhdr : StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0) (AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcb : TcbOk (ms []) F exe endPc n0)
    (hk : k0.toNat + 16384 ≤ 536870912)
    (hfld : ∀ e ∈ ThreadInit.fields (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0),
      StOk (ms []) F (pinA (_root_.Executable.labels exe).label + n0 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : TakeOk (ms []) F exe endPc k0)
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
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEWF (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe
      endPc R F Fw rS n0 k0 c0 L xr) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at [])
      ((MainEF exe endPc Fw rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L).at []) :=
  SegWS.liftS [] (startEF_segW hp hend hc hL hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk hfld htk hok hsub
    hun hFw hFwS hRS hfitS houtS hFt hW) fun _ _ h => h

end StartEF

end Spike.Lib.X64.Rt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.startEF_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.startEF_segWS
