/-
**The runtime's start up to `scc_rt_main`'s entry** (x86-64, any tail):
`startU_segWAt` (`Spike/Lib/Rt/X64SegsAt.lean`) with `_start` in front and
stopped at `scc_rt_main`'s entry, so that `scc_rt_main` itself is the
program's segment (after a setup block, `hello1.w`'s, not the bare shape
`mainU_segW` proves). The code checks are `RtCodeInTi`
(`Spike/Lib/Rt/X64RtCodeSetup.lean`) at `scc_rt_thread_init`'s return point
`xr` (`.x8` after a setup block). The x86-64 twin of
`Spike/Lib/Rt/A64StartE.lean`.

- `SwEW`, `StartE1W`, `StartEW`: the states inside `W` from the switch to
  `call scc_rt_main`; from `scc_rt_start` on (`StartAllUWAt` without
  `scc_rt_main`'s and the user function's); and from `_start` on (`_start`'s
  and, for every frame condition of `scc_rt_start`'s region, `StartE1W`).
- `MainE`: at `scc_rt_main`'s entry, in the callee's region of `call
  scc_rt_main` inside the new region of depth `L` (for some new `%rsp`
  value), the caller's cells outside it holding values, its ghosts the
  pushed return address's slot `top - 8`, the thread pointer and the source
  control `c0`, `%rdi` the thread pointer (`mainE0`).
- `startSwitchE_segW`: from the switch to `MainE` (`startSwitchU_segW`'s
  first part; the call node entered by `at_enter`).
- `entryE_segW`: `_start` to `scc_rt_start`'s entry, in its callee's region
  for some caller's state at the call (`entry_segW'`'s first part, the call
  node entered by `at_enter`).
- `startE_segW`: from `_start` (`entryN0`) to `MainE`: `entryE_segW`,
  `startX0_segW`, `startX0Sw_segWAt`, `startSwitchE_segW`.
- `startE_segWS`: the same at the empty frames (`SegWS.liftS`).

Where x86-64 differs from AArch64: `_start` calls `scc_rt_start` (its own
region the callee's, `R.callee (-8) (-296) 8`), and `entry_segW'` takes a
never-returning continuation, so `_start` is cut at the callee's entry here
(`entryE_segW`) and `scc_rt_start`'s obligations are asked for every frame
condition there (`StartEW.s`); `scc_rt_main` is entered by a `call` after
`xorl %ebp, %ebp` (`SwEW.xor`), so `MainE` is in that call's callee region;
there is no alignment premise (`h16`, `hal` past `_start`'s).
-/
import Spike.Lib.Rt.X64SegsAt
import Spike.Lib.Rt.X64RtCodeSetup
import Spike.Lib.SegS

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-- **From the switch to `call scc_rt_main`: the states inside `W`**, none
moved by `K`: the switch, and `xorl %ebp, %ebp` and the call block in the
new region of depth `L` (for every value of the new `%rsp`). -/
structure SwEW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) :
    Prop where
  sw : NodeW W K exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0)
  xor : ∀ v, NodeW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN7 (_root_.Executable.labels exe).label tcb top c0)
  blk : ∀ v, BlkW W K exe endPc (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v)
    (startN8 (_root_.Executable.labels exe).label tcb top c0) startMain

/-- **`scc_rt_main`'s entry with its argument**: `mainN0`'s ghosts and
`%rdi` the thread pointer (the start tail's `movq -24(%rbp), %rdi`, the
TCB). -/
def mainE0 (lab : Label → Int64) (g : MainG) : ND :=
  ⟨(mainN0 lab g).pc, (mainN0 lab g).o, fun σ c => (mainN0 lab g).J σ c ∧ σ.regs.rdi.toBitVec = g.tp.toBitVec⟩

/-- **At `scc_rt_main`'s entry after the switch**: in the callee's region
of `call scc_rt_main` (`8` below the new top) inside the new region of depth
`L` based at some non-wrapping `v`, under `swFSL` with the caller's cells
outside the callee's region holding values (`SwUW`'s frame condition for
`scc_rt_main`), the entry's ghosts `top - 8`, the thread pointer `tcb` and
the source control `c0`; `%rdi` the thread pointer (`mainE0`). -/
def MainE (exe : _root_.Executable) (endPc : Int64) (rS : Scc.Sem.Range) (tcb top : BitVec 64) (c0 : Ctl) (L : Int) :
    Frag isa := fun s c => ∃ v : BitVec 64, (swR v (-L) 0).OK ∧
  At exe endPc ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
    (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
    (mainE0 (_root_.Executable.labels exe).label ⟨top - 8#64, tpOf tcb, c0⟩) s c

/-- **`MainE`'s region and frame condition**: the callee's region is a
region, and no write inside it breaks the frame condition, when the limit
word lies off the new region (`hfit`, `hout`) and the stack range does not
wrap (`hfitS`). -/
theorem mainE_ok {rS : Scc.Sem.Range} {tcb top v : BitVec 64} {L : Int} (hL : 8 ≤ L) (hL8 : L % 8 = 0)
    (hv : (swR v (-L) 0).OK)
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64) :
    ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8).OK ∧
      FStable ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
        (fun m => swFSL L rS top (limA (tpOf tcb)) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m) := by
  have hlo : (swR v (-L) 0).lo ≤ -8 - 0 + (8 - L) := by show -L ≤ -8 - 0 + (8 - L); omega
  have hlo0 : 8 - L ≤ 0 := by omega
  have hkb : (-8 - 0 : Int) < (swR v (-L) 0).hi := by show (-8 : Int) - 0 < 0; decide
  have hhi : -8 - 0 + 8 ≤ (swR v (-L) 0).hi := by show (-8 : Int) - 0 + 8 ≤ 0; decide
  have hF : FStable (swR v (-L) 0) (swFSL L rS top (limA (tpOf tcb)) v) := fun m m' h hd =>
    ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
  refine ⟨Region.callee_ok hv hlo hlo0 hkb hhi, fun m m' h hd =>
    ⟨FStable.callee hv hlo hlo0 hkb hhi hF m m' h.1 hd, fun k hk hn => ?_⟩⟩
  rw [hd _ (Region.addr_fit hv hk)
    (Region.callee_sep hv hlo hlo0 hkb (by decide) (by omega) (by decide) hk hn)]
  exact h.2 k hk hn

section SwitchE

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **From the switch to `scc_rt_main`'s entry, inside `W`**: the switch
into the new region of depth `L`, `xorl %ebp, %ebp`, the call block, and the
call node entered (`at_enter`) into `scc_rt_main`'s region `8` below the new
top (`startSwitchU_segW` up to `call_nd_FWK`). The limit word is unmapped
(`hun`) and off the new region (`hfit`, `hout`); the new stack's cells hold
values (`hFS`, `hsub`). -/
theorem startSwitchE_segW {W : Frag isa} {K : State → State → Prop} {rS : Scc.Sem.Range}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startTailIn cells = true)
    {L : Int} (tcb top : BitVec 64) (c0 : Ctl) (hL : 8 ≤ L)
    (hok : (swR top (-L) 0).OK)
    (hFS : ∀ m, F m → StackM rS m) (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (hsub : ∀ k, (swR top (-L) 0).Off k → ((swR top (-L) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR top (-L) 0).addr k).toNat ∧ rS.contains (((swR top (-L) 0).addr k).toNat + 7))
    (hfit : (limA (tpOf tcb)).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf tcb)).toNat : Int) + 8 ≤ top.toNat + -L ∨ (top.toNat : Int) + 0 ≤ (limA (tpOf tcb)).toNat)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (tpOf tcb)) 8 = none)
    (hW : SwEW W K exe endPc R F rS tcb top c0 L) :
    SegW W K p lbl ms (At exe endPc R F (startN6 (_root_.Executable.labels exe).label tcb top c0))
      (MainE exe endPc rS tcb top c0 L) := by
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
  refine sw_seqW (lo := -L) (hi := 0) (F' := swFSL L rS top a) (n' := startN7 lab tcb top c0)
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
    exact ⟨hok, ⟨⟨rfl, hun m hD⟩, (hFS m hD).off⟩, sl, hsl, c, .refl c, rfl, by rw [hsp]; exact hax,
      htp'.trans htp, hdi'⟩
  · have hF2 : FStable (swR v (-L) 0) (swFSL L rS top a v) := fun m m' h hd =>
      ⟨swF_stableL hfit hout m m' h.1 hd, stackOff_stable hfitS m m' h.2 hd⟩
    refine (SegW.seq (Q := At exe endPc (swR v (-L) 0) (swFSL L rS top a v) (startN8 lab tcb top c0))
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

end SwitchE

/-! ## `_start` to `scc_rt_start`'s entry -/

section EntryE

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_start`'s frame condition at its entry** from `_start`'s call,
for the caller's state `m0`, `σC` at the call: `_start`'s `F`, its cells
outside the callee's region as in `m0`, and `m0`, `σC` the caller's
(`at_enter`'s). -/
def entryEF (R : Region) (F : MachineData → Prop) (m0 : MachineData) (σC : AS) (m : MachineData) : Prop :=
  F m ∧ CKept R (-8) (-296) 8 m0 m ∧ Abs R ⟨-8, []⟩ m0 σC

/-- **`_start` up to `scc_rt_start`'s entry, inside `W`** (`entry_segW'`
without the callee's segment): `xorl %ebp, %ebp`, `andq $-16, %rsp` (the
region's top 16-aligned, `hal`), the call block, and the call node entered
(`at_enter`) into the callee's region `R.callee (-8) (-296) 8`, for some
caller's state at the call. -/
theorem entryE_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : Code.Start.entryIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -8 + -296) (hhi : 0 ≤ R.hi)
    (c0 : Ctl) (hW : EntryW W K exe endPc R F (_root_.Executable.labels exe).label c0) :
    SegW W K p lbl ms (At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0))
      (fun s c => ∃ m0 σC, At exe endPc (R.callee (-8) (-296) 8) (entryEF R F m0 σC)
        (startN0 (_root_.Executable.labels exe).label c0) s c) := by
  let lab := (_root_.Executable.labels exe).label
  simp only [Code.Start.entryIn, Bool.and_eq_true] at hin
  obtain ⟨⟨hb0, hb1⟩, hb2⟩ := hin
  refine (seg_oneW (flag_ndW (n := entryN0 lab c0) (N := fun _ : Unit => entryN1 lab c0)
    (E := fun e : Empty => e.elim) (fi := .xor_rr32_self .rbp) (z := 2) rfl hF
    (code_field hp hend hb0 (ofNat_zero' _)) hW.xor
    fun σ c hJ fl => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩)).seq ?_
  refine sw_seqW (lo := R.lo) (hi := R.hi) (F' := fun v m => v = R.base ∧ F m) (n' := entryN2 lab c0)
    (swand_ndW (k := -16) (z := 4) (n := entryN1 lab c0) (code_field hp hend hb1 rfl) rfl rfl hW.and
      fun m σ c hA hD hJ fl => ?_) fun v _ => ?_
  · have hsp : σ.regs.get64 .rsp = R.base := by
      rw [hA.so .rsp 0 rfl]; simp [Region.addr]
    have hv : (andRegs (-16) σ.regs).get64 .rsp = R.base := by
      simp only [andRegs, Reg64s.get64_set64_self]; rw [hsp]; exact and16 hal
    rw [hv]
    exact ⟨hR, ⟨rfl, hF _ _ hD fun _ _ _ => rfl⟩, σ.slot, fun k hk => hA.slot k hk, c, .refl c, hJ⟩
  refine SegW.mono_pre (P := At exe endPc R F (entryN2 lab c0)) ?_
    fun s c ⟨he, hn, hdc, hpc, σ, hA, ⟨hvb, hD⟩, hJ⟩ => ⟨he, hn, hdc, hpc, σ, by subst hvb; exact hA, hD, hJ⟩
  refine (seg_oneW (seg_ndW (N := fun _ : Unit => entryNC lab c0) (E := fun e : Empty => e.elim)
    (by simp [Code.Start.entryCall]) entryCallB_ok hF hR (by omega) (by omega)
    (code_field hp hend hb2 (ofNat_add' _ 2 4)) hW.call
    fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_post fun s c h => ?_
  · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
  · rw [show (entryN2 lab c0).o = SO.entry from rfl, entryCallB_run]; rfl
  · exact hJ
  · obtain ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc, -, hJ⟩ :=
      at_enter (e0 := 0) (lo' := -296) (hi' := 8) (by show R.lo ≤ -8 - 0 + -296; omega)
        (by show (-8 : Int) - 0 + 8 ≤ R.hi; omega) (by show ((-8 : Int) - 0) % 8 = 0; decide) h
    exact ⟨m0, σC, he, hn, hdc, hpc, σ, hA, hD, hc.trans hJ⟩

end EntryE

/-! ## From `_start` to `scc_rt_main`'s entry -/

section StartE

/-- **`scc_rt_start`'s states inside `W` up to `scc_rt_main`'s entry**: up
to `.x0`, from `.x0` to the switch (`scc_rt_thread_init` returning to
`xr`), and from the switch to `call scc_rt_main` (with the stack range in
private memory). -/
structure StartE1W (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (xr : Label) : Prop where
  s1 : St0W W K exe endPc R F n0 c0
  s2 : X0WAt W K exe endPc R F rS n0 k0 c0 xr
  s3 : SwEW W K exe endPc R (fun m => F m ∧ StackM rS m) rS
    (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
    (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L

/-- **The start's states inside `W` up to `scc_rt_main`'s entry**:
`_start`'s, and `scc_rt_start`'s (`StartE1W`) in its region for every frame
condition there stable, kept by `K` and giving `_start`'s. -/
structure StartEW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (rS : Scc.Sem.Range) (n0 k0 : BitVec 64) (c0 : Ctl) (L : Int)
    (xr : Label) : Prop where
  e : EntryW W K exe endPc R F (_root_.Executable.labels exe).label c0
  s : ∀ F' : MachineData → Prop, FStable (R.callee (-8) (-296) 8) F' → KStable K F' → (∀ m, F' m → F m) →
    StartE1W W K exe endPc (R.callee (-8) (-296) 8) F' rS n0 k0 c0 L xr

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F : MachineData → Prop}

/-- **From `_start` to `scc_rt_main`'s entry, inside `W`, the take its
outside move**, in any valid layout of any cells with the runtime's code
but `scc_rt_main`'s, `scc_rt_thread_init`'s returning to `xr` (`hc`):
`entryE_segW`, `startX0_segW`, `startX0Sw_segWAt`, `startSwitchE_segW`, with
`startU_segWAt`'s premises but `scc_rt_main`'s and its callee's, at
`_start`'s region (`hRS`, `houtS`, `hFt`; `scc_rt_start`'s region's from
them). -/
theorem startE_segW {W : Frag isa} {rS : Scc.Sem.Range} {kp : Nat}
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
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc R F rS n0 k0 c0 L
      xr) :
    SegW W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      (At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0))
      (MainE exe endPc rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
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
      (startSwitchE_segW hp hend hc.tail _ _ c0 hL hok (fun _ h => h.2) hfitS hsub hfit hout
        (fun m h => hun m h.1.1) hs.s3))

/-- **`startE_segW` at the empty frames** (`SegWS.liftS`): the main
thread's source has no frame before `scc_rt_main`'s entry; its states
inside `W` at `[]`, under the memory side `ms []`. -/
theorem startE_segWS {W : FragS isa} {ms : List TermRun.Frame → MemSide isa} {rS : Scc.Sem.Range} {kp : Nat}
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
    (hfit : (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (hout : ((limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat : Int) + 8 ≤
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat + -L ∨
      ((stacksA (_root_.Executable.labels exe).label + k0 + 16384#64).toNat : Int) + 0 ≤
        (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))).toNat)
    (hun : ∀ m, F m →
      Mem.loadInt m.dmem (limA (tpOf (pinA (_root_.Executable.labels exe).label + n0 + 8#64))) 8 = none)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (hfitS : rS.lo + rS.size ≤ 2 ^ 64)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (takeMem pm rS m))
    (hW : StartEW (fun s c => W s c []) (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) exe endPc
      R F rS n0 k0 c0 L xr) :
    SegWS W (TakeK ((_root_.Executable.labels exe).label StackTake.siteL) rS) p lbl ms
      ((At exe endPc R F (entryN0 (_root_.Executable.labels exe).label c0)).at [])
      ((MainE exe endPc rS (pinA (_root_.Executable.labels exe).label + n0 + 8#64)
        (stacksA (_root_.Executable.labels exe).label + k0 + 16384#64) c0 L).at []) :=
  SegWS.liftS [] (startE_segW hp hend hc hL hK hF hR hal hlo hhi n0 k0 c0 hn hhdr htcb hk hfld htk hok hsub hfit
    hout hun hRS hfitS houtS hFt hW) fun _ _ h => h

end StartE

end Spike.Lib.X64.Rt
