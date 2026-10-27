/-
**The AArch64 main thread `scc_rt_main` after a setup block, parametric in
the program** (`mainS_segW`): `mainU_segW` (`Spike/Lib/Rt/A64Main.lean`)
with two calls, for the `.setup` tail (`SetupCode`,
`Spike/Lib/Rt/A64CodeInSetup.lean`).

- **The code** (`mainSIn`): the stack-checked prologue saving `x0` (the
  TCB) at the frame's base, `bl setup` at `e0`, at `sp0` the marshalling
  block (`marshal`: the `sw` setup words to the frame and back, the TCB to
  `x(sw)`, `bl fn`), and the `exit_group` tail at `sp1`; `mainSIn_of_okS`
  reads it off A11's `rtCodeOkS`.
- **The marshalling block** in closed form (`marshal_run`, `marshal_regs`):
  the words `x0`…`x(sw-1)` as the setup block returned them, `x(sw)` the
  frame's base cell, `sp` and the thread pointer kept, `x30` the return
  point `sp1`.
- **Both callees are interfaces**: the setup block (`SetupCallW`, from the
  user function's entry `uN0` to `uNxS`, which also restores `sp` and the
  thread pointer, its post `PostS` a relation of the source control and the
  whole returned state), and the user function (`MainCallW`, from `uNM`: its
  arguments those of some state `PostS` relates, `x(sw)` the TCB `x0`, to
  `uNx` with `Post`). The TCB cell at the frame's base survives the setup
  call, being outside its region.
-/
import Spike.Lib.Rt.A64CodeInSetup
import Spike.Lib.Rt.A64Main

namespace Spike.Lib.A64.Flow

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64

theorem arun_cat (lab : Label → Int64) (a b : List Directive) (am : AM) :
    arun lab (a ++ b) am = arun lab b (arun lab a am) := by
  simp [arun, List.foldl_append]

/-- Stores into cells inside the region, then a covered block, are
covered. -/
theorem okBlk_spStrs_app {lo hi : Int} {o : SO} (h16 : o.sp % 16 = 0) {ps : List (XReg × Int64)}
    (hps : ∀ p ∈ ps, Spike.Lib.offOk lo hi (o.sp + p.2.toInt) = true) {ds : List Directive}
    (hds : okBlk lo hi o ds = true) :
    okBlk lo hi o (ps.map (fun p => spStr p.1 p.2) ++ ds) = true := by
  induction ps with
  | nil => simpa using hds
  | cons p ps ih =>
    have hc : classify (spStr p.1 p.2) = some (AI.str (.low (.reg p.1) .W64) p.2) := rfl
    simp only [List.map_cons, List.cons_append, okBlk, hc, AI.ok, AI.so, AI.isTerm, Bool.not_false, Bool.or_true,
      Bool.and_true]
    rw [hps p List.mem_cons_self, ih fun q hq => hps q (List.mem_cons_of_mem _ hq)]
    simp [h16]

end Spike.Lib.A64.Flow

namespace Spike.Lib.A64.Rt

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (MainG mainN0 WcG LimOk limA tcbA_limA setXReg_TPIDR seg_oneW CallerCells)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap RGrp rtIn rtIn_sound RtAll RtAll.append BsOk
  GapAt)

set_option linter.unusedSimpArgs false

/-! ## The program's facts -/

/-- **`scc_rt_main`'s code after a setup block in `prog`**: the
stack-checked prologue (frame `Z`, the limit at `[tpidr_el0, #8]`, `x0`
saved at the frame's base), `bl setup` at `e0` returning to `sp0`, the
marshalling block and `bl fn` at `sp0` returning to `sp1`, and the
`exit_group` tail there with the value spilled at `k`. -/
def mainSIn (prog : List Directive) (sc : SetupCode) : Bool :=
  prologueIn prog "scc_rt_main" sc.sc sc.e0 sc.Z 8 sc.grow [(.X0, 0)] &&
    blockAt prog sc.e0 0 [blD sc.setup] && labelGap prog sc.e0 sc.sp0 1 &&
    blockAt prog sc.sp0 0 (marshal sc.sw sc.fn) && labelGap prog sc.sp0 sc.sp1 (2 * sc.sw + 2) &&
    exitIn prog sc.sp1 sc.k

/-- `scc_rt_main`'s check from its groups. -/
theorem mainSIn_of {prog : List Directive} {sc : SetupCode} (h : RtAll prog (mainSGrps sc)) :
    mainSIn prog sc = true := by
  simp only [mainSGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [mainSIn, prologueIn, exitIn, List.length_cons, List.length_nil, h, Bool.and_self]

/-- `scc_rt_main`'s check from A11's runtime code check after a setup
block. -/
theorem mainSIn_of_okS {prog : List Directive} {sc : SetupCode} (h : rtCodeOkS prog sc = true) :
    mainSIn prog sc = true := by
  have h' : RtAll prog (rtCodeTabS sc) := rtIn_sound h
  unfold rtCodeTabS at h'
  exact mainSIn_of (RtAll.append (RtAll.append (RtAll.append (RtAll.append h').1).1).1).2

/-! ## The marshalling block -/

/-- The argument registers are distinct. -/
theorem argX_nodup : ∀ n < 8, ((List.range (n + 1)).map argX).Nodup := by decide

/-- No argument register is the link register. -/
theorem argX_ne_X30 : ∀ i < 8, argX i ≠ .X30 := by decide

/-- The marshalling block's stores: `x(i)` to `8 (i + 1)`. -/
def mshSt (sw : Nat) : List (XReg × Int64) := (List.range sw).map fun i => (argX i, Int64.ofNat (8 * (i + 1)))

/-- The marshalling block's loads: `x(i)` from `8 (i + 1)`, then `x(sw)` from
the frame's base. -/
def mshLd (sw : Nat) : List (XReg × RW) :=
  (List.range sw).map (fun i => (argX i, RW.slot (Int64.ofNat (8 * (i + 1))))) ++ [(argX sw, .slot 0)]

theorem marshal_eq (sw : Nat) (fn : Label) :
    marshal sw fn = (mshSt sw).map (fun p => spStr p.1 p.2) ++ wordDirs (mshLd sw) ++ [blD fn] := by
  simp [marshal, mshSt, mshLd, wordDirs, spLdr, List.map_map, Function.comp_def]

theorem mshLd_fst (sw : Nat) : (mshLd sw).map Prod.fst = (List.range (sw + 1)).map argX := by
  simp [mshLd, List.range_succ, Function.comp_def]

/-- The cells the stores do not write are kept. -/
theorem stSlots_of_not_mem (sp : Int) (regs : Reg64s) (ps : List (XReg × Int64)) (sl : Int → BitVec 64) {k : Int}
    (h : ∀ p ∈ ps, k ≠ sp + p.2.toInt) : stSlots sp regs ps sl k = sl k := by
  induction ps generalizing sl with
  | nil => rfl
  | cons p ps ih =>
    simp only [stSlots]
    rw [ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [Spike.Lib.upd_apply, h p List.mem_cons_self]

/-- A cell a store writes, the stores' cells distinct, holds its register. -/
theorem stSlots_get (sp : Int) (regs : Reg64s) (ps : List (XReg × Int64)) (sl : Int → BitVec 64)
    (hnd : (ps.map fun p => sp + p.2.toInt).Nodup) {r : XReg} {o : Int64} (h : (r, o) ∈ ps) :
    stSlots sp regs ps sl (sp + o.toInt) = (regs.getXReg r).toBitVec := by
  induction ps generalizing sl with
  | nil => cases h
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [stSlots]
    rcases List.mem_cons.1 h with e | h
    · subst e
      rw [stSlots_of_not_mem _ _ _ _ fun q hq he => hnd.1 ⟨q, hq, he.symm⟩]
      simp [Spike.Lib.upd_apply]
    · exact ih _ hnd.2 h

theorem setWords_SP (sp : Int) (sl : Int → BitVec 64) (ps : List (XReg × RW)) (regs : Reg64s) :
    (setWords sp sl ps regs).SP = regs.SP := by
  induction ps generalizing regs with
  | nil => rfl
  | cons p ps ih => obtain ⟨r, w⟩ := p; simp only [setWords, ih, Reg64s.SP_setXReg]

theorem setWords_TPIDR (sp : Int) (sl : Int → BitVec 64) (ps : List (XReg × RW)) (regs : Reg64s) :
    (setWords sp sl ps regs).TPIDR_EL0 = regs.TPIDR_EL0 := by
  induction ps generalizing regs with
  | nil => rfl
  | cons p ps ih => obtain ⟨r, w⟩ := p; simp only [setWords, ih, setXReg_TPIDR]

theorem pc_marshal (pc : Int64) (sw : Nat) :
    pc + Int64.ofNat (4 * sw) + Int64.ofNat (4 * (sw + 1)) + 4 = pc + Int64.ofNat (4 * (2 * sw + 2)) := by
  rw [show 4 * (2 * sw + 2) = 4 * sw + 4 * (sw + 1) + 4 by omega, Int64.ofNat_add, Int64.ofNat_add]
  simp only [Int64.add_assoc]; rfl

/-- **The marshalling block's run**: the stores, the loads, `bl fn` with
the return address `2 sw + 2` instructions on. -/
theorem marshal_run (lab : Label → Int64) (sw : Nat) (fn : Label) (pc : Int64) (sp : Int) (σ : Flow.AS) :
    Flow.arun lab (marshal sw fn) ⟨pc, ⟨sp, []⟩, σ⟩ = ⟨lab fn, ⟨sp, []⟩, { σ with
      slot := stSlots sp σ.regs (mshSt sw) σ.slot,
      regs := (setWords sp (stSlots sp σ.regs (mshSt sw) σ.slot) (mshLd sw) σ.regs).setXReg .X30
        (pc + Int64.ofNat (4 * (2 * sw + 2))).toBitVec }⟩ := by
  rw [marshal_eq, arun_cat, arun_cat, arun_spStrs, arun_words, blD_run]
  have h1 : (mshSt sw).length = sw := by simp [mshSt]
  have h2 : (mshLd sw).length = sw + 1 := by simp [mshLd]
  rw [h1, h2, pc_marshal]

/-- **The marshalling block's registers**: `x0`…`x(sw-1)` as before it,
`x(sw)` the frame's base cell. -/
theorem marshal_regs {sw : Nat} (hsw : sw ≤ 7) (sp : Int) (sl : Int → BitVec 64) (regs : Reg64s) :
    (∀ i < sw, (setWords sp (stSlots sp regs (mshSt sw) sl) (mshLd sw) regs).getXReg (argX i) =
      regs.getXReg (argX i)) ∧
    (setWords sp (stSlots sp regs (mshSt sw) sl) (mshLd sw) regs).getXReg (argX sw) = .ofBitVec (sl sp) := by
  have hnd : ((mshLd sw).map Prod.fst).Nodup := by rw [mshLd_fst]; exact argX_nodup sw (by omega)
  have hof : ∀ i < sw, (Int64.ofNat (8 * (i + 1))).toInt = 8 * ((i : Int) + 1) := fun i hi => by
    rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le (show 8 * (i + 1) < 64 by omega) (by decide))]; omega
  have hsnd : ((mshSt sw).map fun p => sp + p.2.toInt).Nodup := by
    have e : ((mshSt sw).map fun p => sp + p.2.toInt) =
        (List.range sw).map fun i : Nat => sp + 8 * ((i : Int) + 1) := by
      simp only [mshSt, List.map_map]
      exact List.map_congr_left fun i hi => by
        show sp + (Int64.ofNat (8 * (i + 1))).toInt = _
        rw [hof i (List.mem_range.1 hi)]
    rw [e]
    exact List.Pairwise.map _
      (fun a b hab (h : sp + 8 * ((a : Int) + 1) = sp + 8 * ((b : Int) + 1)) => hab (by omega)) List.nodup_range
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [setWords_get _ _ _ _ hnd (w := .slot (Int64.ofNat (8 * (i + 1))))
      (by simp only [mshLd, List.mem_append, List.mem_map, List.mem_range]; exact .inl ⟨i, hi, rfl⟩)]
    simp only [RW.val]
    rw [stSlots_get _ _ _ _ hsnd (r := argX i)
      (by simp only [mshSt, List.mem_map, List.mem_range]; exact ⟨i, hi, rfl⟩), UInt64.ofBitVec_toBitVec]
  · rw [setWords_get _ _ _ _ hnd (w := .slot 0) (by simp [mshLd])]
    simp only [RW.val]
    rw [show (0 : Int64).toInt = 0 from rfl, Int.add_zero, stSlots_of_not_mem]
    intro p hp
    simp only [mshSt, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hi, rfl⟩ := hp
    rw [hof i hi]; omega

/-- **The marshalling block is covered**, its cells in the frame. -/
theorem okBlk_marshal {lo hi sp : Int} (h16 : sp % 16 = 0) {sw : Nat} (hsw : sw ≤ 7) (fn : Label)
    (hst : ∀ i < sw, Spike.Lib.offOk lo hi (sp + 8 * ((i : Int) + 1)) = true)
    (h0 : Spike.Lib.offOk lo hi sp = true) :
    Flow.okBlk lo hi ⟨sp, []⟩ (marshal sw fn) = true := by
  have hof : ∀ i < sw, (Int64.ofNat (8 * (i + 1))).toInt = 8 * ((i : Int) + 1) := fun i hj => by
    rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le (show 8 * (i + 1) < 64 by omega) (by decide))]; omega
  rw [marshal_eq, List.append_assoc]
  refine okBlk_spStrs_app h16 ?_ (okBlk_words h16 ?_ (okBlk_blD _ _ _ _))
  · intro p hp
    simp only [mshSt, List.mem_map, List.mem_range] at hp
    obtain ⟨i, hj, rfl⟩ := hp
    show Spike.Lib.offOk lo hi (sp + (Int64.ofNat (8 * (i + 1))).toInt) = true
    rw [hof i hj]; exact hst i hj
  · intro p hp
    simp only [mshLd, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
    rcases hp with ⟨i, hj, rfl⟩ | rfl
    · show Spike.Lib.offOk lo hi (sp + (Int64.ofNat (8 * (i + 1))).toInt) = true
      rw [hof i hj]; exact hst i hj
    · show Spike.Lib.offOk lo hi (sp + (0 : Int64).toInt) = true
      rw [show (0 : Int64).toInt = 0 from rfl, Int.add_zero]; exact h0

/-! ## Nodes -/

/-- **The user function's arguments after the setup block**: `x0`…`x(sw-1)`
those of some registers `rs` the setup block's post `PostS` relates to the
source control, `x(sw)` the TCB `x0`. -/
def SetupArgs (PostS : Ctl → Reg64s → Prop) (sw : Nat) (x0 : BitVec 64) (c : Ctl) (regs : Reg64s) : Prop :=
  ∃ rs, PostS c rs ∧ (∀ i < sw, regs.getXReg (argX i) = rs.getXReg (argX i)) ∧ regs.getXReg (argX sw) = .ofBitVec x0

section Nodes

variable (lab : Label → Int64) (sc : SetupCode)

/-- `scc_rt_main`'s entry, `x0` (the TCB) as the ghost `x0`. -/
def mainSN0 (g : MainG) (x0 : BitVec 64) : ND := ⟨lab "scc_rt_main", ⟨0, []⟩, fun σ c =>
  (mainN0 lab g).J σ c ∧ σ.regs.X0.toBitVec = x0⟩

/-- `scc_rt_main`'s body entry, the frame of `Z` set up, the TCB at its base. -/
def mainS1 (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.e0, ⟨-sc.Z.toInt, []⟩, fun σ c =>
  c = g.c0 ∧ σ.regs.SP.toBitVec = g.sp0 - sc.Z.toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp ∧ σ.slot (-sc.Z.toInt) = x0⟩

/-- The setup block's call node: at `setup`'s label, the return address `sp0`. -/
def mainSC (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.setup, ⟨-sc.Z.toInt, []⟩, fun σ c =>
  (mainS1 lab sc g x0).J σ c ∧ σ.regs.X30.toBitVec = (lab sc.e0 + 4).toBitVec⟩

/-- Back from the setup block, at `sp0`: its registers related to the source
control by `PostS`, `sp` and the thread pointer kept, the TCB at the frame's
base. -/
def mainS0 (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.sp0, ⟨-sc.Z.toInt, []⟩,
  fun σ c => PostS c σ.regs ∧ σ.regs.SP.toBitVec = g.sp0 - sc.Z.toBitVec ∧ σ.regs.TPIDR_EL0 = g.tp ∧
    σ.slot (-sc.Z.toInt) = x0⟩

/-- The user function's call node: at `fn`'s label, its arguments
(`SetupArgs`), the return address `sp1`. -/
def mainSM (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.fn, ⟨-sc.Z.toInt, []⟩,
  fun σ c => SetupArgs PostS sc.sw x0 c σ.regs ∧ σ.regs.SP.toBitVec = g.sp0 - sc.Z.toBitVec ∧
    σ.regs.TPIDR_EL0 = g.tp ∧ σ.regs.X30.toBitVec = (lab sc.sp1).toBitVec⟩

/-- Back from `fn`, at `sp1`: the source control and the result in `x0`
related by the post `Post`. -/
def mainSR (Post : Ctl → BitVec 64 → Prop) : ND := ⟨lab sc.sp1, ⟨-sc.Z.toInt, []⟩, fun σ c =>
  Post c σ.regs.X0.toBitVec⟩

/-- **The user function's entry after the setup block**: its arguments
(`Pre` of the source control and the registers), the ghosts' registers, and
the limit word's facts for a frame of `ZU`. -/
def uNM (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (fn : Label) (ZU : Int64) (Pre : Ctl → Reg64s → Prop) (g : WcG) : ND := ⟨lab fn, ⟨0, []⟩, fun σ c =>
  (Pre c σ.regs ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
    σ.regs.TPIDR_EL0 = g.tp) ∧ LimOk ms F exe endPc (limA g.tp) (g.sp - ZU.toBitVec)⟩

end Nodes

/-- **The setup block's return**: at the return address, the source control
and the registers related by `PostS`, `x29`/`x30`, `sp` and the thread
pointer restored. -/
def uNxS (PostS : Ctl → Reg64s → Prop) (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨0, []⟩, fun σ c =>
  PostS c σ.regs ∧ σ.regs.X29.toBitVec = g.fp ∧ σ.regs.X30.toBitVec = g.ra ∧ σ.regs.SP.toBitVec = g.sp ∧
    σ.regs.TPIDR_EL0 = g.tp⟩

/-! ## The interfaces and the obligations -/

/-- **The setup block called by `scc_rt_main`, as an interface**: as
`UserCallW`, from its entry `uN0` (limit room `ZU`) to its return `uNxS`
with `PostS` of the source control and the registers. -/
def SetupCallW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (PostS : Ctl → Reg64s → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uN0 (_root_.Executable.labels exe).label ms F exe endPc fn ZU g))
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNxS PostS g))

/-- **The user function called after the setup block, as an interface**: as
`UserCallW`, from its entry `uNM` (arguments `Pre`, limit room `ZU`) to its
return `uNx` with `Post` of the source control and `x0`, for every ghost
with the call's return address `ra` and thread pointer `tp`. -/
def MainCallW (W : Frag isaLSE2) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Pre : Ctl → Reg64s → Prop) (Post : Ctl → BitVec 64 → Prop)
    (ra : BitVec 64) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-Z.toInt) (-D) 0).OK → (R.callee (-Z.toInt) (-D) 0).base.toNat % 16 = 0 →
    FStable (R.callee (-Z.toInt) (-D) 0) F' → (∀ m, F' m → F m ∧ CallerCells R (-Z.toInt) (-D) 0 m) →
    ∀ g : WcG, g.ra = ra → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F'
          (uNM (_root_.Executable.labels exe).label ms F exe endPc fn ZU Pre g))
        (At exe endPc (R.callee (-Z.toInt) (-D) 0) F' (uNx Post g))

/-- **`scc_rt_main`'s own states inside `W`**, none moved by `K`: its
prologue's, the setup call block's, the marshalling block's and the
`exit_group` tail's. -/
structure MainSW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (sc : SetupCode)
    (PostS : Ctl → Reg64s → Prop) (Post : Ctl → BitVec 64 → Prop) (g : MainG) (x0 : BitVec 64) : Prop where
  pro : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") sc.Z 8 sc.grow [(.X0, 0)]
    (mainSN0 (_root_.Executable.labels exe).label g x0).J
  call0 : BlkW W K exe endPc R F (mainS1 (_root_.Executable.labels exe).label sc g x0) [blD sc.setup]
  sp0 : BlkW W K exe endPc R F (mainS0 (_root_.Executable.labels exe).label sc PostS g x0) (marshal sc.sw sc.fn)
  exit : ExitW W K exe endPc R F (mainSR (_root_.Executable.labels exe).label sc Post) sc.k

/-- `scc_rt_main`'s own states are inside the trivial predicate, with no
outside moves. -/
theorem MainSW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : MainG} {x0 : BitVec 64} :
    MainSW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms sc PostS Post g x0 :=
  ⟨ProW.triv, BlkW.triv, BlkW.triv, ExitW.triv⟩

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`scc_rt_main` after a setup block does not return, inside `W`**, in
any valid layout of any program with `mainSIn`: from its entry (`sp` at
offset 0 of a region holding its frame of `Z` and either callee's, `D1`
below it for the setup block, `D2` for the user function; `x0` the TCB) a
segment to any fragment, given the limit word's facts for its frame and the
callees' rooms `ZU1`, `ZU2`, the two callees' interfaces `hS` (to `PostS`)
and `hU` (from `PostS`'s registers marshalled, the TCB in `x(sw)`, to
`Post`), and that the `exit_group` there off an abort site is `main`'s exit
for every control and value `Post` relates (`hexit`). The `sw` words and
the TCB fit in `x0`–`x7` and in the frame (`hsw`, `hZw`). Neither call asks
closure under `K` of the callee (`call_nd_FWK` with `KC := False`). -/
theorem mainS_segW {W : Frag isaLSE2} {K : State → State → Prop} {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) {sc : SetupCode} (hin : mainSIn prog sc = true)
    (h16 : sc.Z.toInt % 16 = 0) (hZ : 16 ≤ sc.Z.toInt) (hsw : sc.sw ≤ 7) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-sc.Z.toInt) 0 (-sc.Z.toInt + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo1 : R.lo ≤ -sc.Z.toInt - D1) (hlo2 : R.lo ≤ -sc.Z.toInt - D2) (hhi : 0 ≤ R.hi) (g : MainG) (x0 : BitVec 64)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec))
    (hlimS : LimOk ms F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU1.toBitVec))
    (hlimU : LimOk ms F exe endPc (limA g.tp) (g.sp0 - sc.Z.toBitVec - ZU2.toBitVec))
    (hS : SetupCallW W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostS
      ((_root_.Executable.labels exe).label sc.e0 + 4).toBitVec g.c0 g.tp)
    (hU : MainCallW W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + 4 + 4 + 4, ⟨-sc.Z.toInt, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc R F ms sc PostS Post g x0)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGap hp hg0
  have esp1 := label_labelGap hp hg1
  have hloZ : R.lo ≤ -sc.Z.toInt := by omega
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainS1 lab sc g x0) h16 hZ hF hR hal hloZ hhi
    (by simp [Spike.Lib.offOk]; omega) rfl (by simp [SO.le, oFr, mainS1]) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainSC lab sc g x0)) ?_
      (SegW.seq (Q := At exe endPc R F (mainS0 lab sc PostS g x0)) ?_
        (SegW.seq (Q := At exe endPc R F (mainSM lab sc PostS g x0)) ?_
          (SegW.seq (Q := At exe endPc R F (mainSR lab sc Post)) ?_
            (exitTail_seg_ofW hp hend hex (n := mainSR lab sc Post) rfl hK hF hR hal (lo := -sc.Z.toInt) (hi := 0)
              hloZ hhi hk (by show (-sc.Z.toInt) % 16 = 0; omega) hW.exit fun s c σ0 hJ hAt => ?_)))))
  · -- the prologue
    rintro σ c ⟨⟨rfl, hsp, htp⟩, hx⟩
    rw [tcbA_limA htp]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [frRegs, ldStep, chkRegs, hsp]
    · rw [hr]; simp [frRegs, ldStep, chkRegs, setXReg_TPIDR, htp]
    · rw [hs, hr]; simp [stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, hx]
  · -- `bl setup`
    refine seg_oneW (seg_ndW (by simp) (okBlk_blD _ _ _ _) hF hR hal hloZ hhi
      (code_of hp hend hb0 (ofNat4_zero _)) hW.call0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [mainS1, mainSC]; rw [blD_run]
    · dsimp only [mainS1, mainSC]; rw [blD_run]; simp [SO.le]
    · dsimp only [mainS1, mainSC] at hJ ⊢; rw [blD_run]
      obtain ⟨rfl, hsp, htp, hsl⟩ := hJ
      exact ⟨⟨rfl, hsp, htp, hsl⟩, rfl⟩
  · -- the setup block's call
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -D1) (hi' := 0) (M := fun _ => True)
      (Ne := uN0 lab ms F exe endPc sc.setup ZU1) (Ex := fun g _ => uNxS PostS g)
      hR hal hF (by show R.lo ≤ -sc.Z.toInt + -D1; omega) (by omega) (by show -sc.Z.toInt < R.hi; omega)
      (by decide) (by show (-sc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp, -⟩, h30⟩, ⟨⟨hc', -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hS F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (hc'.symm.trans hc) (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp, -⟩, h30⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU1.toBitVec)
      rw [hsp]; exact hlimS
    · rintro g' x σC c σx c' σR ⟨⟨rfl, hsp, htp, hsl⟩, h30⟩ ⟨⟨-, -, h30', hsp', htp'⟩, -⟩ ⟨hP, -, -, hspx, htpx⟩ hreg -
        hslot
      refine .inl ⟨(), ?_, by simp [SO.le, mainS0, mainSC, uNxS], ?_⟩
      · show lab sc.sp0 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]; exact esp0
      · show PostS c' σR.regs ∧ σR.regs.SP.toBitVec = g.sp0 - sc.Z.toBitVec ∧ σR.regs.TPIDR_EL0 = g.tp ∧
          σR.slot (-sc.Z.toInt) = x0
        rw [hreg]
        refine ⟨hP, hspx.trans (hsp'.symm.trans hsp), htpx.trans (htp'.symm.trans htp), ?_⟩
        · rw [hslot (-sc.Z.toInt) ⟨by omega, by omega, by omega⟩
            (by simp only [mainSC, Spike.Lib.Region.Off, Spike.Lib.Region.callee]; omega)]
          exact hsl
  · -- the marshalling block and `bl fn`
    refine seg_oneW (seg_ndW (by simp [marshal]) (okBlk_marshal (by omega) hsw _
        (fun i hi => by simp [Spike.Lib.offOk]; omega) (by simp [Spike.Lib.offOk]; omega))
      hF hR hal hloZ hhi (code_of hp hend hb1 (ofNat4_zero _)) hW.sp0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)
    · dsimp only [mainS0, mainSM]; rw [marshal_run]
    · dsimp only [mainS0, mainSM]; rw [marshal_run]; simp [SO.le]
    · dsimp only [mainS0, mainSM] at hJ ⊢; rw [marshal_run]
      obtain ⟨hP, hsp, htp, hsl⟩ := hJ
      obtain ⟨hr, hx⟩ := marshal_regs hsw (-sc.Z.toInt) (σ.slot) σ.regs
      refine ⟨⟨σ.regs, hP, fun i hi => ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp only [Reg64s.getXReg_setXReg, argX_ne_X30 i (by omega), ite_false]; exact hr i hi
      · simp only [Reg64s.getXReg_setXReg, argX_ne_X30 _ (by omega : sc.sw < 8), ite_false, hx, hsl]
      · simp only [Reg64s.SP_setXReg, setWords_SP]; exact hsp
      · simp only [setXReg_TPIDR, setWords_TPIDR]; exact htp
      · simp only [Reg64s.X30_setXReg, ↓reduceIte, UInt64.toBitVec_ofBitVec]
        exact congrArg Int64.toBitVec esp1.symm
  · -- the user function's call
    refine seg_oneW (call_nd_FWK (KC := False) (lo' := -D2) (hi' := 0) (M := fun _ => True)
      (Ne := uNM lab ms F exe endPc sc.fn ZU2 (SetupArgs PostS sc.sw x0)) (Ex := fun g _ => uNx Post g)
      hR hal hF (by show R.lo ≤ -sc.Z.toInt + -D2; omega) (by omega) (by show -sc.Z.toInt < R.hi; omega)
      (by decide) (by show (-sc.Z.toInt) % 16 = 0; omega) (by omega) (by decide) (fun h => h.elim)
      (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' hal' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨-, -, htp, h30⟩, ⟨⟨-, -, h30', -, htp'⟩, -⟩⟩ := hg'
        exact (hU F' hR' hal' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' (h30'.symm.trans h30)
          (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨hA, hsp, htp, -⟩
      refine ⟨⟨σC.regs.X29.toBitVec, σC.regs.X30.toBitVec, σC.regs.SP.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F exe endPc (limA g.tp) (σC.regs.SP.toBitVec - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨-, -, -, h30⟩ ⟨⟨-, -, h30', -⟩, -⟩ ⟨hP, -, -⟩ hreg - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← h30']
        show lab _ = Int64.ofBitVec σC.regs.X30.toBitVec
        rw [h30, Spike.Lib.int64_ofBitVec_toBitVec]
      · show Post c' σR.regs.X0.toBitVec
        rw [hreg]; exact hP
  · -- the exit: `exit_group(v)`
    have hP := hJ
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
    exact SysOk.exitGroup_main (v := σ0.regs.X0.toBitVec.toNat)
      (hexit s c _ hP ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.X0.toBitVec = _; rw [hx]⟩)

end Proof

end Spike.Lib.A64.Rt
