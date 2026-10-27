/-
**The x86-64 main thread `scc_rt_main` after a setup block, parametric in
the program** (`mainS_segW`): `mainU_segW` (`Spike/Lib/Rt/X64Main.lean`)
with two calls, for the `.setup` tail (`SetupCode`,
`Spike/Lib/Rt/X64CodeInSetup.lean`). The x86-64 twin of
`Spike/Lib/Rt/A64MainS.lean`.

- **The code** (`mainSIn`): the stack-checked prologue saving `%rdi` (the
  TCB) at `-8(%rbp)`, `call setup` at `e0`, at `sp0` the marshalling block
  (`marshal`: the `sw` setup words from the result registers to the frame
  and back into the argument registers, the TCB into the next one,
  `call fn`), and the `exit_group` tail at `sp1`; `mainSIn_of_okS` reads it
  off A11's `rtCodeOkS`.
- **The marshalling block** in closed form (`marshal_run`, `marshal_regs`):
  argument register `i < sw` the result register `i` as the setup block
  returned them, argument register `sw` the TCB cell, `%rsp` past the
  pushed return point `sp1`, `%rbp` and `fsBase` kept.
- **Both callees are interfaces**: the setup block (`SetupCallW`, from the
  user function's entry `uN0` to `uNxS`, which also restores `%rbp`,
  `%rsp` and `fsBase`, its post `PostS` a relation of the source control
  and the whole returned registers), and the user function (`MainCallW`,
  from `uNM`: its arguments those of some registers `PostS` relates, the
  TCB in argument register `sw` (`SetupArgs`), to `uNx` with `Post`). The
  TCB cell survives the setup call, being outside its region.

Where x86-64 differs from AArch64 as in `mainU_segW`: each call pushes its
return address (the callee's region reaches `8` above its entry `%rsp`),
the frame's base is `8 + Z` below the entry `%rsp`, `%rbp`'s offset after
each return is restored from the invariant (`At.rbp`), no 16-alignment is
asked; and the setup words come back in the result registers `retXs` but go
out in the argument registers `argXs`.
-/
import Spike.Lib.Rt.X64CodeInSetup
import Spike.Lib.Rt.X64Main

namespace Spike.Lib.X64.Rt

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Kraken.X64.Parser
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (MainG mainN0 WcG LimOk limA seg_oneW CallerCells)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB RGrp rtIn_sound RtAll
  RtAll.append BsOk GapAt)

set_option linter.unusedSimpArgs false

/-! ## The program's facts -/

/-- **`scc_rt_main`'s code after a setup block in `cells`**: the
stack-checked prologue (frame `Z`, the limit at `%fs:8`, `%rdi` stored at
`-8(%rbp)`), `call setup` at `e0` returning to `sp0`, the marshalling block
and `call fn` at `sp0` returning to `sp1`, and the `exit_group` tail there
with the value spilled at `k`; the cells' sizes are today's emitter's
(`mainSGrps`). -/
def mainSIn (cells : List (Directive × Nat)) (sc : SetupCode) : Bool :=
  prologueIn cells "scc_rt_main" sc.sc sc.e0 sc.Z 8 sc.grow 5 9 3 2 4 [(.rdi, -8, 4)] &&
    blockAtB cells sc.e0 0 (callB sc.setup) && labelGapB cells sc.e0 sc.sp0 5 &&
    blockAtB cells sc.sp0 0 (marshal sc.sw sc.fn) && labelGapB cells sc.sp0 sc.sp1 (marshalSz sc.sw) &&
    exitIn cells sc.sp1 sc.k 4 4 5

section Of

variable {cells : List (Directive × Nat)} {sc : SetupCode}

/-- `scc_rt_main`'s check from its groups. -/
theorem mainSIn_of (h : RtAll cells (mainSGrps sc)) : mainSIn cells sc = true := by
  simp only [mainSGrps, setupFr, RtAll, BsOk, GapAt, and_true] at h
  simp only [mainSIn, prologueIn, exitIn, szSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.reduceAdd, h, Bool.and_self]

/-- `scc_rt_main`'s check from A11's runtime code check after a setup
block. -/
theorem mainSIn_of_okS (h : rtCodeOkS cells sc = true) : mainSIn cells sc = true := by
  have h' : RtAll cells (startGrps ++ mainSGrps sc ++ tcbGrps ++ tiGrpsAt sc.ti ++ takeGrps) := rtIn_sound h
  obtain ⟨h, -⟩ := RtAll.append h'
  obtain ⟨h, -⟩ := RtAll.append h
  obtain ⟨h, -⟩ := RtAll.append h
  exact mainSIn_of (RtAll.append h).2

end Of

/-! ## The marshalling block -/

theorem arun_cat (lab : Label → Int64) (a b : List (Directive × Nat)) (am : AM) :
    arun lab (a ++ b) am = arun lab b (arun lab a am) := by
  simp [arun, List.foldl_append]

/-- The marshalling block's stores: result register `i` to `swOff i`. -/
def mshSt (sw : Nat) : List (Reg64 × Int64 × Nat) := (List.range sw).map fun i => (retXs.getD i .rax, swOff i, 4)

/-- The marshalling block's loads: argument register `i` from `swOff i`,
then argument register `sw` from `-8` (the TCB). -/
def mshLd (sw : Nat) : List (Reg64 × Int64 × Nat) :=
  (List.range sw).map (fun i => (argXs.getD i .rdi, swOff i, 4)) ++ [(argXs.getD sw .rdi, -8, 4)]

theorem marshal_eq (sw : Nat) (fn : Label) :
    marshal sw fn = (mshSt sw).map xSt ++ (mshLd sw).map xLd ++ callB fn := by
  simp [marshal, mshSt, mshLd, List.map_map, Function.comp_def]

/-- The registers after the loads `ps` from the cells `sl` (`%rbp` at
`-8`). -/
def xLdRegs (sl : Int → BitVec 64) : List (Reg64 × Int64 × Nat) → Reg64s → Reg64s
  | [], r => r
  | p :: ps, r => xLdRegs sl ps (r.set64 p.1 (sl (-8 + p.2.1.toInt)))

/-- A load with `%rbp` at `-8`, its register's offset unknown. -/
theorem dstep_xLd (lab : String → Int64) (pc : Int64) (o : SO) (ho : o.get .rbp = some (-8)) (σ : AS)
    (p : Reg64 × Int64 × Nat) (hk : o.kill p.1 = o) :
    dstep lab ⟨pc, o, σ⟩ (xLd p) =
      ⟨pc + Int64.ofNat p.2.2, o, { σ with regs := σ.regs.set64 p.1 (σ.slot (-8 + p.2.1.toInt)) }⟩ := by
  simp [xLd, dstep, classify, BlockSpec.AI.step_ld', BlockSpec.AI.tgt_ld', AI.so, ho, hk]

/-- **The loads**, in closed form. -/
theorem arun_xLds (lab : String → Int64) (ps : List (Reg64 × Int64 × Nat)) (pc : Int64) (o : SO)
    (ho : o.get .rbp = some (-8)) (hk : ∀ p ∈ ps, o.kill p.1 = o) (σ : AS) :
    arun lab (ps.map xLd) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (szSum ps), o, { σ with regs := xLdRegs σ.slot ps σ.regs }⟩ := by
  induction ps generalizing pc σ with
  | nil => simp [arun, xLdRegs, szSum]
  | cons p ps ih =>
    simp only [List.map_cons, arun, List.foldl] at ih ⊢
    rw [dstep_xLd lab pc o ho σ p (hk p List.mem_cons_self),
      ih _ (fun q hq => hk q (List.mem_cons_of_mem _ hq)) _]
    simp only [xLdRegs, szSum, List.map_cons, List.sum_cons, AM.mk.injEq, and_true]
    rw [Int64.add_assoc, ← Int64.ofNat_add]

theorem xLdRegs_get_of_not_mem (sl : Int → BitVec 64) (ps : List (Reg64 × Int64 × Nat)) (r : Reg64s) {q : Reg64}
    (h : ∀ p ∈ ps, p.1 ≠ q) : (xLdRegs sl ps r).get64 q = r.get64 q := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [xLdRegs]
    rw [ih _ fun p' hp' => h p' (List.mem_cons_of_mem _ hp'),
      Reg64s.get64_set64_ne _ (h p List.mem_cons_self).symm]

theorem xLdRegs_get (sl : Int → BitVec 64) (ps : List (Reg64 × Int64 × Nat)) (r : Reg64s)
    (hnd : (ps.map (·.1)).Nodup) {p : Reg64 × Int64 × Nat} (h : p ∈ ps) :
    (xLdRegs sl ps r).get64 p.1 = sl (-8 + p.2.1.toInt) := by
  induction ps generalizing r with
  | nil => cases h
  | cons p' ps ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [xLdRegs]
    rcases List.mem_cons.1 h with e | h
    · subst e
      rw [xLdRegs_get_of_not_mem _ _ _ fun q hq he => hnd.1 ⟨q, hq, he⟩, Reg64s.get64_set64_self]
    · exact ih _ hnd.2 h

theorem xLdRegs_fsBase (sl : Int → BitVec 64) (ps : List (Reg64 × Int64 × Nat)) (r : Reg64s) :
    (xLdRegs sl ps r).fsBase = r.fsBase := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [xLdRegs]
    rw [ih]
    cases p.1 <;> rfl

theorem xStSlots_of_not_mem (regs : Reg64s) (ps : List (Reg64 × Int64 × Nat)) (sl : Int → BitVec 64) {k : Int}
    (h : ∀ p ∈ ps, k ≠ -8 + p.2.1.toInt) : xStSlots regs ps sl k = sl k := by
  induction ps generalizing sl with
  | nil => rfl
  | cons p ps ih =>
    simp only [xStSlots]
    rw [ih _ fun q hq => h q (List.mem_cons_of_mem _ hq)]
    simp [Spike.Lib.upd_apply, h p List.mem_cons_self]

theorem xStSlots_get (regs : Reg64s) (ps : List (Reg64 × Int64 × Nat)) (sl : Int → BitVec 64)
    (hnd : (ps.map fun p => -8 + p.2.1.toInt).Nodup) {p : Reg64 × Int64 × Nat} (h : p ∈ ps) :
    xStSlots regs ps sl (-8 + p.2.1.toInt) = regs.get64 p.1 := by
  induction ps generalizing sl with
  | nil => cases h
  | cons p' ps ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    simp only [xStSlots]
    rcases List.mem_cons.1 h with e | h
    · subst e
      rw [xStSlots_of_not_mem _ _ _ fun q hq he => hnd.1 ⟨q, hq, he.symm⟩]
      simp [Spike.Lib.upd_apply]
    · exact ih _ hnd.2 h

/-- The argument registers are distinct (`sw ≤ 5`). -/
theorem argXs_nodup : ∀ n < 6, ((List.range (n + 1)).map fun i => argXs.getD i .rdi).Nodup := by decide

/-- No argument register is `%rsp` or `%rbp`. -/
theorem argXs_getD_ne (i : Nat) : argXs.getD i .rdi ≠ .rsp ∧ argXs.getD i .rdi ≠ .rbp := by
  have hm : argXs.getD i .rdi ∈ argXs := by
    rw [List.getD_eq_getElem?_getD]
    cases h : argXs[i]? with
    | none => simp [argXs]
    | some r => exact List.mem_of_getElem? h
  have := (show ∀ r ∈ argXs, r ≠ .rsp ∧ r ≠ .rbp by decide) _ hm
  exact this

/-- The setup words' slots, from the region's base. -/
theorem swOff_toInt : ∀ i < 6, (swOff i).toInt = -(16 + 8 * (i : Int)) := by decide

theorem mshLd_fst (sw : Nat) : (mshLd sw).map (·.1) = (List.range (sw + 1)).map fun i => argXs.getD i .rdi := by
  simp [mshLd, List.range_succ, Function.comp_def]

theorem szSum_mshSt (sw : Nat) : szSum (mshSt sw) = 4 * sw := by
  simp only [szSum, mshSt, List.map_map, Function.comp_def]
  induction sw with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih]; simp; omega

theorem szSum_mshLd (sw : Nat) : szSum (mshLd sw) = 4 * sw + 4 := by
  have : szSum (mshLd sw) = szSum (mshSt sw) + 4 := by
    simp [szSum, mshLd, mshSt, List.map_map, Function.comp_def]
  rw [this, szSum_mshSt]

/-- The body's offsets know `%rbp` at `-8`. -/
theorem oU_rbp (z : Int) : SO.get ⟨z, [(.rbp, -8)]⟩ .rbp = some (-8) := rfl

/-- Forgetting a register other than `%rbp` keeps the body's offsets. -/
theorem oU_kill (z : Int) {r : Reg64} (h : r ≠ .rbp) : SO.kill ⟨z, [(.rbp, -8)]⟩ r = ⟨z, [(.rbp, -8)]⟩ := by
  simp [SO.kill, Spike.Lib.rm, Ne.symm h]

theorem okBlk_xSt_cons (lo hi : Int) (o : SO) (p : Reg64 × Int64 × Nat) (ds : List (Directive × Nat)) :
    okBlk lo hi o (xSt p :: ds) = (AI.ok lo hi o (.st .rbp p.2.1 p.1) && (ds.isEmpty || !false) && okBlk lo hi o ds) :=
  rfl

theorem okBlk_xLd_cons (lo hi : Int) (o : SO) (p : Reg64 × Int64 × Nat) (ds : List (Directive × Nat)) :
    okBlk lo hi o (xLd p :: ds) =
      (AI.ok lo hi o (.ld p.1 .rbp p.2.1) && (ds.isEmpty || !false) && okBlk lo hi (o.kill p.1) ds) :=
  rfl

/-- Stores into cells inside the region, then a covered block, are
covered. -/
theorem okBlk_xSts_app {lo hi : Int} {o : SO} (ho : o.get .rbp = some (-8)) {ps : List (Reg64 × Int64 × Nat)}
    (hps : ∀ p ∈ ps, Spike.Lib.offOk lo hi (-8 + p.2.1.toInt) = true) {ds : List (Directive × Nat)}
    (hds : okBlk lo hi o ds = true) : okBlk lo hi o (ps.map xSt ++ ds) = true := by
  induction ps with
  | nil => simpa using hds
  | cons p ps ih =>
    rw [List.map_cons, List.cons_append, okBlk_xSt_cons]
    simp only [AI.ok, ho, Bool.not_false, Bool.or_true, Bool.and_true]
    rw [hps p List.mem_cons_self, ih fun q hq => hps q (List.mem_cons_of_mem _ hq)]
    rfl

/-- Loads from cells inside the region into registers other than `%rsp`
whose offsets are unknown, then a covered block, are covered. -/
theorem okBlk_xLds_app {lo hi : Int} {o : SO} (ho : o.get .rbp = some (-8)) {ps : List (Reg64 × Int64 × Nat)}
    (hk : ∀ p ∈ ps, o.kill p.1 = o) (hr : ∀ p ∈ ps, p.1 ≠ .rsp)
    (hps : ∀ p ∈ ps, Spike.Lib.offOk lo hi (-8 + p.2.1.toInt) = true) {ds : List (Directive × Nat)}
    (hds : okBlk lo hi o ds = true) : okBlk lo hi o (ps.map xLd ++ ds) = true := by
  induction ps with
  | nil => simpa using hds
  | cons p ps ih =>
    rw [List.map_cons, List.cons_append, okBlk_xLd_cons, hk p List.mem_cons_self]
    simp only [AI.ok, ho, Bool.not_false, Bool.or_true, Bool.and_true]
    rw [hps p List.mem_cons_self, ih (fun q hq => hk q (List.mem_cons_of_mem _ hq))
      (fun q hq => hr q (List.mem_cons_of_mem _ hq)) fun q hq => hps q (List.mem_cons_of_mem _ hq)]
    simp [hr p List.mem_cons_self]

theorem mem_mshSt {sw i : Nat} (h : i < sw) : (retXs.getD i .rax, swOff i, 4) ∈ mshSt sw := by
  simp only [mshSt, List.mem_map, List.mem_range]; exact ⟨i, h, rfl⟩

theorem mem_mshLd {sw i : Nat} (h : i < sw) : (argXs.getD i .rdi, swOff i, 4) ∈ mshLd sw := by
  simp only [mshLd, List.mem_append, List.mem_map, List.mem_range]; exact .inl ⟨i, h, rfl⟩

theorem mem_mshLd_tcb (sw : Nat) : (argXs.getD sw .rdi, (-8 : Int64), 4) ∈ mshLd sw := by
  simp [mshLd]

theorem mshSt_off {sw : Nat} (hsw : sw ≤ 5) {p : Reg64 × Int64 × Nat} (hp : p ∈ mshSt sw) :
    ∃ i < sw, p = (retXs.getD i .rax, swOff i, 4) ∧ -8 + p.2.1.toInt = -24 - 8 * (i : Int) := by
  simp only [mshSt, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, hi, rfl, by simp only; rw [swOff_toInt i (by omega)]; omega⟩

theorem mshLd_off {sw : Nat} (hsw : sw ≤ 5) {p : Reg64 × Int64 × Nat} (hp : p ∈ mshLd sw) :
    (∃ i < sw, p = (argXs.getD i .rdi, swOff i, 4) ∧ -8 + p.2.1.toInt = -24 - 8 * (i : Int)) ∨
      (p = (argXs.getD sw .rdi, -8, 4) ∧ -8 + p.2.1.toInt = -16) := by
  simp only [mshLd, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ⟨i, hi, rfl⟩ | rfl
  · exact .inl ⟨i, hi, rfl, by simp only; rw [swOff_toInt i (by omega)]; omega⟩
  · exact .inr ⟨rfl, show -8 + (-8 : Int64).toInt = -16 by decide⟩

theorem mshLd_reg {sw : Nat} {p : Reg64 × Int64 × Nat} (hp : p ∈ mshLd sw) :
    p.1 ≠ .rsp ∧ p.1 ≠ .rbp := by
  simp only [mshLd, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hp
  rcases hp with ⟨i, -, rfl⟩ | rfl
  · exact argXs_getD_ne i
  · exact argXs_getD_ne sw

/-- **The marshalling block is covered**, its cells in the frame. -/
theorem okBlk_marshal {lo hi Z : Int} {sw : Nat} (hsw : sw ≤ 5) (fn : Label)
    (hst : ∀ i < sw, Spike.Lib.offOk lo hi (-24 - 8 * (i : Int)) = true)
    (h0 : Spike.Lib.offOk lo hi (-16) = true) (hc : Spike.Lib.offOk lo hi (-8 - Z - 8) = true) :
    okBlk lo hi ⟨-8 - Z, [(.rbp, -8)]⟩ (marshal sw fn) = true := by
  rw [marshal_eq, List.append_assoc]
  refine okBlk_xSts_app (oU_rbp _) (fun p hp => ?_) (okBlk_xLds_app (oU_rbp _)
    (fun p hp => oU_kill _ (mshLd_reg hp).2) (fun p hp => (mshLd_reg hp).1) (fun p hp => ?_) (okBlk_callB _ hc))
  · obtain ⟨i, hi, -, e⟩ := mshSt_off hsw hp
    rw [e]; exact hst i hi
  · rcases mshLd_off hsw hp with ⟨i, hi, -, e⟩ | ⟨-, e⟩
    · rw [e]; exact hst i hi
    · rw [e]; exact h0

/-- The return point after the marshalling block. -/
theorem pc_marshal (pc : Int64) (sw : Nat) :
    (pc + Int64.ofNat (4 * sw) + Int64.ofNat (4 * sw + 4)).toBitVec + 5#64 =
      (pc + Int64.ofNat (marshalSz sw)).toBitVec := by
  have e : Int64.ofNat (marshalSz sw) = Int64.ofNat (4 * sw) + Int64.ofNat (4 * sw + 4) + Int64.ofNat 5 := by
    rw [show marshalSz sw = 4 * sw + (4 * sw + 4) + 5 by simp only [marshalSz]; omega, Int64.ofNat_add,
      Int64.ofNat_add]
  rw [e, ← Int64.add_assoc, ← Int64.add_assoc, Int64.toBitVec_add]
  rfl

/-- **The marshalling block's run**: the stores, the loads, `call fn` with
the return address `marshalSz sw` bytes on (`pc_marshal`). -/
theorem marshal_run (lab : Label → Int64) (sw : Nat) (fn : Label) (pc : Int64) (Z : Int) (σ : AS) :
    arun lab (marshal sw fn) ⟨pc, ⟨-8 - Z, [(.rbp, -8)]⟩, σ⟩ =
      ⟨lab fn, ⟨-8 - Z - 8, [(.rbp, -8)]⟩, { σ with
        regs := (xLdRegs (xStSlots σ.regs (mshSt sw) σ.slot) (mshLd sw) σ.regs).set64 .rsp
          ((xLdRegs (xStSlots σ.regs (mshSt sw) σ.slot) (mshLd sw) σ.regs).rsp.toBitVec - 8#64),
        slot := Spike.Lib.upd (xStSlots σ.regs (mshSt sw) σ.slot) (-8 - Z - 8)
          ((pc + Int64.ofNat (4 * sw) + Int64.ofNat (4 * sw + 4)).toBitVec + 5#64) }⟩ := by
  rw [marshal_eq, arun_cat, arun_cat, arun_xSts _ _ _ _ (oU_rbp _),
    arun_xLds _ _ _ _ (oU_rbp _) (fun p hp => oU_kill _ (mshLd_reg hp).2), callB_run, szSum_mshSt, szSum_mshLd]

/-- **The marshalling block's loads**: argument register `i < sw` the
result register `i` before the stores, argument register `sw` the TCB cell
`-16`, `%rbp` and `fsBase` kept. -/
theorem marshal_regs {sw : Nat} (hsw : sw ≤ 5) (sl : Int → BitVec 64) (regs : Reg64s) :
    (∀ i < sw, (xLdRegs (xStSlots regs (mshSt sw) sl) (mshLd sw) regs).get64 (argXs.getD i .rdi) =
      regs.get64 (retXs.getD i .rax)) ∧
    (xLdRegs (xStSlots regs (mshSt sw) sl) (mshLd sw) regs).get64 (argXs.getD sw .rdi) = sl (-16) ∧
    (xLdRegs (xStSlots regs (mshSt sw) sl) (mshLd sw) regs).get64 .rbp = regs.get64 .rbp ∧
    (xLdRegs (xStSlots regs (mshSt sw) sl) (mshLd sw) regs).fsBase = regs.fsBase := by
  have hnd : ((mshLd sw).map (·.1)).Nodup := by rw [mshLd_fst]; exact argXs_nodup sw (by omega)
  have hsnd : ((mshSt sw).map fun p => -8 + p.2.1.toInt).Nodup := by
    have e : ((mshSt sw).map fun p => -8 + p.2.1.toInt) = (List.range sw).map fun i : Nat => -24 - 8 * (i : Int) := by
      simp only [mshSt, List.map_map]
      exact List.map_congr_left fun i hi => by
        show -8 + (swOff i).toInt = _
        rw [swOff_toInt i (by have := List.mem_range.1 hi; omega)]; omega
    rw [e]
    exact List.Pairwise.map _
      (fun a b hab (h : -24 - 8 * (a : Int) = -24 - 8 * (b : Int)) => hab (by omega)) List.nodup_range
  refine ⟨fun i hi => ?_, ?_, ?_, xLdRegs_fsBase _ _ _⟩
  · rw [xLdRegs_get _ _ _ hnd (mem_mshLd hi)]
    have e : -8 + (swOff i).toInt = -8 + (retXs.getD i .rax, swOff i, 4).2.1.toInt := rfl
    simp only
    rw [e, xStSlots_get _ _ _ hsnd (mem_mshSt hi)]
  · rw [xLdRegs_get _ _ _ hnd (mem_mshLd_tcb sw)]
    rw [show -8 + (-8 : Int64).toInt = -16 by decide]
    refine xStSlots_of_not_mem _ _ _ fun p hp => ?_
    obtain ⟨i, -, -, e⟩ := mshSt_off hsw hp
    rw [e]; omega
  · exact xLdRegs_get_of_not_mem _ _ _ fun p hp => (mshLd_reg hp).2

/-! ## Nodes -/

/-- **The user function's arguments after the setup block**: argument
register `i < sw` the result register `i` of some registers `rs` the setup
block's post `PostS` relates to the source control, argument register `sw`
the TCB `x0`. -/
def SetupArgs (PostS : Ctl → Reg64s → Prop) (sw : Nat) (x0 : BitVec 64) (c : Ctl) (regs : Reg64s) : Prop :=
  ∃ rs, PostS c rs ∧ (∀ i < sw, regs.get64 (argXs.getD i .rdi) = rs.get64 (retXs.getD i .rax)) ∧
    regs.get64 (argXs.getD sw .rdi) = x0

section Nodes

variable (lab : Label → Int64) (sc : SetupCode)

/-- `scc_rt_main`'s entry, `%rdi` (the TCB) as the ghost `x0`. -/
def mainSN0 (g : MainG) (x0 : BitVec 64) : ND := ⟨lab "scc_rt_main", ⟨0, []⟩, fun σ c =>
  (mainN0 lab g).J σ c ∧ σ.regs.rdi.toBitVec = x0⟩

/-- `scc_rt_main`'s body entry, the frame of `Z` set up, the TCB at `-16`
(`-8(%rbp)`). -/
def mainS1 (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.e0, oU sc.Z, fun σ c =>
  c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - sc.Z.toBitVec ∧ σ.regs.fsBase = g.tp ∧ σ.slot (-16) = x0⟩

/-- The body entry with `%rbp` claimed from its offset (`At.rbp_get`). -/
def mainS1R (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.e0, oU sc.Z, fun σ c =>
  (mainS1 lab sc g x0).J σ c ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (oU sc.Z).sp)⟩

/-- The setup block's call node: at `setup`'s label, the return address
`sp0` pushed, the TCB at `-16`. -/
def mainSC (g : MainG) (x0 : BitVec 64) : ND := ⟨lab sc.setup, ⟨-8 - sc.Z.toInt - 8, []⟩, fun σ c =>
  (c = g.c0 ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 ∧ σ.regs.fsBase = g.tp) ∧
    σ.slot (-8 - sc.Z.toInt - 8) = (lab sc.sp0).toBitVec ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt - 8)) ∧ σ.slot (-16) = x0⟩

/-- Back from the setup block, at `sp0`: its registers related to the source
control by `PostS`, `%rsp` and `fsBase` kept, the TCB at `-16`, `%rbp` at the
saved `%rbp`. -/
def mainS0 (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) : ND :=
  ⟨lab sc.sp0, ⟨-8 - sc.Z.toInt, []⟩, fun σ c =>
    (PostS c σ.regs ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - sc.Z.toBitVec ∧ σ.regs.fsBase = g.tp ∧
      σ.slot (-16) = x0) ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))⟩

/-- Back from the setup block with `%rbp`'s offset fixed (`At.rbp`): the
node the marshalling block runs from. -/
def mainS0R (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) : ND :=
  ⟨lab sc.sp0, oU sc.Z, (mainS0 lab sc PostS g x0).J⟩

/-- The user function's call node: at `fn`'s label, its arguments
(`SetupArgs`), the return address `sp1` pushed. -/
def mainSM (PostS : Ctl → Reg64s → Prop) (g : MainG) (x0 : BitVec 64) : ND :=
  ⟨lab sc.fn, ⟨-8 - sc.Z.toInt - 8, []⟩, fun σ c =>
    (SetupArgs PostS sc.sw x0 c σ.regs ∧ σ.regs.rsp.toBitVec = g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 ∧
      σ.regs.fsBase = g.tp) ∧ σ.slot (-8 - sc.Z.toInt - 8) = (lab sc.sp1).toBitVec ∧
    σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt - 8))⟩

/-- Back from `fn`, at `sp1`: the source control and the result in `%rax`
related by the post `Post`, `%rbp` at the saved `%rbp`. -/
def mainSR (Post : Ctl → BitVec 64 → Prop) : ND := ⟨lab sc.sp1, ⟨-8 - sc.Z.toInt, []⟩, fun σ c =>
  Post c σ.regs.rax.toBitVec ∧ σ.regs.get64 .rbp = σ.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))⟩

/-- Back from `fn` with `%rbp`'s offset fixed: the node the `exit_group`
tail runs from. -/
def mainSRR (Post : Ctl → BitVec 64 → Prop) : ND := ⟨lab sc.sp1, oU sc.Z, (mainSR lab sc Post).J⟩

/-- **The user function's entry after the setup block**: its arguments
(`Pre` of the source control and the registers), the ghosts' registers and
return address, and the limit word's facts for a frame of `ZU`. -/
def uNM (ms : MemSide isa) (F : MachineData → Prop) (fn : Label) (ZU : Int64) (Pre : Ctl → Reg64s → Prop)
    (g : WcG) : ND := ⟨lab fn, ⟨0, []⟩, fun σ c =>
  (Pre c σ.regs ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.slot 0 = g.ra ∧ σ.regs.rsp.toBitVec = g.sp ∧
    σ.regs.fsBase = g.tp) ∧ LimOk ms F (limA g.tp) (g.sp - 8#64 - ZU.toBitVec)⟩

end Nodes

/-- **The setup block's return**: at the return address, the source control
and the registers related by `PostS`, `%rbp` restored, `%rsp` past the
return address, `fsBase` kept. -/
def uNxS (PostS : Ctl → Reg64s → Prop) (g : WcG) : ND := ⟨Int64.ofBitVec g.ra, ⟨8, []⟩, fun σ c =>
  PostS c σ.regs ∧ σ.regs.rbp.toBitVec = g.fp ∧ σ.regs.rsp.toBitVec = g.sp + 8#64 ∧ σ.regs.fsBase = g.tp⟩

/-! ## The interfaces and the obligations -/

/-- **The setup block called by `scc_rt_main`, as an interface**: as
`UserCallW`, from its entry `uN0` (limit room `ZU`) to its return `uNxS`
with `PostS` of the source control and the registers. -/
def SetupCallW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (PostS : Ctl → Reg64s → Prop) (ra : BitVec 64) (c0 : Ctl)
    (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.c0 = c0 → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uN0 (_root_.Executable.labels exe).label ms F fn ZU g))
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (uNxS PostS g))

/-- **The user function called after the setup block, as an interface**: as
`UserCallW`, from its entry `uNM` (arguments `Pre`, limit room `ZU`) to its
return `uNx` with `Post` of the source control and `%rax`, for every ghost
with the call's return address `ra` and thread pointer `tp`. -/
def MainCallW (W : Frag isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (fn : Label) (Z : Int64) (D : Int) (ZU : Int64) (Pre : Ctl → Reg64s → Prop) (Post : Ctl → BitVec 64 → Prop)
    (ra : BitVec 64) (tp : UInt64) : Prop :=
  ∀ F' : MachineData → Prop, (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8).OK →
    FStable (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' →
    (∀ m, F' m → F m ∧ CallerCells R (-8 - Z.toInt - 8 - 0) (-D) 8 m) →
    ∀ g : WcG, g.ra = ra → g.tp = tp →
      SegW W K p lbl ms
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F'
          (uNM (_root_.Executable.labels exe).label ms F fn ZU Pre g))
        (At exe endPc (R.callee (-8 - Z.toInt - 8 - 0) (-D) 8) F' (uNx Post g))

/-- **`scc_rt_main`'s own states inside `W`**, none moved by `K`: its
prologue's, the setup call block's, the marshalling block's and the
`exit_group` tail's. -/
structure MainSW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable)
    (endPc : Int64) (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (sc : SetupCode)
    (PostS : Ctl → Reg64s → Prop) (Post : Ctl → BitVec 64 → Prop) (g : MainG) (x0 : BitVec 64) : Prop where
  pro : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") sc.Z 8 sc.grow
    5 9 3 2 4 [(.rdi, -8, 4)] (mainSN0 (_root_.Executable.labels exe).label g x0).J
  call0 : BlkW W K exe endPc R F (mainS1R (_root_.Executable.labels exe).label sc g x0) (callB sc.setup)
  sp0 : BlkW W K exe endPc R F (mainS0R (_root_.Executable.labels exe).label sc PostS g x0) (marshal sc.sw sc.fn)
  exit : XExitW W K exe endPc R F (mainSRR (_root_.Executable.labels exe).label sc Post) (-8 - sc.Z.toInt) (-8)
    sc.k 4 4 5

/-- `scc_rt_main`'s own states are inside the trivial predicate, with no
outside moves. -/
theorem MainSW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {sc : SetupCode} {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    {g : MainG} {x0 : BitVec 64} :
    MainSW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms sc PostS Post g x0 :=
  ⟨XProW.triv, BlkW.triv, BlkW.triv, XExitW.triv⟩

/-! ## The segment -/

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `%rbp`'s offset moved by `8` with `%rsp`. -/
private theorem rbp_shift (r : BitVec 64) (z : Int) :
    r + BitVec.ofInt 64 (-8 - (-8 - z)) = r - 8#64 + BitVec.ofInt 64 (-8 - (-8 - z - 8)) := by
  rw [show -8 - (-8 - z - 8) = (-8 - (-8 - z)) + 8 by omega, BitVec.ofInt_add]
  generalize BitVec.ofInt 64 (-8 - (-8 - z)) = y
  show r + y = r - 8#64 + (y + 8#64)
  bv_omega

/-- `%rbp` back at the saved `%rbp` after a call's return: the callee
restored `%rbp` and popped the return address. -/
private theorem rbp_ret {rbpC rspC rbpR rspR : BitVec 64} (z : Int)
    (hb : rbpC = rspC + BitVec.ofInt 64 (-8 - (-8 - z - 8))) (hbR : rbpR = rbpC) (hspR : rspR = rspC + 8#64) :
    rbpR = rspR + BitVec.ofInt 64 (-8 - (-8 - z)) := by
  rw [hbR, hspR, hb]
  have := rbp_shift (rspC + 8#64) z
  rw [show rspC + 8#64 - 8#64 = rspC by bv_omega] at this
  exact this.symm

/-- **`scc_rt_main` after a setup block does not return, inside `W`**, in
any valid layout of any cells with `mainSIn`: from its entry (`%rsp` at
offset 0 of a region holding its frame of `Z` under the saved `%rbp`, each
call's return address and either callee's region, `D1` below the return
address for the setup block, `D2` for the user function; `%rdi` the TCB
`x0`) a segment to any fragment, given the limit word's facts for its frame
and the callees' rooms `ZU1`, `ZU2`, the two callees' interfaces `hS` (to
`PostS`) and `hU` (from `PostS`'s result registers marshalled into the
argument registers, the TCB in argument register `sw`, to `Post`), and that
the `exit_group` there off an abort site is `main`'s exit for every control
and value `Post` relates (`hexit`). The `sw` words and the TCB fit in the
six argument registers and in the frame (`hsw`, `hZw`). Neither call asks
closure under `K` of the callee (`call_nd_FWK` with `KC := False`). -/
theorem mainS_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) {sc : SetupCode} (hin : mainSIn cells sc = true)
    (hZ8 : sc.Z.toInt % 8 = 0) (hsw : sc.sw ≤ 5) (hZw : 8 * (sc.sw : Int) + 8 ≤ sc.Z.toInt)
    (hk : Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + sc.k.toInt) = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostS : Ctl → Reg64s → Prop} {Post : Ctl → BitVec 64 → Prop}
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo1 : R.lo ≤ -8 - sc.Z.toInt - 8 - D1) (hlo2 : R.lo ≤ -8 - sc.Z.toInt - 8 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec))
    (hlimS : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU1.toBitVec))
    (hlimU : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - sc.Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hS : SetupCallW W K p lbl ms exe endPc R F sc.setup sc.Z D1 ZU1 PostS
      ((_root_.Executable.labels exe).label sc.sp0).toBitVec g.c0 g.tp)
    (hU : MainCallW W K p lbl ms exe endPc R F sc.fn sc.Z D2 ZU2 (SetupArgs PostS sc.sw x0) Post
      ((_root_.Executable.labels exe).label sc.sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label sc.sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU sc.Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc R F ms sc PostS Post g x0)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)) Q := by
  let lab := (_root_.Executable.labels exe).label
  simp only [mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨hpro, hb0⟩, hg0⟩, hb1⟩, hg1⟩, hex⟩ := hin
  have esp0 := label_labelGapB hp hg0
  have esp1 := label_labelGapB hp hg1
  have hloZ : R.lo ≤ -8 - sc.Z.toInt := by omega
  refine SegW.seq (prologue_seg_ofW hp hend hpro (nb := mainS1 lab sc g x0) (by omega) hF hR hloZ hhi ?_ rfl
    (by simp [SO.le, lk, mainS1]) hW.pro ?_)
    (SegW.seq (Q := At exe endPc R F (mainSC lab sc g x0)) ?_
      (SegW.seq (Q := At exe endPc R F (mainS0 lab sc PostS g x0)) ?_
        (SegW.seq (Q := At exe endPc R F (mainSM lab sc PostS g x0)) ?_
          (SegW.seq (Q := At exe endPc R F (mainSR lab sc Post)) ?_
            ((exitTail_seg_ofW (lo := -8 - sc.Z.toInt) (hi := 0) hp hend hex (n := mainSRR lab sc Post) rfl rfl hK
                hF hR hloZ hhi hk hW.exit fun s c σ0 hJ0 hs => ?_).mono_pre
              fun _ _ h => At.rbp h fun _ _ h => h.2)))))
  · -- the TCB's store
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    show Spike.Lib.offOk (-8 - sc.Z.toInt) 0 (-8 + (-8 : Int64).toInt) = true
    rw [show (-8 : Int64).toInt = -8 by decide]
    simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega
  · -- the prologue
    rintro σ c ⟨⟨rfl, hsp, htp⟩, hx⟩
    have ha : σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec = limA g.tp := by rw [limA, htp]
    rw [ha]
    refine ⟨hlimM.rt, hlimM.mp, hlimM.unmapped, fun v hv => ⟨?_, fun σ' hr hs => ⟨rfl, ?_, ?_, ?_⟩⟩⟩
    · rw [hsp]; exact hlimM.room v hv
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]
    · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
    · rw [hs, hr]
      simp [xStSlots, xS1, Spike.Lib.upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hx]
  · -- `call setup`
    refine (seg_oneW (seg_ndW (n := mainS1R lab sc g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0) (by simp [callB])
      (okBlk_callB _ (by simp [Spike.Lib.offOk, mainS1R]; omega)) hF hR (by omega) hhi
      (code_field hp hend hb0 (ofNat_zero' _)) hW.call0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => Ret0.At.rbp_get rfl h
    · dsimp only [mainS1R, mainSC]; rw [callB_run]
    · dsimp only [mainS1R, mainSC]; rw [callB_run]; simp [SO.le]
    · dsimp only [mainS1R, mainS1, mainSC] at hJ ⊢; rw [callB_run]
      obtain ⟨⟨rfl, hsp, htp, hsl⟩, hb⟩ := hJ
      refine ⟨⟨rfl, ?_, ?_⟩, ?_, ?_, ?_⟩
      · simp [Reg64s.set64, hsp]
      · simp [Reg64s.set64, htp]
      · simp only [Spike.Lib.upd_apply, ↓reduceIte]
        rw [show lab sc.sp0 = _ from esp0]; rfl
      · simp only [Reg64s.get64, Reg64s.set64] at hb ⊢; rw [hb]
        exact rbp_shift _ _
      · dsimp only
        simp only [Spike.Lib.upd_apply, show ((-16 : Int) = -8 - sc.Z.toInt - 8) = False from eq_false (by omega),
          ↓reduceIte]
        exact hsl
  · -- the setup block's call
    refine seg_oneW (call_nd_FWK (KC := False) (e0 := 0) (lo' := -D1) (hi' := 8) (M := fun _ => True)
      (Ne := uN0 lab ms F sc.setup ZU1) (Ex := fun g _ => uNxS PostS g)
      hR hF (by show R.lo ≤ -8 - sc.Z.toInt - 8 - 0 + -D1; omega) (by omega)
      (by show -8 - sc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - sc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
      (by show (-8 - sc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨hc, -, htp⟩, hsl, -, -⟩, ⟨⟨hc', -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab sc.sp0).toBitVec := by
          rw [← hra, ← hsl]; show σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
        exact (hS F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' hr (hc'.symm.trans hc)
          (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨rfl, hsp, htp⟩, -, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, g.c0⟩, rfl,
        ⟨rfl, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU1.toBitVec)
      rw [hsp]; exact hlimS
    · rintro g' x σC c σx c' σR ⟨⟨rfl, hspC, htpC⟩, hsl, hb, hx0⟩ ⟨⟨hc, hfp, hra, hsp, htp'⟩, -⟩
        ⟨hP, hb', hsp', htpx⟩ hregs - - hslot
      refine .inl ⟨(), ?_, by simp [SO.le, mainS0, mainSC, uNxS], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · show lab sc.sp0 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · rw [hregs]; exact hP
      · rw [hregs, hsp', ← hsp]
        show σC.regs.rsp.toBitVec + 8#64 = _
        rw [hspC]; exact BitVec.sub_add_cancel _ _
      · rw [hregs, htpx, ← htp']; exact htpC
      · rw [hslot (-16) ⟨by omega, by omega, by omega⟩
          (by simp only [Region.Off, Region.callee, mainSC]; omega)]
        exact hx0
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        exact rbp_ret sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  · -- the marshalling block and `call fn`
    refine (seg_oneW (seg_ndW (n := mainS0R lab sc PostS g x0) (lo := -8 - sc.Z.toInt - 8) (hi := 0)
      (by simp [marshal, callB])
      (okBlk_marshal hsw _ (fun i hi => by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)
        (by simp only [Spike.Lib.offOk, decide_eq_true_eq]; omega)) hF hR (by omega) hhi
      (code_field hp hend hb1 (ofNat_zero' _)) hW.sp0
        fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩)).mono_pre
      fun _ _ h => At.rbp h fun _ _ h => h.2
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]
    · dsimp only [mainS0R, mainSM]; rw [marshal_run]; simp [SO.le]
    · dsimp only [mainS0R, mainS0, mainSM] at hJ ⊢; rw [marshal_run]
      obtain ⟨⟨hP, hsp, htp, hsl⟩, hb⟩ := hJ
      obtain ⟨hr, hx, hrbp, hfs⟩ := marshal_regs hsw σ.slot σ.regs
      have hrsp := xLdRegs_get_of_not_mem (xStSlots σ.regs (mshSt sc.sw) σ.slot) (mshLd sc.sw) σ.regs
        (q := .rsp) fun p hp => (mshLd_reg hp).1
      refine ⟨⟨⟨σ.regs, hP, fun i hi => ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne i).1]; exact hr i hi
      · rw [Reg64s.get64_set64_ne _ (argXs_getD_ne _).1, hx]; exact hsl
      · show (Reg64s.set64 _ .rsp _).get64 .rsp = _
        rw [Reg64s.get64_set64_self]
        simp only [Reg64s.get64] at hrsp
        rw [hrsp, hsp]
      · simp only [Reg64s.set64]; rw [hfs]; exact htp
      · simp only [Spike.Lib.upd_apply, ↓reduceIte]
        rw [pc_marshal]; exact congrArg Int64.toBitVec esp1.symm
      · rw [Reg64s.get64_set64_ne _ (by decide), Reg64s.get64_set64_self, hrbp, hb]
        simp only [Reg64s.get64] at hrsp ⊢
        rw [hrsp]
        exact rbp_shift _ _
  · -- the user function's call
    refine seg_oneW (call_nd_FWK (KC := False) (e0 := 0) (lo' := -D2) (hi' := 8) (M := fun _ => True)
      (Ne := uNM lab ms F sc.fn ZU2 (SetupArgs PostS sc.sw x0)) (Ex := fun g _ => uNx Post g)
      hR hF (by show R.lo ≤ -8 - sc.Z.toInt - 8 - 0 + -D2; omega) (by omega)
      (by show -8 - sc.Z.toInt - 8 - 0 < R.hi; omega) (by show -8 - sc.Z.toInt - 8 - 0 + 8 ≤ R.hi; omega)
      (by show (-8 - sc.Z.toInt - 8 - 0) % 8 = 0; omega) (by omega) (by decide)
      (fun h => h.elim) (fun h => h.elim) (fun _ h _ => h)
      (fun R' F' hR' _ _ hF' _ hFF hR'e hcc g' hg' _ => by
        subst hR'e
        obtain ⟨σC, c, ⟨⟨-, -, htp⟩, hsl, -⟩, ⟨⟨-, -, hra, -, htp'⟩, -⟩⟩ := hg'
        have hr : g'.ra = (lab sc.sp1).toBitVec := by
          rw [← hra, ← hsl]; show σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0) = _; congr 1; omega
        exact (hU F' hR' hF' (fun m h => ⟨hFF m h, hcc m h⟩) g' hr
          (htp'.symm.trans htp)).mono_post fun _ _ h => ⟨(), h, trivial⟩)
      (fun _ => rfl) ?_ ?_)
    · rintro σC c ⟨⟨hA, hsp, htp⟩, -, -⟩
      refine ⟨⟨σC.regs.rbp.toBitVec, σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0), σC.regs.rsp.toBitVec, g.tp, c⟩, rfl,
        ⟨hA, rfl, rfl, rfl, htp⟩, ?_⟩
      show LimOk ms F (limA g.tp) (σC.regs.rsp.toBitVec - 8#64 - ZU2.toBitVec)
      rw [hsp]; exact hlimU
    · rintro g' x σC c σx c' σR ⟨-, hsl, hb⟩ ⟨⟨-, hfp, hra, hsp, -⟩, -⟩ ⟨hP, hb', hsp'⟩ hregs - - -
      refine .inl ⟨(), ?_, by simp [SO.le, mainSR, mainSM, uNx], by rw [hregs]; exact hP, ?_⟩
      · show lab sc.sp1 = Int64.ofBitVec g'.ra
        rw [← hra]
        show lab _ = Int64.ofBitVec (σC.slot (-8 - sc.Z.toInt - 8 - 0 + 0))
        rw [show -8 - sc.Z.toInt - 8 - 0 + 0 = -8 - sc.Z.toInt - 8 by omega, hsl, int64_ofBitVec_toBitVec]
      · show σR.regs.get64 .rbp = σR.regs.get64 .rsp + BitVec.ofInt 64 (-8 - (-8 - sc.Z.toInt))
        rw [hregs]
        simp only [Reg64s.get64] at hb ⊢
        exact rbp_ret sc.Z.toInt hb (hb'.trans hfp.symm) (hsp'.trans (by rw [← hsp]; rfl))
  · -- the exit: `exit_group(v)`
    have hP := hJ0.1
    obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hs
    exact SysOk.exitGroup_main (v := σ0.regs.rax.toBitVec.toNat)
      (hexit s c _ hP ⟨he, hn, hdc, hpc, σ, hA, hD, by show σ.regs.rdi.toBitVec = _; rw [hx]⟩)

end Proof

/-- `setupMC sw`'s side conditions of `mainS_segW` other than the depths',
at `hello1.w`'s four words. -/
example : (setupMC 4).Z.toInt % 8 = 0 ∧ (setupMC 4).sw ≤ 5 ∧ 8 * ((setupMC 4).sw : Int) + 8 ≤ (setupMC 4).Z.toInt ∧
    Spike.Lib.offOk (-8 - (setupMC 4).Z.toInt) 0 (-8 + (setupMC 4).k.toInt) = true := by
  decide

end Spike.Lib.X64.Rt
