/-
**wake's main after its `clone` inside `mainW`: the parent and the exit
tail** (AArch64): the two ends of main's post-spawn path
(`MainPost.seg_mainPost`) as `SegW` segments inside any `W`, given every
node's states in it, and those node obligations at
`W := WakeInst.mainW lab exe Λ lbl`.

- `ParentW`, `seg_parentW`: `Parent.seg_parent` inside `W` (each of the
  four blocks' states in `W`).
- `parentRuns`, `parentW_main`: the parent's blocks inside `mainW`: the
  source `cP` (past the spawn, at its tail call) reads only `cv`, placed at
  the frame's cell `-72` (the published cell's address `A`).
- `exitNP`: the `exit_group` tail's `svc` node, keeping the entry's cell
  `-32` and `x9` (where the source past the load is placed).
- `seg_waitExitW`: `MainPost.seg_waitExit` inside `W`.
- `exitRuns`, `exitW0_main`, `exitW1_main`: the tail's states inside
  `mainW`.
-/
import Spike.Lib.A64WakeMainW
import Spike.Lib.A64WakeMainPost

namespace Spike.Lib.A64WakeMainSegW

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Scc.Sem (ValRep LocRep)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb cbzD pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0 wake_exitIn)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64WakeOff (PcOffA RunsOffA pcOffA_add pcOffA_at)
open Spike.Lib.WakeInst (mainW)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.A64WakeMainW (blkW_main nodeW_main placed_c0 placed_past placeVal_cell)

set_option linter.unusedSimpArgs false

/-! ## The parent inside `W` -/

/-- **The parent's states inside `W`**: each block node's (`BlkW`). -/
structure ParentW (W : Frag isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Spike.Lib.Region)
    (F : MachineData → Prop) (cP : Ctl) (A x29 ra tp : BitVec 64) : Prop where
  wcb : BlkW W (fun _ _ => False) exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)
    (cb pfxM)
  wcl : BlkW W (fun _ _ => False) exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cl)
    (cl pfxM)
  wbs : BlkW W (fun _ _ => False) exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .bs)
    (bs pfxM)
  wsp : BlkW W (fun _ _ => False) exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .sp)
    spB

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **Main after its clone inside `W`** (`seg_parent` with every block's
states in `W`, `hW`). -/
theorem seg_parentW {W : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {cP c0 : Ctl} {A x29 ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hrun : LocalRun p cP c0) (hW : ParentW W exe endPc R F cP A x29 ra tp) :
    SegW W (fun _ _ => False) p lbl ms
      (At exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb))
      (At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A x29 ra tp)) := by
  have hin := wake_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, hgap⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  have hg := label_labelGap hp hgap
  rw [show 4 * 15 = 4 * (13 + 1 + 1) from rfl, ofNat4_succ, ofNat4_succ] at hg
  refine (fn_segW (N := pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp)
    (E := fun _ : Unit => pE (_root_.Executable.labels exe).label c0 A x29 ra tp) (fun i => ?_) PN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case cb =>
    refine seg_ndW (by simp [cb]) cbP_ok hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero])) hW.wcb fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hS, h0, h1⟩ := hJ
    rw [pN, cbP_run, cbPT_run]
    have hne : ¬ σ.regs.X0.toBitVec = 0 := fun h => by rw [h] at h0; simp at h0
    refine .inl ⟨PN.cl, ?_, rfl, hS, ?_⟩
    · simp only [pN, rl, Reg64s.getRegOrZr]
      simp [hne, Reg64s.getRegOrZr, Reg64s.getXReg, hg]
      exact fun h => (hne h).elim
    · exact ⟨by simpa [Reg64s.getRegOrZr] using h0, by simpa [Reg64s.getRegOrZr] using h1⟩
  case cl =>
    refine seg_ndW (by simp [cl]) cl_ok hF hR hal hlo hhi
      (code_of hp hend hcl (ofNat4_zero _)) hW.wcl fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hS, h0, h1⟩ := hJ
    rw [pN, cl_run, clT_run]
    have hnv := subs0_nv (x := σ.regs.X0.toBitVec) (by unfold Scc.Sem.Kernel.pidMax at h1; omega)
    refine .inl ⟨PN.bs, ?_, rfl, ?_⟩
    · simp only [pN, rl, hnv, ite_true]
      rw [show 4 * 5 = 4 * (0 + 1 + 1 + 1 + 1 + 1) from rfl]
      simp only [ofNat4_succ, ofNat4_zero]
    · obtain ⟨rfl, h72, h16, h8, htp⟩ := hS
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [pN, JS, Spike.Lib.upd_apply]
  case bs =>
    refine seg_ndW (by simp [bs]) bs_ok hF hR hal hlo hhi
      (code_of hp hend hbs rfl) hW.wbs fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [pN, bs_run, bsT_run]
    refine .inl ⟨PN.sp, ?_, rfl, ?_⟩ <;> simp_all [pN, rl, JS]
  case sp =>
    refine seg_ndW (by simp [spB]) spB_ok hF hR hal hlo hhi
      (code_of hp hend hsp (ofNat4_zero _)) hW.wsp fun σ c hJ => ⟨c0, ?_, ?_⟩
    · obtain ⟨rfl, -⟩ := hJ; exact hrun
    obtain ⟨-, h72, h16, h8, htp⟩ := hJ
    rw [pN, spB_run]
    refine .inr ⟨(), ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [pE, Spike.Lib.upd_apply]

end Seg

/-! ## The parent inside `mainW` -/

/-- **The parent's pcs**: the `cbz` after the clone, `.clone9`'s two
blocks, `.2_spawned6`. -/
def parentRuns : List (String × Nat × Nat) :=
  [(pfxM ++ ".sp6", 14, 15), (pfxM ++ ".clone9", 0, 6), (pfxM ++ ".2_spawned6", 0, 5)]

section Main

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {cv : String} {ty : Ty} {w : TermRun.Word}
  {A x29 ra tp : BitVec 64}

set_option hygiene false in
/-- A parent block's pcs from `parentRuns`: the run `(l, lo, hi)`, the
node's offset `c` in it, the block's definitions. -/
macro "pc_par " l:term:max lo:term:max hi:term:max c:term:max "[" bs:ident,* "]" : tactic =>
  `(tactic| (intro k hk
             simp only [$[$bs:ident],*, List.length_append, List.length_cons, List.length_nil] at hk
             exact pcOffA_add (l := $l) (lo := $lo) (hi := $hi) (c := $c) hruns (by simp [parentRuns])
               (by omega) (by omega)
               (by simp only [pN, Int64.add_assoc] <;> first | rfl | simp | decide)))

/-- **The parent's states are in `mainW`** (`ParentW`): the pcs off the
exits (`hruns`), the states wide (`hwide`); the source past the spawn
(`cP`, off `wlRet`) reads only `cv` (`hfvP`), bound to the flag's locative
`w` with base `A` (`hlP`, `hloc`), whose address the frame's cell `-72`
holds. -/
theorem parentW_main (hruns : RunsOffA (_root_.Executable.labels exe).label parentRuns)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.Off (-72))
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    ParentW (mainW (_root_.Executable.labels exe).label exe Λ lbl) exe endPc R F cP A x29 ra tp where
  wcb := by
    refine blkW_main (by pc_par (pfxM ++ ".sp6") 14 15 14 [cb]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨rfl, h72, -⟩, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-72)).toNat) hfvP hlP hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-72) (by keep_blk [cb, cbzD]) k, h72]
  wcl := by
    refine blkW_main (by pc_par (pfxM ++ ".clone9") 0 6 0 [cl, clp]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨rfl, h72, -⟩, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-72)).toNat) hfvP hlP hloc ?_⟩
    erw [placeVal_cell hA' hR _ rfl, arun_take_slotO (blk := cl pfxM) oP (-72) (by keep_blkO [cl, clp]) k, h72]
  wbs := by
    refine blkW_main (by pc_par (pfxM ++ ".clone9") 0 6 5 [bs]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h72, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-72)).toNat) hfvP hlP hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-72) (by keep_blk [bs]) k, h72]
  wsp := by
    refine blkW_main (by pc_par (pfxM ++ ".2_spawned6") 0 5 0 [spB]) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h72, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-72)).toNat) hfvP hlP hloc ?_⟩
    rw [placeVal_cell hA' hR _ rfl, arun_take_slot (-72) (by keep_blk [spB]) k, h72]

end Main

/-! ## The `exit_group` tail inside `W` -/

/-- **The tail's `svc` node, keeping the source's places**: `exitNx` with
the cell `-32` and `x9` as at the tail's entry. -/
def exitNP (n : ND) : ND :=
  ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ c => σ.regs.X8.toNat = 94 ∧ ∃ σ0, n.J σ0 c ∧
    σ.regs.X0 = σ0.regs.X0 ∧ σ.slot (-32) = σ0.slot (-32) ∧ σ.regs.X9 = σ0.regs.X9⟩

section SegX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {A ra tp : BitVec 64}

/-- **The loop's return does not come back, inside `W`** (`seg_waitExit`
with the tail block's states (`hW0`) and the `svc`'s (`hW1`) in `W`). -/
theorem seg_waitExitW {W : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {x29 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ s c, Spike.Lib.A64.WaitLoop.Past c0 x e ty Rd c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hW0 : BlkW W (fun _ _ => False) exe endPc R F (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 8))
    (hW1 : NodeW W (fun _ _ => False) exe endPc R F (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret))) :
    SegW W (fun _ _ => False) p lbl ms (At exe endPc R F (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret))
      (fun _ _ => False) := by
  have hin := wake_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  refine SegW.seq (Q := At exe endPc R F (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret))) ?_
    (exit_ndW hK (code_of hp hend hin.2 ?_) hW1 (fun _ _ h => h.1) ?_)
  · refine (seg_ndW (W := W) (K := fun _ _ => False) (n := Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret)
      (N := fun _ : Unit => exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret))
      (E := fun e : Empty => e.elim) (by simp [exitTail]) (exitTail_ok (lo := 0) (hi := 16) rfl rfl) hF hR hal
      hlo hhi (code_of hp hend hin.1 ?_) hW0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]
    rw [exitTail_run]
    refine ⟨rfl, by simp [SO.le, exitNP], rfl, σ, hJ, rfl, ?_, rfl⟩
    show Spike.Lib.upd σ.slot (0 + (8 : Int64).toInt) σ.regs.X0.toBitVec (-32) = σ.slot (-32)
    simp [Spike.Lib.upd_apply]
  · show _ = Int64.ofBitVec ra + 4 + 4 + 4; rw [hra]; simp only [ofNat4_succ, ofNat4_zero]
  · rintro s c σ ⟨he, hn, hdc, hpc, σ', hA, hD, -⟩ ⟨-, σ0, hJ0, hx0, -, -⟩ hreg
    obtain ⟨hP, h0, -⟩ := hJ0
    have hv : σ.regs.X0.toNat = 0 := by
      rw [hx0]; show σ0.regs.X0.toBitVec.toNat = 0; rw [h0]; rfl
    rw [hv]
    refine SysOk.exitGroup_main fun hab => hexit s c hP ⟨he, hn, hdc, ?_, σ', hA, hD, ?_⟩ hab
    · rw [hpc]; show Int64.ofBitVec ra + 4 + 4 + 4 = _; rw [hra]
    · show σ'.regs.X0.toBitVec = 0#64
      rw [← hA.regs, hreg, hx0]; exact h0

end SegX

/-! ## The `exit_group` tail inside `mainW` -/

/-- **The tail's pcs**: the four instructions at `scc_rt_main`'s return
point. -/
def exitRuns : List (String × Nat × Nat) := [(mainSp0, 0, 4)]

/-- **The tail's prefixes keep the cell `-32` and `x9`** (from offsets
`⟨0, []⟩`: it stores only at `sp + 8`). -/
theorem exitTail_keep (lab : Label → Int64) (pc : Int64) (σ : AS) (k : Nat) :
    (arun lab ((exitTail 8).take k) ⟨pc, ⟨0, []⟩, σ⟩).σ.slot (-32) = σ.slot (-32) ∧
      (arun lab ((exitTail 8).take k) ⟨pc, ⟨0, []⟩, σ⟩).σ.regs.getXReg .X9 = σ.regs.getXReg .X9 := by
  refine ⟨arun_take_slotO ⟨0, []⟩ (-32) ?_ k pc σ, arun_take_reg .X9 ?_ k _⟩
  · rintro d hd pc σ
    simp only [exitTail, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp only [spStr, RW.dir, AI.toDir] <;> dstep_keep <;>
      try simp [Spike.Lib.upd_apply, Spike.Lib.rm, Spike.Lib.A64.Flow.regDst] <;> try rfl
  · rintro d hd ⟨pc, o, σ⟩
    simp only [exitTail, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;> simp only [spStr, RW.dir, AI.toDir] <;> dstep_keep

section MainX

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} {c0 : Ctl} {x cv : String} {e : Expr}
  {ty : Ty} {w : TermRun.Word} {A x29 ra tp : BitVec 64}

/-- **The tail block's states are in `mainW`**: the source past the load,
`cv` in the (dead) loop frame's cell `-32`, `x` in `x9`; the tail stores
only at `sp + 8`. -/
theorem exitW0_main (hruns : RunsOffA (_root_.Executable.labels exe).label exitRuns)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.Off (-32))
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    BlkW (mainW (_root_.Executable.labels exe).label exe Λ lbl) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret) (exitTail 8) := by
  refine blkW_main ?_ hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
  · intro k hk
    simp only [exitTail, List.length_cons, List.length_nil] at hk
    exact pcOffA_add (l := mainSp0) (lo := 0) (hi := 4) (c := 0) hruns (by simp [exitRuns]) (by omega) (by omega)
      (by show Int64.ofBitVec ra = _; rw [hra, ofNat4_zero])
  obtain ⟨⟨w', ⟨-, hw'⟩, rfl⟩, -, -, -, -, h32, h9⟩ := hJ
  obtain ⟨k32, k9⟩ := exitTail_keep (_root_.Executable.labels exe).label
    (Spike.Lib.A64.WaitLoop.E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret).pc σ k
  refine ⟨hE, placed_past (pc := .slot (R.addr (-32)).toNat) hfvE hxc hl hloc ?_ hw' ?_⟩
  · erw [placeVal_cell hA' hR _ rfl, k32, h32]
  · show (m.regs.getXReg .X9).toBitVec = 1#64
    erw [hA'.regs, k9]; exact h9

/-- **The tail's `svc` state is in `mainW`**: as at the tail's entry (the
cell `-32` and `x9` kept, `exitNP`). -/
theorem exitW1_main (hruns : RunsOffA (_root_.Executable.labels exe).label exitRuns)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.Off (-32))
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    NodeW (mainW (_root_.Executable.labels exe).label exe Λ lbl) (fun _ _ => False) exe endPc R F
      (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret)) := by
  refine nodeW_main (pcOffA_at (l := mainSp0) (lo := 0) (hi := 4) (c := 3) hruns (by simp [exitRuns]) (by omega)
    (by omega) (by show Int64.ofBitVec ra + 4 + 4 + 4 = _; rw [hra]; simp only [ofNat4_succ, ofNat4_zero])) hwide
    fun s σ c _ hA _ hJ => ?_
  obtain ⟨-, σ0, ⟨⟨w', ⟨-, hw'⟩, rfl⟩, -, -, -, -, h32, h9⟩, -, k32, k9⟩ := hJ
  refine ⟨hE, placed_past (pc := .slot (R.addr (-32)).toNat) hfvE hxc hl hloc ?_ hw' ?_⟩
  · rw [placeVal_cell hA hR _ rfl, k32, h32]
  · show (s.st.1.regs.getXReg .X9).toBitVec = 1#64
    rw [hA.regs]; show σ.regs.X9.toBitVec = _; rw [k9]; exact h9

end MainX

end Spike.Lib.A64WakeMainSegW
