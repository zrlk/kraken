/-
**wake's main after its `clone` inside `mainW`: the parent and the exit
tail** (x86-64): the x64 twin of
`Spike/Lib/A64WakeMainSegW.lean`. The two ends of main's post-spawn path
(`MainPost.seg_mainPost`) as `SegW` segments inside any `W`, given every
node's states in it, and those node obligations at
`W := X64WakeInst.mainW lab exe Λ lbl`.

- `ParentW`, `seg_parentW`: `Parent.seg_parent` inside `W` (the test row's
  states and each of the four blocks').
- `parent_keep`, `parentW_main`: the parent's blocks inside `mainW`: the
  source `cP` (past the spawn, at its tail call) reads only `cv`, placed at
  the frame's cell `-16` (the published cell's address `A`).
- `exitN`: the loop's return `WaitLoop.E … .ret` with `%rbp`'s offset (`40`,
  `scc_rt_main`'s frame); `exitNP`: the tail's `syscall` node, keeping the
  cells `-16` and `-24` (where the source past the load is placed).
- `seg_waitExitW`: `MainPost.seg_waitExit` inside `W`.
- `xExit_slot`, `exitW0_main`, `exitW1_main`: the tail's states inside
  `mainW`.

The pcs are off the exits by `X64WakeRunsOffPost` (`parentRuns`,
`exitRuns`).
-/
import Spike.Lib.X64WakeMainW
import Spike.Lib.X64WakeMainPost
import Spike.Lib.X64WakeRunsOffPost
import Spike.Lib.X64Dead

namespace Spike.Lib.X64WakeMainSegW

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep LocRep)
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays code_field)
open Spike.Lib.X64.WakePh.WcClone (oW x21L)
open Spike.Lib.X64.WakePh.Parent
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64.WakeRunsOff (parentRuns exitRuns)
open Spike.Lib.X64WakeOff (PcOffA RunsOffA pcOffA_add pcOffA_at)
open Spike.Lib.X64WakeInst (mainW)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64WakeMainW (blkW_main nodeW_main placed_c0 placed_past placeVal_cell)

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over concrete blocks (as
`X64WakeMainW`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.X64.arun, Spike.Lib.X64.dstep, Spike.Lib.X64.classify, Spike.Lib.X64.RegOnly,
    Spike.Lib.X64.AI.so, Spike.Lib.X64.soReg,
    Spike.Lib.X64.regDst, Spike.Lib.X64.regRes, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp, AddrExpr.interp, Spike.Lib.X64.SO.get,
    Spike.Lib.X64.SO.set, Spike.Lib.X64.SO.kill, Spike.Lib.X64.SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply,
    Spike.Lib.X64.Reg64s.get_low64, Spike.Lib.X64.BlockSpec.AI.step_ld',
    Spike.Lib.X64.BlockSpec.AI.step_st', Spike.Lib.X64.BlockSpec.AI.step_push',
    Spike.Lib.X64.BlockSpec.AI.step_pop', Spike.Lib.X64.BlockSpec.AI.step_reg',
    Spike.Lib.X64.BlockSpec.AI.step_jmp', Spike.Lib.X64.BlockSpec.AI.step_jcc',
    Spike.Lib.X64.BlockSpec.AI.step_call', Spike.Lib.X64.Reg64s.get64_set64_ne,
    Spike.Lib.X64.Reg64s.get64_set64_self])

/-! ## The parent inside `W` -/

/-- **The parent's states inside `W`**: the test row's (`NodeW`) and each
block node's (`BlkW`). -/
structure ParentW (W : Frag isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (cP : Ctl) (A fp ra tp : BitVec 64) : Prop where
  wts : NodeW W (fun _ _ => False) exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
  wje : BlkW W (fun _ _ => False) exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .je) jeB
  wx22 : BlkW W (fun _ _ => False) exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .x22) x22B
  wbs : BlkW W (fun _ _ => False) exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .bs) bsB
  wsp : BlkW W (fun _ _ => False) exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .sp) spB

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **Main after its clone inside `W`** (`seg_parent` with every node's
states in `W`, `hW`). -/
theorem seg_parentW {W : Frag isa} {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : parentIn cells = true)
    {cP c0 : Ctl} {A fp ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) (hrun : LocalRun p cP c0)
    (hW : ParentW W exe endPc R F cP A fp ra tp) :
    SegW W (fun _ _ => False) p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A fp ra tp)) := by
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, hgap⟩, b22⟩, bbs⟩, bsp⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hg : lab x22L = lab x21L + Int64.ofNat 53 := label_labelGap_lays hp hgap
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l) b :=
    fun h s he hn => by simpa using code h s he hn
  refine (fn_segW (N := pN lab cP A fp ra tp) (E := fun _ : Unit => pE lab c0 A fp ra tp) (fun i => ?_)
    PN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_ndW hF (fun s he hn => code bts s he hn) hW.wts
      fun σ c hJ af => ⟨c, .refl c, .inl ⟨PN.je, ?_, rfl, ?_⟩⟩
    · show lab x21L + 51 = lab x21L + Int64.ofNat 48 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0, h1⟩ := hJ
      refine ⟨hS, ⟨h0, h1⟩, ?_⟩
      rw [testStep_zf, BitVec.and_self]
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h; rw [h] at h0; simp at h0
  case je =>
    refine seg_ndW (by simp [jeB]) jeB_ok hF hR hlo hhi (fun s he hn => code bje s he hn) hW.wje
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.x22, ?_, rfl, hJ.1, hJ.2.1⟩⟩
    obtain ⟨-, -, hz⟩ := hJ
    show lab x22L = (arun lab jeB ⟨lab x21L + 51, oW, σ⟩).pc
    rw [jeB_run]
    simp only [hz, hg, Bool.false_eq_true, ite_false, Int64.add_assoc]; rfl
  case x22 =>
    refine seg_ndW (by simp [x22B]) x22B_ok hF hR hlo hhi (fun s he hn => code0 b22 s he hn) hW.wx22
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.bs, ?_, rfl, ?_⟩⟩
    · obtain ⟨-, -, h1⟩ := hJ
      have hm : σ.regs.rax.toBitVec.msb = false := by
        have : (σ.regs.get64 .rax).toNat < 2 ^ 63 := by unfold Scc.Sem.Kernel.pidMax at h1; omega
        rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]
        exact this
      show lab x22L + 20 = (arun lab x22B ⟨lab x22L, oW, σ⟩).pc
      rw [x22B_run]; simp only [hm, Bool.false_eq_true, ite_false]
    · obtain ⟨⟨rfl, h16, h0, h8, htp⟩, -⟩ := hJ
      show JS c A fp ra tp (arun lab x22B ⟨lab x22L, oW, σ⟩).σ c
      rw [x22B_run]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp [upd, h16, h0, h8, htp, Reg64s.set64]
  case bs =>
    refine seg_ndW (by simp [bsB]) bsB_ok hF hR hlo hhi (fun s he hn => code bbs s he hn) hW.wbs
      fun σ c hJ => ⟨c, .refl c, .inl ⟨PN.sp, ?_, rfl, ?_⟩⟩
    · show lab spL = (arun lab bsB ⟨lab x22L + 20, oW, σ⟩).pc
      rw [bsB_run]
    · show JS cP A fp ra tp (arun lab bsB ⟨lab x22L + 20, oW, σ⟩).σ c
      rw [bsB_run]; exact hJ
  case sp =>
    refine seg_ndW (by simp [spB]) spB_ok hF hR hlo hhi (fun s he hn => code0 bsp s he hn) hW.wsp
      fun σ c hJ => ⟨c0, ?_, .inr ⟨(), ?_, ?_, ?_⟩⟩
    · obtain ⟨rfl, -⟩ := hJ; exact hrun
    · show lab "wc_waitLoop" = (arun lab spB ⟨lab spL, oW, σ⟩).pc
      rw [spB_run]
    · show SO.le ⟨8, []⟩ (arun lab spB ⟨lab spL, oW, σ⟩).so = true
      rw [spB_run]; rfl
    · obtain ⟨-, h16, h0, h8, htp⟩ := hJ
      show c0 = c0 ∧ _
      simp only [pN]
      rw [spB_run]
      refine ⟨trivial, ?_, ?_, h8, ?_⟩ <;>
        simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne, h16, h0]
      simpa [Reg64s.set64] using htp

end Seg

/-! ## The parent inside `mainW` -/

/-- **The parent's block prefixes keep the cell `-16`** (from `oW`: `.x22`
stores only at `-56`). -/
theorem parent_keep (l : String → Int64) (pc : Int64) (σ : AS) {blk : List (Directive × Nat)}
    (hb : blk = jeB ∨ blk = x22B ∨ blk = bsB ∨ blk = spB) {k : Nat} (hk : k < blk.length) :
    (arun l (blk.take k) ⟨pc, oW, σ⟩).σ.slot (-16) = σ.slot (-16) := by
  rcases hb with rfl | rfl | rfl | rfl <;> simp only [jeB, x22B, bsB, spB] at hk ⊢ <;>
    simp only [List.length_zip, List.length_cons, List.length_nil] at hk <;>
    rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

set_option hygiene false in
/-- A parent block's pcs from `parentRuns`: the run `(l, lo, hi)`, the
node's offset `c` in it, the block. -/
local macro "pc_par " l:term:max lo:term:max hi:term:max c:term:max b:term:max : tactic =>
  `(tactic| (intro k hk
             exact pcOffA_add (l := $l) (lo := $lo) (hi := $hi) (c := $c) hruns (by simp [parentRuns])
               (by omega) ((show ∀ k < ($b).length, $c + cellOff $b k < $hi by decide) k hk)
               (by simp only [pN]; first | rfl | exact (ofNat_zero' _).symm)))

section Main

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {cP : Ctl} {cv : String} {ty : Ty} {w : TermRun.Word}
  {A fp ra tp : BitVec 64}

/-- **The parent's states are in `mainW`** (`ParentW`): the pcs off the
exits (`hruns`), the states wide (`hwide`); the source past the spawn
(`cP`, off `wlRet`) reads only `cv` (`hfvP`), bound to the flag's locative
`w` with base `A` (`hlP`, `hloc`), whose address the frame's cell `-16`
holds. -/
theorem parentW_main (hruns : RunsOffA (_root_.Executable.labels exe).label parentRuns)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (hR : R.Off (-16))
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    ParentW (mainW (_root_.Executable.labels exe).label exe Λ lbl) exe endPc R F cP A fp ra tp where
  wts := by
    refine nodeW_main (pcOffA_at hruns (l := x21L) (lo := 48) (hi := 53) (c := 48) (by simp [parentRuns])
      (by omega) (by omega) rfl) hwide fun s σ c _ hA _ hJ => ?_
    obtain ⟨⟨rfl, h16, -⟩, -⟩ := hJ
    exact ⟨hcP, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfvP hlP hloc (by rw [placeVal_cell hA hR _ rfl, h16])⟩
  wje := by
    refine blkW_main (by pc_par x21L 48 53 51 jeB) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨rfl, h16, -⟩, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfvP hlP hloc ?_⟩
    erw [placeVal_cell hA' hR _ rfl, parent_keep _ _ _ (.inl rfl) hk, h16]
  wx22 := by
    refine blkW_main (by pc_par x22L 0 22 0 x22B) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨⟨rfl, h16, -⟩, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfvP hlP hloc ?_⟩
    erw [placeVal_cell hA' hR _ rfl, parent_keep _ _ _ (.inr (.inl rfl)) hk, h16]
  wbs := by
    refine blkW_main (by pc_par x22L 0 22 20 bsB) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h16, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfvP hlP hloc ?_⟩
    erw [placeVal_cell hA' hR _ rfl, parent_keep _ _ _ (.inr (.inr (.inl rfl))) hk, h16]
  wsp := by
    refine blkW_main (by pc_par spL 0 13 0 spB) hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
    obtain ⟨rfl, h16, -⟩ := hJ
    refine ⟨hcP, placed_c0 (pc := .slot (R.addr (-16)).toNat) hfvP hlP hloc ?_⟩
    erw [placeVal_cell hA' hR _ rfl, parent_keep _ _ _ (.inr (.inr (.inr rfl))) hk, h16]

end Main

/-! ## The `exit_group` tail inside `W` -/

/-- **The loop's return with `%rbp`'s offset**: `WaitLoop.E … .ret` at
offsets `⟨8, [(.rbp, 40)]⟩` (`scc_rt_main`'s `%rbp`, `fp = R.addr 40`). -/
def exitN (c0 : Ctl) (x : String) (e : Expr) (ty : Ty) (Rd : TermRun.Word → Prop) (A fp ra tp sp : BitVec 64) :
    ND :=
  ⟨Int64.ofBitVec ra, ⟨8, [(.rbp, 40)]⟩, (WaitLoop.E c0 x e ty Rd A fp ra tp sp .ret).J⟩

/-- **The tail's `syscall` node, keeping the source's places**: `xExitNx`
with the cells `-16` and `-24` as at the tail's entry. -/
def exitNP (n : ND) : ND :=
  ⟨n.pc + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5, n.o, fun σ c => σ.regs.rax.toNat = 231 ∧ ∃ σ0, n.J σ0 c ∧
    σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec ∧ σ.slot (-16) = σ0.slot (-16) ∧ σ.slot (-24) = σ0.slot (-24)⟩

/-- **The tail's prefixes keep every cell but `24`** (from `%rbp` at `40`:
it stores only at `-16(%rbp)`). -/
theorem xExit_slot (l : String → Int64) (pc : Int64) (σ : AS) (k : Nat) {j : Int} (hj : j ≠ 24) :
    (arun l ((xExit (-16) 4 4 5).take k) ⟨pc, ⟨8, [(.rbp, 40)]⟩, σ⟩).σ.slot j = σ.slot j := by
  simp only [xExit]
  rcases k with _|_|_|k <;> arun_simp <;> intro h <;> exact absurd (by omega) hj

section SegX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {kp : Nat} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {A fp ra tp sp : BitVec 64}

/-- **The loop's return does not come back, inside `W`** (`seg_waitExit`
with the tail block's states (`hW0`) and the `syscall`'s (`hW1`) in `W`). -/
theorem seg_waitExitW {W : Frag isa} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : exitIn cells mainX2 (-16) 4 4 5 = true)
    {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hfp : fp = R.addr 40)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, WaitLoop.Past c0 x e ty Rd c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hW0 : BlkW W (fun _ _ => False) exe endPc R F (exitN c0 x e ty Rd A fp ra tp sp) (xExit (-16) 4 4 5))
    (hW1 : NodeW W (fun _ _ => False) exe endPc R F (exitNP (exitN c0 x e ty Rd A fp ra tp sp))) :
    SegW W (fun _ _ => False) p lbl ms (At exe endPc R F (WaitLoop.E c0 x e ty Rd A fp ra tp sp .ret))
      (fun _ _ => False) := by
  rw [exitIn, Bool.and_eq_true] at hin
  refine (SegW.seq (Q := At exe endPc R F (exitNP (exitN c0 x e ty Rd A fp ra tp sp))) ?_
    (exit_ndW hK (code_field hp hend hin.2 ?_) hW1 (fun _ _ h => h.1) ?_)).mono_pre
    fun s c h => WaitLoop.At.rbpOf h fun σ c hJ => by
      show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.1, hfp]
  · refine (seg_ndW (W := W) (K := fun _ _ => False) (n := exitN c0 x e ty Rd A fp ra tp sp)
      (N := fun _ : Unit => exitNP (exitN c0 x e ty Rd A fp ra tp sp))
      (E := fun e : Empty => e.elim) (by simp [xExit]) (xExit_ok (lo := 0) (hi := 32) (-16) 4 4 5 (by decide))
      hF hR hlo hhi (code_field hp hend hin.1 ?_) hW0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    · show _ = Int64.ofBitVec ra; rw [hra, ofNat_zero']
    obtain ⟨h1, h2, h3⟩ := xExit_run (_root_.Executable.labels exe).label (Int64.ofBitVec ra) 8 40 σ (-16) 4 4 5
    refine ⟨h1.symm, ?_, h2, σ, hJ, h3, xExit_slot _ _ _ 3 (by decide), xExit_slot _ _ _ 3 (by decide)⟩
    simp only [xExit]; x64simp; simp [exitN, exitNP, SO.le, lk] <;> rfl
  · show _ = Int64.ofBitVec ra + _ + _ + _
    rw [ofNat_add', ofNat_add', hra]
  · rintro s c σ ⟨he, hn, hdc, hpc, σ', hA, hD, -⟩ ⟨-, σ0, hJ0, hx0, -, -⟩ hreg
    obtain ⟨hP, h0, -⟩ := hJ0
    have hv : σ.regs.rdi.toNat = 0 := by
      show σ.regs.rdi.toBitVec.toNat = 0
      rw [hx0, h0]; rfl
    rw [hv]
    refine SysOk.exitGroup_main fun hab => hexit s c hP ⟨he, hn, hdc, ?_, σ', hA, hD, ?_⟩ hab
    · rw [hpc]; show Int64.ofBitVec ra + _ + _ + _ = _; rw [hra]; rfl
    · show σ'.regs.rdi.toBitVec = 0#64
      rw [← hA.regs, hreg, hx0]; exact h0

end SegX

/-! ## The `exit_group` tail inside `mainW` -/

section MainX

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ms : MemSide isa} {c0 : Ctl} {x cv : String} {e : Expr}
  {ty tyv : Ty} {w : TermRun.Word} {A fp ra tp sp : BitVec 64}

/-- **The tail block's states are in `mainW`**: the source past the load,
`cv` in the (dead) loop frame's cell `-16`, `x` in its cell `-24`; the tail
stores only at `24`. -/
theorem exitW0_main (hruns : RunsOffA (_root_.Executable.labels exe).label exitRuns)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (h16 : R.Off (-16)) (h24 : R.Off (-24))
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    BlkW (mainW (_root_.Executable.labels exe).label exe Λ lbl) (fun _ _ => False) exe endPc R F
      (exitN c0 x e ty (WaitLoop.RdOne (ms := ms) lbl) A fp ra tp sp) (xExit (-16) 4 4 5) := by
  refine blkW_main ?_ hwide fun s σ c _ _ _ hJ k hk m hA' => ?_
  · intro k hk
    exact pcOffA_add (l := mainX2) (lo := 0) (hi := 15) (c := 0) hruns (by simp [exitRuns]) (Nat.zero_le _)
      ((show ∀ k < (xExit (-16) 4 4 5).length, 0 + cellOff (xExit (-16) 4 4 5) k < 15 by decide) k hk)
      (by show Int64.ofBitVec ra = _; rw [hra, ofNat_zero'])
  obtain ⟨⟨w', ⟨-, hw'⟩, rfl⟩, -, -, -, -, k16, k24⟩ := hJ
  refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .slot (R.addr (-24)).toNat) hfvE hxc hl
    hloc ?_ hw' ?_⟩
  · erw [placeVal_cell hA' h16 _ rfl, xExit_slot _ _ _ k (by decide), k16]
  · erw [placeVal_cell hA' h24 _ rfl, xExit_slot _ _ _ k (by decide), k24]; rfl

/-- **The tail's `syscall` state is in `mainW`**: as at the tail's entry
(the cells `-16` and `-24` kept, `exitNP`). -/
theorem exitW1_main (hruns : RunsOffA (_root_.Executable.labels exe).label exitRuns)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s) (h16 : R.Off (-16)) (h24 : R.Off (-24))
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0) :
    NodeW (mainW (_root_.Executable.labels exe).label exe Λ lbl) (fun _ _ => False) exe endPc R F
      (exitNP (exitN c0 x e ty (WaitLoop.RdOne (ms := ms) lbl) A fp ra tp sp)) := by
  refine nodeW_main (pcOffA_at (l := mainX2) (lo := 0) (hi := 15) (c := 13) hruns (by simp [exitRuns]) (by omega)
    (by omega) (by show Int64.ofBitVec ra + _ + _ + _ = _; rw [hra, Int64.add_assoc, Int64.add_assoc]; rfl)) hwide
    fun s σ c _ hA _ hJ => ?_
  obtain ⟨-, σ0, ⟨⟨w', ⟨-, hw'⟩, rfl⟩, -, -, -, -, k16, k24⟩, -, e16, e24⟩ := hJ
  refine ⟨hE, placed_past (pc := .slot (R.addr (-16)).toNat) (px := .slot (R.addr (-24)).toNat) hfvE hxc hl
    hloc ?_ hw' ?_⟩
  · rw [placeVal_cell hA h16 _ rfl, e16, k16]
  · rw [placeVal_cell hA h24 _ rfl, e24, k24]; rfl

end MainX

end Spike.Lib.X64WakeMainSegW

/-- info: 'Spike.Lib.X64WakeMainSegW.seg_parentW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSegW.seg_parentW

/-- info: 'Spike.Lib.X64WakeMainSegW.parentW_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSegW.parentW_main

/-- info: 'Spike.Lib.X64WakeMainSegW.seg_waitExitW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSegW.seg_waitExitW

/-- info: 'Spike.Lib.X64WakeMainSegW.exitW0_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSegW.exitW0_main

/-- info: 'Spike.Lib.X64WakeMainSegW.exitW1_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainSegW.exitW1_main
