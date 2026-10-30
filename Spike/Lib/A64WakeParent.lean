/-
**wake.w on AArch64: main after its `clone`** (the spawn's
parent half): back from main's `clone` (`Spike.Lib.WakePreA.cloneAt`, the
`svc` at `wc_main`'s `.sp6` plus 13 instructions) with the child's id
`0 < x0 < pidMax` (`Spike.Lib.A64Handover.parent_st`), main runs

    cbz x0, .child9                 -- not taken
    .clone9: str x0, [sp, #48]; ldr x9, [sp, #48]; movz x10, #0
             subs xzr, x9, x10; b.lt .1_spawnfail5   -- not taken
             b .2_spawned6
    .2_spawned6: ldr x0, [sp, #8]; ldr x29, [sp, #64]; ldr x30, [sp, #72]
                 add sp, sp, #80; b wc_waitLoop      -- the tail call

in its frame (`sp` at offset `-80`, the published cell's address at `-72`,
the caller's `x29` and the return address at `-16`/`-8`), to `wc_waitLoop`'s
entry with `x0` the cell, `sp` at offset 0, `x29`/`x30` the caller's: the
node `.e` of `Spike.Lib.A64.WaitLoop.N` (`JE`). The source (past its
`spawn`, at `tail waitLoop c`) takes its tail call on the last block
(`hrun`; `localStep_tailCall` gives the step).

- `pN pfx lab cP A x29 ra tp`: the nodes (`PN`: `cb`, `cl`, `bs`, `sp`);
  `pE`: the exit, `WaitLoop.N … .e`'s pc, offsets and invariant.
- `parentIn`, `wake_parentIn`: the blocks in wake's program.
- `seg_parent`: main from `pN .cb` (past the clone) to `pE`.
- `localStep_tailCall`: the source's tail call `tail f [] a []` enters `f`'s
  body on `a`'s words.
-/
import Spike.Lib.A64WakeChild
import Spike.Lib.A64WaitLoop

namespace Spike.Lib.A64.Flow.Worker.Wake.Parent

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (cbT cbT_eq cb cbzD dstep_cbz pfxM)
open Spike.Lib.A64.WakeLabels (wakeProg)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- The offsets in main's frame. -/
abbrev oP : SO := ⟨-80, []⟩

/-- The `cbz` (template), in main's frame. -/
def cbPT : List Directive := parseAArch64("cbz x0, pfx.child9")

/-- `.clone9`'s first block (template). -/
def clT : List Directive := parseAArch64("str x0, [sp, #48]
ldr x9, [sp, #48]
movz x10, #0
subs xzr, x9, x10
b.lt pfx.1_spawnfail5")

/-- `clT` without its branch. -/
def clp : List Directive := parseAArch64("str x0, [sp, #48]
ldr x9, [sp, #48]
movz x10, #0
subs xzr, x9, x10")

/-- The branch to `.2_spawned6` (template). -/
def bsT : List Directive := parseAArch64("b pfx.2_spawned6")

/-- `.2_spawned6`: the frame's exit and the tail call. -/
def spB : List Directive := parseAArch64("ldr x0, [sp, #8]
ldr x29, [sp, #64]
ldr x30, [sp, #72]
add sp, sp, #80
b wc_waitLoop")

block_spec cbPT (-80) 0 oP cbPT
block_spec clT (-80) 0 oP clT
block_spec bsT (-80) 0 oP bsT
block_spec spB (-80) 0 oP spB

theorem cbPT_eq : cbPT = [] ++ [cbzD .X0 "pfx.child9"] := by decide
theorem clT_eq : clT = clp ++ [bcD .LT "pfx.1_spawnfail5"] := by decide
theorem bsT_eq : bsT = [] ++ [bD "pfx.2_spawned6"] := by decide

/-- `.clone9`'s first block at prefix `pfx`. -/
def cl (pfx : String) : List Directive := clp ++ [bcD .LT (pfx ++ ".1_spawnfail5")]
/-- The branch to `.2_spawned6` at prefix `pfx`. -/
def bs (pfx : String) : List Directive := [] ++ [bD (pfx ++ ".2_spawned6")]

theorem cbP_ok {pfx : String} : okBlk (-80) 0 oP (cb pfx) = true := by
  rw [cb, okBlk_snoc (t := cbzD .X0 (pfx ++ ".child9")) (t' := cbzD .X0 "pfx.child9") (fun _ => rfl), ← cbPT_eq]
  exact cbPT_ok
theorem cl_ok {pfx : String} : okBlk (-80) 0 oP (cl pfx) = true := by
  rw [cl, okBlk_snoc (t := bcD .LT (pfx ++ ".1_spawnfail5")) (t' := bcD .LT "pfx.1_spawnfail5") (fun _ => rfl),
    ← clT_eq]
  exact clT_ok
theorem bs_ok {pfx : String} : okBlk (-80) 0 oP (bs pfx) = true := by
  rw [bs, okBlk_snoc (t := bD (pfx ++ ".2_spawned6")) (t' := bD "pfx.2_spawned6") (fun _ => rfl), ← bsT_eq]
  exact bsT_ok

theorem cbP_run {pfx : String} (lab : Label → Int64) (am : AM) :
    arun lab (cb pfx) am = arun (rl lab "pfx.child9" (pfx ++ ".child9")) cbPT am := by
  rw [cbPT_eq]; exact arun_snoc (by decide) (dstep_cbz _ _ _ _) am
theorem cl_run {pfx : String} (lab : Label → Int64) (am : AM) :
    arun lab (cl pfx) am = arun (rl lab "pfx.1_spawnfail5" (pfx ++ ".1_spawnfail5")) clT am := by
  rw [clT_eq]; exact arun_snoc (by decide) (dstep_bc _ _ _ _) am
theorem bs_run {pfx : String} (lab : Label → Int64) (am : AM) :
    arun lab (bs pfx) am = arun (rl lab "pfx.2_spawned6" (pfx ++ ".2_spawned6")) bsT am := by
  rw [bsT_eq]; exact arun_snoc (by decide) (dstep_b _ _ _) am

/-- The parent's blocks in wake's program. -/
abbrev parentIn : Bool :=
  blockAt wakeProg (pfxM ++ ".sp6") 14 (cb pfxM) && labelGap wakeProg (pfxM ++ ".sp6") (pfxM ++ ".clone9") 15 &&
    blockAt wakeProg (pfxM ++ ".clone9") 0 (cl pfxM) && blockAt wakeProg (pfxM ++ ".clone9") 5 (bs pfxM) && blockAt wakeProg (pfxM ++ ".2_spawned6") 0 spB

theorem wake_parentIn : parentIn = true := by decide +kernel

/-- `subs xzr, x, #0` of a non-negative `x`: `n = v`, `b.lt` not taken. -/
theorem subs0_nv {x : BitVec 64} (h : x.toNat < 2 ^ 63) :
    (StatusFlags.subs x x 0#64).n = (StatusFlags.subs x x 0#64).v := by
  have hm : x.msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  simp [StatusFlags.subs, hm]

/-! ## The nodes -/

/-- In main's frame: the source at `cP`, the cell's address `A`, the
caller's `x29` and return address in their cells, the thread pointer. -/
def JS (cP : Ctl) (A x29 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  c = cP ∧ σ.slot (-72) = A ∧ σ.slot (-16) = x29 ∧ σ.slot (-8) = ra ∧ σ.regs.TPIDR_EL0.toBitVec = tp

/-- Back from the clone: `JS` and `x0` the child's id, `0 < x0 < pidMax`. -/
def JP (cP : Ctl) (A x29 ra tp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  JS cP A x29 ra tp σ c ∧ 0 < σ.regs.X0.toBitVec.toNat ∧ σ.regs.X0.toBitVec.toNat < Scc.Sem.Kernel.pidMax

/-- The parent's internal nodes. -/
inductive PN where
  | cb | cl | bs | sp

/-- **The parent's nodes**: past the clone (`cb`), `.clone9` (`cl`), its
branch (`bs`), `.2_spawned6` (`sp`). -/
def pN (pfx : String) (lab : Label → Int64) (cP : Ctl) (A x29 ra tp : BitVec 64) : PN → ND
  | .cb => ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 13) + 4, oP, JP cP A x29 ra tp⟩
  | .cl => ⟨lab (pfx ++ ".clone9"), oP, JP cP A x29 ra tp⟩
  | .bs => ⟨lab (pfx ++ ".clone9") + Int64.ofNat (4 * 5), oP, JS cP A x29 ra tp⟩
  | .sp => ⟨lab (pfx ++ ".2_spawned6"), oP, JS cP A x29 ra tp⟩

/-- **The exit**: `wc_waitLoop`'s entry (`WaitLoop.N … .e`), the source at
`c0`. -/
def pE (lab : Label → Int64) (c0 : Ctl) (A x29 ra tp : BitVec 64) : ND :=
  ⟨lab "wc_waitLoop", WaitLoop.oE, WaitLoop.JE c0 A x29 ra tp⟩

/-- `pE` is `wc_waitLoop`'s entry node. -/
theorem pE_eq (lab : Label → Int64) (pfx : String) (c0 : Ctl) (x : String) (e : Expr) (ty : Ty)
    (Rd : TermRun.Word → Prop) (A x29 ra tp : BitVec 64) :
    pE lab c0 A x29 ra tp = WaitLoop.N lab pfx c0 x e ty Rd A x29 ra tp .e := rfl

/-! ## The source's tail call -/

/-- **`tail f [] a []`** enters `f`'s body with its argument bound to `a`'s
words. -/
theorem localStep_tailCall {p : Prog} {c : Ctl} {f : String} {is : List String} {a : CoreTerm.At} {d : Decl}
    {t : Ty} {ws : List TermRun.Word} (ht : c.term = .tail f is a [])
    (hd : p.find? (·.name == f) = some d) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStep p c ⟨d.body, [(d.arg, TermRun.close [] d.argTy, ws)], none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th hg ht' he hσ _
  subst hg
  simp [TermRun.tstep, ht', ht, TermRun.enter, hd, he, ha, hσ, TermRun.ol]

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **Main after its clone is one segment** in any valid layout of
`wakeProg`, from `pN .cb` to `wc_waitLoop`'s entry: the `cbz` and the
`b.lt` are not taken (`x0` the child's id), the frame is left and the
source takes its tail call (`hrun`). -/
theorem seg_parent (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {cP c0 : Ctl} {A x29 ra tp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hrun : LocalRun p cP c0) :
    Seg p lbl ms (At exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb))
      (At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A x29 ra tp)) := by
  have hin := wake_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, hgap⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  have hg := label_labelGap hp hgap
  rw [show 4 * 15 = 4 * (13 + 1 + 1) from rfl, ofNat4_succ, ofNat4_succ] at hg
  refine (fn_seg (N := pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp)
    (E := fun _ : Unit => pE (_root_.Executable.labels exe).label c0 A x29 ra tp) (fun i => ?_) PN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case cb =>
    refine seg_nd (by simp [cb]) cbP_ok hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero])) fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hS, h0, h1⟩ := hJ
    rw [pN, cbP_run, cbPT_run]
    have hne : ¬ σ.regs.X0.toBitVec = 0 := fun h => by rw [h] at h0; simp at h0
    refine .inl ⟨PN.cl, ?_, rfl, hS, ?_⟩
    · simp only [pN, rl, Reg64s.getRegOrZr]
      simp [hne, Reg64s.getRegOrZr, Reg64s.getXReg, hg]
      exact fun h => (hne h).elim
    · exact ⟨by simpa [Reg64s.getRegOrZr] using h0, by simpa [Reg64s.getRegOrZr] using h1⟩
  case cl =>
    refine seg_nd (by simp [cl]) cl_ok hF hR hal hlo hhi
      (code_of hp hend hcl (ofNat4_zero _)) fun σ c hJ => ⟨c, .refl c, ?_⟩
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
    refine seg_nd (by simp [bs]) bs_ok hF hR hal hlo hhi
      (code_of hp hend hbs rfl) fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [pN, bs_run, bsT_run]
    refine .inl ⟨PN.sp, ?_, rfl, ?_⟩ <;> simp_all [pN, rl, JS]
  case sp =>
    refine seg_nd (by simp [spB]) spB_ok hF hR hal hlo hhi
      (code_of hp hend hsp (ofNat4_zero _)) fun σ c hJ => ⟨c0, ?_, ?_⟩
    · obtain ⟨rfl, -⟩ := hJ; exact hrun
    obtain ⟨-, h72, h16, h8, htp⟩ := hJ
    rw [pN, spB_run]
    refine .inr ⟨(), ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all [pE, Spike.Lib.upd_apply]

end Seg

end Spike.Lib.A64.Flow.Worker.Wake.Parent
