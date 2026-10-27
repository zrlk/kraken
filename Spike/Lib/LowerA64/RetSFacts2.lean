/-
**The state's facts at `main`'s `ret` block** (AArch64): `SFacts` at
`dumN n` for the loads of a `ret`'s words, the frame's exit and `ret`
(`Kind2`'s `ret` arm), at a node with the frame's offsets whose controls
have the saved pair in their cells (`FrJ`), as `blkW_w2BP`'s `hS` for a
block without a `ret`. The `hS` premise of `blkW_heldTailN` at `main`'s
`ret a` block, which has no other producer among the `W2` lemmas; the twin
of `Spike/Lib/LowerX64/RetSFacts2.lean` (only `Kind2`'s `ret` arm; its
`Kind1` arms are `blkW_w2C`'s).

- `okBlk_ret2`: the `ret` block is covered at the frame's offsets
  (`okBlk_retLoads`, `okBlk_epi`);
- `hret_ret2`: it returns to the saved `ra` (`arun_retLoads`, `arun_epi`);
- `blkW_sfacts_ret2P`: `SFacts` at `dumN n` for it given its code and phase
  check (`blkW_postO'`);
- `blkW_sfacts_ret2`: the same for a block of the code predicate `CdC`
  (`SubCd`, as `blkW_w2CP`).
-/
import Spike.Lib.LowerA64.LaneW2
import Spike.Lib.LowerA64.Node2Edges

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer (SFacts blkPh hret_of_run Own Lbl)
open Spike.Lib.A64.Flow (BlkW ND okBlk arun classify AI)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Emit.A64 Scc.Lower.InvA64

section R2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {cx : FnCtx} {fp ra : BitVec 64}

/-- **`main`'s `ret` block is covered** at the frame's offsets
(`okBlk_retLoads`, `okBlk_epi`; as `ret_edgeSL`). -/
theorem okBlk_ret2 (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls) :
    okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
  rw [directives_leave hf h1 ls, okBlk_retLoads hf h1 h16 _ _ hl]
  have := Spike.Lib.A64.Flow.okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
  rwa [hF64] at this

/-- **`main`'s `ret` block returns to the saved `ra`** (`blkW_postO`'s
`hret`): the loads keep the slots and the offsets (`arun_retLoads`), the
exit's `ret` jumps to the slot `-8` (`arun_epi`), `ra` by `FrJ`. -/
theorem hret_ret2 (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {n : ND}
    (hno : n.o = oF cx) (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot)
    {vs : List Scc.IR.Operand} {ls : List Item} (hl : retLoads cx (vs.zip argRegs) = .ok ls) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < (directives (ls ++ cx.leave ++ [ret])).length) r,
      classify (directives (ls ++ cx.leave ++ [ret]))[k] = some (.ret r) →
      Int64.ofInt ((arun lab ((directives (ls ++ cx.leave ++ [ret])).take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr
        r).signed = Int64.ofBitVec ra := by
  refine hret_of_run (hno ▸ okBlk_ret2 hf h1 h16 hl) fun σ c hJ => ?_
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  rw [hno, directives_leave hf h1, arun_append]
  obtain ⟨R', hrun, -⟩ := arun_retLoads hf h1 lab _ hl n.pc σ
  rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, hrun]
  obtain ⟨hpc', -⟩ := Spike.Lib.A64.Flow.arun_epi lab (n.pc + Int64.ofNat (4 * (directives ls).length))
    (-(cx.frame : Int)) { σ with regs := R' } (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl,
      Spike.Lib.A64.Flow.bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc'
  rw [hpc']
  exact congrArg Int64.ofBitVec (hfj σ c hJ).2

omit [Kraken.Executable.ValidLayout exe] in
/-- **`SFacts` at `main`'s `ret` block at its code** (`blkW_postO'` at
`dumN n`): the block in the code at its node's pc (`hcode`), passing the
phase check there at the saved `ra` (`hph`), at a node with the frame's
offsets (`hno`) whose controls have the saved pair in their cells
(`hfj`). -/
theorem blkW_sfacts_ret2P {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {vs : List Scc.IR.Operand} {ls : List Item}
    (hgo : retLoads cx (vs.zip argRegs) = .ok ls)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (directives (ls ++ cx.leave ++ [ret])))
    (hph : blkPh okPc ph (fun _ => false) lab n.pc (Int64.ofBitVec ra) (directives (ls ++ cx.leave ++ [ret])) =
      true) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) (directives (ls ++ cx.leave ++ [ret])) :=
  blkW_postO' (n := dumN n) (dead := fun _ => false) (ra := Int64.ofBitVec ra) hI hcode
    (hno ▸ okBlk_ret2 hf h1 h16 hgo) hR hal hlo hhi (fun _ _ h => h.1 ▸ cfacts_c0) hph
    (hret_ret2 (n := dumN n) hf h1 h16 hno (fun σ _ ⟨_, c1, hJ1⟩ => hfj σ c1 hJ1) hgo)
    (fun _ _ _ => rfl) hl hh hsub hfit hFO

/-- **`SFacts` at `main`'s `ret` block of the code**
(`blkW_sfacts_ret2P`): a block of the code predicate `CdC` at the saved
return address (`SubCd`, its phase from the run's check, as `blkW_w2CP`).
The `hS` of `blkW_heldTailN` at the `ret a` node. -/
theorem blkW_sfacts_ret2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {vs : List Scc.IR.Operand} {ls : List Item}
    (hgo : retLoads cx (vs.zip argRegs) = .ok ls)
    (hcd : SubCd (CdC prog okPc ph lab (Int64.ofBitVec ra)) n.pc (directives (ls ++ cx.leave ++ [ret]))) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) (directives (ls ++ cx.leave ++ [ret])) := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hok : okBlk (-(cx.frame : Int)) 0 n.o (directives (ls ++ cx.leave ++ [ret])) = true :=
    hno ▸ okBlk_ret2 hf h1 h16 hgo
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  rw [hpc] at hph
  exact blkW_sfacts_ret2P hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hno hfj hgo
    (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk (blockAt_sub hb) (by rw [hI.labOk]; exact he)) hph

end R2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.
/-- info: 'Spike.Lib.LowerA64.okBlk_ret2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.okBlk_ret2

/-- info: 'Spike.Lib.LowerA64.hret_ret2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hret_ret2

/-- info: 'Spike.Lib.LowerA64.blkW_sfacts_ret2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_sfacts_ret2
