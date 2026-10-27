/-
**The state's facts at a body block of `Kind2`** (AArch64; the twin of
`Spike/Lib/LowerX64/RetSFacts2.lean`'s `Kind2` lemmas): `SFacts` at
`dumN n` for a block of a construct or of a many-word `ret` (`Kind2`), at a
node with the frame's offsets whose controls have the saved pair in their
cells (`FrJ`), as `blkW_w2BP`'s `hS` and for `ret` blocks (`BlkW.w2`'s `hS`).

- `hret_kind1`: a construct's block returns only to the saved `ra` (no
  `ret` but in the one-word `ret` arm, `arun_getOp`, `arun_epi`);
- `okBlk_kind2`: a `Kind2` block is covered at the frame's offsets
  (`kind1_ok`, `okBlk_ret2`);
- `hret_kind2`: a `Kind2` block returns only to the saved `ra`
  (`hret_kind1`, `hret_ret2`);
- `blkW_sfacts_k2P`: `SFacts` at `dumN n` for a `Kind2` block given its code
  and phase check (`blkW_postO'`);
- `blkW_sfacts_k2`: the same for a block of the code predicate `CdC`
  (`SubCd`, as `blkW_w2CP`).
-/
import Spike.Lib.LowerA64.RetSFacts2
import Spike.Lib.LowerA64.BodyW1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64Consumer (SFacts blkPh hret_of_run noRetBlk noRet_false Own Lbl)
open Spike.Lib.A64.Flow (BlkW ND okBlk arun classify AI)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.AllocG (dumN)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (cfacts_c0)
open Scc.Emit.A64 Scc.Lower.InvA64

section K2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {R : Region} {F : MachineData → Prop} {cx : FnCtx} {fp ra : BitVec 64}

/-- **A construct's block returns only to the saved `ra`** (`blkW_postO`'s
`hret`): the checked `+`, the saturating `-`, the branch, the store and the
jump have no `ret` (`noRet_of_last`, `noRet_false`); the one-word `ret`'s
run ends at the slot `-8` (`arun_getOp`, `arun_epi`), `ra` by `FrJ`. As
`blkW_body1`'s. -/
theorem hret_kind1 (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {n : ND}
    (hno : n.o = oF cx) (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive} (hk : Kind1 cx blk) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = Int64.ofBitVec ra := by
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ kind1_ok hf h1 h16 hk
  rcases hk with ⟨a, b, la, lb, ha, hb', h | h | ⟨T, h⟩⟩ | ⟨d, off, hd, rfl⟩ | ⟨F, rfl⟩ | ⟨w, lw, hg, rfl⟩
  · subst h
    intro σ _ _ k hk r hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
    rw [addDirs, directives_append, directives_addChecked, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · subst h
    intro σ _ _ k hk r hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
    rw [subDirs, directives_append, directives_subSat, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · subst h
    intro σ _ _ k hk r hr
    refine (noRet_of_last lab (am := ⟨n.pc, n.o, σ⟩) hok (fun d hd r => ?_) k hk r hr).elim
    rw [brDirs, directives_append, directives_cmpJcc, List.getLast?_append] at hd
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some_or, Option.some.injEq] at hd
    subst hd
    simp [Spike.Lib.A64.Flow.classify]
  · have hn : noRetBlk (strDirs off) = true := by
      simp [noRetBlk, strDirs, directives, ins, Spike.Lib.A64.Flow.classify, Spike.Lib.A64.Flow.RegOnly, spW64,
        i64]
    exact fun _ _ _ k hk r hr => (noRet_false hn k hk r hr).elim
  · have hn : noRetBlk (jmpDirs F) = true := by
      simp [noRetBlk, jmpDirs, directives, jmp, ins, Spike.Lib.A64.Flow.classify]
    exact fun _ _ _ k hk r hr => (noRet_false hn k hk r hr).elim
  · refine hret_of_run hok fun σ c hJ => ?_
    have hge := frame_ge16 hf
    have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
    show (arun lab (directives (lw ++ cx.leave ++ [ret])) ⟨n.pc, n.o, σ⟩).pc = _
    rw [hno, directives_leave hf h1, arun_append]
    obtain ⟨v, -, hrun⟩ := arun_getOp hf h1 hg lab n.pc σ
    rw [show oF cx = ⟨-(cx.frame : Int), []⟩ from rfl, hrun]
    obtain ⟨hpc', -⟩ := Spike.Lib.A64.Flow.arun_epi lab (n.pc + Int64.ofNat (4 * (directives lw).length))
      (-(cx.frame : Int)) { σ with regs := σ.regs.setXReg .X0 v } (Int64.ofInt cx.frame)
    have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
      rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl,
        Spike.Lib.A64.Flow.bmod_sub (by omega) (by rw [hF64]; omega), hF64]
    rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc'
    rw [hpc']
    exact congrArg Int64.ofBitVec (hfj σ c hJ).2

/-- **A `Kind2` block is covered** at the frame's offsets (`kind1_ok`,
`okBlk_ret2`). -/
theorem okBlk_kind2 (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {blk : List Directive}
    (hk : Kind2 cx blk) : okBlk (-(cx.frame : Int)) 0 (oF cx) blk = true := by
  rcases hk with hk | ⟨vs, ls, -, hl, rfl⟩
  · exact kind1_ok hf h1 h16 hk
  · exact okBlk_ret2 hf h1 h16 hl

/-- **A `Kind2` block returns only to the saved `ra`** (`blkW_postO`'s
`hret`): `hret_kind1` for a construct's block, `hret_ret2` for a `ret`'s. -/
theorem hret_kind2 (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {n : ND}
    (hno : n.o = oF cx) (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive} (hk : Kind2 cx blk) :
    ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = Int64.ofBitVec ra := by
  rcases hk with hk | ⟨vs, ls, -, hl, rfl⟩
  · exact hret_kind1 hf h1 h16 hno hfj hk
  · exact hret_ret2 hf h1 h16 hno hfj hl

omit [Kraken.Executable.ValidLayout exe] in
/-- **`SFacts` at a `Kind2` block at its code** (`blkW_postO'` at
`dumN n`): a block of a construct or of a `ret` (`hk`), in the code at its
node's pc (`hcode`), passing the phase check there at the saved `ra`
(`hph`), at a node with the frame's offsets (`hno`) whose controls have the
saved pair in their cells (`hfj`). -/
theorem blkW_sfacts_k2P {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive} (hk : Kind2 cx blk)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hph : blkPh okPc ph (fun _ => false) lab n.pc (Int64.ofBitVec ra) blk = true) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk :=
  blkW_postO' (n := dumN n) (dead := fun _ => false) (ra := Int64.ofBitVec ra) hI hcode
    (hno ▸ okBlk_kind2 hf h1 h16 hk) hR hal hlo hhi (fun _ _ h => h.1 ▸ cfacts_c0) hph
    (hret_kind2 (n := dumN n) hf h1 h16 hno (fun σ _ ⟨_, c1, hJ1⟩ => hfj σ c1 hJ1) hk)
    (fun _ _ _ => rfl) hl hh hsub hfit hFO

/-- **`SFacts` at a `Kind2` block of the code** (`blkW_sfacts_k2P`): a
block of the code predicate `CdC` at the saved return address (`SubCd`,
its phase from the run's check, as `blkW_w2CP`). -/
theorem blkW_sfacts_k2 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int)) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) {n : ND} (hno : n.o = oF cx)
    (hfj : ∀ σ c, n.J σ c → FrJ fp ra σ.slot) {blk : List Directive} (hk : Kind2 cx blk)
    (hcd : SubCd (CdC prog okPc ph lab (Int64.ofBitVec ra)) n.pc blk) :
    BlkW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F (dumN n) blk := by
  obtain ⟨pc0, pre, post, ⟨-, L, j, hpc0, hb, hrun⟩, hpc⟩ := hcd
  have hok : okBlk (-(cx.frame : Int)) 0 n.o blk = true := hno ▸ okBlk_kind2 hf h1 h16 hk
  have hph := Scc.Cert.Ph1A64.blkPh_of_runPhB hrun (classify_of_okBlk hok)
  have he : lab L + Int64.ofNat (4 * (j + pre.length)) = n.pc := by
    rw [← hpc, ← hpc0, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  rw [hpc] at hph
  exact blkW_sfacts_k2P hI hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hno hfj hk
    (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk (blockAt_sub hb) (by rw [hI.labOk]; exact he)) hph

end K2

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hret_kind2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hret_kind2

/-- info: 'Spike.Lib.LowerA64.blkW_sfacts_k2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.blkW_sfacts_k2
