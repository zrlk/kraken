/-
**The abort paths' states keep the write abort's phase** (AArch64): the
per-node bundles `StubOAb` and `StubHAb` (`Spike/Lib/LowerA64/AbortW2.lean`)
at `Ab := WriteAb.Ab lab`, for any executable with `InstOk`, its program
holding the runtime's code (`printIn`, `abortIn`) and passing the paths'
phase checks (`abortPhOk`, `abortPhHeapOk`). The twin of
`Spike/Lib/LowerX64/StubAbW2.lean`.

The write abort's pcs are label-relative positions (`AllocRa.abPos`), and
positions that differ sit at different pcs (`pc_ne_of_inRun`): a block's
every target is a position (`PrintG.tgt_pos`), decided on the concrete
block. The stubs' targets are all off `abPos`. The dispatcher's are in it:
its prologue is in the phase only at `x0 = 4` and its tests only at
`[sp] = 4`, so there the data the nodes carry (the code 1 or 2) keeps the
phase out (`not_ab_pos`).

- `dispEPos`, `dispTPos`, `nvPos`, `nvPcs`, `pos_of_mem`, `not_ab_pos`: a
  position's state off the phase, from its data at the dispatcher's
  positions.
- `sp_slot`: the word at `[sp]` from the abstract state.
- `arun_succ_eq`, `blkW_abPos`: a block keeping the phase, the targets in
  `abPos` by their data (`hdat`).
- `nodeW_ab_svc`, `nodeW_ab_exit`: an `svc` resuming off the phase, and the
  exit call (`exit_group`, no successor).
- `d0_end`, `tj_keep`, `dispTChk`, `blkW_abDispT`, `blkW_abD0`: the
  dispatcher's blocks.
- `stubAb_nodes`, `stubOAb`, `stubHAb`: the bundles.
- `ovf_hW_w2_fi`: `ovf_hW_w2` for a function other than the runtime's.
-/
import Spike.Lib.LowerA64.AbortW2
import Spike.Lib.A64PrintGAb
import Spike.Lib.A64StubWA
import Spike.Lib.A64Dead

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (pcOf abi atSvc_of_cellAt mem_certSuccs_svc)
open Spike.Lib (Region)
open Spike.Lib.A64Consumer (blkPh noRet_false noRetBlk)
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.A64.Flow (NodeW BlkW ND AS SO AI AM Abs classify okBlk arun dstep)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt InRun pc_ne_of_inRun Lays label_labelGap)
open Spike.Lib.A64.WriteAb (Ab abPcs not_ab_of_pc spLoad pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)
open Spike.Lib.A64.PrintG (posTgts wfChk extPos offChk tgt_pos notAb_of_pos notAbPc_of_pos inRun0)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Spike.Lib.A64.Flow.Ret0 (ofNat4_succ')

/-! ## The write abort's positions by data -/

section Pos

/-- The dispatcher's prologue's positions (`WriteAb.dispEPcs`). -/
def dispEPos : List (Label × Nat) := (abPos.drop 23).take 5

/-- The dispatcher's tests' positions (`WriteAb.dispTPcs`). -/
def dispTPos : List (Label × Nat) := (abPos.drop 28).take 19

/-- The write abort's positions with no data condition but the stored
length and result's (all but the dispatcher's). -/
def nvPos : List (Label × Nat) := abPos.take 23 ++ abPos.drop 47

/-- `nvPos`'s pcs. -/
def nvPcs (lab : Label → Int64) : List Int64 :=
  pcRet lab :: tailPcs lab ++ failPcs lab ++ g4Pcs lab ++ stubPcs lab

theorem dispEPcs_eq (lab : Label → Int64) :
    dispEPcs lab = dispEPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [dispEPcs, dispEPos, abPos, List.range_succ]

theorem dispTPcs_eq (lab : Label → Int64) :
    dispTPcs lab = dispTPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [dispTPcs, dispTPos, abPos, List.range_succ]

theorem nvPcs_eq (lab : Label → Int64) : nvPcs lab = nvPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [nvPcs, nvPos, abPos, pcRet, tailPcs, failPcs, g4Pcs, stubPcs, Spike.Lib.A64.PrintD.pcSvc,
    List.range_succ]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Int64.add_assoc] <;> rfl

theorem dispEPos_sub : dispEPos.all abPos.contains = true := by decide
theorem dispTPos_sub : dispTPos.all abPos.contains = true := by decide
theorem nvPos_sub : nvPos.all abPos.contains = true := by decide

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

/-- **A position at one of a list of the write abort's positions' pcs is
in the list**, in a layout of a program with the runtime's code. -/
theorem pos_of_mem (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {P : List (Label × Nat)} (hP : P.all abPos.contains = true)
    {q : Label × Nat} (hr : InRun prog q.1 q.2)
    (h : lab q.1 + Int64.ofNat (4 * q.2) ∈ P.map fun p => lab p.1 + Int64.ofNat (4 * p.2)) : q ∈ P := by
  subst hl
  obtain ⟨p, hp', he⟩ := List.mem_map.mp h
  by_cases hq : p = q
  · exact hq ▸ hp'
  · have hpa := List.all_eq_true.mp hP p hp'
    rw [List.contains_iff_mem] at hpa
    exact absurd he (pc_ne_of_inRun hp (abPos_inRun hpr hab p hpa) hr hq)

/-- **A state at a position is off the phase** when the position is none
of those without a data condition (`hn`), and at the dispatcher's
prologue `x0 ≠ 4` (`hE`), at its tests `[sp] ≠ 4` (`hT`). -/
theorem not_ab_pos (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {q : Label × Nat} (hr : InRun prog q.1 q.2) {s : State}
    (hs : s.st.2 = lab q.1 + Int64.ofNat (4 * q.2))
    (hn : nvPos.contains q = false) (hE : dispEPos.contains q = true → s.st.1.regs.X0 ≠ 4)
    (hT : dispTPos.contains q = true → spLoad s 0 ≠ some 4#64) : ¬ Ab lab s := by
  have hnv : s.st.2 ∉ nvPcs lab := by
    rw [hs, nvPcs_eq]
    intro hm
    have := pos_of_mem hp hpr hab hl nvPos_sub hr hm
    rw [← List.contains_iff_mem, hn] at this
    cases this
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, h4⟩ | ⟨h, h4⟩ | h | h)
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])
  · rw [hs, dispEPcs_eq] at h
    exact hE (List.contains_iff_mem.mpr (pos_of_mem hp hpr hab hl dispEPos_sub hr h)) h4
  · rw [hs, dispTPcs_eq] at h
    exact hT (List.contains_iff_mem.mpr (pos_of_mem hp hpr hab hl dispTPos_sub hr h)) h4
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])

/-- **The word at `[sp]` from the abstract state**, `sp` at the frame's
`-32`. -/
theorem sp_slot {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ) (ho : o.sp = -32)
    (hoff : R.Off (-32)) : spLoad s 0 = some (σ.slot (-32)) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-32) hoff
  have hsp := hA.so .SP o.sp rfl
  rw [← hA.regs, ho] at hsp
  simp only [Reg64s.getRegOrSp64] at hsp
  simp only [spLoad, Scc.Sem.A64.privLoad, hsp]
  rw [show R.addr (-32) + 0 = R.addr (-32) from BitVec.add_zero _, hj, Option.map_some, hjv]

end Pos

/-! ## Blocks and single instructions keeping the phase -/

section Nodes

/-- **An instruction's next static offsets and abstract state are the
abstract run's past it.** -/
theorem arun_succ_eq (lab : Label → Int64) {lo hi : Int} {blk : List Directive} {am : AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) {a : AI} (hca : classify blk[k] = some a) :
    a.so (arun lab (blk.take k) am).so = (arun lab (blk.take (k + 1)) am).so ∧
      a.step (arun lab (blk.take k) am).so (am.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun lab (blk.take k) am).σ = (arun lab (blk.take (k + 1)) am).σ := by
  have hpc := Spike.Lib.A64.Flow.arun_pc lab h hk
  rw [Spike.Lib.A64.Flow.arun_take_succ lab hk, ← hpc]
  simp [dstep, hca]

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64Consumer.Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**: at a block of the
program at `(L, j0)` (`hb`) passing its phase check (`hph`), with no `ret`
(`hnr`), every target a position (`hwf`, `hnx`, `hIn`) off `abPos` or, if in
it, off the phase by the data past the instruction (`hdat`). -/
theorem blkW_abPos {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {L : Label} {j0 : Nat} {nxt : Option (Label × Nat)}
    (hb : blockAt prog L j0 blk = true) (he : lab L + Int64.ofNat (4 * j0) = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi) (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat (4 * j0)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (4 * (j0 + blk.length)) = lab q.1 + Int64.ofNat (4 * q.2))
    (hIn : ∀ q ∈ extPos blk nxt, InRun prog q.1 q.2)
    (hdat : ∀ σ c, n.J σ c → ∀ k, k < blk.length → ∀ q ∈ posTgts L j0 blk nxt k, abPos.contains q = true →
      InRun prog q.1 q.2 → ∀ s' : State, s'.st.2 = lab q.1 + Int64.ofNat (4 * q.2) →
      Abs R (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1 (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine Spike.Lib.A64.AllocG.blkW_abG hI hb he hok hR hal hlo hhi hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    fun σ c hJ k hk a hca s' _ _ hpc' hA' => ?_
  obtain ⟨hso, hst⟩ := arun_succ_eq lab (am := ⟨n.pc, n.o, σ⟩) hok hk hca
  rw [hso, hst] at hA'
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with
    ⟨r, rfl⟩ | ⟨q, hq, hqr, hqe⟩
  · exact (noRet_false hnr k hk r hca).elim
  rw [he] at hqe
  have hs' : s'.st.2 = lab q.1 + Int64.ofNat (4 * q.2) := hpc'.trans hqe
  by_cases hqa : abPos.contains q = true
  · exact hdat σ c hJ k hk q hq hqa hqr s' hs' hA'
  · have hl := hI.labOk
    subst hl
    exact notAb_of_pos hI.lays hpr hab hqr (Bool.eq_false_iff.mpr hqa) hs'

/-- **An `svc` resuming off the write abort's pcs keeps its phase**: at `p`
off the sites (`hok`), `p + 4` off `abPcs` (`hnx`), every state the kernel
resumes in is at `p + 4`. -/
theorem nodeW_ab_svc {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 4 ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSvc_of_cellAt (imm := 0) hc]; decide),
    fun _ _ call hd s' hs' hab' => ?_, fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩, fun _ h => h⟩
  exfalso
  obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hc hd).1 hs'
  exact not_ab_of_pc (by show s.st.2 + Int64.ofNat 4 ∉ _; rw [hpc]; exact hnx) hab'

/-- **An exit call keeps the write abort's phase**: at `x8 = 94` (`hx`) the
call is `exit_group`, which resumes in no state; its pc off the take site
(`htk`). -/
theorem nodeW_ab_exit {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {k : Nat} {p : Int64} (hb : blockAt prog l k [Spike.Lib.A64.Flow.svcDir] = true)
    (he : lab l + Int64.ofNat (4 * k) = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.X8 = 94) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSvc_of_cellAt (imm := 0) hc]; decide),
    fun _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) =
      some (.exitGroup s.st.1.regs.X0.toNat) := by
    rw [← Spike.Lib.A64.Flow.svcCall_exitGroup (r := s.st.1.regs) (by rw [hA.regs, hx σ c hJ]; rfl)]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.A64.Flow.certSuccs_exitGroup] at hs'
  cases hs'

end Nodes

/-! ## The dispatcher's data -/

section Disp

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.dstep, Spike.Lib.A64.Flow.classify,
    Spike.Lib.A64.Flow.RegOnly, Spike.Lib.A64.Flow.AI.so, Spike.Lib.A64.Flow.AI.step,
    Spike.Lib.A64.Flow.AI.tgt, Spike.Lib.A64.Flow.soReg, Spike.Lib.A64.Flow.regDst, Spike.Lib.A64.Flow.zrB,
    Spike.Lib.A64.Flow.regRes, Operation.interp, MachineData.setRegOrZr, MachineData.setRegOrSp,
    Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64, Reg64s.setRegOrSp,
    Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg, Reg64s.getXReg,
    ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Spike.Lib.A64.Flow.SO.get, Spike.Lib.A64.Flow.SO.set, Spike.Lib.A64.Flow.SO.kill,
    Spike.Lib.A64.Flow.SO.write, Spike.Lib.A64.Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm, Spike.Lib.upd_apply])

/-- **The dispatcher's prologue stores `x0` at `[sp]`**, `sp` at the
frame's `-32`. -/
theorem d0_end (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab (A64.Abort.Disp.d0.take 5) ⟨pc, A64.Abort.oE, σ⟩).so.sp = -32 ∧
      (arun lab (A64.Abort.Disp.d0.take 5) ⟨pc, A64.Abort.oE, σ⟩).σ.slot (-32) = σ.regs.X0.toBitVec := by
  simp only [A64.Abort.Disp.d0]
  arun_simp

/-- **The dispatcher's tests and jumps keep `sp` at the frame's `-32` and
`[sp]`.** -/
theorem tj_keep (lab : Label → Int64) {blk : List Directive}
    (hb : blk = A64.Abort.Disp.t1 ∨ blk = A64.Abort.Disp.t2 ∨ blk = A64.Abort.Disp.j1) (pc : Int64) (σ : AS)
    {j : Nat} (hj : j ≤ blk.length) :
    (arun lab (blk.take j) ⟨pc, A64.Abort.Disp.oD, σ⟩).so.sp = -32 ∧
      (arun lab (blk.take j) ⟨pc, A64.Abort.Disp.oD, σ⟩).σ.slot (-32) = σ.slot (-32) := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [A64.Abort.Disp.t1, A64.Abort.Disp.t2, A64.Abort.Disp.j1] at hj ⊢ <;>
    simp only [List.length_cons, List.length_nil] at hj <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

/-- **Every target in the write abort is one of the dispatcher's tests'.** -/
def dispTChk (L : Label) (j0 : Nat) (blk : List Directive) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k => (posTgts L j0 blk nxt k).all fun q =>
    !abPos.contains q || (dispTPos.contains q && !nvPos.contains q && !dispEPos.contains q)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64Consumer.Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A test or jump of the dispatcher keeps the write abort's phase** at a
code `≠ 4` at `[sp]` (`hJ`): its targets in the write abort are tests
(`dispTChk`), where the code is still the node's (`tj_keep`). -/
theorem blkW_abDispT {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {L : Label} {j0 : Nat} {nxt : Option (Label × Nat)}
    (hblk : blk = A64.Abort.Disp.t1 ∨ blk = A64.Abort.Disp.t2 ∨ blk = A64.Abort.Disp.j1)
    (hb : blockAt prog L j0 blk = true) (he : lab L + Int64.ofNat (4 * j0) = n.pc)
    (hno : n.o = A64.Abort.Disp.oD) (hok : okBlk (-32) 0 n.o blk = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat (4 * j0)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (4 * (j0 + blk.length)) = lab q.1 + Int64.ofNat (4 * q.2))
    (hIn : ∀ q ∈ extPos blk nxt, InRun prog q.1 q.2) (hchk : dispTChk L j0 blk nxt = true)
    (hJ : ∀ σ c, n.J σ c → σ.slot (-32) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abPos hI hpr hab hb he hok hR hal (by omega) hhi hph hnr hwf hnx hIn
    fun σ c hj k hk q hq hqa hqr s' hs' hA' => ?_
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk)) q hq
  simp only [hqa, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨-, hnv⟩, hE⟩ := hc
  rw [hno] at hA'
  obtain ⟨hsp, hsl⟩ := tj_keep lab hblk n.pc σ (j := k + 1) (by omega)
  refine not_ab_pos hI.lays hpr hab hI.labOk hqr hs' hnv (fun h => by rw [hE] at h; cases h) fun _ => ?_
  rw [sp_slot hA' hsp ⟨by decide, by omega, by omega⟩, hsl]
  exact fun h => hJ σ c hj (Option.some.inj h)

/-- **The dispatcher's prologue keeps the write abort's phase** at a code
`≠ 4` in `x0` (`hJ`): its targets are the prologue's, where `x0` is kept
(`StubW.d0_x0`), and the first test, where the code is stored at `[sp]`
(`d0_end`). -/
theorem blkW_abD0 {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} (hpc : n.pc = lab "scc_rt_abort") (hno : n.o = A64.Abort.oE) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat (4 * 0)) 0 A64.Abort.Disp.d0 = true)
    (hJ : ∀ σ c, n.J σ c → σ.regs.X0 ≠ 4) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n A64.Abort.Disp.d0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg⟩ := hdi
  have hent := label_labelGap hI.lays hg
  rw [hI.labOk] at hent
  have hl5 : A64.Abort.Disp.d0.length = 5 := by decide
  refine blkW_abPos hI hpr hab (nxt := some (".L12_scc_rt_abort.0_entry", 0)) hd0
    (by rw [hpc]; exact add0 _) (hno ▸ A64.Abort.Disp.d0_ok) hR hal (by omega) hhi hph (by decide) (by decide)
    (fun q hq => by
      cases hq
      rw [hent, show Int64.ofNat (4 * ((".L12_scc_rt_abort.0_entry", 0) : Label × Nat).2) = 0 from rfl,
        Int64.add_zero, hl5]) ?_ ?_
  · intro q hq
    rw [show extPos A64.Abort.Disp.d0 (some (".L12_scc_rt_abort.0_entry", 0)) =
      [(".L12_scc_rt_abort.0_entry", 0)] by decide, List.mem_singleton] at hq
    subst hq
    exact abPos_inRun hpr hab _ (by decide)
  intro σ c hj k hk q hq hqa hqr s' hs' hA'
  rw [hno, hpc] at hA'
  -- the prologue's own pcs, `x0` kept
  have hE : k < 4 → s'.st.1.regs.X0 ≠ 4 := fun h4 => by
    rw [hA'.regs, Spike.Lib.A64.StubW.d0_x0 (lab := lab) (lab "scc_rt_abort") σ (k := k + 1) (by omega)]
    exact hJ σ c hj
  have hpe : ∀ j, j < 4 → posTgts "scc_rt_abort" 0 A64.Abort.Disp.d0 (some (".L12_scc_rt_abort.0_entry", 0)) j =
      [("scc_rt_abort", j + 1)] := by decide
  by_cases h4 : k < 4
  · rw [hpe k h4, List.mem_singleton] at hq
    subst hq
    have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    refine not_ab_pos hI.lays hpr hab hI.labOk hqr hs' ?_ (fun _ => hE h4) fun h => ?_
    · rcases hk with rfl | rfl | rfl | rfl <;> decide
    · exfalso; revert h; rcases hk with rfl | rfl | rfl | rfl <;> decide
  · have hk4 : k = 4 := by omega
    subst hk4
    rw [show posTgts "scc_rt_abort" 0 A64.Abort.Disp.d0 (some (".L12_scc_rt_abort.0_entry", 0)) 4 =
      [(".L12_scc_rt_abort.0_entry", 0)] by decide, List.mem_singleton] at hq
    subst hq
    obtain ⟨hsp, hsl⟩ := d0_end lab (lab "scc_rt_abort") σ
    refine not_ab_pos hI.lays hpr hab hI.labOk hqr hs' (by decide) (fun h => absurd h (by decide)) fun _ h => ?_
    exact hJ σ c hj (UInt64.toBitVec_inj.mp (hsl.symm.trans (Option.some.inj ((sp_slot hA' hsp
      ⟨by decide, by omega, by omega⟩).symm.trans h))))

end Disp

/-! ## The bundles -/

section Bundles

open Spike.Lib.A64.StubW (abortPhOk abortPhHeapOk phOne)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64Consumer.Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl}

/-- **A stub's nodes keep the write abort's phase**: the stub `st` with the
argument block `b1` in the program (`hst`), its blocks passing their phase
checks (`hp0`, `hp1`, `hp2`) and the single instructions theirs (`ho1`,
`ho1b`, `ho7`), the exit call off the take site (`htk`), every position the
stub reaches off the write abort's (the decided `hw*`, `hf*`, `hx*`, `h1`,
`h2`, `h8`). -/
theorem stubAb_nodes {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {st : A64.Abort.Stub}
    {b1 : List Directive} (hst : Scc.Cert.Rt.A64.Abort.stubIn prog st b1 = true)
    (hp0 : blkPh okPc ph (fun _ => false) lab (lab st.fn + Int64.ofNat (4 * 0)) 0 A64.Abort.b0 = true)
    (ho1 : okPc (lab st.entry + Int64.ofNat (4 * 0)).toBitVec.toNat = true)
    (ho1b : okPc (lab st.entry + Int64.ofNat (4 * 1)).toBitVec.toNat = true)
    (hp1 : blkPh okPc ph (fun _ => false) lab (lab st.entry + Int64.ofNat (4 * 2)) 0 b1 = true)
    (ho7 : okPc (lab st.entry + Int64.ofNat (4 * 7)).toBitVec.toNat = true)
    (hp2 : blkPh okPc ph (fun _ => false) lab (lab st.entry + Int64.ofNat (4 * 8)) 0 A64.Abort.b2 = true)
    (htk : ∀ a, μ.site .take = some a → (lab st.exit).toBitVec.toNat ≠ a)
    (hw0 : wfChk st.fn 0 A64.Abort.b0 (some (st.entry, 0)) = true)
    (hf0 : offChk st.fn 0 A64.Abort.b0 (some (st.entry, 0)) = true)
    (hx0 : extPos A64.Abort.b0 (some (st.entry, 0)) = [(st.entry, 0)])
    (hok1 : okBlk (-48) 0 A64.Abort.oI b1 = true) (hnr1 : noRetBlk b1 = true) (hl1 : b1.length = 5)
    (hw1 : wfChk st.entry 2 b1 (some (st.entry, 7)) = true)
    (hf1 : offChk st.entry 2 b1 (some (st.entry, 7)) = true)
    (hx1 : extPos b1 (some (st.entry, 7)) = [(st.entry, 7)])
    (hw2 : wfChk st.entry 8 A64.Abort.b2 (some (st.exit, 0)) = true)
    (hf2 : offChk st.entry 8 A64.Abort.b2 (some (st.exit, 0)) = true)
    (hx2 : extPos A64.Abort.b2 (some (st.exit, 0)) = [(st.exit, 0)])
    (h1 : abPos.contains (st.entry, 1) = false) (h2 : abPos.contains (st.entry, 2) = false)
    (h8 : abPos.contains (st.entry, 8) = false) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .e) A64.Abort.b0 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .n1) ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .n1b) ∧
      BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .n2) b1 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .svc) ∧
      BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .n5) A64.Abort.b2 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (A64.Abort.N (_root_.Executable.labels exe).label st c0 .ex) := by
  have hl := hI.labOk
  subst hl
  have hst' := hst
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst'
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, hg, hg'⟩ := hst'
  have hent := label_labelGap hI.lays hg
  have hext := label_labelGap hI.lays hg'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Spike.Lib.A64.PrintG.blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0)
      (nxt := some (st.entry, 0)) hb0 (add0 _) A64.Abort.b0_ok hR hal hlo hhi hp0
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hw0
      (fun q hq => by
        cases hq
        rw [hent, show Int64.ofNat (4 * ((st.entry, 0) : Label × Nat).2) = 0 from rfl, Int64.add_zero]
        rfl) ?_ hf0 (fun k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    intro q hq
    rw [hx0, List.mem_singleton] at hq
    subst hq
    exact inRun0 hn1 (by simp)
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1 rfl (add0 _).symm ho1
      (notAbPc_of_pos hI.lays hpr hab (inRun0 hn1b (by simp)) h1 (ofNat4_succ' _ 0))
  · exact Spike.Lib.A64.AllocG.nodeW_ab_si hI hn1b rfl (by simp only [A64.Abort.N, add4, add0]) ho1b
      (notAbPc_of_pos hI.lays hpr hab (inRun0 hb1 (by rw [hl1]; decide)) h2 (ofNat4_succ' _ 1))
  · refine Spike.Lib.A64.PrintG.blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0)
      (nxt := some (st.entry, 7)) hb1 (by simp only [A64.Abort.N, add4, add0]) hok1 hR hal hlo hhi hp1
      (fun _ _ _ k hk r hr => (noRet_false hnr1 k hk r hr).elim) (fun _ _ _ => rfl) hw1
      (fun q hq => by cases hq; rw [hl1]) ?_ hf1 (fun k hk r hr => (noRet_false hnr1 k hk r hr).elim)
    intro q hq
    rw [hx1, List.mem_singleton] at hq
    subst hq
    exact inRun0 hsvcIn (by decide)
  · exact nodeW_ab_svc hI hsvcIn rfl (by simp only [A64.Abort.N, A64.Abort.pcSvc, add4, add0]) ho7
      (notAbPc_of_pos hI.lays hpr hab (inRun0 hb2 (by decide)) h8 (ofNat4_succ' _ 7))
  · refine Spike.Lib.A64.PrintG.blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0)
      (nxt := some (st.exit, 0)) hb2 (by simp only [A64.Abort.N, A64.Abort.pcSvc, add4, add0]) A64.Abort.b2_ok
      hR hal hlo hhi hp2 (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) hw2
      (fun q hq => by
        cases hq
        rw [hext, show Int64.ofNat (4 * ((st.exit, 0) : Label × Nat).2) = 0 from rfl, Int64.add_zero]
        rfl) ?_ hf2 (fun k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    intro q hq
    rw [hx2, List.mem_singleton] at hq
    subst hq
    exact inRun0 hx (by decide)
  · exact nodeW_ab_exit hI hx (add0 _) rfl htk fun _ _ h => h.2.1

/-- **`StubOAb` at the write abort's phase**: the overflow abort path's
nodes keep it, for an executable with `InstOk` (`hI`), the runtime's code in
its program (`hpr`, `hab`) and the path's phase check (`hphs`), the stub's
frame in a 16-aligned region (`hal`, `hlo`, `hhi`) and its exit call off
the take site (`htk`). -/
theorem stubOAb {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhOk okPc ph lab = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.overflow.exit).toBitVec.toNat ≠ a) :
    StubOAb μ (Ab lab) exe endPc R F c0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨-, ht1, -, hg1, -⟩ := hdi
  have hst := hsd.1.1.1.1.1
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pg1, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  obtain ⟨se, sn1, sn1b, sn2, hsvc, sn5, sex⟩ := stubAb_nodes (c0 := c0) (F := F) hI hpr hab hR hal hlo hhi hst
    pb0 o1 o1b pb1 o7 pb2 htk (by decide) (by decide) (by decide) A64.Abort.b1Overflow_ok (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hl := hI.labOk
  subst hl
  refine ⟨?_, ?_, ?_, se, sn1, sn1b, sn2, hsvc, sn5, sex⟩
  · exact blkW_abD0 hI hpr hab rfl rfl hR hal hlo hhi pd0 fun _ _ h he => by
      have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := some (".L12_scc_rt_abort.0_entry", 4)) (.inl rfl) ht1 (add0 _) rfl
      A64.Abort.Disp.t1_ok hR hal hlo hhi pt1 (by decide) (by decide) (fun q hq => by cases hq; rfl) ?_
      (by decide) fun _ _ h he => by
        have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
    intro q hq
    rw [show extPos A64.Abort.Disp.t1 (some (".L12_scc_rt_abort.0_entry", 4)) =
      [(".L12_scc_rt_abort.0_entry", 4), (".L12_scc_rt_abort.1_is0", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRun hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      exact inRun0 hg1 (by decide)
  · refine Spike.Lib.A64.PrintG.blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0) (nxt := none) hg1
      (add0 _) A64.Abort.Disp.g1_ok hR hal (by omega) hhi pg1
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide)
      (fun _ h => by cases h) ?_ (by decide) (fun k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    intro q hq
    rw [show extPos A64.Abort.Disp.g1 none = [(A64.Abort.overflow.fn, 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
    exact inRun0 hst.1 (by decide)

/-- **`StubHAb` at the write abort's phase**: the heap abort path's nodes
keep it, as `stubOAb` with the path's phase check `abortPhHeapOk`. -/
theorem stubHAb {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhHeapOk okPc ph lab = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi) (htk : ∀ a, μ.site .take = some a → (lab A64.Abort.heap.exit).toBitVec.toNat ≠ a) :
    StubHAb μ (Ab lab) exe endPc R F c0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨-, ht1, hj1, hg1, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, o1b, -, pb1, o7, -, pb2, -⟩ := hphs
  obtain ⟨se, sn1, sn1b, sn2, hsvc, sn5, sex⟩ := stubAb_nodes (c0 := c0) (F := F) hI hpr hab hR hal hlo hhi hst
    pb0 o1 o1b pb1 o7 pb2 htk (by decide) (by decide) (by decide) A64.Abort.b1Heap_ok (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hl := hI.labOk
  subst hl
  refine ⟨?_, ?_, ?_, ?_, ?_, se, sn1, sn1b, sn2, hsvc, sn5, sex⟩
  · exact blkW_abD0 hI hpr hab rfl rfl hR hal hlo hhi pd0 fun _ _ h he => by
      have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := some (".L12_scc_rt_abort.0_entry", 4)) (.inl rfl) ht1 (add0 _) rfl
      A64.Abort.Disp.t1_ok hR hal hlo hhi pt1 (by decide) (by decide) (fun q hq => by cases hq; rfl) ?_
      (by decide) fun _ _ h he => by
        have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
    intro q hq
    rw [show extPos A64.Abort.Disp.t1 (some (".L12_scc_rt_abort.0_entry", 4)) =
      [(".L12_scc_rt_abort.0_entry", 4), (".L12_scc_rt_abort.1_is0", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRun hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      exact inRun0 hg1 (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := none) (.inr (.inr rfl)) hj1
      (by simp only [A64.Abort.Disp.DN.nd2, add4, add0]) rfl A64.Abort.Disp.j1_ok hR hal hlo hhi pj1
      (by decide) (by decide) (fun _ h => by cases h) ?_ (by decide)
      fun _ _ h he => by have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
    intro q hq
    rw [show extPos A64.Abort.Disp.j1 none = [(".L12_scc_rt_abort.2_next1", 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    exact abPos_inRun hpr hab _ (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := some (".L12_scc_rt_abort.2_next1", 4)) (.inr (.inl rfl)) ht2
      (add0 _) rfl A64.Abort.Disp.t2_ok hR hal hlo hhi pt2 (by decide) (by decide)
      (fun q hq => by cases hq; rfl) ?_ (by decide) fun _ _ h he => by
        have h2 := h.2; rw [he] at h2; exact absurd h2 (by decide)
    intro q hq
    rw [show extPos A64.Abort.Disp.t2 (some (".L12_scc_rt_abort.2_next1", 4)) =
      [(".L12_scc_rt_abort.2_next1", 4), (".L12_scc_rt_abort.3_is2", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRun hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      exact inRun0 hg2 (by decide)
  · refine Spike.Lib.A64.PrintG.blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0) (nxt := none) hg2
      (add0 _) A64.Abort.Disp.g2_ok hR hal (by omega) hhi pg2
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl) (by decide)
      (fun _ h => by cases h) ?_ (by decide) (fun k hk r hr => (noRet_false (by decide) k hk r hr).elim)
    intro q hq
    rw [show extPos A64.Abort.Disp.g2 none = [(A64.Abort.heap.fn, 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
    exact inRun0 hst.1 (by decide)

end Bundles

/-! ## The function's overflow block off the runtime -/

section Ovf

open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open A9NoSpawn Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.A64.Flow (FStable)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad SlotRepAt)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64Consumer.Own}
  {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout}
  {rS : Range} {R : Region} {F : MachineData → Prop} {p : Prog} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {ar : Arena} {J : InvS} {Dt : State → Prop} {lbl : Spike.Lib.A64Consumer.Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame} {rs : Scc.IR.Reg → Option Int} {c0 : Ctl}

/-- **`ovf_hW_w2` for a function other than the runtime's**: its overflow
label off `abLabs` by its index (`hfi`, `local_not_abLabs`). -/
theorem ovf_hW_w2_fi {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {cx : Scc.Emit.A64.FnCtx} {fp ra : BitVec 64}
    (hblk : blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true) (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) (hFO : ∀ m, F m → StackOff rS R m)
    (hFS : FStable R F) (hp : ProgNoS ZBad p) {ra' : Int64}
    (hph : blkPh okPc ph (fun _ => false) lab (lab (cx.local "abort_overflow")) ra' A64.Abort.Local.lb = true)
    (hJp : ∀ σ c, (abortN2 i T p lbl cx lab fp ra c0).J σ c → SlotRepAt Λ.imms lbl rs σ.slot c)
    (hrs : ∀ r k, rs r = some k → R.Off k)
    (hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI Λ lbl s fs B)
    (hJ : ∀ σ c, (abortN2 i T p lbl cx lab fp ra c0).J σ c → (fs = [] → ∀ a, c.term ≠ .ret a) ∧ FrOk2 c fs) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs) K exe endPc
      R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) A64.Abort.Local.lb :=
  ovf_hW_w2 hI hpr habt hblk (local_not_abLabs hfi "abort_overflow") hR hal hl hh hsub hfit hFO hFS hp hph hJp
    hrs hfp hJ

end Ovf

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.not_ab_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_ab_pos

/-- info: 'Spike.Lib.LowerA64.blkW_abPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abPos

/-- info: 'Spike.Lib.LowerA64.nodeW_ab_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_svc

/-- info: 'Spike.Lib.LowerA64.nodeW_ab_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_exit

/-- info: 'Spike.Lib.LowerA64.blkW_abDispT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abDispT

/-- info: 'Spike.Lib.LowerA64.blkW_abD0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abD0

/-- info: 'Spike.Lib.LowerA64.stubAb_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubAb_nodes

/-- info: 'Spike.Lib.LowerA64.stubOAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubOAb

/-- info: 'Spike.Lib.LowerA64.stubHAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHAb

/-- info: 'Spike.Lib.LowerA64.ovf_hW_w2_fi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovf_hW_w2_fi

end Spike.Lib.LowerA64
