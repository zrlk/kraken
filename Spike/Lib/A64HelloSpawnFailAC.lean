/-
**hello.w on AArch64: main after a refused `clone` inside `SFactsAC`**: the block obligations `hWcb`, `hWcl`, `hWfl`
of
`seg_spawnFailW_hello` (`Spike/Lib/A64HelloSpawnFail.lean`) at
`W := SFactsAC … frs Dt (fun _ => False) Cl (Hello.ThreadsAb.AcH lab pfxM)`.
wake.w's (`Spike/Lib/A64SpawnFailAC.lean`) at hello's frame of 144 and
listing (`SccCode.helloProg`): the `cbz` at `pcRetH` (`.sp6 + 4·25 + 4`),
`.clone13`'s store and tests with the stored result `[sp + 112]` (`slot
(-32)` of main's frame), `.1_spawnfail5`; each is `blkW_threadsAC`
(`Spike/Lib/A64StubTAC.lean`, generic in the phase).

- `cl_run_sp`: `.clone13`'s block past its store keeps main's frame offset
  and has the stored `x0` at `slot (-32)`.
- `sp112`: the word at `[sp + 112]` from the abstract state in main's frame.
- `ac_cb`, `ac_cl`, `ac_fl`: the blocks' states in `AcH`.
- `blkWs_spawnFail_hello`: the three obligations for an instance of
  `helloProg`, given the blocks' phase checks.

Deferred: the threads stub's `StubTW` at `AcH` (wake's
`A64StubTAC` names `ThreadsAb.Ac`) and the phase's `AcSt` checks
(`A64ThreadsAcSt`) are B4c.
-/
import Spike.Lib.A64HelloSpawnFail
import Spike.Lib.A64HelloThreadsAb
import Spike.Lib.A64StubTAC

namespace Spike.Lib.A64.Flow.Worker.Hello.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (abi)
open Scc.Cert.Rt.A64 (blockAt labelGap)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (SFactsAC)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cbzD)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (oP clp cl cbP_ok cl_ok)
open SccCode (helloProg)
open Spike.Lib.A64.ThreadsAb (CloneRef)
open Spike.Lib.A64.Hello.ThreadsAb (AcH)
open Spike.Lib.A64.StubW (RefCtl blkW_threadsAC)

set_option linter.unusedSimpArgs false

/-! ## The blocks' abstract runs -/

/-- The abstract run's simp set (`Spike/Lib/A64StubWA.lean`'s, with `upd`). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Flow.arun, Flow.dstep, Flow.classify, Flow.RegOnly, Flow.AI.so, Flow.AI.step, Flow.AI.tgt,
    Flow.soReg, Flow.regDst, Flow.zrB, Flow.regRes, Operation.interp, MachineData.setRegOrZr,
    MachineData.setRegOrSp, Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64,
    Reg64s.setRegOrSp, Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg,
    Reg64s.getXReg, ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Flow.SO.get, Flow.SO.set, Flow.SO.kill, Flow.SO.write, Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm,
    Spike.Lib.upd_apply])

/-- `.clone13`'s block past its store keeps main's frame offset and has the
stored `x0` at `slot (-32)` (`[sp + 112]`). -/
theorem cl_run_sp (lab : Label → Int64) (pfx : String) (pc : Int64) (σ : AS) {k : Nat}
    (hk : k < (cl pfx).length) (h1 : 1 ≤ k) :
    (arun lab ((cl pfx).take k) ⟨pc, oP, σ⟩).so.sp = -144 ∧
      (arun lab ((cl pfx).take k) ⟨pc, oP, σ⟩).σ.slot (-32) = σ.regs.X0.toBitVec := by
  simp only [cl, clp] at hk ⊢
  simp only [List.length_cons, List.length_nil, List.length_append] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

theorem cb_noRet (pfx : String) : noRetBlk (cb pfx) = true := by
  simp [noRetBlk, cb, cbzD, Flow.classify]

theorem cl_noRet (pfx : String) : noRetBlk (cl pfx) = true := by
  simp [noRetBlk, cl, clp, bcD, Flow.classify]

theorem flB_noRet : noRetBlk flB = true := by decide

/-- The word at `[sp + 112]` from the abstract state, `sp` at main's frame's
`-144`: `slot (-32)`. -/
theorem sp112 {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ) (ho : o.sp = -144)
    (hoff : R.Off (-32)) : Spike.Lib.A64.WriteAb.spLoad s 112 = some (σ.slot (-32)) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-32) hoff
  have hsp := hA.so .SP o.sp rfl
  rw [← hA.regs, ho] at hsp
  simp only [Reg64s.getRegOrSp64] at hsp
  simp only [Spike.Lib.A64.WriteAb.spLoad, Scc.Sem.A64.privLoad, hsp]
  have h112 : R.addr (-144) + 112 = R.addr (-32) := by
    rw [show (-32 : Int) = -144 + 112 by rfl, Spike.Lib.Region.addr_add]; rfl
  rw [h112, hj, Option.map_some, hjv]

/-! ## The blocks' states in `Ac` -/

section Ac

variable {lab : Label → Int64} {pfx : String} {cP : Ctl} {cA mT : BitVec 64} {R : Spike.Lib.Region}

/-- The `cbz` after the call, `x0` a refusal, is in `Ac`. -/
theorem ac_cb (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData) (hJ : (fN pfx lab cP cA mT .cb).J σ c)
    (hj : j < (cb pfx).length)
    (hA : Abs R (arun lab ((cb pfx).take j) ⟨(fN pfx lab cP cA mT .cb).pc, (fN pfx lab cP cA mT .cb).o, σ⟩).so m
      (arun lab ((cb pfx).take j) ⟨(fN pfx lab cP cA mT .cb).pc, (fN pfx lab cP cA mT .cb).o, σ⟩).σ) :
    AcH lab pfx { s with st := (m, (fN pfx lab cP cA mT .cb).pc + Int64.ofNat (4 * j)) } := by
  obtain rfl : j = 0 := by simp only [cb, List.length_append, List.length_nil, List.length_cons] at hj; omega
  refine Spike.Lib.A64.Hello.ThreadsAb.ac_ret ?_ ?_
  · show lab (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4 + Int64.ofNat (4 * 0) =
      lab (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4
    exact Scc.Cert.Rt.A64.Print.add0 _
  · show CloneRef m.regs.X0.toBitVec
    rw [hA.regs]
    exact hJ.2.1

/-- `.clone13`'s store and tests are in `Ac`: `x0` a refusal at the store,
the stored result `[sp + 112]` past it. -/
theorem ac_cl (hoff : R.Off (-32)) (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData)
    (hJ : (fN pfx lab cP cA mT .cl).J σ c) (hj : j < (cl pfx).length)
    (hA : Abs R (arun lab ((cl pfx).take j) ⟨(fN pfx lab cP cA mT .cl).pc, (fN pfx lab cP cA mT .cl).o, σ⟩).so m
      (arun lab ((cl pfx).take j) ⟨(fN pfx lab cP cA mT .cl).pc, (fN pfx lab cP cA mT .cl).o, σ⟩).σ) :
    AcH lab pfx { s with st := (m, (fN pfx lab cP cA mT .cl).pc + Int64.ofNat (4 * j)) } := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · refine .inr (.inl ⟨?_, ?_⟩)
    · show lab (pfx ++ ".clone13") + Int64.ofNat (4 * 0) = lab (pfx ++ ".clone13")
      exact Scc.Cert.Rt.A64.Print.add0 _
    · show CloneRef m.regs.X0.toBitVec
      rw [hA.regs]
      exact hJ.2.1
  · obtain ⟨hsp, hsl⟩ := cl_run_sp lab pfx (fN pfx lab cP cA mT .cl).pc σ hj h1
    refine .inr (.inr (.inl ⟨?_, _, sp112 (s := { s with st := (m, _) }) hA hsp hoff, ?_⟩))
    · have hj5 : j < 5 := by
        simpa only [cl, clp, List.length_append, List.length_nil, List.length_cons] using hj
      show lab (pfx ++ ".clone13") + Int64.ofNat (4 * j) ∈ Spike.Lib.A64.Hello.ThreadsAb.tailPcsH lab pfx
      rcases j with _|_|_|_|_|j <;> (try omega) <;> simp [Spike.Lib.A64.Hello.ThreadsAb.tailPcs]
    · show CloneRef ((arun lab ((cl pfx).take j) ⟨(fN pfx lab cP cA mT .cl).pc, oP, σ⟩).σ.slot (-32))
      rw [hsl]
      exact hJ.2.1

/-- `.1_spawnfail5` is in `Ac`. -/
theorem ac_fl (s : State) (j : Nat) (m : MachineData) (hj : j < flB.length) :
    AcH lab pfx { s with st := (m, (fN pfx lab cP cA mT .fl).pc + Int64.ofNat (4 * j)) } := by
  have hj2 : j < 2 := by simpa [flB] using hj
  refine Spike.Lib.A64.Hello.ThreadsAb.ac_fail ?_
  show lab (pfx ++ ".1_spawnfail5") + Int64.ofNat (4 * j) ∈ Spike.Lib.A64.ThreadsAb.failPcs lab pfx
  rcases j with _|_|j <;> (try omega) <;> simp [Spike.Lib.A64.ThreadsAb.failPcs]

end Ac

/-! ## The obligations in hello's program -/

section Hello

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {lab : Label → Int64} {μ : Marks} {own : Spike.Lib.A64ConsumerS.OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`seg_spawnFailW_hello`'s block obligations inside `SFactsAC`** (`hWcb`,
`hWcl`, `hWfl`) at the threads abort phase of main (`pfxM`), for an instance
of `helloProg` at the frames `frs` (`hI`), main's frame in `R` (`hlo`,
`hhi`), the source control `cP` with `RefCtl`'s facts (`hc`), every `Cl`
state at a `clone` (`hCl`) and the blocks' phase checks (`pcb`, `pcl`,
`pfl`). -/
theorem blkWs_spawnFail_hello {kp : Nat}
    (hI : InstOk exe endPc helloProg lab μ (fun s => own s frs) Tk K okPc ph kp)
    {cP : Ctl} {cA mT : BitVec 64} {Dt Cl : State → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F cP frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (pcb : blkPh okPc ph (fun _ => false) lab (lab (pfxM ++ ".sp6") + Int64.ofNat (4 * 26)) 0 (cb pfxM) = true)
    (pcl : blkPh okPc ph (fun _ => false) lab (lab (pfxM ++ ".clone13") + Int64.ofNat (4 * 0)) 0 (cl pfxM) = true)
    (pfl : blkPh okPc ph (fun _ => false) lab (lab (pfxM ++ ".1_spawnfail5") + Int64.ofNat (4 * 0)) 0 flB = true) :
    BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (AcH lab pfxM))
        K exe endPc R F (fN pfxM lab cP cA mT .cb) (cb pfxM) ∧
      BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (AcH lab pfxM))
        K exe endPc R F (fN pfxM lab cP cA mT .cl) (cl pfxM) ∧
      BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (AcH lab pfxM))
        K exe endPc R F (fN pfxM lab cP cA mT .fl) flB := by
  have hlab := hI.labOk
  subst hlab
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hin := hello_failIn
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, -⟩, hcl⟩, hfl⟩ := hin
  refine ⟨?_, ?_, ?_⟩
  · exact blkW_threadsAC hI hcb (by simp only [fN, ofNat4_succ]) cbP_ok hR hal hlo hhi hl hh hF hsub hfit hFO
      pcb (cb_noRet _) (fun _ _ h => h.1) hc hCl fun s σ c j m hJ hj hA => ac_cb s σ c j m hJ hj hA
  · exact blkW_threadsAC hI hcl (by simp only [fN, ofNat4_zero]) cl_ok hR hal hlo hhi hl hh hF hsub hfit hFO
      pcl (cl_noRet _) (fun _ _ h => h.1) hc hCl fun s σ c j m hJ hj hA => ac_cl hoff s σ c j m hJ hj hA
  · exact blkW_threadsAC hI hfl (by simp only [fN, ofNat4_zero]) flB_ok hR hal hlo hhi hl hh hF hsub hfit hFO
      pfl flB_noRet (fun _ _ h => h.1) hc hCl fun s _ _ j m _ hj _ => ac_fl s j m hj

end Hello

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.blkWs_spawnFail_hello' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms blkWs_spawnFail_hello

end Spike.Lib.A64.Flow.Worker.Hello.SpawnFail
