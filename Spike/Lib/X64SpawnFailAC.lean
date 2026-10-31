/-
**wake.w on x86-64: main after a refused `clone` inside `SFactsAC`**: the
obligations `hWts`, `hWje`, `hWx22`, `hWfl` of `seg_failW` /
`seg_spawnFailW` (`Spike/Lib/X64WakeSpawnFail.lean`) at
`W := SFactsAC … frs Dt (fun _ => False) Cl (ThreadsAb.Ac lab pfxM)`, the
twin of `Spike/Lib/A64SpawnFailAC.lean`.

Every state of the path is in the threads abort phase `Ac`
(`Spike/Lib/X64ThreadsAb.lean`): the `testq` at `pcRet` and the `je` at
`pcJe` with `%rax` a refusal, `.x22`'s store at `pcSt` with `%rax` a
refusal, `.x22`'s tests with the stored result `-56(%rbp)` (`slot (-56)` of
main's frame) a refusal, `.spawnfail5` unconditionally; the blocks are
`blkW_threadsAC` and the test row `nodeW_test_threadsAC`.

- `sfactsAC_silentT`: `SFactsAC` in the phase at an instruction whose step
  is a silent tree (`sfactsAC_doneT`'s twin for a `choose`).
- `nodeW_test_threadsAC`: a `testq` row inside `SFactsAC` (`nodeW_si_threadsAC`'s
  twin at `testDir`, its tree a choice of the `AF` bit).
- `x22_run`: `.x22`'s block past its store keeps `%rbp` at the frame's base
  and has the stored `%rax` at `slot (-56)`.
- `bp56`: the word at `-56(%rbp)` from the abstract state.
- `ac_ts`, `ac_je'`, `ac_x22`, `ac_fl`: the nodes' states in `Ac`.
- `failInB`, `wake_failInB`: the path's code as `blockAtB` facts in
  `wakeCells`.
- `blkWs_spawnFail_wake`: the four obligations for an instance of
  `wakeCells`, given the nodes' phase checks.

**Unlike AArch64**: four nodes (`ts`, `je`, `x22`, `fl`; A64: `cb`, `cl`,
`fl`), the result's test a row whose obligation is a `NodeW`
(`nodeW_test_threadsAC`, with its phase check as `okPc`/`ph` premises
`pts`/`phts` rather than a `blkPh`) and the `je` a block at `pcJe` (no A64
counterpart); the stored result is at `-56(%rbp)` (`slot (-56)`, A64:
`[sp + 48]`, `slot (-32)`), so `.x22`'s tail needs `R.Off (-56)` and `%rbp`
at the frame's base (`x22_run`); the code facts are `blockAtB` on
`wakeCells` (`wake_failInB`, by `decide +kernel`: `blkW_threadsAC` reads
`blockAtB`, `X64WakeSpawnFail.failIn` is `blockAt`); the region is
`[-72, 16)` (`.spawnfail5`'s `call` pushes at `-72`) with `R.base`
8-aligned (`hR8`, no `hal`); main's word is `mT` (`fN`'s `m`).
-/
import Spike.Lib.X64WakeSpawnFail
import Spike.Lib.X64StubTAC
import Spike.Lib.X64WakeStartWfL

namespace Spike.Lib.X64.WakePh.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf abi atSyscall_false_of_cellAt)
open Spike.Lib.Consumer1 (OwnTree)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerS (OwnS)
open Spike.Lib.X64ConsumerA
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk owned_off)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower (SilentTree)
open Kraken.Promising.Lower.X64 (CellAt after)
open Spike.Lib.X64.WakePh.WcClone (oW x21L)
open Spike.Lib.X64.WakePh.Parent (tsB jeB x22B x22L jeB_ok x22B_ok)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.ThreadsAb (CloneRef Ac)
open Spike.Lib.X64.StubW (RefCtl blkW_threadsAC)

/-! ## `SFactsAC` at a silent tree and a `testq` row -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop} {F : MachineData → Prop}
  {Cl Ac : State → Prop}

/-- **`SFactsAC` in the phase `Ac` at an instruction whose step is a silent
tree** (not a `syscall`) off the marks' sites, at a control with `RefCtl`'s
facts (`sfactsAC_doneT` at a `choose`): every leaf owns what `s` owns and is
in the take phase iff `s` is; `Cl` at `s` is at a `clone` (`hClS`). -/
theorem sfactsAC_silentT {d : Directive} {sz : Nat} {P : State → Prop} {tree : EvTree State}
    (hc : RefCtl Λ p own lbl F c fs) (hpl : Spike.Lib.X64ConsumerS.PlacedSE Λ lbl s c fs) (hP : PcOff μ s)
    (hcl : CellAt s d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some tree)
    (hst : SilentTree P tree) (hnext : ∀ s', P s' → own s' fs = own s fs ∧ (Tk s' ↔ Tk s))
    (hO : Tk s → Owned Λ rS s) (hAc : Ac s)
    (hClS : Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl Ac := by
  have hs : abi.atSys s = false := atSyscall_false_of_cellAt hcl hd
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hP.noSite
      mapped := fun _ e he => by
        rw [hex] at he; cases he
        exact (silent_facts (Q := fun _ => True) (G := fun _ _ => True) (G' := fun _ _ => True)
          (fun _ _ => trivial) hst).1
      place := hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ t he => by
        rw [hex] at he; cases he
        have h := silent_facts (p := fun _ _ => True) (Q := fun s' => own s' fs' = own s fs')
          (G := fun _ _ => True) (G' := fun l _ => ∀ w, (l, w) ∉ own s fs')
          (fun s' hs' => by rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]; exact (hnext s' hs').1) hst
        exact .inl ⟨h.2.1, h.2.2⟩
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ t he => by
        rw [hex] at he; cases he
        exact (silent_facts (p := fun _ _ => True) (Q := fun s' => Tk s' ↔ Tk s) (G := fun _ _ => True)
          (G' := fun _ _ => True) (fun s' hs' => (hnext s' hs').2) hst).2.1
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr fun L hL => by
        rcases hL with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [hex] at h <;> cases h <;> exact hst.elim
      zero := hc.zero
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false
      acSt := AcSt.of_ac hAc
      clSvc := hClS }

end State

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop} {Cl Ac : State → Prop}

/-- **A `testq %b, %a` row of the threads abort path inside `SFactsAC`**
(`nodeW_si_threadsAC` at `testDir a b`, its step a choice of the `AF` bit,
`exec_test`): every state at its pc in the phase `Ac` from the node's
invariant and abstract state (`hAc`), every `Cl` state at a `clone`
(`hCl`). -/
theorem nodeW_test_threadsAC {kp : Nat}
    (hI : InstOk exe endPc cells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {a b : Reg64} {l : Label} {off z : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAtB cells l off [(testDir a b, z)] = true) (he : lab l + Int64.ofNat off = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat z).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hAc : ∀ (s : State) σ c, n.J σ c → Abs R n.o s.st.1 σ → s.st.2 = q → Ac s) :
    NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl Ac)
      K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  rw [hp] at hpc
  have hac := hAc s σ c hJc hA hpc
  obtain rfl := hJ σ c hJc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  obtain ⟨t, hex, hst⟩ := exec_test hcell
  refine ⟨sfactsAC_silentT hc (hc.place s hD) hP.1 hcell (by intro w w' h; cases h) hex hst
    (fun s' ⟨_, h⟩ => by subst h; exact hnx _)
    (fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_) hac (hCl s), hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## The path's states in `Ac` -/

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over `.x22`'s block
(`Spike/Lib/X64ThreadsAcSt.lean`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- `.x22`'s block past its store keeps `%rbp` at main's frame's base and
has the stored `%rax` at `slot (-56)`. -/
theorem x22_run (lab : Label → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < x22B.length) (h1 : 1 ≤ k) :
    (arun lab (x22B.take k) ⟨pc, oW, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (x22B.take k) ⟨pc, oW, σ⟩).σ.slot (-56) = σ.regs.get64 .rax := by
  simp only [x22B] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The word at `-56(%rbp)` from the abstract state, `%rbp` at the frame's
base. -/
theorem bp56 {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ)
    (ho : o.get .rbp = some 0) (hoff : R.Off (-56)) :
    Spike.Lib.X64.WriteAb.bpLoad s (-56) = some (σ.slot (-56)) := by
  have := ThreadsAcSt.load_of_abs hA (r := .rbp) (k := -56) (d := -56) (by simpa using ho) hoff
  rw [← this]; rfl

/-- A disjunction of up to four equations, one of them by `rfl`. -/
local macro "pick_rfl" : tactic =>
  `(tactic| first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) |
    exact Or.inr (Or.inr (Or.inr rfl)) | exact Or.inr rfl | rfl)

section Ac

variable {lab : Label → Int64} {cP : Ctl} {cA mT : BitVec 64} {R : Region}

/-- The `testq` after the call, `%rax` a refusal, is in `Ac`. -/
theorem ac_ts (s : State) (σ : AS) (c : Ctl) (hJ : (fN lab cP cA mT .ts).J σ c)
    (hA : Abs R (fN lab cP cA mT .ts).o s.st.1 σ) (hp : s.st.2 = lab x21L + Int64.ofNat 48) :
    Ac lab pfxM s := by
  refine Spike.Lib.X64.ThreadsAb.ac_ret ?_ ?_
  · rw [hp]; show lab x21L + Int64.ofNat 48 = lab x21L + 46 + 2
    rw [Int64.add_assoc]; rfl
  · rw [hA.regs]; exact hJ.2.1

/-- The `je` after the test, `%rax` a refusal, is in `Ac`. -/
theorem ac_je' (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData) (hJ : (fN lab cP cA mT .je).J σ c)
    (hj : j < jeB.length)
    (hA : Abs R (arun lab (jeB.take j) ⟨(fN lab cP cA mT .je).pc, (fN lab cP cA mT .je).o, σ⟩).so m
      (arun lab (jeB.take j) ⟨(fN lab cP cA mT .je).pc, (fN lab cP cA mT .je).o, σ⟩).σ) :
    Ac lab pfxM { s with st := (m, (fN lab cP cA mT .je).pc + Int64.ofNat (cellOff jeB j)) } := by
  obtain rfl : j = 0 := by simp only [jeB, List.length_zip, List.length_cons, List.length_nil] at hj; omega
  refine Spike.Lib.X64.ThreadsAb.ac_je ?_ ?_
  · show lab x21L + 51 + Int64.ofNat (cellOff jeB 0) = lab x21L + 46 + 5
    rw [cellOff_zero, ofNat_zero', Int64.add_assoc]; rfl
  · show CloneRef m.regs.rax.toBitVec
    rw [hA.regs]
    exact hJ.2.1

/-- `.x22`'s store and tests are in `Ac`: `%rax` a refusal at the store,
the stored result `-56(%rbp)` past it. -/
theorem ac_x22 (hoff : R.Off (-56)) (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData)
    (hJ : (fN lab cP cA mT .x22).J σ c) (hj : j < x22B.length)
    (hA : Abs R (arun lab (x22B.take j) ⟨(fN lab cP cA mT .x22).pc, (fN lab cP cA mT .x22).o, σ⟩).so m
      (arun lab (x22B.take j) ⟨(fN lab cP cA mT .x22).pc, (fN lab cP cA mT .x22).o, σ⟩).σ) :
    Ac lab pfxM { s with st := (m, (fN lab cP cA mT .x22).pc + Int64.ofNat (cellOff x22B j)) } := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · refine .inr (.inl ⟨?_, ?_⟩)
    · show lab x22L + Int64.ofNat (cellOff x22B 0) = lab x22L
      rw [cellOff_zero]; exact ofNat_zero' _
    · show CloneRef m.regs.rax.toBitVec
      rw [hA.regs]
      exact hJ.2.1
  · obtain ⟨hbp, hsl⟩ := x22_run lab (fN lab cP cA mT .x22).pc σ hj h1
    refine .inr (.inr (.inl ⟨?_, _, bp56 (s := { s with st := (m, _) }) hA hbp hoff, ?_⟩))
    · have hj5 : j < 5 := by simp [x22B] at hj; omega
      show lab x22L + Int64.ofNat (cellOff x22B j) ∈ Spike.Lib.X64.ThreadsAb.tailPcs lab pfxM
      simp only [Spike.Lib.X64.ThreadsAb.tailPcs, List.mem_cons, List.mem_nil_iff, or_false]
      rcases j with _|_|_|_|_|j <;> (try omega) <;> pick_rfl
    · exact (congrArg CloneRef hsl).mpr hJ.2.1

/-- `.spawnfail5` is in `Ac`. -/
theorem ac_fl (s : State) (j : Nat) (m : MachineData) (hj : j < flB.length) :
    Ac lab pfxM { s with st := (m, (fN lab cP cA mT .fl).pc + Int64.ofNat (cellOff flB j)) } := by
  have hj2 : j < 2 := by simpa [flB] using hj
  refine Spike.Lib.X64.ThreadsAb.ac_fail ?_
  show lab flL + Int64.ofNat (cellOff flB j) ∈ Spike.Lib.X64.ThreadsAb.failPcs lab pfxM
  simp only [Spike.Lib.X64.ThreadsAb.failPcs, List.mem_cons, List.mem_nil_iff, or_false]
  rcases j with _|_|j
  · exact .inl (by rw [cellOff_zero]; exact ofNat_zero' _)
  · exact .inr rfl
  · omega

end Ac

/-! ## The obligations in wake's program -/

/-- **The refusal path's code as `blockAtB` facts** (`failIn`'s blocks and
row, by byte offset). -/
def failInB (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells x21L 48 tsB && blockAtB cells x21L 51 jeB && blockAtB cells x22L 0 x22B &&
    blockAtB cells flL 0 flB

theorem wake_failInB : failInB SccCode.wakeCells = true := by decide +kernel

section Wake

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.X64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop}

/-- **`seg_spawnFailW`'s node obligations inside `SFactsAC`** (`hWts`,
`hWje`, `hWx22`, `hWfl`) at the threads abort phase of main (`pfxM`), for an
instance of `wakeCells` at the frames `frs` (`hI`), main's frame in `R`
(`hlo`, `hhi`), the source control `cP` with `RefCtl`'s facts (`hc`), every
`Cl` state at a `clone` (`hCl`) and the nodes' phase checks (`pts`/`phts`,
`pje`, `px22`, `pfl`). -/
theorem blkWs_spawnFail_wake {kp : Nat}
    (hI : InstOk exe endPc SccCode.wakeCells lab μ (fun s => own s frs) Tk K okPc ph kp)
    {cP : Ctl} {cA mT : BitVec 64} {Dt Cl : State → Prop}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F cP frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (pts : okPc (lab x21L + Int64.ofNat 48).toBitVec.toNat = true)
    (phts : ph (lab x21L + Int64.ofNat 48 + Int64.ofNat 3).toBitVec.toNat =
      ph (lab x21L + Int64.ofNat 48).toBitVec.toNat)
    (pje : blkPh okPc ph (fun _ => false) lab (lab x21L + Int64.ofNat 51) 0 jeB = true)
    (px22 : blkPh okPc ph (fun _ => false) lab (lab x22L + Int64.ofNat 0) 0 x22B = true)
    (pfl : blkPh okPc ph (fun _ => false) lab (lab flL + Int64.ofNat 0) 0 flB = true) :
    NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (Ac lab pfxM))
        K exe endPc R F (fN lab cP cA mT .ts) ∧
      BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (Ac lab pfxM))
        K exe endPc R F (fN lab cP cA mT .je) jeB ∧
      BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (Ac lab pfxM))
        K exe endPc R F (fN lab cP cA mT .x22) x22B ∧
      BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl (Ac lab pfxM))
        K exe endPc R F (fN lab cP cA mT .fl) flB := by
  have hlab := hI.labOk
  subst hlab
  have hoff : R.Off (-56) := ⟨by decide, by omega, by omega⟩
  have hin := wake_failInB
  simp only [failInB, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hts, hje⟩, hx22⟩, hfl⟩ := hin
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact nodeW_test_threadsAC hI hts rfl rfl pts phts hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun s σ c hJ hA hp => ac_ts s σ c hJ hA hp
  · exact blkW_threadsAC hI hje rfl jeB_ok hR hR8 (by omega) hhi hl hh hF hsub hfit hFO
      pje (by decide) (fun _ _ h => h.1) hc hCl fun s σ c j m hJ hj hA => ac_je' s σ c j m hJ hj hA
  · exact blkW_threadsAC hI hx22 (ofNat_zero' _) x22B_ok hR hR8 (by omega) hhi hl hh hF hsub hfit hFO
      px22 (by decide) (fun _ _ h => h.1) hc hCl fun s σ c j m hJ hj hA => ac_x22 hoff s σ c j m hJ hj hA
  · exact blkW_threadsAC hI hfl (ofNat_zero' _) flB_ok hR hR8 hlo hhi hl hh hF hsub hfit hFO
      pfl (by decide) (fun _ _ h => h.1) hc hCl fun s _ _ j m _ hj _ => ac_fl s j m hj

end Wake

end Spike.Lib.X64.WakePh.SpawnFail

/--
info: 'Spike.Lib.X64.WakePh.SpawnFail.sfactsAC_silentT' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.sfactsAC_silentT

/--
info: 'Spike.Lib.X64.WakePh.SpawnFail.nodeW_test_threadsAC' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.nodeW_test_threadsAC

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.x22_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.x22_run

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.bp56' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.bp56

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.ac_ts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.ac_ts

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.ac_je'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.ac_je'

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.ac_x22' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.ac_x22

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.ac_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.ac_fl

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.wake_failInB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.wake_failInB

/--
info: 'Spike.Lib.X64.WakePh.SpawnFail.blkWs_spawnFail_wake' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.blkWs_spawnFail_wake
