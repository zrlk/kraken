/-
**The threads abort path's obligations inside `SFactsAC`** (AArch64): the
`Abort.Disp.StubTW` of a jump to `scc_rt_abort` with `x0 = 5` and the
return address `raT lab pfx` (`Spike/Lib/A64AbortThreadsW.lean`) at
`W := SFactsAC … frs Dt (fun _ => False) Cl (ThreadsAb.Ac lab pfx)`, the
twin of `Spike/Lib/A64StubWA.lean` (the write path inside `SFactsA`), for any
program with the abort code (`Scc.Cert.Rt.A64.Abort.abortIn`), an instance's
facts at the frames `frs` and the path's phase check (`abortPhThreadsOk`,
`Spike/Lib/A64AbortPhT.lean`).

The write abort phase is empty (`Ab := fun _ => False`, no `write` refusal
after a spawn); every state of the path is in the threads abort phase `Ac`
(`Spike/Lib/A64ThreadsAb.lean`), so its `AcSt` is `AcSt.of_ac`.

* `sfactsAC_doneT`, `sfactsAC_svcT`: `SFactsAC` in the phase `Ac` at an
  instruction without an event off the sites, and at `svc #0` with the
  threads abort facts and the write tail given;
* `ac_g5A`, `ac_stubA`: the jump to the stub's and the stub's states in `Ac`
  from the abstract state;
* `blkW_threadsAC`, `nodeW_si_threadsAC`: a block and a single instruction of
  the path, each state in the phase (`hAc`);
* `seg_svcTW`, `stubTW_of_code`: the stub's `write` call over `NT` and
  `StubTW` from the abort code (`stubWW_of_code`'s twin);
* `stubTW_sfactsAC`: `StubTW` inside `SFactsAC`, the exit call the threads
  abort site.

Concrete k=5 over `NT`; to be folded into the generic abort files together
with `Abort.NT` (pre-hello.w-release cleanup).
-/
import Spike.Lib.A64StubWA
import Spike.Lib.A64AbortPhT
import Spike.Lib.A64AbortThreadsW
import Spike.Lib.A64SFactsAC
import Spike.Lib.A64ThreadsAcSt

namespace Spike.Lib.A64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Lib.Consumer1 (allInv_true OneCellTy)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerS (OwnS PlacedS)
open Spike.Lib.A64ConsumerA
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.A64.Rt (InstOk owned_off)
open Scc.Cert.Rt.A64 (blockAt Lays endOf)
open Scc.Cert.Rt.A64.Print (code_field add4 add0)

/-! ## `SFactsAC` at one state in the phase -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop} {F : MachineData → Prop}
  {Cl Ac : State → Prop}

open Kraken.Promising.Lower.A64 (CellAt after)

/-- **`SFactsAC` in the phase `Ac` at an instruction without an event** (not
an `svc`, its step `.done s'`), off the marks' sites, at a control with
`RefCtl`'s facts (`sfactsA_doneW` with no write abort phase): the leaf owns
what `s` owns and is in the take phase iff `s` is; `Cl` at `s` is at a
`clone` (`hClS`). -/
theorem sfactsAC_doneT {s' : State} {d : Directive} {sz : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c fs) (hP : PcOff μ s)
    (hcl : CellAt s d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec s = some (.done s'))
    (hown : own s' fs = own s fs) (htk : Tk s' ↔ Tk s) (hO : Tk s → Owned Λ rS s) (hAc : Ac s)
    (hClS : Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl Ac := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hcl hd
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hP.noSite
      mapped := fun _ e he => by rw [hex] at he; cases he; nofun
      place := hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ tree he => by
        rw [hex] at he; cases he
        refine .inl ⟨?_, trivial⟩
        show own s' fs' = own s fs'
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact hown
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ tree he => by rw [hex] at he; cases he; exact htk
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr (noWr_done hex)
      zero := hc.zero
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false
      acSt := AcSt.of_ac hAc
      clSvc := hClS }

/-- **`SFactsAC` in the phase `Ac` at `svc #0`** off the release and take
sites, at a control with `RefCtl`'s facts, with the threads abort facts
(`hab`) and the write tail (`hwr`) given (`sfactsA_svcW` with no write abort
phase): every state the kernel resumes in is past it, owning what `s` owns
and in the take phase iff `s` is. -/
theorem sfactsAC_svcT (hc : RefCtl Λ p own lbl F c fs) (hpl : Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c fs)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hcl : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) fs = own s fs ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → k = .threads ∧
      ∀ v, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) →
        v % 256 = Scc.Sem.Kernel.abortStatus)
    (hwr : ∀ fd buf n, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s)
    (hAc : Ac s)
    (hClS : Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt (fun _ => False) Cl Ac := by
  have hs : abi.atSys s = true := atSvc_of_cellAt hcl
  have hsucc : ∀ call, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call, own s' fs = own s fs ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hcl hd).1 hs'
    exact hnext _
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hrel
      mapped := fun h => by rw [hs] at h; cases h
      place := hpl
      svc := fun _ => ⟨0, 4, hcl⟩
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun _ _ _ h => by rw [hs] at h; cases h
      ownSys := fun c' fs' hr _ call hd s' hs' => by
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact (hsucc call hd s' hs').1
      ownTake := fun a ha hpc => (htake a ha hpc).elim
      site := fun a ha hpc => (htake a ha hpc).elim
      tkTake := fun a ha hpc => (htake a ha hpc).elim
      tkInstr := fun _ h => by rw [hs] at h; cases h
      tkSys := fun _ call hd s' hs' => (hsucc call hd s' hs').2
      owned := hO
      wrTail := fun _ => hwr
      wr := fun _ _ _ h => by rw [hs] at h; cases h
      zero := hc.zero
      abortOk := fun k a ha hpc => let ⟨h1, h2⟩ := hab k a ha hpc; ⟨.inr (.inr (.inr ⟨h1, hAc⟩)), h2⟩
      abInstr := abInstr_false
      abSys := abSys_false
      abTake := abTake_false
      acSt := AcSt.of_ac hAc
      clSvc := hClS }

end State

/-! ## The stub's states in the phase -/

section Phase

variable {lab : Label → Int64} {pfx : String}

/-- A state of the jump to the threads stub with the threads return address,
from the abstract state, is in `Ac`. -/
theorem ac_g5A {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS}
    (hmem : s.st.2 ∈ ThreadsAb.g5Pcs lab) (hA : Flow.Abs R o s.st.1 σ)
    (hr : σ.regs.X30.toBitVec = ThreadsAb.raT lab pfx) : ThreadsAb.Ac lab pfx s :=
  ThreadsAb.ac_g5 hmem (by rw [hA.regs]; exact hr)

/-- A state of the threads stub with the threads return address, from the
abstract state, is in `Ac`. -/
theorem ac_stubA {R : Spike.Lib.Region} {o : Flow.SO} {s : State} {σ : Flow.AS}
    (hmem : s.st.2 ∈ ThreadsAb.stubPcs lab) (hA : Flow.Abs R o s.st.1 σ)
    (hr : σ.regs.X30.toBitVec = ThreadsAb.raT lab pfx) : ThreadsAb.Ac lab pfx s :=
  ThreadsAb.ac_stub hmem (by rw [hA.regs]; exact hr)

end Phase

/-! ## The path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop} {Cl Ac : State → Prop}

/-- **A block of the threads abort path inside `SFactsAC`** at the frames
`frs`: as `blkW_writeA` with no write abort phase, each state before an
instruction in the phase `Ac` (`hAc`), every `Cl` state at a `clone`
(`hCl`). -/
theorem blkW_threadsAC {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hAc : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Flow.Abs R (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Ac { s with st := (m, n.pc + Int64.ofNat (4 * j)) }) :
    BlkW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl Ac)
      K exe endPc R F n blk := by
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [he, ← hI.labOk] at hph
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
  intro s σ c hs hn _ _ hA hD hJc k hk m hA' hDm
  have hac := hAc s σ c k m hJc hk hA'
  obtain rfl := hJ σ c hJc
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } hs hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := Flow.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hcell : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s hs hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hlA : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [hs]
  obtain ⟨m', hex, -, -⟩ := Flow.exec_ai haok hR hal hlo hhi hcell hreg hA'
  rw [hlA] at hex
  obtain ⟨hown, htk⟩ := hph' σ c hJc k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } hs hn hs hn rfl rfl
  exact sfactsAC_doneT hc (hc.place _ (hF _ _ hD hDm)) hP hcell (AI.not_svc hreg) hex
    hown htk (fun _ => owned_off hR (by omega) hl hh hsub (stackOff_stable hfit _ _ (hFO _ hD) hDm)
      fun k' hk' => Option.isSome_iff_exists.mpr (by obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩))
    hac (hCl _)

/-- **A single instruction without an event (`SI`) of the threads abort path
inside `SFactsAC`**: as `nodeW_si_writeA` with no write abort phase, every
state at its pc in the phase `Ac` from the node's invariant and abstract
state (`hAc`), every `Cl` state at a `clone` (`hCl`). -/
theorem nodeW_si_threadsAC {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {si : SI} {l : Label} {k : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat 4).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hAc : ∀ (s : State) σ c, n.J σ c → Flow.Abs R n.o s.st.1 σ → s.st.2 = q → Ac s) :
    NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl Ac)
      K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  rw [hp] at hpc
  have hac := hAc s σ c hJc hA hpc
  obtain rfl := hJ σ c hJc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.A64.Rt.next_same hI hpc hph
  refine ⟨sfactsAC_doneT hc (hc.place s hD) hP.1 hcell
    (by cases si <;> intro imm h <;> cases h) (exec_si hcell) (hnx _).1 (hnx _).2
    (fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_) hac (hCl s), hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## The stub's `write` call and `StubTW` from the code -/

section Code

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region}
  {F : MachineData → Prop} {c0 : Ctl} {ra : BitVec 64} {W : Frag isaLSE2} {K : State → State → Prop}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A stub's `write` system call with the return address inside `W`**
(`seg_svcW` over `Abort.NT`): a segment to its next node, given its code
and its states inside `W`. -/
theorem seg_svcTW {st : Abort.Stub} (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (Abort.NT (_root_.Executable.labels exe).label st c0 ra .svc).pc [svcDir])
    (hW : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .svc)) :
    SegW W K p lbl ms (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .svc))
      (At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label st c0 ra .n5)) := by
  refine (svc_ndW (N := fun _ : Unit => Abort.NT (_root_.Executable.labels exe).label st c0 ra .n5)
    (E := fun e : Empty => e.elim) hK hF hcode hW ?_ ?_).mono_post ?_
  · rintro σ c ⟨hJ, h0, h8⟩
    obtain ⟨buf, n, hc⟩ := svcCall_write h0 h8
    exact ⟨_, hc, fun v _ => ⟨c, .refl c, .inl ⟨(), rfl, rfl, hJ⟩⟩⟩
  · rintro s c σ call - ⟨-, h0, h8⟩ hcall
    obtain ⟨buf, n, hc⟩ := svcCall_write h0 h8
    rw [hc] at hcall
    cases hcall
    exact ⟨nofun, nofun, fun fd b n' h => by cases h; decide, fun _ h => by cases h⟩
  · rintro s c (⟨_, h⟩ | ⟨x, _⟩)
    · exact h
    · exact x.elim

/-- **The threads abort path's obligations from the abort code**: `StubTW`
for a program with `abortIn` (`stubWW_of_code`'s twin), given the
dispatcher's nodes at code 5 and the threads stub's nodes with the return
address inside `W` (the stub's `write` call among them, `hsvc`) and the exit
call at an abort site (`hab`). -/
theorem stubTW_of_code {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (de : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .e) Abort.Disp.d0)
    (dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t1) Abort.Disp.t1)
    (dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j1) Abort.Disp.j1)
    (dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t2) Abort.Disp.t2)
    (dj2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j2) Abort.Disp.j2)
    (dt3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t3) Abort.Disp.t3)
    (dj3 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j3) Abort.Disp.j3)
    (dt4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t4) Abort.Disp.t4)
    (dj4 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .j4) Abort.Disp.j4)
    (dt5 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .t5) Abort.Disp.t5)
    (dg5 : BlkW W K exe endPc R F (Abort.Disp.DN.nd5 (_root_.Executable.labels exe).label c0 ra .g5) Abort.Disp.g5)
    (se : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .e) Abort.b0)
    (sn1 : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n1))
    (sn1b : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n1b))
    (sn2 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n2)
      Abort.b1Threads)
    (hsvc : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .svc))
    (sn5 : BlkW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .n5) Abort.b2)
    (sex : NodeW W K exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .ex))
    (hab : ∀ s c, At exe endPc R F (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0 ra .ex) s c →
      ms.abortAt s) :
    Abort.Disp.StubTW W K p lbl ms exe endPc R F c0 ra := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  have hst := hpr.1.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨-, -, -, -, hsvcIn, -⟩ := hst
  exact ⟨Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2, de, dt1, dj1, dt2, dj2, dt3, dj3, dt4, dj4, dt5, dg5,
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .threads, se, sn1, sn1b, sn2, sn5, sex,
    seg_svcTW hK hF (code_field hp hend hsvcIn (by simp only [Abort.NT, Abort.pcSvc, add4, add0])) hsvc, hab⟩

end Code

/-! ## `StubTW` inside `SFactsAC` (the phase check `abortPhThreadsOk`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop}

open Spike.Lib.A64ConsumerA.ThreadsAcSt

/-- **The threads abort path's obligations inside `SFactsAC … frs Dt
(fun _ => False) Cl (ThreadsAb.Ac lab pfx)`** (`Abort.Disp.StubTW` at the
return address `ThreadsAb.raT lab pfx`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`); as `stubWW_sfactsA`. Every `Cl` state is at a `clone`
(`hCl`). The exit call is the threads abort site: off the release and take
sites (`hrel`, `htk`), no other kind's (`hk`), no outside move (`hKex`), the
memory side's abort (`hms`). The write tail `Dt` holds at the stub's
`write` (`hwr`). -/
theorem stubTW_sfactsAC {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop} {pfx : String} {Cl : State → Prop}
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhThreadsOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hCl : ∀ s, Cl s → abi.atSys s = true ∧
      ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.threads.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.threads.exit).toBitVec.toNat = a → k = .threads)
    (hKex : ∀ s s', pcOf s = (lab Abort.threads.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.threads.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.NT lab Abort.threads c0 (ThreadsAb.raT lab pfx) .svc) s c → Dt s) :
    Abort.Disp.StubTW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
        (ThreadsAb.Ac lab pfx))
      K p al ms exe endPc R F c0 (ThreadsAb.raT lab pfx) := by
  have hlab := hI.labOk
  subst hlab
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, hj4, -, ht5, -, hg5, -⟩ := hdi
  simp only [abortPhThreadsOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pj4, pt5, pg5, pb0, o1, q1, o1b, q1b, pb1, o7, q7, pb2, qx⟩ :=
    hphs
  have hown : ∀ (s : State) (o : SO) σ, Flow.Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he7 : (_root_.Executable.labels exe).label Abort.threads.entry + Int64.ofNat (4 * 7) =
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .svc).pc := by
    simp only [Abort.NT, Abort.pcSvc, add4, add0]
  have hsvcT : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ.1
    subst hc0
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s :=
      ac_stubA (by rw [hpc]; exact memSvcT) hA hJ.2
    rw [← he7] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
    exact ⟨sfactsAC_svcT hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc q7) (hown s _ σ hA hD)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAc (hCl s), hP.2⟩
  have hsex : NodeW (fun s c => SFactsAC Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (fun _ => False) Cl
      (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx)) K exe endPc R F
      (Abort.NT (_root_.Executable.labels exe).label Abort.threads c0
        (ThreadsAb.raT (_root_.Executable.labels exe).label pfx) .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, ⟨hc0, hra⟩, h8, h0⟩
    change c = c0 at hc0
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.threads.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAc : ThreadsAb.Ac (_root_.Executable.labels exe).label pfx s :=
      ac_stubA (by rw [hpc]; exact memExT) hA hra
    have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ.regs.X0.toNat) := by
      rw [← svcCall_exitGroup (by rw [h8]; rfl), svcCall, ← hA.regs]; rfl
    refine ⟨sfactsAC_svcT hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.A64.Rt.cellOf hI hx (add0 _) hs hn hpc)
      (Spike.Lib.A64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨hk k a ha (hpcN ▸ e), fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAc (hCl s), fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    rw [h0]; rfl
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 ∨ Abort.Disp.t1 = Abort.Disp.t5 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 ∨ Abort.Disp.t2 = Abort.Disp.t5 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 ∨ Abort.Disp.t3 = Abort.Disp.t5 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 ∨ Abort.Disp.t4 = Abort.Disp.t5 := .inr (.inr (.inr (.inl rfl)))
  have hT5 : Abort.Disp.t5 = Abort.Disp.t1 ∨ Abort.Disp.t5 = Abort.Disp.t2 ∨ Abort.Disp.t5 = Abort.Disp.t3 ∨
    Abort.Disp.t5 = Abort.Disp.t4 ∨ Abort.Disp.t5 = Abort.Disp.t5 := .inr (.inr (.inr (.inr rfl)))
  have hj : ∀ {j : Nat}, j < Abort.Disp.j1.length → j < 1 := fun h => h
  exact stubTW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_threadsAC hI hd0 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.d0_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispEA (memE5 hk) hA ((congrArg (fun x => x.toBitVec.toNat) (d0_x0 _ _ hk)).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (d0_x30 _ _ hk)).trans hJ.2.2))
    (blkW_threadsAC hI ht1 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t1_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inl rfl) hT1 hk) hA (t_run5 hT1 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT1 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT1 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj1 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j1_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inl rfl) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht2 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t2_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inl rfl)) hT2 hk) hA (t_run5 hT2 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT2 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT2 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj2 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j2_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inl rfl)) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht3 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t3_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_dispTA (memT5 (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run5 hT3 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT3 _ _ hk).2.1).trans hJ.2.1)
        ((congrArg (fun x => x.toBitVec) (t_run5 hT3 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj3 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j3_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inr (.inl rfl))) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht4 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t4_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inl rfl)))) hT4 hk) hA (t_run5 hT4 _ _ hk).1 hoff
          ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT4 _ _ hk).2.1).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (t_run5 hT4 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hj4 (by simp only [Abort.Disp.DN.nd5, add4, add0]) Abort.Disp.j4_ok hR hal (by omega) hhi
      hl hh hF hsub hfit hFO pj4 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ac_dispTA (memJ5 (.inr (.inr (.inr rfl))) (by decide)) hA rfl hoff hJ.2.1 hJ.2.2.2)
    (blkW_threadsAC hI ht5 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.t5_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_dispTA (memT5 (.inr (.inr (.inr (.inr rfl)))) hT5 hk) hA (t_run5 hT5 _ _ hk).1 hoff
          ((congrArg (fun f => (f (-32)).toNat) (t_run5 hT5 _ _ hk).2.1).trans hJ.2.1)
          ((congrArg (fun x => x.toBitVec) (t_run5 hT5 _ _ hk).2.2).trans hJ.2.2.2))
    (blkW_threadsAC hI hg5 (by simp only [Abort.Disp.DN.nd5, add0]) Abort.Disp.g5_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pg5 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA => ac_g5A (memG5 hk) hA (g5_x30 _ _ hJ.2.1 hJ.2.2 hk))
    (blkW_threadsAC hI hb0 (by simp only [Abort.NT, add0]) Abort.b0_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubA (memB0T hk) hA ((congrArg (fun x => x.toBitVec) (b0_x30 _ _ hk)).trans hJ.2))
    (nodeW_si_threadsAC (si := .adrp .X9 Abort.threads.msg) hI hn1 rfl (by simp only [Abort.NT, add0]) o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubA (by rw [h, add0]; exact memN1T.1) hA hJ.2)
    (nodeW_si_threadsAC (si := .addLo12 .X9 .X9 Abort.threads.msg) hI hn1b rfl
      (by simp only [Abort.NT, add4, add0]) o1b q1b hR hR8 hl hh hsub hFO (fun _ _ h => h.1) hc hCl
      fun _ _ _ hJ hA h => ac_stubA (by rw [h, add4, add0]; exact memN1T.2) hA hJ.2)
    (blkW_threadsAC hI hb1 (by simp only [Abort.NT, add4, add0]) Abort.b1Threads_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubA (memB1T hk) hA ((congrArg (fun x => x.toBitVec) (b1T_x30 _ _ hk)).trans hJ.2))
    hsvcT
    (blkW_threadsAC hI hb2 (by simp only [Abort.NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h.1) hc hCl
      fun _ σ _ _ _ hJ hk hA =>
        ac_stubA (memB2T hk) hA ((congrArg (fun x => x.toBitVec) (b2_x30 _ _ hk)).trans hJ.2))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.StubW.stubTW_sfactsAC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubTW_sfactsAC

end Spike.Lib.A64.StubW
