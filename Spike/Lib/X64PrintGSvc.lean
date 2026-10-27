/-
**`scc_rt_print`'s system call at any instance** (x86-64): the state's
facts (`SFactsSt`) and the write abort's phase (`AbSt` at `WriteAb.Ab`) at
`PrintA.N … .sys`, the `write` of `print`'s loop, for any executable with
`InstOk`, its cells holding the routine's code (`printIn`) passing the
phase check `printPhOk`: the twin of `Spike/Lib/A64PrintGSvc.lean`, the
place-independent parts of `PrintW`'s system-call obligation at `W2`
(`Spike/Lib/LowerX64/PrintCallC2.lean`).

- `decode_print`: `%rax = 1`, `%rdi = 1` decode to a `write` to the
  standard output of `%rdx` bytes at `%rsi`.
- `pcRet_nmem`: the pc after the call is no other pc of the phase.
- `ret_ab`: a kernel return from the call in the phase refuses the stored
  length (`-16(%rbp)`).
- `bpLoad_of_abs`: the stored length is the frame's cell `-16` (`%rbp` at
  `0`).
- `pcSys_eq`, `sys_cell`: the call's pc, and its facts at a state of its
  node.
- `printSvcSt`: the call's states carry `SFactsSt`, the write tail `Dt`
  given at the node (`hDt`), the range owned from the frame condition
  (`hFO`).
- `callee_facts`: a callee's region at a 16-aligned offset is valid and
  16-aligned.
- `printSvcStP`: `printSvcSt` in `print`'s region at a call, under a frame
  condition inside `print`'s (`pF`, `PrintW`'s system-call clause).
- `printSvcAb`: the call's states keep the write abort's phase: off it, a
  return lands in it only as a refusal of the length passed (`%rdx`, the
  frame's cell `-16`).
- `printSvcWe`: every refused result of the call lands in the phase (`WeAb`).

Where x86-64 differs from AArch64: the call is a 2-byte `syscall` at
`.Lscc_rt_print.write + 20`; the kernel may also resume an `arch_prctl`
(not this call, but `SFactsSt` quantifies over every decoded call); the
stored length is read at `%rbp - 16`; `print`'s region at a call is
`R.callee kb (-40) 16`.
-/
import Spike.Lib.X64PrintG
import Spike.Lib.X64PrintCall
import Spike.Lib.LowerX64.AllocRa
import Spike.Lib.X64PrintAb

namespace Spike.Lib.X64.PrintG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW ND AS)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB InRunB pc_ne_of_inRunB Lays)
open Spike.Lib.X64ConsumerA (SFactsSt AbSt)
open Spike.Lib.X64.WriteAb (Ab abPcs bpLoad pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)
open Spike.Lib.LowerX64 (abPos abPcs_eq abPos_inRunB)
open Spike.Lib.X64.AllocG (phOne_spec)
open Spike.Lib.X64.PrintA (N)
open Kraken.Promising.Lower.X64 (CellAt after op64)

/-! ## The call and its return -/

/-- **`%rax = 1`, `%rdi = 1` decode to a `write`** to the standard output of
`%rdx` bytes at `%rsi`. -/
theorem decode_print {s : State} (hax : s.st.1.regs.get64 .rax = 1) (hdi : s.st.1.regs.get64 .rdi = 1) :
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) =
      some (.write 1 (s.st.1.regs.get64 .rsi).toNat (s.st.1.regs.get64 .rdx).toNat) := by
  simp only [Reg64s.get64] at hax hdi ⊢
  have h1 : s.st.1.regs.rax.toNat = 1 := by show s.st.1.regs.rax.toBitVec.toNat = 1; rw [hax]; rfl
  have h2 : s.st.1.regs.rdi.toNat = 1 := by show s.st.1.regs.rdi.toBitVec.toNat = 1; rw [hdi]; rfl
  simp [abi, Kernel.decode, Kernel.Nrs.x64, h1, h2]

section Ret

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **The pc after the call is no other pc of the phase**: `pcRet` is
`abPos`'s first position, its others told apart from it by
`pc_ne_of_inRunB`. -/
theorem pcRet_nmem (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) :
    pcRet (_root_.Executable.labels exe).label ∉
      tailPcs (_root_.Executable.labels exe).label ++ failPcs (_root_.Executable.labels exe).label ++
        dispEPcs (_root_.Executable.labels exe).label ++ dispTPcs (_root_.Executable.labels exe).label ++
        g4Pcs (_root_.Executable.labels exe).label ++ stubPcs (_root_.Executable.labels exe).label := by
  have hpos : abPos = (".Lscc_rt_print.write", 22) :: abPos.tail := by decide
  have hnin : (".Lscc_rt_print.write", 22) ∉ abPos.tail := by decide
  have h := abPcs_eq (_root_.Executable.labels exe).label
  rw [hpos, List.map_cons] at h
  simp only [abPcs, List.cons_append] at h
  obtain ⟨he0, h⟩ := List.cons.inj h
  rw [h, List.mem_map]
  rintro ⟨q, hq, he⟩
  have hq' : q ∈ abPos := by rw [hpos]; exact List.mem_cons_of_mem _ hq
  have h22 : (".Lscc_rt_print.write", 22) ∈ abPos := by rw [hpos]; exact List.mem_cons_self
  refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab q hq') (abPos_inRunB hpr hab _ h22) ?_ (he.trans he0)
  intro hq22
  exact hnin (hq22 ▸ hq)

/-- **A kernel return from the call in the phase refuses the stored
length**: at the pc after the call, `Ab` is its first case. -/
theorem ret_ab (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {s : State}
    (hs : s.st.2 = pcRet (_root_.Executable.labels exe).label) (h : Ab (_root_.Executable.labels exe).label s) :
    ∃ l, bpLoad s (-16) = some l ∧ Refusal l.toNat (s.st.1.regs.get64 .rax) := by
  have hn := pcRet_nmem hp hpr hab
  rw [← hs] at hn
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | h | h
  · exact h
  all_goals exact (hn (by simp [h])).elim

end Ret

/-- **The stored length is the frame's cell `-16`** (`%rbp` at `0`). -/
theorem bpLoad_of_abs {R : Region} {o : Spike.Lib.X64.SO} {s : State} {σ : AS}
    (hA : Spike.Lib.X64.Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hlo : R.lo ≤ -16) (hhi : -8 ≤ R.hi) :
    bpLoad s (-16) = some (σ.slot (-16)) := by
  have hbp : s.st.1.regs.get64 .rbp = R.addr 0 := by rw [hA.regs]; exact hA.so .rbp 0 ho
  obtain ⟨j, hj, ej⟩ := hA.slot (-16) ⟨by decide, by omega, by omega⟩
  have a16 : R.addr 0 + (-16 : BitVec 64) = R.addr (-16) := by
    rw [show (-16 : Int) = 0 + -16 by rfl, Region.addr_add]; rfl
  simp only [Reg64s.get64] at hbp
  simp only [bpLoad, privLoad, hbp, a16, hj, Option.map_some, ej]

/-! ## The call's states -/

section Svc

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- The call's pc at its label and offset. -/
theorem pcSys_eq (lab : Label → Int64) :
    Spike.Lib.X64.Print.pcSys lab = lab ".Lscc_rt_print.write" + Int64.ofNat 20 := rfl

/-- The call's facts at a state of its node: off the marks' sites, no
outside move, at the `syscall` cell, its next pc in its phase. -/
theorem sys_cell (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true) {s : State}
    (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hpc : s.st.2 = Spike.Lib.X64.Print.pcSys (_root_.Executable.labels exe).label) :
    (PcOff μ s ∧ ∀ s', ¬ K s s') ∧ CellAt s (op64 .syscall) 2 ∧
      ∀ m, own (after s 2 m) = own s ∧ (Tk (after s 2 m) ↔ Tk s) := by
  obtain ⟨-, -, -, -, -, h5, -⟩ := printIn_spec hin
  obtain ⟨-, -, -, -, -, p5, -⟩ := printPhOk_spec hph
  obtain ⟨hok, hph5⟩ := phOne_spec p5
  rw [hI.labOk, pcSys_eq] at hpc
  exact ⟨hI.off s (by unfold pcOf; rw [hpc]; exact hok), Spike.Lib.X64.Rt.cellOf hI h5 rfl hs hn hpc,
    Spike.Lib.X64.Rt.next_same hI hpc hph5⟩

/-- **`scc_rt_print`'s system call carries the state's facts**, none moved
by `K`, its code in the cells (`hin`) passing the phase check (`hph`), in a
region whose frame condition gives the stack range off it (`hFO`), the
write tail `Dt` given at the node (`hDt`). -/
theorem printSvcSt (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {Dt : State → Prop}
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hDt : ∀ s c, Spike.Lib.X64.At exe endPc R F
      (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c → Dt s) :
    NodeW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc R F
      (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) := by
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, hD, -⟩ := id hAt
  obtain ⟨⟨hP, hK⟩, hc, hnext⟩ := sys_cell hI hin hph hs hn hpc
  have hO : Tk s → Owned Λ rS s := fun _ =>
    Spike.Lib.X64.Rt.owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have hsy : abi.atSys s = true := atSyscall_of_cellAt hc
  have hsucc : ∀ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Kernel.certSuccs abi s call, own s' = own s ∧ (Tk s' ↔ Tk s) := by
    intro call _ s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | head => exact hnext _
      | tail _ h => cases h
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      exact hnext _
  refine ⟨⟨hP.noSite, fun h => ?_, fun _ => ⟨2, hc⟩, fun h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').1, fun a ha hpc => (hP.noTake a ha hpc).elim,
    fun a ha hpc => (hP.noTake a ha hpc).elim, fun a ha hpc => (hP.noTake a ha hpc).elim, fun _ h => ?_,
    fun _ call hd s' hs' => (hsucc call hd s' hs').2, hO, fun _ _ _ _ _ => hDt s c hAt⟩, hK⟩
  all_goals (rw [hsy] at h; cases h)

/-- **`scc_rt_print`'s system call keeps the write abort's phase**: off
the phase (its pc is), a kernel return lands in it only as a refusal of the
length passed (`%rdx`, the frame's cell `-16`, read back at `-16(%rbp)`);
its and the abort's code in the cells (`hpr`, `hab`) passing the phase
check (`hph`), in a region holding the frame's cell `-16`. -/
theorem printSvcAb (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true) (hlo : R.lo ≤ -16) (hhi : -8 ≤ R.hi) :
    NodeW (fun s _ => AbSt μ (Ab (_root_.Executable.labels exe).label) s) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) := by
  intro s c hAt
  obtain ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩ := hAt
  obtain ⟨⟨hP, -⟩, hc, -⟩ := sys_cell hI hpr hph hs hn hpc
  obtain ⟨-, hdi, hax, -, hdx⟩ := hJ
  have hsy : abi.atSys s = true := atSyscall_of_cellAt hc
  have hd := decode_print (s := s) (by rw [hA.regs]; exact hax) (by rw [hA.regs]; exact hdi)
  refine ⟨⟨fun _ h => (by rw [hsy] at h; cases h), fun _ _ call hd' s' hs' hab' => ?_,
    fun _ a ha hpc => (hP.noTake a ha hpc).elim⟩, fun _ h => h⟩
  rw [hd] at hd'
  cases hd'
  refine ⟨_, _, _, rfl, fun r hr => ?_⟩
  subst hr
  have hret : (abi.ret s r).st.2 = pcRet (_root_.Executable.labels exe).label := by
    show nextPc s = _
    rw [nextPc_of_cellAt hc, hpc]
    simp only [N, Spike.Lib.X64.Print.pcSys, pcRet]
    rw [Int64.add_assoc]; rfl
  obtain ⟨l, hl, hrf⟩ := ret_ab hI.lays hpr hab hret hab'
  have e16 := bpLoad_of_abs hA rfl hlo hhi
  have hl' : bpLoad (abi.ret s r) (-16) = bpLoad s (-16) := rfl
  rw [hl', e16, Option.some_inj] at hl
  have hx : (abi.ret s r).st.1.regs.get64 .rax = r := by simp [abi, retRegs64, Reg64s.get64]
  rw [hx, ← hl, ← hdx, ← hA.regs] at hrf
  exact hrf

/-- **A callee's region at a 16-aligned offset** of a valid 16-aligned
region, below its top (`hhi`), is valid and 16-aligned. -/
theorem callee_facts {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) {kc lo' hi' : Int}
    (hlo : R.lo ≤ kc + lo') (hlo0 : lo' ≤ 0) (hkc : kc < R.hi) (hhi : kc + hi' ≤ R.hi) (h16 : kc % 16 = 0) :
    (R.callee kc lo' hi').OK ∧ (R.callee kc lo' hi').base.toNat % 16 = 0 := by
  refine ⟨Region.callee_ok hR hlo hlo0 hkc hhi, ?_⟩
  have hb := Region.callee_base (hi' := hi') hR hlo hlo0 hkc
  have : (((R.callee kc lo' hi').base.toNat : Int)) % 16 = 0 := by rw [hb]; omega
  omega

/-- **`printSvcSt` in `print`'s region at a call** (`PrintCall.pR kb R`),
under any frame condition `F'` inside `print`'s (`hFF`, as `PrintW`'s system
call clause gives it): the stack range off the callee's region from the
caller's frame condition (`hFO`) and the caller's cells outside it
(`stackOff_callee`). -/
theorem printSvcStP (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    {Λ : Scc.Sem.Layout} {rS : Range} {Dt : State → Prop} {kb : Int} {F' : MachineData → Prop}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hlo : R.lo ≤ kb + -40) (hkb : kb + 16 ≤ R.hi) (hk16 : kb % 16 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hFF : ∀ m, F' m → Spike.Lib.X64.PrintCall.pF kb R F m)
    (hDt : ∀ s c, Spike.Lib.X64.At exe endPc (Spike.Lib.X64.PrintCall.pR kb R) F'
      (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c → Dt s) :
    NodeW (fun s _ => SFactsSt Λ μ own rS Tk s Dt) K exe endPc (Spike.Lib.X64.PrintCall.pR kb R) F'
      (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) := by
  obtain ⟨hR', hal'⟩ := callee_facts hR hal hlo (by decide) (by omega) hkb hk16
  refine printSvcSt hI hin hph hR' (by show (R.callee kb (-40) 16).base.toNat % 8 = 0; omega)
    (by simp [Region.callee]) (by simp [Region.callee]) hsub (fun m hm => ?_) hDt
  obtain ⟨hF, hcc⟩ := hFF m hm
  exact Spike.Lib.X64.Rt.stackOff_callee hR (by omega) hl hh hlo (by decide) (by omega) (by omega)
    (hFO m hF) hcc

/-- **Every refused result of `scc_rt_print`'s call lands in the write
abort's phase** (`WeAb`'s obligation): the return is at the pc after the
call, the stored length (`-16(%rbp)`, the frame's cell `-16`) at most the
length `len0 < 2^63` (`hlen`), so a refusal of it (`refusal_of_refused`). -/
theorem printSvcWe (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hin : Scc.Cert.Rt.X64.Print.printIn cells = true) (hph : printPhOk okPc ph lab = true)
    (hlo : R.lo ≤ -16) (hhi : -8 ≤ R.hi) (hlen : len0 < 2 ^ 63) {s : State} {c : Ctl}
    (hAt : Spike.Lib.X64.At exe endPc R F (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys)
      s c) :
    ∀ r, Kernel.writeRefused r = true → Ab (_root_.Executable.labels exe).label (abi.ret s r) := by
  intro r hr
  obtain ⟨hs, hn, -, hpc, σ, hA, -, ⟨k, ⟨-, -, -, h16, hk⟩, -, -⟩, -⟩ := hAt
  obtain ⟨-, hc, -⟩ := sys_cell hI hin hph hs hn hpc
  have hret : (abi.ret s r).st.2 = pcRet (_root_.Executable.labels exe).label := by
    show nextPc s = _
    rw [nextPc_of_cellAt hc, hpc]
    simp only [N, Spike.Lib.X64.Print.pcSys, pcRet]
    rw [Int64.add_assoc]; rfl
  have hl : bpLoad (abi.ret s r) (-16) = some (σ.slot (-16)) := bpLoad_of_abs (s := s) hA rfl hlo hhi
  have hx : (abi.ret s r).st.1.regs.get64 .rax = r := by simp [abi, retRegs64, Reg64s.get64]
  refine .inl ⟨hret, σ.slot (-16), hl, ?_⟩
  rw [hx]
  refine Spike.Lib.X64.PrintAb.refusal_of_refused ?_ hr
  rw [h16, BitVec.toNat_ofNat]
  omega

end Svc

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PrintG.printSvcSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcSt

/-- info: 'Spike.Lib.X64.PrintG.printSvcStP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcStP

/-- info: 'Spike.Lib.X64.PrintG.printSvcAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcAb

/-- info: 'Spike.Lib.X64.PrintG.printSvcWe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printSvcWe

end Spike.Lib.X64.PrintG
