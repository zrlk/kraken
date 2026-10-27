/-
**A call of `print` keeps the thread pointer** (AArch64): `scc_rt_print`
has no `MSR`, so its node obligations hold inside `NoMsrW W K`
(`Spike/Lib/A64Hello1RodataTP.lean`) and `SegW.keepTPN` carries the
thread pointer across the call.

- `PrintAW.noMsr`: `print`'s block obligations, at the code of any valid
  layout of a program with `printIn`, inside `NoMsrW W K`;
- `print_call_segWB_tp`: `print_call_segWB` (`Spike/Lib/A64PrintByteOut.lean`)
  with `TP t` at entry and exit. The premises are `print_call_segWB`'s
  under the caller's `ms` and `W`; the memory side `tpXa ms t` and the
  fragment `NoMsrW W K` the inner call runs under are built here (the
  system call's cell is a `svc`, not an `MSR`);
- `print_call_segW_tp`: `print_call_segW` (`Spike/Lib/A64PrintCall.lean`, any
  byte step `ms.bo`, the output row `emitW_of_out`) with `TP t` at entry
  and exit;
- `print_call_emptyW_tp`: `print_call_emptyW` (`Spike/Lib/A64PrintEmpty.lean`,
  count 0) with `TP t` at entry and exit.
-/
import Spike.Lib.A64PrintByteOut
import Spike.Lib.A64PrintEmpty
import Spike.Lib.A64Hello1RodataTP

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.ByteOut
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Rt.A64.Print (code_field add4 add0 printIn)
open Spike.Lib.A64.KeepTP (NoMsrAt dNoMsr TP tpXa)
open Spike.Lib.PrintSrc (PrintC printN printLD loadC nextC)
open PrintCall

set_option linter.unusedSimpArgs false

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`scc_rt_print` at its code is inside `NoMsrW W K`**: none of its
blocks is an `MSR`. -/
theorem PrintAW.noMsr {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : printIn prog = true)
    (h : PrintA.PrintAW x29 ra buf0 len0 P Q W K exe endPc R F) :
    PrintA.PrintAW x29 ra buf0 len0 P Q (NoMsrW W K) K exe endPc R F := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, -⟩ := hprog
  exact ⟨BlkW.noMsr h.e (code_field hp hend h0 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n1 (code_field hp hend h1 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.loop (code_field hp hend h2 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n3 (code_field hp hend h3 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.write (code_field hp hend h4 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n5 (code_field hp hend h5 (by simp only [PrintA.N, PrintA.pcSvc, add4, add0])) (by decide),
    BlkW.noMsr h.n6 (code_field hp hend h6 (by simp only [PrintA.N, PrintA.pcSvc, add4, add0])) (by decide),
    BlkW.noMsr h.n7 (code_field hp hend h7 (by simp only [PrintA.N, PrintA.pcSvc, add4, add0])) (by decide),
    BlkW.noMsr h.chk2 (code_field hp hend h8 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n9 (code_field hp hend h9 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n10 (code_field hp hend h10 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.chk3 (code_field hp hend h11 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.n12 (code_field hp hend h12 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.adv (code_field hp hend h13 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.fail (code_field hp hend h14 (by simp only [PrintA.N, add4, add0])) (by decide),
    BlkW.noMsr h.done (code_field hp hend h15 (by simp only [PrintA.N, add4, add0])) (by decide)⟩

/-- **A state at `print`'s system call is at a cell other than an `MSR`**
(the cell is `svc`). -/
theorem print_svc_noMsr {prog : List Directive} {kp : Nat} {x29 ra buf0 : BitVec 64} {len0 : Nat}
    {P Q : Nat → Ctl → Prop} {F' : MachineData → Prop} {s : State} {c : Ctl}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : printIn prog = true)
    (hAt : At exe endPc R F' (PrintA.N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .svc) s c) :
    NoMsrAt s := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨-, -, -, -, -, hs, -⟩ := hprog
  obtain ⟨he, hn, -, hpc, -⟩ := id hAt
  exact noMsrAt_of_code (code_field hp hend hs (q := (PrintA.N (_root_.Executable.labels exe).label x29 ra
    buf0 len0 P Q .svc).pc) (by simp only [PrintA.N, PrintA.pcSvc, add4, add0]) s he hn)
    (by decide) (j := 0) (by simp) rfl rfl (by rw [hpc, ofNat4_zero])

/-- **A call of `print` keeps the thread pointer**: `print_call_segWB` with
`TP t` at entry and exit, under the caller's memory side `ms` and
fragment `W` (the inner call runs under `tpXa ms t` and `NoMsrW W K`:
`PrintAW.noMsr`, `print_svc_noMsr`, `SegW.keepTPN`). -/
theorem print_call_segWB_tp {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hpw : ∀ σ c, nC.J σ c → ∃ l, (pw σ).val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σ.regs.X0.toBitVec.toNat)
    (hov : ∀ σ c, nC.J σ c → σ.regs.X0.toBitVec.toNat + printN (n σ) (m σ) < 2 ^ 64)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.A64.abi) (hbo : ms.bo = ByteOut (I := isaLSE2) p lbl)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  SegW.keepTPN hK (print_call_segWB (ms := tpXa ms t) (W := NoMsrW W K) hp hend hprog hF hR hal hlo hhi hk16
    hpc hP0 hN hm hpw hov (fun σC c hJ => PrintAW.noMsr hp hend hprog (hW σC c hJ)) hd hK hbo
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_svc_noMsr hp hend hprog hAt, h.2⟩, h.2⟩)
    hwe hret habort)

/-- **A call of `print` keeps the thread pointer**, any byte step:
`print_call_segW` (`BO := ms.bo`, `WE := ms.we`, the output row
`emitW_of_out`) with `TP t` at entry and exit (`PrintAW.noMsr`,
`print_svc_noMsr`, `SegW.keepTPN`). -/
theorem print_call_segW_tp {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p ms.bo)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF nC.o.sp R F m) → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  SegW.keepTPN hK (print_call_segW (ms := tpXa ms t) (W := NoMsrW W K) hp hend hprog hF hR hal hlo hhi hk16
    hpc hP0 hN hm (fun σC c hJ => PrintAW.noMsr hp hend hprog (hW σC c hJ)) hd PrintA.emitW_of_out hK hcl
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_svc_noMsr hp hend hprog hAt, h.2⟩, h.2⟩)
    hlb hwe hret habort)

/-- **A call of `print` with count 0 keeps the thread pointer**:
`print_call_emptyW` with `TP t` at entry and exit (`PrintAW.noMsr`,
`SegW.keepTPN`). -/
theorem print_call_emptyW_tp {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop} {t : UInt64}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = 0)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pe σC c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  SegW.keepTPN hK (print_call_emptyW (ms := tpXa ms t) (W := NoMsrW W K) hp hend hprog hF hR hal hlo hhi hk16
    hpc hP0 hz (fun σC c hJ => PrintAW.noMsr hp hend hprog (hW σC c hJ)) hret)

/-- **A call of `print` keeps the thread pointer**, with `print`'s blocks
and the system call's premises asked only under frame conditions that
know the call (`pFJ`): `print_call_segW'` as `print_call_segW_tp` is
`print_call_segW`. -/
theorem print_call_segW_tp' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R) F')
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p ms.bo)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      ms.bo s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.X0 = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  SegW.keepTPN hK (print_call_segW' (ms := tpXa ms t) (W := NoMsrW W K) hp hend hprog hF hR hal hlo hhi hk16
    hpc hP0 hN hm (fun σC c hJ F' hJF => PrintAW.noMsr hp hend hprog (hW σC c hJ F' hJF)) hd
    PrintA.emitW_of_out hK hcl
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_svc_noMsr hp hend hprog hAt, h.2⟩, h.2⟩)
    hlb hwe hret habort)

/-- **A call of `print` with count 0 keeps the thread pointer**, with
`print`'s blocks asked only under frame conditions that know the call
(`pFJ`): `print_call_emptyW'` with `TP t` at entry and exit. -/
theorem print_call_emptyW_tp' {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop} {t : UInt64}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ nC.o.sp + -48) (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = 0)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR nC.o.sp R) F')
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      Pe σC c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  SegW.keepTPN hK (print_call_emptyW' (ms := tpXa ms t) (W := NoMsrW W K) hp hend hprog hF hR hal hlo hhi hk16
    hpc hP0 hz (fun σC c hJ F' hJF => PrintAW.noMsr hp hend hprog (hW σC c hJ F' hJF)) hret)

end Fn

end Spike.Lib.A64.Flow
