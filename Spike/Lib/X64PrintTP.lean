/-
**A call of `print` keeps the thread pointer** (x86-64): the twin of
`Spike/Lib/A64PrintTP.lean`. `scc_rt_print`'s only `syscall` is its
`write` (`%rax = 1` at the system call's node), so its node obligations
hold inside `NoSetFsW W K` (`Spike/Lib/X64Hello1RodataTP.lean`) and
`SegW.keepTPN` carries `fsBase` across the call.

- `PrintAW.noSetFs`: `print`'s block obligations, at the code of any valid
  layout of cells with `printIn`, inside `NoSetFsW W K` (no block has a
  `syscall`);
- `print_sys_noSetFs`: a state at `print`'s system call asks for `write`,
  not `arch_prctl`;
- `print_call_segWB_tp`: `print_call_segWB` (`Spike/Lib/X64PrintByteOut.lean`)
  with `TP t` at entry and exit. The premises are `print_call_segWB`'s
  under the caller's `ms` and `W`; the memory side `tpXa ms t` and the
  fragment `NoSetFsW W K` the inner call runs under are built here;
- `print_call_segW_tp`: the same for `print_call_segW` (any byte step `BO`
  of the memory side, `BO := ms.bo`, `WE := ms.we`);
- `print_call_emptyW_tp`: `print_call_emptyW` (`Spike/Lib/X64PrintEmpty.lean`,
  count 0) with `TP t` at entry and exit;
- `print_call_segW_tp'`, `print_call_emptyW_tp'`: the same over
  `print_call_segW'`, `print_call_emptyW'` (`print`'s blocks asked only under
  frame conditions that know the call, `PrintCall.pFJ`).
-/
import Spike.Lib.X64PrintByteOut
import Spike.Lib.X64PrintEmpty
import Spike.Lib.X64Hello1RodataTP

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
  Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.ByteOut
open Scc.Cert.Rt.X64 (Lays endOf code_field)
open Spike.Lib.X64.KeepTP (NoSetFsAt TP tpXa)
open Spike.Lib.X64.Flow (NoSetFsW)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open PrintCall

set_option linter.unusedSimpArgs false

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`scc_rt_print` at its code is inside `NoSetFsW W K`**: none of its
blocks is a `syscall`. -/
theorem PrintAW.noSetFs {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (h : PrintA.PrintAW rbp0 ra buf0 len0 P Q W K exe endPc R F) :
    PrintA.PrintAW rbp0 ra buf0 len0 P Q (NoSetFsW W K) K exe endPc R F := by
  simp only [Scc.Cert.Rt.X64.Print.printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, -, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := hprog
  exact ⟨Flow.BlkW.noSetFs h.e (code_field hp hend h0 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.n1 (code_field hp hend h1 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.loop (code_field hp hend h2 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.n3 (code_field hp hend h3 rfl) (by decide),
    Flow.BlkW.noSetFs h.write (code_field hp hend h4 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.n5 (code_field hp hend h5 rfl) (by decide),
    Flow.BlkW.noSetFs h.n6 (code_field hp hend h6 rfl) (by decide),
    Flow.BlkW.noSetFs h.chk2 (code_field hp hend h7 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.n8 (code_field hp hend h8 rfl) (by decide),
    Flow.BlkW.noSetFs h.chk3 (code_field hp hend h9 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.n10 (code_field hp hend h10 rfl) (by decide),
    Flow.BlkW.noSetFs h.adv (code_field hp hend h11 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.fail (code_field hp hend h12 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide),
    Flow.BlkW.noSetFs h.done (code_field hp hend h13 (Scc.Cert.Rt.X64.Print.off0 _)) (by decide)⟩

omit [Executable.ValidLayout exe] in
/-- **A state at `print`'s system call asks for `write`** (`%rax = 1`,
`%rdi = 1`), not `arch_prctl`. -/
theorem print_sys_noSetFs {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}
    {F' : MachineData → Prop} {s : State} {c : Ctl}
    (hAt : At exe endPc R F' (PrintA.N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .sys) s c) :
    NoSetFsAt s := by
  obtain ⟨-, -, -, -, σ, hA, -, -, hdi, hax, -, -⟩ := id hAt
  have hrax : s.st.1.regs.rax.toNat = 1 := by
    have : s.st.1.regs.get64 .rax = 1 := by rw [hA.regs]; exact hax
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  have hrdi : s.st.1.regs.rdi.toNat = 1 := by
    have : s.st.1.regs.get64 .rdi = 1 := by rw [hA.regs]; exact hdi
    simp only [Reg64s.get64] at this; rw [UInt64.toNat, this]; rfl
  intro _ a hd
  simp [Scc.Sem.X64.abi, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, hrax, hrdi] at hd

/-- **A call of `print` keeps the thread pointer**: `print_call_segWB` with
`TP t` at entry and exit, under the caller's memory side `ms` and
fragment `W` (the inner call runs under `tpXa ms t` and `NoSetFsW W K`:
`PrintAW.noSetFs`, `print_sys_noSetFs`, `SegW.keepTPN`). -/
theorem print_call_segWB_tp {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hpw : ∀ σ c, nC.J σ c → ∃ l, (pw σ).val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σ.regs.get64 .rdi).toNat)
    (hov : ∀ σ c, nC.J σ c → (σ.regs.get64 .rdi).toNat + printN (n σ) (m σ) < 2 ^ 64)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.X64.abi) (hbo : ms.bo = ByteOut (I := isa) p lbl)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  Flow.SegW.keepTPN hK (print_call_segWB (ms := tpXa ms t) (W := NoSetFsW W K) hp hend hprog hF hR hlo hhi hk8
    hpc hP0 hN hm hpw hov (fun σC c hJ => PrintAW.noSetFs hp hend hprog (hW σC c hJ)) hd hK hbo
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_sys_noSetFs hAt, h.2⟩, h.2⟩)
    hwe hret habort)

/-- **A call of `print` keeps the thread pointer**, any byte step:
`print_call_segW` (`BO := ms.bo`, `WE := ms.we`, the output row
`emitW_of_out`) with `TP t` at entry and exit. -/
theorem print_call_segW_tp {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.X64.abi) (hcl : LocalClosed p ms.bo)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), (∀ m, F' m → pF (nC.o.sp - 8) R F m) → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  Flow.SegW.keepTPN hK (print_call_segW (ms := tpXa ms t) (W := NoSetFsW W K) hp hend hprog hF hR hlo hhi hk8
    hpc hP0 hN hm (fun σC c hJ => PrintAW.noSetFs hp hend hprog (hW σC c hJ)) hd PrintA.emitW_of_out hK hcl
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_sys_noSetFs hAt, h.2⟩, h.2⟩)
    hlb hwe hret habort)

/-- **A call of `print` with count 0 keeps the thread pointer**:
`print_call_emptyW` with `TP t` at entry and exit (`PrintAW.noSetFs`,
`SegW.keepTPN`). -/
theorem print_call_emptyW_tp {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop} {t : UInt64}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = 0)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → Pe σC c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  Flow.SegW.keepTPN hK (print_call_emptyW (ms := tpXa ms t) (W := NoSetFsW W K) hp hend hprog hF hR hlo hhi hk8
    hpc hP0 hz (fun σC c hJ => PrintAW.noSetFs hp hend hprog (hW σC c hJ)) hret)


/-- **A call of `print` keeps the thread pointer**, with `print`'s blocks
and the system call's premises asked only under frame conditions that
know the call (`pFJ`): `print_call_segW'` as `print_call_segW_tp` is
`print_call_segW`. -/
theorem print_call_segW_tp' {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {pw wn : AS → TermRun.Word} {n m : AS → Nat} {t : UInt64}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R) F')
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the memory side
    (hK : ms.K = some Scc.Sem.X64.abi) (hcl : LocalClosed p ms.bo)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      ms.bo s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop), pFJ R F nC σC F' → ∀ s c',
      At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → ms.we s c1)
    -- where the return and the abort land
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    (habort : ∀ σC c σR c' k, nC.J σC c → σR.regs.get64 .rdi = 4 → PrintC (pw σC) (wn σC) (n σC) (m σC) k c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  Flow.SegW.keepTPN hK (print_call_segW' (ms := tpXa ms t) (W := NoSetFsW W K) hp hend hprog hF hR hlo hhi hk8
    hpc hP0 hN hm (fun σC c hJ F' hJF => PrintAW.noSetFs hp hend hprog (hW σC c hJ F' hJF)) hd
    PrintA.emitW_of_out hK hcl
    (fun σC c hJ F' hFF s c' hAt =>
      have h := hWs σC c hJ F' hFF s c' hAt
      ⟨⟨h.1, print_sys_noSetFs hAt, h.2⟩, h.2⟩)
    hlb hwe hret habort)


/-- **A call of `print` with count 0 keeps the thread pointer**, with
`print`'s blocks asked only under frame conditions that know the call
(`pFJ`): `print_call_emptyW'` with `TP t` at entry and exit. -/
theorem print_call_emptyW_tp' {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    {nC : ND} {Pe : AS → Ctl → Prop} {t : UInt64}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ nC.o.sp - 8 + -40) (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    (hP0 : ∀ σ c, nC.J σ c → Pe σ c)
    (hz : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = 0)
    (hW : ∀ σC c, nC.J σC c → ∀ F' : MachineData → Prop, pFJ R F nC σC F' →
      PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (fun _ => Pe σC) (fun _ _ => False) W K exe endPc (pR (nC.o.sp - 8) R) F')
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec → Pe σC c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c') :
    SegW W K p lbl ms (fun s c => At exe endPc R F nC s c ∧ TP t s)
      (fun s c => Next exe endPc R F N E s c ∧ TP t s) :=
  Flow.SegW.keepTPN hK (print_call_emptyW' (ms := tpXa ms t) (W := NoSetFsW W K) hp hend hprog hF hR hlo hhi hk8
    hpc hP0 hz (fun σC c hJ F' hJF => PrintAW.noSetFs hp hend hprog (hW σC c hJ F' hJF)) hret)

end Fn

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.PrintAW.noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.PrintAW.noSetFs

/-- info: 'Spike.Lib.X64.print_sys_noSetFs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_sys_noSetFs

/-- info: 'Spike.Lib.X64.print_call_segWB_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_segWB_tp

/-- info: 'Spike.Lib.X64.print_call_segW_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_segW_tp

/-- info: 'Spike.Lib.X64.print_call_emptyW_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_emptyW_tp

/-- info: 'Spike.Lib.X64.print_call_segW_tp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_segW_tp'

/-- info: 'Spike.Lib.X64.print_call_emptyW_tp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.print_call_emptyW_tp'
