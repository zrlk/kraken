/-
**The x64 kernel view at a cell**: `X64.abi` (`Scc/Sem/TargetX64.lean`) read
through Kraken's cell rows (`Kraken/Promising/Lower/EventsX64Sys.lean`).

The kernel model (`Scc/Sem/Kernel.lean`) reads a thread state through
`Abi`: `atSys`, `nr`, `arg`, `ret`, `skip`, `atNop`. Kraken's rows state a
cell (`CellAt st d sz`, the only hypothesis on the cell) in its own terms:
`syscallInfo`, `syscallRet`, `after`. This file equates the two, so that a
proof about a cell can take a kernel step (generic facts in
`Scc/Sem/SysLink.lean`).

- **The cell.** `atSyscall_of_cellAt`, `atSyscall_false_of_cellAt`,
  `atNop_of_cellAt`, `atNop_false_of_cellAt` (from `CellAt.directive`);
  `nextPc_of_cellAt`: the pc plus the cell's size (from
  `CellAt.dirSize`).
- **The registers.** `abi_nr_syscall`, `abi_arg_syscall`: `%rax` and
  `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`, `%r9`, as `syscallInfo` reads them;
  `abi_ret_of_cellAt`: `abi.ret` (`retRegs64`) is `syscallRet` of
  `kret (rflags …)`, i.e. `%rax := r`, `%rcx :=` the next pc,
  `%r11 := RFLAGS`; `abi_skip_of_cellAt`: `abi.skip` is `after` with the state
  unchanged (the state `exec_nop` gives); `abi_child_of_cellAt`: the child at
  `clone`.
- **Certification.** `certSuccs_syscall`: but for `arch_prctl`, the states
  the kernel may resume the thread in are `syscallRet` of `results call`
  (`mem_certSuccs_syscall`), and at `arch_prctl` the one state with the `%fs`
  base set first (`certSuccs_archSetFs`);
  `certExec_syscall`: `certExec abi` at such a supported `syscall` is the
  choice over them, the shape of Kraken's `execCert_syscall`;
  `certExec_archSetFs`: at `arch_prctl(ARCH_SET_FS, a)`, the one state with
  the `%fs` base set first; `certExec_syscall_unsupported`: at an unsupported
  call, the fault `exec_syscall` gives; `kresults` and
  `certExec_eq_execCert`: but for `arch_prctl`, `certExec abi` at a
  supported `syscall` is Kraken's `execCert (kresults fl)`, `fl` being
  `RFLAGS` (Kraken's `SyscallInfo` does not carry the flags, so the `%r11`
  the kernel writes is a parameter).
-/
import Scc.Sem.TargetX64
import Kraken.Promising.Lower.EventsX64Sys

namespace Scc.Sem.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

variable {st : State} {d : Directive} {sz : Nat}

/-! ## The cell -/

/-- **At a `syscall` cell the kernel sees a system call.** -/
theorem atSyscall_of_cellAt (hc : CellAt st (op64 .syscall) sz) : atSyscall st = true := by
  unfold atSyscall; rw [hc.directive]

/-- **At a cell other than a `syscall` the kernel sees no system call**:
the thread's step there is the ISA's (`Kernel.certExec_of_not_atSys`). -/
theorem atSyscall_false_of_cellAt (hc : CellAt st d sz) (hd : ∀ w w', d ≠ .instr (.regular w w' .syscall)) :
    atSyscall st = false := by
  unfold atSyscall; rw [hc.directive]
  split
  · rename_i h; cases h; exact absurd rfl (hd _ _)
  · rfl

/-- **At a `nop` cell the kernel sees a transfer site's instruction.** -/
theorem atNop_of_cellAt {n : Nat} (hc : CellAt st (op64 (.nop n)) sz) : atNop st = true := by
  unfold atNop; rw [hc.directive]

/-- **At a cell other than a `nop` the kernel sees no transfer site.** -/
theorem atNop_false_of_cellAt (hc : CellAt st d sz) (hd : ∀ w w' n, d ≠ .instr (.regular w w' (.nop n))) :
    atNop st = false := by
  unfold atNop; rw [hc.directive]
  split
  · rename_i h; cases h; exact absurd rfl (hd _ _ _)
  · rfl

/-- **The next pc at a cell** is the pc plus the cell's size. -/
theorem nextPc_of_cellAt (hc : CellAt st d sz) : nextPc st = st.st.2 + Int64.ofNat sz := by
  unfold nextPc; rw [hc.dirSize]

/-! ## The registers -/

/-- The system-call number is `%rax`, as `syscallInfo` reads it. -/
theorem abi_nr_syscall : abi.nr st = (syscallInfo st sz).num.toNat := rfl

/-- The arguments are `%rdi`, `%rsi`, `%rdx`, `%r10`, `%r8`, `%r9`, as
`syscallInfo` reads them. -/
theorem abi_arg_syscall (i : Fin 6) : abi.arg st i = ((syscallInfo st sz).args.getD i.val 0).toNat := by
  obtain ⟨i, hi⟩ := i
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- **What the kernel returns, as Kraken's `SyscallRet`**: `%rax := r`,
`%rcx :=` the address after the instruction (`info.nextPc`), `%r11 := fl`
(`RFLAGS`). -/
def kret (fl : BitVec 64) (info : SyscallInfo) (r : BitVec 64) : SyscallRet := ⟨r, info.nextPc, fl⟩

/-- **`abi.ret` at a cell is Kraken's `syscallRet`** of `kret` with the
flags `RFLAGS`: `%rax := r`, `%rcx :=` the next pc, `%r11 := RFLAGS`, the pc
past the cell. -/
theorem abi_ret_of_cellAt (hc : CellAt st d sz) (r : BitVec 64) :
    abi.ret st r = syscallRet st sz (kret (rflags st.st.1.status) (syscallInfo st sz) r) := by
  simp only [abi, retRegs64]; rw [nextPc_of_cellAt hc]; rfl

/-- **`abi.skip` at a cell** is `after` with the machine state unchanged
(the state `exec_nop` gives). -/
theorem abi_skip_of_cellAt (hc : CellAt st d sz) : abi.skip st = after st sz st.st.1 := by
  simp only [abi]; rw [nextPc_of_cellAt hc]

/-- **`abi.child` at a cell**: the parent's registers as `ret 0` leaves
them, but `%rsp` and the `%fs` base from the arguments, no private memory,
the pc past the cell. -/
theorem abi_child_of_cellAt (hc : CellAt st d sz) (stack tls : Nat) :
    abi.child st stack tls = after st sz { st.st.1 with
      regs := { retRegs64 st 0 with rsp := UInt64.ofNat stack, fsBase := UInt64.ofNat tls }, dmem := ∅ } := by
  simp only [abi]; rw [nextPc_of_cellAt hc]

/-! ## Certification -/

/-- A choice over a mapped list is the choice over the list. -/
theorem choose_map {α σ : Type} (l : List α) (f : α → σ) :
    (EvTree.choose (l.map f).length fun i => .done (l.map f)[i]) =
      EvTree.choose l.length fun i => .done (f l[i]) := by
  have h : (l.map f).length = l.length := List.length_map ..
  have key : ∀ (n : Nat) (hn : n = l.length) (g : Fin n → EvTree σ),
      (∀ i : Fin n, g i = .done (f l[i.val])) → EvTree.choose n g = EvTree.choose l.length fun i => .done (f l[i]) := by
    intro n hn g hg
    subst hn
    congr 1
    funext i
    exact hg i
  exact key _ h _ fun i => by simp

/-- A choice over a list equal to a mapped list is the choice over the
list. -/
theorem choose_of_eq_map {α σ : Type} {l : List σ} {l' : List α} {f : α → σ} (h : l = l'.map f) :
    (EvTree.choose l.length fun i => .done l[i]) = EvTree.choose l'.length fun i => .done (f l'[i]) := by
  subst h; exact choose_map l' f

/-- A choice over equal lists is the same choice. -/
theorem choose_congr {α σ : Type} {l l' : List α} (h : l = l') (f : α → σ) :
    (EvTree.choose l.length fun i => .done (f l[i])) = EvTree.choose l'.length fun i => .done (f l'[i]) := by
  subst h; rfl

/-- A choice over a mapped list, through `g`, is the choice over the list. -/
theorem choose_map_comp {α β σ : Type} (l : List α) (f : α → β) (g : β → σ) :
    (EvTree.choose (l.map f).length fun i => .done (g (l.map f)[i])) =
      EvTree.choose l.length fun i => .done (g (f l[i])) := by
  have h : (l.map f).length = l.length := List.length_map ..
  have key : ∀ (n : Nat) (hn : n = l.length) (k : Fin n → EvTree σ),
      (∀ i : Fin n, k i = .done (g (f l[i.val]))) →
        EvTree.choose n k = EvTree.choose l.length fun i => .done (g (f l[i])) := by
    intro n hn k hk
    subst hn
    congr 1
    funext i
    exact hk i
  exact key _ h _ fun i => by simp

/-- **The states the kernel may resume a `syscall` cell in**, but for
`arch_prctl`: `syscallRet` of each of `results call`. -/
theorem certSuccs_syscall (hc : CellAt st d sz) {call : Kernel.Call} (hna : ∀ a, call ≠ .archSetFs a) :
    Kernel.certSuccs abi st call =
      (Kernel.results call).map fun r => syscallRet st sz (kret (rflags st.st.1.status) (syscallInfo st sz) r) := by
  cases call with
  | archSetFs a => exact absurd rfl (hna a)
  | _ => simp only [Kernel.certSuccs]; congr 1; funext r; exact abi_ret_of_cellAt hc r

/-- `abi.setTp` keeps the cell. -/
theorem cellAt_setTp (hc : CellAt st d sz) (a : Nat) : CellAt (abi.setTp st a) d sz :=
  ⟨hc.valid, hc.ne, hc.code⟩

/-- **A state the kernel may resume a `syscall` cell in**, but for
`arch_prctl`, is `syscallRet` of one of `results call`. -/
theorem mem_certSuccs_syscall (hc : CellAt st d sz) {call : Kernel.Call} (hna : ∀ a, call ≠ .archSetFs a)
    {s' : State} :
    s' ∈ Kernel.certSuccs abi st call ↔
      ∃ r ∈ Kernel.results call, syscallRet st sz (kret (rflags st.st.1.status) (syscallInfo st sz) r) = s' := by
  rw [certSuccs_syscall hc hna]; exact List.mem_map

/-- **The state the kernel resumes `arch_prctl(ARCH_SET_FS, a)` in**: the
`%fs` base `a`, then the return of 0. -/
theorem certSuccs_archSetFs (hc : CellAt st d sz) (a : Nat) :
    Kernel.certSuccs abi st (.archSetFs a) =
      [syscallRet (abi.setTp st a) sz (kret (rflags st.st.1.status) (syscallInfo st sz) 0)] := by
  simp only [Kernel.certSuccs, abi_ret_of_cellAt (cellAt_setTp hc a)]
  rfl

/-- **`certExec abi` at a supported `syscall` cell**, but for
`arch_prctl`: the choice over `syscallRet` of `results call`, the shape of
Kraken's `execCert_syscall`. -/
theorem certExec_syscall (hc : CellAt st (op64 .syscall) sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.x64 (abi.nr st) (abi.arg st) = some call) (hna : ∀ a, call ≠ .archSetFs a) :
    Kernel.certExec abi st = some (.choose (Kernel.results call).length fun i =>
      .done (syscallRet st sz (kret (rflags st.st.1.status) (syscallInfo st sz) (Kernel.results call)[i]))) := by
  have hs : abi.atSys st = true := atSyscall_of_cellAt hc
  unfold Kernel.certExec
  simp only [hs, ite_true]
  rw [show abi.nrs = Kernel.Nrs.x64 from rfl, hd]
  exact congrArg some (choose_of_eq_map (certSuccs_syscall hc hna))

/-- **`certExec abi` at `arch_prctl(ARCH_SET_FS, a)`**: the one state with
the `%fs` base `a`, then the return of 0. -/
theorem certExec_archSetFs (hc : CellAt st (op64 .syscall) sz) {a : Nat}
    (hd : Kernel.decode Kernel.Nrs.x64 (abi.nr st) (abi.arg st) = some (.archSetFs a)) :
    Kernel.certExec abi st = some (.choose 1 fun _ =>
      .done (syscallRet (abi.setTp st a) sz (kret (rflags st.st.1.status) (syscallInfo st sz) 0))) := by
  have hs : abi.atSys st = true := atSyscall_of_cellAt hc
  unfold Kernel.certExec
  simp only [hs, ite_true]
  rw [show abi.nrs = Kernel.Nrs.x64 from rfl, hd]
  simp only [Kernel.certSuccs, List.length_singleton, abi_ret_of_cellAt (cellAt_setTp hc a)]
  congr 2; funext i; match i with | ⟨0, _⟩ => rfl

/-- **`certExec abi` at an unsupported `syscall` cell** is the ISA's: the
fault `exec_syscall` gives. -/
theorem certExec_syscall_unsupported (hc : CellAt st (op64 .syscall) sz)
    (hd : Kernel.decode Kernel.Nrs.x64 (abi.nr st) (abi.arg st) = none) :
    Kernel.certExec abi st = some (.fault pendingSyscallMsg) := by
  have hs : abi.atSys st = true := atSyscall_of_cellAt hc
  unfold Kernel.certExec
  simp only [hs, ite_true]
  rw [show abi.nrs = Kernel.Nrs.x64 from rfl, hd]
  exact exec_syscall hc

/-- **The kernel model's results, as Kraken's `results` parameter**, with
`%r11 := fl`: what the call `info` names may return (`Kernel.results`, as
`kret fl info`), nothing for an unsupported one. -/
def kresults (fl : BitVec 64) (info : SyscallInfo) : List SyscallRet :=
  match Kernel.decode Kernel.Nrs.x64 info.num.toNat (fun j => (info.args.getD j.val 0).toNat) with
  | some call => (Kernel.results call).map (kret fl info)
  | none => []

/-- `kresults` of the call at a `syscall` cell is `results` of the decoded
call. -/
theorem kresults_syscall (fl : BitVec 64) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.x64 (abi.nr st) (abi.arg st) = some call) :
    kresults fl (syscallInfo st sz) = (Kernel.results call).map (kret fl (syscallInfo st sz)) := by
  unfold kresults
  rw [← abi_nr_syscall, show (fun j : Fin 6 => ((syscallInfo st sz).args.getD j.val 0).toNat) = abi.arg st from
    funext fun j => (abi_arg_syscall j).symm, hd]

/-- **`certExec abi` at a supported `syscall` cell is Kraken's
`execCert (kresults (rflags …))`**, but for `arch_prctl`. -/
theorem certExec_eq_execCert (hc : CellAt st (op64 .syscall) sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.x64 (abi.nr st) (abi.arg st) = some call) (hna : ∀ a, call ≠ .archSetFs a) :
    Kernel.certExec abi st = execCert (kresults (rflags st.st.1.status)) st := by
  rw [certExec_syscall hc hd hna, execCert_syscall _ hc]
  exact congrArg some ((choose_congr (kresults_syscall _ hd) _).trans (choose_map_comp _ _ _)).symm

end Scc.Sem.X64
