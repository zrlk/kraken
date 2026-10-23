/-
**The AArch64 kernel view at a cell**: `A64.abi` (`Scc/Sem/TargetA64.lean`)
read through Kraken's cell rows (`Kraken/Promising/Lower/EventsA64Sys.lean`).

The kernel model (`Scc/Sem/Kernel.lean`) reads a thread state through
`Abi`: `atSys`, `nr`, `arg`, `ret`, `skip`, `atNop`. Kraken's rows state a
cell (`CellAt st d sz`, the only hypothesis on the cell) in its own terms:
`svcInfo`, `svcRet`, `after`. This file equates the two, so that a proof
about a cell can take a kernel step (generic facts in `Scc/Sem/SysLink.lean`).

- **The cell.** `atSvc_of_cellAt`, `atNop_of_cellAt` (from
  `CellAt.directive`), `atSvc_false_of_cellAt`, `atNop_false_of_cellAt`
  (any other directive); `nextPc_of_cellAt`: the pc plus the cell's size (from
  `CellAt.dirSize`).
- **The registers.** `abi_nr_svc`, `abi_arg_svc`: `x8` and `x0`–`x5`, as
  `svcInfo` reads them; `abi_ret_of_cellAt`: `abi.ret` is `svcRet`;
  `abi_skip_of_cellAt`: `abi.skip` is `after` with the state unchanged (the
  state `exec_nop` gives); `abi_child_of_cellAt`: the child at `clone`.
- **Certification.** `certSuccs_svc`: the states the kernel may resume the
  thread in are `svcRet` of `results call` (AArch64 has no `arch_prctl`,
  `decode_a64_ne_archSetFs`), so `mem_certSuccs_svc`: a kernel return lands
  in `svcRet st sz r` for some `r ∈ results call`; `certExec_svc`: `certExec abi` at a supported
  `svc` is the choice over them, the shape of Kraken's `execCert_svc`;
  `certExec_svc_unsupported`: at an unsupported one, the fault `exec_svc`
  gives; `kresults` and `certExec_eq_execLSE2Cert`: `certExec abi` at a
  supported `svc` is Kraken's `execLSE2Cert kresults`.
-/
import Scc.Sem.TargetA64
import Kraken.Promising.Lower.EventsA64Sys

namespace Scc.Sem.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

variable {st : State} {d : Directive} {sz : Nat}

/-! ## The cell -/

/-- **At an `svc` cell the kernel sees a system call.** -/
theorem atSvc_of_cellAt {imm : Nat} (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz) : atSvc st = true := by
  unfold atSvc; rw [hc.directive]

/-- **At a cell other than an `svc` the kernel sees no system call**: the
thread's step there is the ISA's (`Kernel.certExec_of_not_atSys`). -/
theorem atSvc_false_of_cellAt (hc : CellAt st d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) :
    atSvc st = false := by
  unfold atSvc; rw [hc.directive]
  split
  · rename_i h; cases h; exact absurd rfl (hd _)
  · rfl

/-- **At a `nop` cell the kernel sees a transfer site's instruction.** -/
theorem atNop_of_cellAt {w : RegWidth} (hc : CellAt st (.instr ⟨w, .NOP⟩) sz) : atNop st = true := by
  unfold atNop; rw [hc.directive]

/-- **At a cell other than a `nop` the kernel sees no transfer site.** -/
theorem atNop_false_of_cellAt (hc : CellAt st d sz) (hd : ∀ w, d ≠ .instr ⟨w, .NOP⟩) : atNop st = false := by
  unfold atNop; rw [hc.directive]
  split
  · rename_i h; cases h; exact absurd rfl (hd _)
  · rfl

/-- **The next pc at a cell** is the pc plus the cell's size. -/
theorem nextPc_of_cellAt (hc : CellAt st d sz) : nextPc st = st.st.2 + Int64.ofNat sz := by
  unfold nextPc; rw [hc.dirSize]

/-! ## The registers -/

/-- The system-call number is `x8`, as `svcInfo` reads it. -/
theorem abi_nr_svc (imm : Nat) : abi.nr st = (svcInfo st imm).num.toNat := rfl

/-- The arguments are `x0`–`x5`, as `svcInfo` reads them. -/
theorem abi_arg_svc (imm : Nat) (i : Fin 6) : abi.arg st i = ((svcInfo st imm).args.getD i.val 0).toNat := by
  obtain ⟨i, hi⟩ := i
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl

/-- **`abi.ret` at a cell is Kraken's `svcRet`**: `x0 := r`, the pc past
the cell. -/
theorem abi_ret_of_cellAt (hc : CellAt st d sz) (r : BitVec 64) : abi.ret st r = svcRet st sz r := by
  simp only [abi]; rw [nextPc_of_cellAt hc]

/-- **`abi.skip` at a cell** is `after` with the machine state unchanged
(the state `exec_nop` gives). -/
theorem abi_skip_of_cellAt (hc : CellAt st d sz) : abi.skip st = after st sz st.st.1 := by
  simp only [abi]; rw [nextPc_of_cellAt hc]

/-- **`abi.child` at a cell**: the parent's registers but `x0 = 0`, `sp`
and `TPIDR_EL0` from the arguments, no private memory, the pc past the
cell. -/
theorem abi_child_of_cellAt (hc : CellAt st d sz) (stack tls : Nat) :
    abi.child st stack tls = after st sz { st.st.1 with
      regs := { st.st.1.regs with X0 := 0, SP := UInt64.ofNat stack, TPIDR_EL0 := UInt64.ofNat tls },
      dmem := ∅ } := by
  simp only [abi]; rw [nextPc_of_cellAt hc]

/-! ## Certification -/

/-- Only a number with an `arch_prctl` entry decodes to `arch_prctl`. -/
theorem decode_archSetFs {N : Kernel.Nrs} {nr : Nat} {a : Fin 6 → Nat} {x : Nat}
    (h : Kernel.decode N nr a = some (.archSetFs x)) : N.archPrctl = some nr := by
  revert h
  unfold Kernel.decode
  repeat' split
  all_goals simp_all

/-- AArch64 has no `arch_prctl`: `decode` never gives one. -/
theorem decode_a64_ne_archSetFs (nr : Nat) (a : Fin 6 → Nat) (x : Nat) :
    Kernel.decode Kernel.Nrs.a64 nr a ≠ some (.archSetFs x) := fun h => by
  have := decode_archSetFs h
  simp [Kernel.Nrs.a64] at this

/-- **The states the kernel may resume an `svc` cell in**: `svcRet` of each
of `results call`. -/
theorem certSuccs_svc (hc : CellAt st d sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = some call) :
    Kernel.certSuccs abi st call = (Kernel.results call).map (svcRet st sz) := by
  cases call with
  | archSetFs x => exact absurd hd (decode_a64_ne_archSetFs _ _ x)
  | _ => simp only [Kernel.certSuccs]; congr 1; funext r; exact abi_ret_of_cellAt hc r

/-- **A state the kernel may resume an `svc` cell in** is `svcRet` of one of
`results call`. -/
theorem mem_certSuccs_svc (hc : CellAt st d sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = some call) {s' : State} :
    s' ∈ Kernel.certSuccs abi st call ↔ ∃ r ∈ Kernel.results call, svcRet st sz r = s' := by
  rw [certSuccs_svc hc hd]; exact List.mem_map

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

/-- **`certExec abi` at a supported `svc` cell** is the choice over
`svcRet st sz` of `results call`: the shape of Kraken's `execCert_svc`. -/
theorem certExec_svc {imm : Nat} (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = some call) :
    Kernel.certExec abi st =
      some (.choose (Kernel.results call).length fun i => .done (svcRet st sz (Kernel.results call)[i])) := by
  have hs : abi.atSys st = true := atSvc_of_cellAt hc
  unfold Kernel.certExec
  simp only [hs, ite_true]
  rw [show abi.nrs = Kernel.Nrs.a64 from rfl, hd]
  exact congrArg some (choose_of_eq_map (certSuccs_svc hc hd))

/-- **`certExec abi` at an unsupported `svc` cell** is the ISA's: the fault
`exec_svc` gives. -/
theorem certExec_svc_unsupported {imm : Nat} (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz)
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = none) :
    Kernel.certExec abi st = some (.fault (pendingSyscallMsg imm)) := by
  have hs : abi.atSys st = true := atSvc_of_cellAt hc
  unfold Kernel.certExec
  simp only [hs, ite_true]
  rw [show abi.nrs = Kernel.Nrs.a64 from rfl, hd]
  exact exec_svc hc

/-- **The kernel model's results, as Kraken's `results` parameter**: what
the call `info` names may return (`Kernel.results`), nothing for an
unsupported one. -/
def kresults (info : SyscallInfo) : List (BitVec 64) :=
  match Kernel.decode Kernel.Nrs.a64 info.num.toNat (fun j => (info.args.getD j.val 0).toNat) with
  | some call => Kernel.results call
  | none => []

/-- `kresults` of the call at an `svc` cell is `results` of the decoded call. -/
theorem kresults_svc {imm : Nat} {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = some call) :
    kresults (svcInfo st imm) = Kernel.results call := by
  unfold kresults
  rw [← abi_nr_svc imm, show (fun j : Fin 6 => ((svcInfo st imm).args.getD j.val 0).toNat) = abi.arg st from
    funext fun j => (abi_arg_svc imm j).symm, hd]

/-- **`certExec abi` at a supported `svc` cell is Kraken's
`execLSE2Cert kresults`.** -/
theorem certExec_eq_execLSE2Cert {imm : Nat} (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz) {call : Kernel.Call}
    (hd : Kernel.decode Kernel.Nrs.a64 (abi.nr st) (abi.arg st) = some call) :
    Kernel.certExec abi st = execLSE2Cert kresults st := by
  rw [certExec_svc hc hd, execCert_svc kresults hc]
  exact congrArg some (choose_congr (kresults_svc hd).symm _)

end Scc.Sem.A64
