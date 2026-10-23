/-
**The one-thread consumer on the canonical x86-64 target**: the x86-64
instance of `Spike/Lib/ExtThread.lean`, the twin of `Spike/Lib/A64Ext.lean`
(`X64.isa` under `Arch.tso`, `Scc.Sem.X64.abi`, the fragment
`Scc.Cert.WideX64.WideSt`).

- `inv1_promSemC`: a certified promise step of a thread of the one-word
  fragment keeps `Inv1`: the promised message is one word wide
  (`Inv1.promise_cert_on` with `soloWide8CodeOn`, `soloWideInv`), and the thread
  stays in the fragment.
- `wideSt_promThread`: a promise does not change the thread's state.
- `step_cases`: `Spike.Lib.ExtThread.step_cases` on the canonical machine
  (`X64.machine (X64.kernel n)`) for the fragment (`WideSt`);
  `step_cases_site`: the same from a thread at no transfer site.
- `wide8_exec`: off a system call, the instruction of a thread of the
  fragment writes words only (`ExtRows.out_local`'s `hw8`).
-/
import Spike.Lib.ExtThread
import Spike.Lib.ExtRows
import Scc.Cert.Rt.WideX64

namespace Spike.Lib.X64Ext

open Kraken.Promising Scc.Sem Scc.Cert.WideX64

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {sm : WeakMem.Memory}

/-- A promise leaves the thread's state, so its fragment, alone. -/
theorem wideSt_promThread {t : Thread X64.isa} {mem : Memory} {w : Msg} (h : WideSt t.st) :
    WideSt (Live.Sem.promThread t mem w).st := h

/-- **A certified promise step of a thread of the fragment keeps `Inv1`**:
the step replaces the thread by `promThread` and appends the promised
message, which is one word wide. -/
theorem inv1_promSemC {tid : Nat} {c c' : Config X64.isa} {t : Thread X64.isa}
    (ht : c.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.mem sm)
    {μ : Marks} {x : Kernel.KState}
    (hp : PromSemC Arch.tso (Kernel.certSem Scc.Sem.X64.abi Arch.tso μ x tid) tid c c') :
    ∃ w, c' = c.withThread tid (Live.Sem.promThread t c.mem w) (c.mem.append w).1 ∧
      Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.mem w) (c.mem.append w).1 sm := by
  obtain ⟨t', w, ht', -, hc, rfl⟩ := hp
  rw [ht] at ht'
  cases ht'
  exact ⟨w, rfl, h.promise_cert_on (soloWide8CodeOn μ x tid) (soloWideInv μ x tid) hw hc⟩

/-- **A step of the canonical x86-64 machine from a thread of the
fragment** that is neither a spawn nor a range transfer: an instruction off
a system call (one `stepOne` outcome, the thread in the fragment), a promise
that keeps `Inv1`, or a kernel step that keeps `Inv1`. -/
theorem step_cases {n : Nat} {μ : Marks} {tid : Nat} {es : List Ev} {c c' : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Cfg}
    {t : Thread X64.isa} (ht : c.1.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Step μ tid c es c')
    (hsp : ¬ (Scc.Sem.X64.kernel n).spawn μ tid c c')
    (hxf : ∀ k, ¬ (Scc.Sem.X64.kernel n).xfer k tid c c') :
    (es = [] ∧ Scc.Sem.X64.abi.atSys t.st = false ∧ ∃ outs o, stepOne Arch.tso t tid c.1.mem = some outs ∧
        .ok o ∈ outs ∧ c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ WideSt o.thread.st ∧
        CertOkC Arch.tso (Kernel.certSem Scc.Sem.X64.abi Arch.tso μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC Arch.tso (Kernel.certSem Scc.Sem.X64.abi Arch.tso μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w)
          (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep Scc.Sem.X64.abi Arch.tso tid c p = some (es, c') ∧
        Kernel.CertAfter Scc.Sem.X64.abi Arch.tso μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) :=
  ExtThread.step_cases exec_wide8CodeOn exec_wideInv
    (fun _ _ hs h => wideSt_soloLeaf hs h) ht hw h hs hsp hxf

/-- `step_cases` from a thread at no transfer site (`Step.xfer` happens only
there). -/
theorem step_cases_site {n : Nat} {μ : Marks} {tid : Nat} {es : List Ev} {c c' : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Cfg}
    {t : Thread X64.isa} (ht : c.1.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).Step μ tid c es c')
    (hsp : ¬ (Scc.Sem.X64.kernel n).spawn μ tid c c')
    (hsite : ∀ k, ¬ (Scc.Sem.X64.machine (Scc.Sem.X64.kernel n)).AtSite μ k c tid) :
    (es = [] ∧ Scc.Sem.X64.abi.atSys t.st = false ∧ ∃ outs o, stepOne Arch.tso t tid c.1.mem = some outs ∧
        .ok o ∈ outs ∧ c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ WideSt o.thread.st ∧
        CertOkC Arch.tso (Kernel.certSem Scc.Sem.X64.abi Arch.tso μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC Arch.tso (Kernel.certSem Scc.Sem.X64.abi Arch.tso μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w)
          (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep Scc.Sem.X64.abi Arch.tso tid c p = some (es, c') ∧
        Kernel.CertAfter Scc.Sem.X64.abi Arch.tso μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) :=
  ExtThread.step_cases_of exec_wide8CodeOn exec_wideInv
    (fun _ _ hs h => wideSt_soloLeaf hs h) ht hw h hs hsp fun k hk => absurd hk (hsite k)

/-- **Off a system call, an instruction of the fragment writes words
only.** -/
theorem wide8_exec {s : X64.State} (hw : WideSt s) (hns : Scc.Sem.X64.abi.atSys s = false) :
    ∀ tree, X64.isa.exec s = some tree → Wide8Tree tree :=
  fun _ he => wide8CodeOn _ _ hw ((Kernel.certExec_of_not_atSys Scc.Sem.X64.abi hns).trans he)

end Spike.Lib.X64Ext
