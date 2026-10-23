/-
**The one-thread consumer on the canonical AArch64 target**: the AArch64
instance of `Spike/Lib/ExtThread.lean`.

- `inv1_promSemC`: a certified promise step of a thread of the one-word
  fragment (`Scc.Cert.WideA64.WideSt`) keeps `Inv1`: the promised message is
  one word wide (`Inv1.promise_cert_on` with `soloWide8CodeOn`, `soloWideInv`), and
  the thread stays in the fragment.
- `wideSt_promThread`: a promise does not change the thread's state.
- `step_cases`: `Spike.Lib.ExtThread.step_cases` on the canonical machine
  (`A64.machine (A64.kernel n)`) for the fragment (`WideSt`);
  `step_cases_site`: the same from a thread at no transfer site.
- `wide8_exec`: off a system call, the instruction of a thread of the
  fragment writes words only (`ExtRows.out_local`'s `hw8`).
-/
import Spike.Lib.ExtThread
import Spike.Lib.ExtRows
import Scc.Cert.Rt.WideA64

namespace Spike.Lib.A64Ext

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Cert.WideA64

variable {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ts : Nat → Option Nat} {sm : WeakMem.Memory}

/-- A promise leaves the thread's state, so its fragment, alone. -/
theorem wideSt_promThread {t : Thread isaLSE2} {mem : Memory} {w : Msg} (h : WideSt t.st) :
    WideSt (Live.Sem.promThread t mem w).st := h

/-- **A certified promise step of a thread of the fragment keeps `Inv1`**:
the step replaces the thread by `promThread` and appends the promised
message, which is one word wide. -/
theorem inv1_promSemC {tid : Nat} {c c' : Config isaLSE2} {t : Thread isaLSE2}
    (ht : c.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.mem sm)
    {μ : Marks} {x : Kernel.KState}
    (hp : PromSemC Arch.armv8 (Kernel.certSem A64.abi Arch.armv8 μ x tid) tid c c') :
    ∃ w, c' = c.withThread tid (Live.Sem.promThread t c.mem w) (c.mem.append w).1 ∧
      Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.mem w) (c.mem.append w).1 sm := by
  obtain ⟨t', w, ht', -, hc, rfl⟩ := hp
  rw [ht] at ht'
  cases ht'
  exact ⟨w, rfl, h.promise_cert_on (soloWide8CodeOn μ x tid) (soloWideInv μ x tid) hw hc⟩

/-- **A step of the canonical AArch64 machine from a thread of the
fragment** that is neither a spawn nor a range transfer: an instruction off
a system call (one `stepOne` outcome, the thread in the fragment), a promise
that keeps `Inv1`, or a kernel step that keeps `Inv1`. -/
theorem step_cases {n : Nat} {μ : Marks} {tid : Nat} {es : List Ev} {c c' : (A64.machine (A64.kernel n)).Cfg}
    {t : Thread isaLSE2} (ht : c.1.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (A64.machine (A64.kernel n)).Step μ tid c es c') (hsp : ¬ (A64.kernel n).spawn μ tid c c')
    (hxf : ∀ k, ¬ (A64.kernel n).xfer k tid c c') :
    (es = [] ∧ A64.abi.atSys t.st = false ∧ ∃ outs o, stepOne Arch.armv8 t tid c.1.mem = some outs ∧
        .ok o ∈ outs ∧ c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ WideSt o.thread.st ∧
        CertOkC Arch.armv8 (Kernel.certSem A64.abi Arch.armv8 μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC Arch.armv8 (Kernel.certSem A64.abi Arch.armv8 μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w)
          (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep A64.abi Arch.armv8 tid c p = some (es, c') ∧
        Kernel.CertAfter A64.abi Arch.armv8 μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) :=
  ExtThread.step_cases exec_wide8CodeOn exec_wideInv
    (fun _ _ hs h => wideSt_soloLeaf hs h) ht hw h hs hsp hxf

/-- `step_cases` from a thread at no transfer site (`Step.xfer` happens only
there). -/
theorem step_cases_site {n : Nat} {μ : Marks} {tid : Nat} {es : List Ev} {c c' : (A64.machine (A64.kernel n)).Cfg}
    {t : Thread isaLSE2} (ht : c.1.threads[tid]? = some t) (hw : WideSt t.st) (h : Inv1 Λ lbl lsize ts t c.1.mem sm)
    (hs : (A64.machine (A64.kernel n)).Step μ tid c es c') (hsp : ¬ (A64.kernel n).spawn μ tid c c')
    (hsite : ∀ k, ¬ (A64.machine (A64.kernel n)).AtSite μ k c tid) :
    (es = [] ∧ A64.abi.atSys t.st = false ∧ ∃ outs o, stepOne Arch.armv8 t tid c.1.mem = some outs ∧
        .ok o ∈ outs ∧ c' = (c.1.withThread tid o.thread o.mem, c.2) ∧ WideSt o.thread.st ∧
        CertOkC Arch.armv8 (Kernel.certSem A64.abi Arch.armv8 μ c.2 tid) tid o.thread o.mem) ∨
      (es = [] ∧ ∃ w, c' = (c.1.withThread tid (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1, c.2) ∧
        Inv1 Λ lbl lsize ts (Live.Sem.promThread t c.1.mem w) (c.1.mem.append w).1 sm ∧
        CertOkC Arch.armv8 (Kernel.certSem A64.abi Arch.armv8 μ c.2 tid) tid (Live.Sem.promThread t c.1.mem w)
          (c.1.mem.append w).1 ∧
        w.tid = tid) ∨
      (∃ p, Kernel.sysStep A64.abi Arch.armv8 tid c p = some (es, c') ∧
        Kernel.CertAfter A64.abi Arch.armv8 μ tid c' ∧
        (c'.1 = c.1 ∨ ∃ u, c'.1 = c.1.withThread tid u c.1.mem ∧ Inv1 Λ lbl lsize ts u c.1.mem sm)) :=
  ExtThread.step_cases_of exec_wide8CodeOn exec_wideInv
    (fun _ _ hs h => wideSt_soloLeaf hs h) ht hw h hs hsp fun k hk => absurd hk (hsite k)

/-- **Off a system call, an instruction of the fragment writes words
only.** -/
theorem wide8_exec {s : State} (hw : WideSt s) (hns : A64.abi.atSys s = false) :
    ∀ tree, isaLSE2.exec s = some tree → Wide8Tree tree :=
  fun _ he => wide8CodeOn _ _ hw ((Kernel.certExec_of_not_atSys A64.abi hns).trans he)

end Spike.Lib.A64Ext
