/-
**Discharging `PromShared` on the canonical AArch64 target**
(`Spike/Lib/A64Consumer.lean`; `Scc/Sem/CertProm.lean`).

`PromShared` says that a certified promise made from `Pre` is to a shared
region, of a value the runtime memory's value invariant `G` allows. A
promise is certified by a promise-free solo run under `Kernel.certSem`
that empties the promise set, and a promise leaves the set only when a
write of the run fulfils it with the promised location and value
(`stepOneWith_fulfil`). So it suffices to give an invariant `Q` of the
thread and memory, holding right after the promise and kept along
certifying runs (`StepG`), every fulfilment of whose steps writes a shared
location a `G` value (`certOkC_prom_good_cfg`).

- `PromG`: the property of the promised message.
- `promShared_of`: `PromShared` from such a `Q`, given that `Pre` and a
  certified promise land in it.
- `stepG_of`: `StepG` for `Q := ∃ s, Core th mem s`, from a core invariant
  whose shared-region and `G` clauses are `MsgsExcept` over the outstanding
  promises, kept by the machine instruction step off a system call and the
  transfer sites, and by the certification step at one or at a site.
-/
import Spike.Lib.A64Consumer
import Scc.Sem.CertStep

namespace Spike.Lib.A64PromShared

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer

variable {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : CoreTerm.Prog} {G : Loc → Val → Prop} {own : Own} {I : Inv}
  {rS : Range} {Tk : State → Prop} {μ : Marks}

/-- **The property of a promised message** that `PromShared` asks for: to a
shared region (every byte), of a value `G` allows. -/
def PromG (Λ : Scc.Sem.Layout) (G : Loc → Val → Prop) (w : Msg) : Prop :=
  LocIn Λ.shared w.loc ∧ G w.loc w.val

/-- **`PromShared` from an invariant of the certification run**: if `Q` is
kept along certifying runs under `Kernel.certSem` (any kernel state), its steps fulfilling
only `PromG` messages (`StepG`), and `Pre` followed by a certified promise
lands in `Q`, then every certified promise from `Pre` is `PromG`. -/
theorem promShared_of {Q : Thread isaLSE2 × Memory → Prop}
    (hQ : ∀ x, StepG Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x 0) 0 Q (PromG Λ G))
    (h0 : ∀ t s th w, Pre Λ P p G own I rS Tk μ t s → t.1.threads = #[th] → w.tid = 0 →
      CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
        (t.1.mem.append w).1 →
      Q (Live.Sem.promThread th t.1.mem w, (t.1.mem.append w).1)) :
    PromShared Λ P p G own I rS Tk μ := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg (hQ t.2) (h0 t s th w hpre hth hw hc) hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`StepG` from a core invariant with the memory clauses as
`MsgsExcept`**: `Core th mem s` (a thread and memory paired with a source
configuration `s`) whose shared-region and `G` clauses exempt only the
outstanding promises (`hpm`), kept by every certification step off a system
call and the transfer sites (`hins`, where `certSem` is the ISA's: a machine
instruction step), at a system call (`hsys`) and at a transfer site
(`hsite`). The fulfilment half is `fulfil_of_msgsExcept` on the
result. -/
theorem stepG_of {Core : Thread isaLSE2 → Memory → TermRun.Cfg → Prop}
    (hpm : ∀ th mem s, Core th mem s →
      MsgsExcept (fun m => LocIn Λ.shared m.loc) th.prom mem ∧ MsgsExcept (fun m => G m.loc m.val) th.prom mem)
    (hins : ∀ th mem s outs o, Core th mem s → Kernel.siteAt abi μ th.st = none → abi.atSys th.st = false →
      stepOne Arch.armv8 th 0 mem = some outs → .ok o ∈ outs → ∃ s', Core o.thread o.mem s')
    (hsys : ∀ k th mem s outs o, Core th mem s → Kernel.siteAt abi μ th.st = none → abi.atSys th.st = true →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', Core o.thread o.mem s')
    (hsite : ∀ k th mem s outs o, Core th mem s → Kernel.siteAt abi μ th.st ≠ none →
      (Kernel.certSem abi Arch.armv8 μ k 0).step Arch.armv8 th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', Core o.thread o.mem s')
    (k : Kernel.KState) :
    StepG Arch.armv8 (Kernel.certSem abi Arch.armv8 μ k 0) 0 (fun x => ∃ s, Core x.1 x.2 s) (PromG Λ G) := by
  intro x y ⟨s, hc⟩ hs _
  have hy : ∃ s', Core y.1 y.2 s' := by
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    cases hsi : Kernel.siteAt abi μ x.1.st
    · cases hat : abi.atSys x.1.st
      · rw [Kernel.certSem_step_of_not_site hsi hat] at hso
        exact hins _ _ _ _ _ hc hsi hat hso ho
      · exact hsys _ _ _ _ _ _ hc hsi hat hso ho
    · exact hsite _ _ _ _ _ _ hc (by rw [hsi]; exact Option.some_ne_none _) hso ho
  obtain ⟨s', hc'⟩ := hy
  obtain ⟨h1, h2⟩ := hpm _ _ _ hc'
  exact ⟨⟨s', hc'⟩, fun p hp hpy w hg =>
    ⟨fulfil_of_msgsExcept hs h1 p hp hpy w hg, fulfil_of_msgsExcept hs h2 p hp hpy w hg⟩⟩

/-- **`PromShared` from the node obligations**: `Pre`'s core (`PreCore`) is
the certification run's invariant (`stepG_of`): an instruction step keeps
it (`core_ins`: off the transfer sites by the node obligations), and so do a
system call's certification step (`core_sys`) and the take site's
(`core_site`, by `TakePath.site`'s local run); a certified promise from
`Pre` lands in it (`pre_core_promise`). -/
theorem promShared_a64 {μ : Marks} {rd : TermRun.Word → Prop} (hP : HookOK P p)
    (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p) (hsafe : SrcSafe P p I) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hT : TakePath Λ p μ I rS Tk) :
    PromShared Λ P p G own I rS Tk μ :=
  promShared_of
    (stepG_of (Core := PreCore Λ P p G own I) (fun _ _ _ h => h.msgs)
      (core_ins hP hN hS hsafe hrd hwf hGpl)
      (fun _ _ _ _ _ _ h hsi hs hso ho => (core_sys hP hN hT h hsi hs hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_site hP hN hT h hsi hso ho).imp fun _ h => h.2))
    (fun _ s _ _ hpre hth hw hc => ⟨s, pre_core_promise hpre hth hw hc⟩)

end Spike.Lib.A64PromShared
