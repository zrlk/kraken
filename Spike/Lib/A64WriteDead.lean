/-
**The certification premises at the output `write`** of the
allocation-capable consumer with the output extern
(`Spike/Lib/A64ConsumerAEStart.lean`'s `correctKOnAE`), with `write` a
certification dead end (`Kernel.prom_nil_of_write`,
`Spike.Lib.WriteDead.certStep_write_none`): no thread at a `write` has a
promise, and no promise is certified there.

- `not_take_of_sys`: a system call is not the transfer site.
- `writeNoPromA_b`, `writeNoPromAE_b`: `hsvc`, `hsvcE`.
- `promSharedAE_b`: `hpsE` (vacuous: no promise is certified at the `write`).
- `promSharedA_b`: `hps` (`promSharedAX`, the output `write`'s certification
  steps having no outcome).
-/
import Spike.Lib.WriteDead
import Spike.Lib.A64ConsumerAEStart

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)} {Top : Ctl → Prop}
  {rS : Range} {Tk : State → Prop}

/-- **A system call is not the transfer site** (`TakePathS.site`: the take
site is a `nop`). -/
theorem not_take_of_sys (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha hpc => by
  obtain ⟨-, -, hsys, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
  rw [hs] at hsys; cases hsys

/-- **No promise at a `write`** at any depth (`hsvc`): the thread is
certified there (`PreJA`), and no outstanding promise is
(`Kernel.prom_nil_of_write`). -/
theorem writeNoPromA_b (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) :
    WriteNoPromA Λ P p G own I rS Tk μ ar := by
  intro t s th hpre hth hs ⟨fd, b, n, hc⟩
  obtain ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth', -, -, -, -, hcert, -, -, -, hI, -⟩ := hpre
  obtain rfl : th' = th := by
    have h := congrArg (fun a : Array _ => a[0]?) (hth'.symm.trans hth); exact Option.some.inj h
  exact Kernel.prom_nil_of_write (siteAt_noneA hN hI (not_take_of_sys hT hI hs)) hs hc hcert

/-- **No promise in the middle of the output `write`** (`hsvcE`): as
`writeNoPromA_b` at `EmitSA`'s `write(1, …)`. -/
theorem writeNoPromAE_b (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) :
    WriteNoPromAE Λ P p G own I Top rS Tk μ ar := by
  intro t s th h hth
  obtain ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth', -, -, -, -, hcert, -, -, -, hJ, -⟩ := h
  obtain rfl : th' = th := by
    have h := congrArg (fun a : Array _ => a[0]?) (hth'.symm.trans hth); exact Option.some.inj h
  obtain ⟨-, -, -, -, hs, c₀, fs₀, c₁, b, n, Pw, hI, -, hdc, -⟩ := hJ
  exact Kernel.prom_nil_of_write (siteAt_noneA hN hI (not_take_of_sys hT hI hs)) hs hdc hcert

/-- **No promise is certified in the middle of the output `write`**
(`hpsE`, vacuously): the promising thread is at the `write`, and has an
outstanding promise (`Kernel.prom_nil_of_write`). -/
theorem promSharedAE_b (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) :
    PromSharedAE Λ P p G own I Top rS Tk μ ar := by
  intro t s th w h hth _ hc
  obtain ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth', -, -, -, -, -, -, -, -, hJ, -⟩ := h
  obtain rfl : th' = th := by
    have h := congrArg (fun a : Array _ => a[0]?) (hth'.symm.trans hth); exact Option.some.inj h
  obtain ⟨-, -, -, -, hs, c₀, fs₀, c₁, b, n, Pw, hI, -, hdc, -⟩ := hJ
  have := Kernel.prom_nil_of_write (t := Live.Sem.promThread _ t.1.mem w)
    (siteAt_noneA hN hI (not_take_of_sys hT hI hs)) hs hdc hc
  simp at this

/-- **`PromSharedA` from the node obligations** with the output extern
(`hps`): `promSharedAX`, a certification step at the output `write` having
no outcome (`Spike.Lib.WriteDead.certStep_write_none`). -/
theorem promSharedA_b (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    (hT : TakePathS Λ p μ I rS Tk) :
    PromSharedA Λ P p G own I rS Tk μ ar :=
  promSharedAX hP hN hsafe hrd hwf hGpl hok hT fun _ _ _ _ _ _ _ hsi hs ⟨_, _, hd⟩ hso ho =>
    (Spike.Lib.WriteDead.certStep_write_none hsi hs hd hso ho).elim

end Spike.Lib.A64ConsumerA
