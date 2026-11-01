/-
**hello's clone facts at `h2`'s invariant** (AArch64): `A64HelloHClW`'s `hClH_of` with the third level's invariant
fixed to
`HelloH2Inv.inv2H`, whose per-state facts `X2H` hold at every clone state.

`hClH_of` leaves two facts about `inv2`'s clone states open: the child's stack
owned (`hown2`) and `x1` at its top (`hx1`). At `inv2H` both are `X2H`'s clone
clause (`HelloH2Inv.own2_of`, `x1_2_of`), so the instance has neither premise.
`h1` is taken as `H1StmtHF … fr` (the real run's, rodata landing under main's
frame), converted by `H1StmtHF.toH` as `A64HelloHClWF` does.

- `hClH_ofI`: `ClonePreH` at `r0Of`, `r1Of` at the clone, `inv2 := inv2H`.
-/
import Spike.Lib.A64HelloHClWF
import Spike.Lib.A64HelloH2Inv

namespace Spike.Lib.HelloHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Scc.Sem.A64 (abi pcOf)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize HeldOk2)
open Spike.Lib.A64ConsumerA (NodesA I3)
open Spike.Lib.A64ConsumerS (TakeSiteS OwnS)
open Spike.Lib.HelloPreA (clonePcH ClonePreH BufAtSpawn H0StmtH H1StmtHF H2StmtH pfxM)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloH2Inv (inv2H own2_of x1_2_of)
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Rt.Ti2 (r0Of)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isaLSE2} {L : RuntimeLayout} {a endPc : Int64} {Start inv0 : FragS isaLSE2}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}

/-- **`ClonePreH` at main's `clone` with `inv2 := inv2H`** (`hClH_of`): the
child's stack owned and `x1` its top at the clone are `X2H`'s (`own2_of`,
`x1_2_of`); `h1` from `H1StmtHF` (`H1StmtHF.toH`). The remaining premises are
`hClH_of`'s: the fragment's nodes and take site, the clone's pc, the levels'
statements, the stacks not wrapping (`hbd`), main's state and call, the
certificate, `HeldOk2`, main's source id and the buffer fact `hbuf`. -/
theorem hClH_ofI (hN : NodesA Λ helloSrc μ rd G own ar (I3 ar L0 ls0 inv0 inv1 (inv2H W2 K ms2 L a endPc L0 ls0)) ab
      Cl)
    (hT : TakeSiteS helloSrc μ (I3 ar L0 ls0 inv0 inv1 (inv2H W2 K ms2 L a endPc L0 ls0)))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtHF W1 K ar L0 ms1 L Rd inv1 fr)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box (inv2H W2 K ms2 L a endPc L0 ls0))
    (hbd : L.stacksA.toNat + 32768 < 2 ^ 64)
    {A : Arch} {x : Scc.Sem.Kernel.KState} {mem : Memory}
    {d : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {th0 : TermRun.TTh} {hd : Option (Nat × TermRun.Word)}
    {lbl : Lbl} {lsize : Lsize} (hth : d.1.threads = #[th]) (hs : s.ths = #[th0])
    (hI : I3 ar L0 ls0 inv0 inv1 (inv2H W2 K ms2 L a endPc L0 ls0) lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack)
    (hsys : abi.atSys th.st = true) {st tl : Nat}
    (hcall : Scc.Sem.Kernel.callOf abi th = some (.clone st tl))
    (hcert : Scc.Sem.CertOkC A (Scc.Sem.Kernel.certSem abi A μ x 0) 0 th mem)
    (hH : HeldOk2 L.Λ (r0Of L.lab) (r1Of L.lab) th.st d.2.held)
    (htid : th0.tidLbl = some (mainTidLbl 2))
    (hbuf : ∀ l ws lb, SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb) :
    ClonePreH pfxM L.Λ (r0Of L.lab) (r1Of L.lab) (· = th.st) lbl d s :=
  hClH_of hN hT hCl h0 h1.toH h2 hbd
    (fun _ _ _ _ _ _ _ _ _ hi hpc => own2_of hi hpc)
    (fun _ _ _ _ _ _ _ _ _ hi hpc => x1_2_of hi hpc)
    hth hs hI hsys hcall hcert hH htid hbuf

end Spike.Lib.HelloHClW

/-- info: 'Spike.Lib.HelloHClW.hClH_ofI' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHClW.hClH_ofI
