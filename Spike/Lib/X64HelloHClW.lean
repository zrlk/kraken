/-
**hello's clone facts from the pre-spawn fragment, on x86-64** (the twin of `Spike/Lib/A64HelloHClW.lean`; the
hello counterpart of wake's `X64WakeHClW`/`X64WakeHClC`, at hello's three-level fragment `I3` and
`ClonePostH`/`CloneInvH`/`ClonePreH`).

At main's `clone` the one thread is at a system call that decodes to `clone`. A fragment state off `Cl` at a
system call is not at a `clone` (`NodesA.sysOkXCT`), so the state is `Cl`'s, hence at the clone's pc
(`clonePcH`). `h0`'s and `h1`'s levels are never there, so the state is `h2`'s and in `CloneInvH`
(`i3_cloneInvH`).

- `pc_of_cloneH`: a fragment state at a `clone` call is at `clonePcH L`, given `Cl` only there (wake's
  `pc_of_clone`).
- `hClH_of`: `ClonePreH` at `r0Of`, `r1Of` with `X` main's state (wake's `hCl_of`'s core, through
  `clonePreH_of`), from the fragment's nodes and take path, the certificate (`hcert`: the empty promises),
  `HeldOk2` (the child's stack owned at `h2`'s clone states, `hown2`), the child's stack top in `%rsi` there
  (`hx1`: `ClonePostH` leaves it existential), the stacks not wrapping (`hbd`), main's source id (`htid`) and
  the buffer fact `hbuf` (`clonePreH_of`'s open hypothesis).

The instance plumbing (`SpawnPrem`, the pre-spawn relation's `R1O`, which give `hth`, `hs`, `hI`, `hH`,
`hcert`, `htid`) is hello's `W`, as in `X64HelloClonePreHOf`.

## Differences from the AArch64 version

- Over x86-64's `X64ConsumerA` (`NodesA`, `I3`, `siteAt_noneA`), `X64ConsumerS`, `X64HelloSrc.helloSrc`,
  `X64HelloMainPreSrc.SpawnSrcH`, `X64HelloInst.BufAtSpawn`, `X64WakeSrcDefs.mainTidLbl`, `X64.Rt.Ti2`,
  `X64.Rt.PreChild`, `X64.WakeOSplit.owned_not_unowned`.
- The child's stack top is `%rsi` (`hx1`; AArch64: `x1`), at wake's `X64.Flow.WakeWc.kOf`.
- `ClonePreH` has no label prefix (AArch64's `pfxM` has no counterpart).
- A64's `cloneInvH_of_I3` and `hpostH_of` are dead and not twinned (`hClH_of` uses `i3_cloneInvH` directly).
-/
import Spike.Lib.X64HelloWcInv3
import Spike.Lib.X64ConsumerASys
import Spike.Lib.Handover
import Spike.Lib.X64WakeOSplit
import Spike.Lib.X64WakeWcSp4Seg

namespace Spike.Lib.X64HelloHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (abi pcOf)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize Owned HeldOk2)
open Spike.Lib.X64ConsumerA (NodesA I3)
open Spike.Lib.X64ConsumerS (TakeSiteS InvS OwnS)
open Spike.Lib.X64HelloPreA (clonePcH CloneInvH ClonePreH H0StmtH H1StmtH H2StmtH i3_cloneInvH clonePreH_of)
open Spike.Lib.X64HelloInst (BufAtSpawn)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Rt.Ti2 (r0Of)

/-- **A fragment state at a `clone` call is at the clone's pc**, where `Cl`
marks only states there: off `Cl`, `NodesA.sysOkXCT` rules the call out. -/
theorem pc_of_cloneH {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS}
    {ab : Option (State → Prop)} {Cl : State → Prop} {L : RuntimeLayout}
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hT : TakeSiteS p μ I) (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    pcOf s = clonePcH L := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT hI hs fun h => hne (hCl s h)
  rw [hcall] at hd
  cases hd
  exact hcl st tl rfl

section I3

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {L0 : Lbl} {ls0 : Lsize}
  {ms0 : List TermRun.Frame → MemSide isa} {L : RuntimeLayout} {endPc : Int64} {Start inv0 : FragS isa}
  {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {ar : Arena}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}

/-- **`ClonePreH` at main's `clone`** (wake's `hCl_of`'s core) with `X`
main's state, at `r0Of`, `r1Of`:
- `CloneInvH` from the fragment (`pc_of_cloneH`, `i3_cloneInvH`);
- the promises empty (`hcert`, `Handover.prom_nil_of_clone`, the take
  site off the call by `TakeSiteS.off_sys`);
- the held list `[(0, r1), (0, r0)]`, both owned, from `HeldOk2`: the
  other two disjuncts leave `r1` unowned, but `h2`'s clone states own it
  (`hown2`);
- the child's stack top `%rsi` (`hx1` at `h2`'s clone states, the stacks
  not wrapping `hbd`);
- main's source id label (`htid`), the buffer fact (`hbuf`).

`H1StmtH`'s `[]`-landing is unsatisfiable at the real run (rodata lands under a frame); `h1` is read only
through its clone component, so pass an `H1StmtH` with no landing. -/
theorem hClH_of (hN : NodesA Λ helloSrc μ rd G own ar (I3 ar L0 ls0 inv0 inv1 inv2) ab Cl)
    (hT : TakeSiteS helloSrc μ (I3 ar L0 ls0 inv0 inv1 inv2)) (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K L0 ms0 L Start inv0) (h1 : H1StmtH W1 K ar L0 ms1 L Rd inv1)
    (h2 : H2StmtH W2 K ar L0 ms2 L endPc Box inv2)
    (hbd : L.stacksA.toNat + 32768 < 2 ^ 64)
    (hown2 : ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      Owned L.Λ (r1Of L.lab) s)
    (hx1 : ∀ l b n l' b' n' s c fs, inv2 l b n l' b' n' s c fs → pcOf s = clonePcH L →
      s.st.1.regs.get64 .rsi = Spike.Lib.X64.Flow.WakeWc.kOf L.lab)
    {A : Arch} {x : Scc.Sem.Kernel.KState} {mem : Memory}
    {d : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} {th : Thread isa} {th0 : TermRun.TTh}
    {hd : Option (Nat × TermRun.Word)}
    {lbl : Lbl} {lsize : Lsize} (hth : d.1.threads = #[th]) (hs : s.ths = #[th0])
    (hI : I3 ar L0 ls0 inv0 inv1 inv2 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack)
    (hsys : abi.atSys th.st = true) {st tl : Nat}
    (hcall : Scc.Sem.Kernel.callOf abi th = some (.clone st tl))
    (hcert : Scc.Sem.CertOkC A (Scc.Sem.Kernel.certSem abi A μ x 0) 0 th mem)
    (hH : HeldOk2 L.Λ (r0Of L.lab) (r1Of L.lab) th.st d.2.held)
    (htid : th0.tidLbl = some (mainTidLbl 2))
    (hbuf : ∀ l ws lb, SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → BufAtSpawn s lb) :
    ClonePreH L.Λ (r0Of L.lab) (r1Of L.lab) (· = th.st) lbl d s := by
  have hpc := pc_of_cloneH hN hT hCl hI hsys hcall
  have hci := i3_cloneInvH h0 h1 h2 hI hpc
  have hprom : th.prom = [] :=
    Spike.Lib.Handover.prom_nil_of_clone (Spike.Lib.X64ConsumerA.siteAt_noneA hN hI (hT.off_sys hI hsys))
      hsys hcall hcert
  have hlabS : Spike.Lib.X64.Flow.Ret0.stacksA L.lab = L.stacksA := L.lab_stacks
  have hbd' : (Spike.Lib.X64.Flow.Ret0.stacksA L.lab).toNat + 32768 < 2 ^ 64 := by rw [hlabS]; exact hbd
  obtain ⟨hr1lo, hr1sz⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd'
  obtain ⟨hr0lo, hr0sz⟩ := Spike.Lib.X64.Rt.Ti2.r0Of_eq L.lab
  rw [hlabS] at hr1lo hr0lo
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, hl, hb, -, -, hi⟩ | ⟨l, b, n, l', b', n', -, -, -, -, -, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l b n hl hb).2.2 _ _ _ hi)
  have hO1 := hown2 l b n l' b' n' _ _ _ hi hpc
  have hX1 := hx1 l b n l' b' n' _ _ _ hi hpc
  rcases hH with ⟨-, -, hu⟩ | ⟨-, -, hu⟩ | ⟨hheld, hO0, -⟩
  · exact (Spike.Lib.X64.WakeOSplit.owned_not_unowned hO1 hu (by rw [hr1lo]; have := L.stacks_al; omega)
      (by rw [hr1sz]; decide)).elim
  · exact (Spike.Lib.X64.WakeOSplit.owned_not_unowned hO1 hu (by rw [hr1lo]; have := L.stacks_al; omega)
      (by rw [hr1sz]; decide)).elim
  have e1 : (th.st.st.1.regs.get64 .rsi).toNat = (r1Of L.lab).lo + (r1Of L.lab).size := by
    rw [hX1, hr1lo, hr1sz]
    show (Spike.Lib.X64.Flow.Ret0.stacksA L.lab + 16384#64 + 16384#64).toNat = _
    rw [hlabS]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact clonePreH_of hth hs hsys hcall hprom hci hheld (Spike.Lib.X64.Rt.Ti2.r01_disj hbd') hO0 hO1
    ⟨by rw [hr0lo], hr0sz⟩ e1 htid hbuf

end I3

end Spike.Lib.X64HelloHClW

/-- info: 'Spike.Lib.X64HelloHClW.pc_of_cloneH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHClW.pc_of_cloneH

/-- info: 'Spike.Lib.X64HelloHClW.hClH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHClW.hClH_of
