/-
**wake's clone facts from `h1`** (AArch64): `OpenW.hpost` and the core of
`OpenW.hCl` (`Spike/Lib/WakeFinalCAW.lean`) from the pre-spawn relation at
main's `clone`.

At a `SpawnPrem`, main is at a system call that decodes to `clone`. A
fragment state off `Cl` at a system call is not at a `clone`
(`NodesA.sysOkXCT`), so the state is `Cl`, hence at the clone's pc. `inv0`
is never there, so the state is `inv1`'s and has `CloneInv`.

- `pc_of_clone`: a fragment state at a `clone` call is at the clone's pc,
  given `Cl` only there.
- `cloneInv_of_I2`: `CloneInv` at an `I2` state at a `clone` call (the
  `inv0` side off the clone's pc, the `inv1` side's clone clause).
- `cloneInv_of_spawnPrem`: the same at `PreJAH`'s witnesses, from a
  `SpawnPrem` under any relation below `R1O`.
- `hpost_of`: `OpenW.hpost`'s statement (main's state after the clone is
  `ClonePost`'s).
- `clone_args`: a `clone` call's stack and thread pointer are `x1`, `x3`.
- `hCl_of`: `OpenW.hCl`'s statement (`ClonePre` with `X` main's state and
  the request `tcb2Q`), given in addition the data's ranges, the stacks not
  wrapping, at `inv1`'s clone states the child's stack owned and `c`'s
  label of positive size, and main's id at its TCB; main's source thread id
  from `PreJAH`'s source run (`MainTidLbl.mainTidLbl_of_reach`).
- At `wakeD` with `h1`'s invariant `inv1W` (`A64WakeH1Inv`): `hbd_W` (the
  stacks below `2 ^ 64`, from `hsub1`), `hme_W` (main's id at `pinA + 8`),
  `nodes_of` (`NodesA`, `TakeSiteS` from `OPrem`), and `hpost_W`, `hCl_W`:
  `OpenW.hpost`, `OpenW.hCl` from `OPrem`, the child's stack owned at
  `inv1W`'s clone states by `WakeH1Inv.own1_of`.
-/
import Spike.Lib.WakeHPre
import Spike.Lib.A64WakeWcInv
import Spike.Lib.A64SFactsACH
import Spike.Lib.A64WakeTcb2Call
import Spike.Lib.WakeTcbArea
import Spike.Lib.WakeOSplit
import Spike.Lib.A64WakeH1Inv
import Spike.Lib.WakeOD
import Spike.Lib.Src.MainTidLbl

namespace Spike.Lib.WakeHClW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (I2 NodesA)
open Spike.Lib.A64ConsumerS (TakeSiteS InvS OwnS)
open Spike.Lib.A64.Flow.WakeWc (clonePc CloneInv ClonePost)
open Spike.Lib.WakeSpawnR (ιR endR QG PreR)
open Spike.Lib.A64Consumer (HeldOk2 Owned)
open Spike.Lib.WakePreA (ClonePre cloneAt)
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.A64.Rt.Ti2 (r0Of)

/-- **A `clone` call's arguments**: the stack in `x1`, the thread pointer in
`x3` (AArch64's `cloneTls`). -/
theorem clone_args {s : State} {st tl : Nat}
    (h : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    st = (s.st.1.regs.getXReg .X1).toNat ∧ tl = (s.st.1.regs.getXReg .X3).toNat := by
  unfold Kernel.decode at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨by simp [abi, xRegs, Reg64s.getXReg], by simp [abi, xRegs, Reg64s.getXReg, Kernel.Nrs.a64]; rfl⟩)
    | cases h

/-- **A fragment state at a `clone` call is at the clone's pc**, where `Cl`
marks only states there: off `Cl`, `NodesA.sysOkXCT` rules the call out. -/
theorem pc_of_clone {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {I : InvS}
    {ab : Option (State → Prop)} {Cl : State → Prop} {L : RuntimeLayout}
    (hN : NodesA Λ p μ rd G own ar I ab Cl) (hT : TakeSiteS p μ I) (hCl : ∀ s, Cl s → pcOf s = clonePc L)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) : pcOf s = clonePc L := by
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT hI hs fun h => hne (hCl s h)
  rw [hcall] at hd
  cases hd
  exact hcl st tl rfl

/-- **`CloneInv` at an `I2` state at a `clone` call**: `inv0` is off the
clone's pc (`hnc0`), `inv1` has `CloneInv` there (`hcl1`). -/
theorem cloneInv_of_I2 {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop}
    {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)} {Cl : State → Prop}
    {L : RuntimeLayout} {endPc : Int64} {L0 : Lbl} {ls0 : Lsize} {inv0 : FragS isaLSE2}
    {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    (hN : NodesA Λ wakeSrc μ rd G own ar (I2 ar L0 ls0 inv0 inv1) ab Cl)
    (hT : TakeSiteS wakeSrc μ (I2 ar L0 ls0 inv0 inv1)) (hCl : ∀ s, Cl s → pcOf s = clonePc L)
    (hnc0 : ∀ s c fs, inv0 s c fs → pcOf s ≠ clonePc L)
    (hcl1 : ∀ l b n s c fs, inv1 l b n s c fs → pcOf s = clonePc L →
      CloneInv L endPc (A64ConsumerA.upd L0 l b) s c fs)
    {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I2 ar L0 ls0 inv0 inv1 lbl lsize s c fs) (hs : abi.atSys s = true) {st tl : Nat}
    (hcall : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    CloneInv L endPc lbl s c fs := by
  have hpc := pc_of_clone hN hT hCl hI hs hcall
  rcases hI with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, rfl, -, hi⟩
  · exact absurd hpc (hnc0 s c fs hi)
  · exact hcl1 l b n s c fs hi hpc

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

variable {asm : String} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
  {M : WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {D : WakeO.OData} {μ' : Marks}

/-- **`CloneInv` at `PreJAH`'s witnesses** from a `SpawnPrem` under a
relation below `R1O` (`hR1`): main's thread, its source thread with empty
stack's control in `I2`, main at the clone's pc with `CloneInv`. -/
theorem cloneInv_of_spawnPrem (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (endR hp i) (A64ConsumerA.upd D.L0 l b) s c fs)
    {d : Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    (hP : SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r) :
    ∃ (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (hd : Option (Nat × TermRun.Word)),
      d.1.threads = #[th] ∧ s.ths = #[th0] ∧
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧
      CloneInv (Ly) (endR hp i) lbl th.st ⟨th0.term, th0.env, hd⟩ th0.stack := by
  obtain ⟨h1, -, h3, h4, -, h6, h7, -⟩ := id hP
  obtain ⟨⟨⟨⟨hRS, -⟩, -⟩, -⟩, -⟩ := hR1 _ _ h1
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at h6; cases h6
  obtain ⟨thm, th0, -, lbl, lsize, -, -, -, hd, hth, -, -, -, -, -, hs, -, -, hJ, -⟩ := hPre
  obtain rfl : thm = th := by rw [hth] at h3; exact Option.some.inj h3
  exact ⟨th0, lbl, lsize, hd, hth, hs, hJ, cloneInv_of_I2 hN hT hCl hnc0 hcl1 hJ h4 h7⟩

/-- **`OpenW.hpost`'s statement**: main's state at the clone is
`ClonePost`'s (`cloneInv_of_spawnPrem`'s `CloneInv`). -/
theorem hpost_of (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (endR hp i) (A64ConsumerA.upd D.L0 l b) s c fs) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, ClonePost (Ly) (endR hp i) J t th.st c := by
  intro d s th stack tls r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP _ _
  obtain ⟨_, _, _, _, -, -, -, hci⟩ := cloneInv_of_spawnPrem hp i hR1 hN hT hCl hnc0 hcl1 hP
  obtain ⟨-, J, t, _, hcp, -⟩ := hci
  exact ⟨_, J, t, hcp⟩

/-- **`OpenW.hCl`'s statement** (`WakeHPre.hpre_of`'s `hCl`): `ClonePre` at
`D.r0`, `r1Of`, with `X` main's state there, the second TCB request
`tcb2Q`, from `CloneInv` (`ClonePost`'s registers and frame), `SpawnPrem`
(the call, `PreJAH`'s certificate for the promises) and `HeldOk2` (the
third disjunct: the child's stack is owned at the clone, `hown1`).

Premises beyond `cloneInv_of_spawnPrem`'s: the data's ranges (`hr0`,
`hr1`), the stacks not wrapping (`hbd`), and at `inv1`'s clone states the
child's stack owned (`hown1`) and `c`'s label of positive size (`hlsz`);
main's id placed at its TCB (`hme`). Main's source thread id is from
`PreJAH`'s source run. -/
theorem hCl_of (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (endR hp i) (A64ConsumerA.upd D.L0 l b) s c fs)
    (hr0 : D.r0 = r0Of (Ly).lab) (hr1 : D.r1 = r1Of (Ly).lab)
    (hbd : (Ly).stacksA.toNat + 32768 < 2 ^ 64)
    (hown1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) → Owned (Ly).Λ D.r1 s)
    (hlsz : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) → ∀ l',
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < A64ConsumerA.updN D.ls0 l n l')
    (hme : D.L0 (mainTidLbl 2) = some ((Ly).pinA + 8#64).toNat) :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ D.r0 D.r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : Spike.Lib.A64.Rt.TcbGG), ClonePre pfxM (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt pfxM (Ly).exe ∧
          (st.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Rt.tcbOf (Ly).lab q) ∧
        Spike.Lib.WakeTcbArea.Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l) ∧
        BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64 = (Ly).pinA + 24#64 := by
  intro d s th stack tls r th0 lbl lsize ts hd hP hth hs _ _ hJ hH _
  obtain ⟨h1, -, -, h4, -, h6, h7, -⟩ := id hP
  obtain ⟨⟨⟨⟨hRS, -⟩, -⟩, -⟩, -⟩ := hR1 _ _ h1
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at h6; cases h6
  obtain ⟨thm, th0', _, _, _, _, _, _, _, hthm, -, -, -, -, hcert, hs', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨_, hreach⟩⟩ := hPre
  have htid0 : th0.tidLbl = some (mainTidLbl 2) := by
    rw [hs] at hs'
    obtain rfl : th0 = th0' := List.singleton_inj.mp (congrArg Array.toList hs')
    exact Spike.Lib.MainTidLbl.mainTidLbl_of_reach hreach hs
  obtain rfl : th = thm := by
    rw [hth] at hthm; exact List.singleton_inj.mp (congrArg Array.toList hthm)
  have hpc := pc_of_clone hN hT hCl hJ h4 h7
  have hprom : th.prom = [] :=
    Spike.Lib.Handover.prom_nil_of_clone (A64ConsumerA.siteAt_noneA hN hJ (hT.off_sys hJ h4)) h4 h7 hcert
  obtain ⟨hst1, htl3⟩ := clone_args h7
  rcases hJ with ⟨-, -, hi⟩ | ⟨l, b, n, hl, -, rfl, rfl, hi⟩
  · exact absurd hpc (hnc0 _ _ _ hi)
  have hO1 := hown1 l b n _ _ _ hi hpc
  have hlz := hlsz l b n _ _ _ hi hpc
  obtain ⟨hstk, J, t, lc, hcp, hterm, -, hc, hmev, -, h9l, h10l⟩ := hcl1 l b n _ _ _ hi hpc
  obtain ⟨R, F₂, σC, cA, m, fr, -, -, hS, -, hat, -, hsp, -⟩ := hcp
  obtain ⟨hexe, hend, hdecl, -, σ, hA, -, -, -, hx1, -, hx3, -, -, hx9, hx10, -⟩ := hS
  obtain ⟨-, -, -, hpcS, -⟩ := hat
  have hlabS : Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks
  have hbd' : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by rw [hlabS]; exact hbd
  obtain ⟨hr1lo, hr1sz⟩ := Spike.Lib.A64.Rt.Ti2.r1Of_eq hbd'
  obtain ⟨hr0lo, hr0sz⟩ := Spike.Lib.A64.Rt.Ti2.r0Of_eq (Ly).lab
  rw [hlabS] at hr1lo hr0lo
  have hal16 := (Ly).stacks_al
  have e1 : (th.st.st.1.regs.getXReg .X1).toNat = (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size := by
    show th.st.st.1.regs.X1.toBitVec.toNat = _
    rw [hA.regs, hx1, hr1lo, hr1sz]
    show (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 16384#64 + 16384#64).toNat = _
    rw [hlabS]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hcall : callOf abi th = some (.clone ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) tls) := by
    rw [← e1, ← hst1]; exact h7
  have hO1' : Owned (Ly).Λ (r1Of (Ly).lab) th.st := hr1 ▸ hO1
  rcases hH with ⟨-, -, hu⟩ | ⟨-, -, hu⟩ | ⟨hheld, hO0, -⟩
  · exact (Spike.Lib.WakeOSplit.owned_not_unowned hO1' (hr1 ▸ hu) (by rw [hr1lo]; omega) (by rw [hr1sz]; decide)).elim
  · exact (Spike.Lib.WakeOSplit.owned_not_unowned hO1' (hr1 ▸ hu) (by rw [hr1lo]; omega) (by rw [hr1sz]; decide)).elim
  have hne : mainTidLbl 2 ≠ l := fun h => by rw [h] at hme; rw [hme] at hl; cases hl
  have h10 : (th.st.st.1.regs.getXReg .X10).toNat = ((Ly).pinA + 8#64).toNat := by
    simp only [A64ConsumerA.upd, hne, ↓reduceIte, hme, Option.some.injEq] at h10l
    exact h10l.symm
  have hr0' : D.r0.lo = (Ly).stacksA.toNat ∧ D.r0.size = 16384 := by rw [hr0]; exact ⟨hr0lo, hr0sz⟩
  let q := Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q ⟨0#64, 0#64, 0#64⟩ ⟨th0.term, th0.env, hd⟩
  have hx3' : (th.st.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Rt.tcbOf (Ly).lab q := by
    show th.st.st.1.regs.X3.toBitVec = _
    rw [hA.regs, hx3, Spike.Lib.A64.WakePh.Tcb2Call.tcb2Q_tcbOf]
  refine ⟨(· = th.st), q, ⟨th, th0, tls, (th.st.st.1.regs.getXReg .X9).toNat,
    (th.st.st.1.regs.getXReg .X10).toNat, lc, hth, hs, by rw [hexe]; exact hpcS, h4, hprom, hcall, e1, htl3.symm,
    rfl, rfl, by rw [hheld, hr1], by rw [hr0]; exact Spike.Lib.A64.Rt.Ti2.r01_disj hbd', hO0, hO1', rfl,
    by omega, by omega, by omega, hr0'.2, hterm, hc, hmev, htid0,
    ⟨by decide, _, by simp [Scc.Sem.wordAddr, h9l], rfl⟩,
    ⟨by decide, _, by simp [Scc.Sem.wordAddr, h10l], rfl⟩⟩,
    fun st hst => by subst hst; exact ⟨hexe, hend, hdecl⟩,
    fun st hst => by subst hst; exact ⟨hpcS, hx3'⟩, ⟨rfl, rfl⟩, hstk, fun l' hl' => hlz l' hl', ?_⟩
  rw [h10]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [BitVec.add_assoc]; rfl

/-! ## At `wakeD` with `inv1W` -/

section W

variable (E : Entry) (cT : Loc) (Dt : State → Prop) (Ctx : FragS isaLSE2) (ls0 : Lsize)
  (frM : TermRun.Frame) (inv0 : FragS isaLSE2)

set_option hygiene false in
/-- `wakeD` at the levels with `h1`'s invariant `inv1W`. -/
local notation "DH" => WakeOD.wakeD hp i E cT Dt ls0 (WakeOPremW.W0W hp i E Dt Ctx ls0 frM) inv0
  (WakeOPremW.W1W hp i E Dt Ctx ls0) (WakeH1Inv.inv1W hp i E cT Dt Ctx ls0)

/-- **The stacks do not wrap**: the child's range is in the pool. -/
theorem hbd_W (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) : (Ly).stacksA.toNat + 32768 < 2 ^ 64 := by
  have hs := (Ly).stacks_sub
  have hf := (Ly).pool_fit
  have hlabS : Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks
  obtain ⟨-, h2⟩ := hsub1
  obtain ⟨-, h4⟩ := hs
  simp only [WakeOSide.r1W, r1Of, hlabS, BitVec.toNat_add, BitVec.toNat_ofNat] at h2
  simp only at h4
  omega

/-- **Main's id at its TCB** in the start's labels. -/
theorem hme_W : Spike.Lib.WakeLoadT.L0T (Ly).Λ (mainTidLbl 2) = some ((Ly).pinA + 8#64).toNat := by
  have hp0 := PlaceW.pinA_toNat_ofPlaceW hp i
  have hsm := (Ly).words_small _ (Ly).pin_mem
  simp only [Spike.Lib.WakeLoadT.L0T, A64ConsumerA.upd, ↓reduceIte, Spike.Lib.WakeLoadT.tcb0,
    BitVec.toNat_add, BitVec.toNat_ofNat, Option.some.injEq]
  omega

variable {B : Budget} {Ab Ac : State → Prop}

/-- **The fragment's nodes and take path** from `OPrem` (`inst_of_segWA2CH2`). -/
theorem nodes_of (hO : WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    NodesA (Ly).Λ wakeSrc ((target (kernel 2) E).marks asm (Ly).Λ) (DH).rd (DH).G (DH).own (DH).ar
        (I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1) none (DH).Cl ∧
      TakeSiteS wakeSrc ((target (kernel 2) E).marks asm (Ly).Λ) (I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1) :=
  let h := A64ConsumerA.inst_of_segWA2CH2 hO.h1 hO.h0 hO.ha hO.hW0 hO.hW1 hO.hsplit hO.hs0 hO.hs1 hO.hz0 hO.hz1
    hO.hro hO.hd hO.hw0 hO.hw1
  ⟨h.1, h.2.1.toTakeSiteS⟩

/-- **`OpenW.hpost` at `wakeD` with `inv1W`**, from `OPrem` there. -/
theorem hpost_W (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q,
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      (wakeS arch).Run s [] s' →
      PreR hp i arch R1 μ M r0 r1 d th stack s s' w s0 s1 lbl lsize ts j own₀ T S l pT w1 w2 ty1 r0' X q →
      ∃ c J t, ClonePost (Ly) (endR hp i) J t th.st c :=
  hpost_of hp i hR1 (nodes_of hp i E cT Dt Ctx ls0 frM inv0 hO).1 (nodes_of hp i E cT Dt Ctx ls0 frM inv0 hO).2
    (fun _ h => h.1) (Spike.Lib.A64.WakeWf.noClone_of hO.h0)
    (fun l b n => WakeH1Inv.cloneInv_of hp i E cT Dt Ctx ls0 l b n)

/-- **`OpenW.hCl` at `wakeD` with `inv1W`**, from `OPrem` there (`c`'s
label sized by `WakeH1Inv.lsize_of`, the child's stack owned at
`inv1W`'s clone states by `WakeH1Inv.own1_of`: `X1W`'s clone clause, from
`CloneP`'s `StackM` through `scc_rt_thread_init`'s post). -/
theorem hCl_W (hR1 : ∀ d s, R1 d s → WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH)
    (hsub1 : (WakeOSide.r1W hp i).Sub (Ly).Λ.stackPool) :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ (DH).r0 (DH).r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : Spike.Lib.A64.Rt.TcbGG), ClonePre pfxM (Ly).Λ (DH).r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt pfxM (Ly).exe ∧
          (st.st.1.regs.getXReg .X3).toBitVec = Spike.Lib.A64.Rt.tcbOf (Ly).lab q) ∧
        Spike.Lib.WakeTcbArea.Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l) ∧
        BitVec.ofNat 64 (th.st.st.1.regs.getXReg .X10).toNat + 16#64 = (Ly).pinA + 24#64 :=
  hCl_of hp i hR1 (nodes_of hp i E cT Dt Ctx ls0 frM inv0 hO).1 (nodes_of hp i E cT Dt Ctx ls0 frM inv0 hO).2
    (fun _ h => h.1) (Spike.Lib.A64.WakeWf.noClone_of hO.h0)
    (fun l b n => WakeH1Inv.cloneInv_of hp i E cT Dt Ctx ls0 l b n) rfl rfl (hbd_W hp i hsub1)
    (fun l b n => WakeH1Inv.own1_of hp i E cT Dt Ctx ls0 l b n)
    (fun l b n => WakeH1Inv.lsize_of hp i E cT Dt Ctx ls0 l b n)
    (hme_W hp i)

end W

end Inst

end Spike.Lib.WakeHClW

/-- info: 'Spike.Lib.WakeHClW.hpost_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHClW.hpost_of

/-- info: 'Spike.Lib.WakeHClW.hCl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHClW.hCl_of

/-- info: 'Spike.Lib.WakeHClW.hCl_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHClW.hCl_W

/-- info: 'Spike.Lib.WakeHClW.hpost_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeHClW.hpost_W
