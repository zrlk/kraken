/-
**wake's clone facts at `PreJAH`'s witnesses** (x86-64): `X64WakeFinal`'s
`OpenX.hCl` (`ClonePre` with `X` main's state and the second TCB request
`tcb2Q`) from the pre-spawn relation at main's `clone`.

At a `SpawnPrem`, main is at the clone's pc (`X64WakeHClW.pc_of_clone`), so
in `inv1`'s disjunct with `CloneInv`: `ClonePost`'s `wcNS` gives the
registers (`%rsi` the child's stack top `kOf`, `%r8` the second TCB `t2`,
`%r12`/`%rbx` the labels' words by `CloneInv`'s own clauses), `HeldOk2`'s
third disjunct the ranges held (the child's stack owned at `inv1`'s clone
states rules the others out).

- `clone_args`: a `clone` call's stack and thread pointer are `%rsi`, `%r8`.
- `hbd_W`: the stacks do not wrap (`X64WakeOSide.stacks_lt`).
- `hCl_of`: `OpenX.hCl`'s statement, given the data's ranges, the stacks not
  wrapping, at `inv1`'s clone states the child's stack owned and `c`'s label
  of positive size; main's source thread id from `PreJAH`'s source run
  (`X64MainTidLbl.mainTidLbl_of_reach`).
- `hCl_W`: the same at `wakeD` with `W0W`/`W1W`/`inv1W` and any `inv0`, from
  `OPrem` (`X64WakeHClW.nodes_of`, `X64.WakeH1Inv.own1_of`/`lsize_of`).

x86-64 twin of `Spike/Lib/A64WakeHClW.lean`'s `clone_args`/`hCl_of`/`hCl_W`.
**Unlike AArch64**:
- the call's arguments are `%rsi`, `%r8` (A64 `x1`, `x3`);
- `ClonePre` reads `%r12`/`%rbx` as the label words, which `CloneInv` states
  directly (`lbl l`, `lbl (mainTidLbl 2)`), so no `hme` premise and no `X10`
  conjunct;
- `hown1` is stated at `r1Of` (`own1_of`'s range), and `hbd` needs no
  `hsub1`.
-/
import Spike.Lib.X64WakeHClW
import Spike.Lib.X64WakeTcb2Call
import Spike.Lib.X64WakeTcbArea
import Spike.Lib.X64WakeOSplit
import Spike.Lib.Src.X64MainTidLbl

namespace Spike.Lib.X64WakeHClC

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout TcbGG tcbOf)
open Spike.Lib.X64WakeSpawn (SpawnPrem)
open Spike.Lib.X64Consumer (Lbl Lsize Owned HeldOk2)
open Spike.Lib.X64ConsumerA (I2 NodesA)
open Spike.Lib.X64ConsumerS (TakeSiteS)
open Spike.Lib.X64.Flow.WakeWc (clonePc CloneInv ClonePost)
open Spike.Lib.X64WakeSpawnR (ιR QG)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64.Rt.Ti2 (r0Of)
open Spike.Lib.X64WakeTcbArea (Q2)
open Spike.Lib.X64WakeHClW (pc_of_clone)

/-- **A `clone` call's arguments**: the stack in `%rsi`, the thread pointer
in `%r8` (x86-64's `cloneTls`). -/
theorem clone_args {s : State} {st tl : Nat}
    (h : Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)) :
    st = (s.st.1.regs.get64 .rsi).toNat ∧ tl = (s.st.1.regs.get64 .r8).toNat := by
  unfold Kernel.decode at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨rfl, rfl⟩)
    | (cases h; simp [abi, Kernel.Nrs.x64]; rfl)
    | cases h

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hp i

/-- **The stacks do not wrap** (`X64WakeOSide.stacks_lt`). -/
theorem hbd_W : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
  have hlt := X64WakeOSide.stacks_lt hp i
  simp only at hlt
  omega

variable {asm : Asm} {E : Entry} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
  {M : X64WakeM0.MSide (ιR hp i)} {r0 r1 : ιR hp i → Range} {D : X64WakeO.OData} {μ' : Marks}

/-- **`OpenX.hCl`'s statement**: `ClonePre` at `D.r0`, `r1Of`, with `X`
main's state there, the second TCB request `tcb2Q`, from `CloneInv`
(`ClonePost`'s registers), `SpawnPrem` (the call, `PreJAH`'s certificate
for the promises) and `HeldOk2` (the third disjunct: the child's stack is
owned at the clone, `hown1`).

Premises beyond `X64WakeHClW.cloneInv_of_spawnPrem`'s: the data's ranges
(`hr0`, `hr1`), the stacks not wrapping (`hbd`), and at `inv1`'s clone
states the child's stack owned (`hown1`) and `c`'s label of positive size
(`hlsz`). Main's source thread id is from `PreJAH`'s source run. -/
theorem hCl_of (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ μ' D d s)
    (hN : NodesA (Ly).Λ wakeSrc μ' D.rd D.G D.own D.ar (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1) none D.Cl)
    (hT : TakeSiteS wakeSrc μ' (I2 D.ar D.L0 D.ls0 D.inv0 D.inv1))
    (hCl : ∀ s, D.Cl s → pcOf s = clonePc (Ly)) (hnc0 : ∀ s c fs, D.inv0 s c fs → pcOf s ≠ clonePc (Ly))
    (hcl1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) →
      CloneInv (Ly) (X64WakeAssemblyR.endR hp i) (X64ConsumerA.upd D.L0 l b) s c fs)
    (hr0 : D.r0 = r0Of (Ly).lab) (hr1 : D.r1 = r1Of (Ly).lab)
    (hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64)
    (hown1 : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) → Owned (Ly).Λ (r1Of (Ly).lab) s)
    (hlsz : ∀ l b n s c fs, D.inv1 l b n s c fs → pcOf s = clonePc (Ly) → ∀ l',
      TermRun.evalAt c.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l', 0⟩ 0)]) →
      0 < X64ConsumerA.updN D.ls0 l n l') :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 D.ar D.L0 D.ls0 D.inv0 D.inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ D.r0 D.r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : TcbGG), ClonePre (Ly).Λ D.r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = X64WakeAssemblyR.endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt (Ly).exe ∧ st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q) ∧
        Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l) := by
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
    exact Spike.Lib.X64MainTidLbl.mainTidLbl_of_reach hreach hs
  obtain rfl : th = thm := by
    rw [hth] at hthm; exact List.singleton_inj.mp (congrArg Array.toList hthm)
  have hpc := pc_of_clone hN hT hCl hJ h4 h7
  have hprom : th.prom = [] :=
    Spike.Lib.Handover.prom_nil_of_clone (X64ConsumerA.siteAt_noneA hN hJ (hT.off_sys hJ h4)) h4 h7 hcert
  obtain ⟨hst1, htl⟩ := clone_args h7
  rcases hJ with ⟨-, -, hi⟩ | ⟨l, b, n, -, -, rfl, rfl, hi⟩
  · exact absurd hpc (hnc0 _ _ _ hi)
  have hO1 := hown1 l b n _ _ _ hi hpc
  have hlz := hlsz l b n _ _ _ hi hpc
  obtain ⟨hstk, J, t, lc, hcp, hterm, -, hc, hmev, -, h12l, hbxl⟩ := hcl1 l b n _ _ _ hi hpc
  obtain ⟨R, F₂, σC, cA, m, fr, -, hS, -, hat, -, hsp, -⟩ := hcp
  obtain ⟨hexe, hend, hdecl, -, σ, hA, -, ⟨-, h12, hbx, hsi, h8, -⟩, -⟩ := hS
  obtain ⟨-, -, -, hpcS, -⟩ := hat
  have hlabS : Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab = (Ly).stacksA := (Ly).lab_stacks
  obtain ⟨hr1lo, hr1sz⟩ := Spike.Lib.X64.Rt.Ti2.r1Of_eq hbd
  obtain ⟨hr0lo, hr0sz⟩ := Spike.Lib.X64.Rt.Ti2.r0Of_eq (Ly).lab
  rw [hlabS] at hr1lo hr0lo
  have hbd' := hbd
  rw [hlabS] at hbd'
  have e1 : (th.st.st.1.regs.get64 .rsi).toNat = (r1Of (Ly).lab).lo + (r1Of (Ly).lab).size := by
    rw [hA.regs, hsi, hr1lo, hr1sz]
    show (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab + 16384#64 + 16384#64).toNat = _
    rw [hlabS]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hcall : callOf abi th = some (.clone ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) tls) := by
    rw [← e1, ← hst1]; exact h7
  rcases hH with ⟨-, -, hu⟩ | ⟨-, -, hu⟩ | ⟨hheld, hO0, -⟩
  · exact (Spike.Lib.X64.WakeOSplit.owned_not_unowned hO1 (hr1 ▸ hu) (by rw [hr1lo]; have := (Ly).stacks_al; omega)
      (by rw [hr1sz]; decide)).elim
  · exact (Spike.Lib.X64.WakeOSplit.owned_not_unowned hO1 (hr1 ▸ hu) (by rw [hr1lo]; have := (Ly).stacks_al; omega)
      (by rw [hr1sz]; decide)).elim
  have hr0' : D.r0.lo = (Ly).stacksA.toNat ∧ D.r0.size = 16384 := by rw [hr0]; exact ⟨hr0lo, hr0sz⟩
  let q := Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q ⟨0#64, 0#64, 0#64⟩ ⟨th0.term, th0.env, hd⟩
  have h8' : th.st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q := by
    rw [hA.regs, h8, Spike.Lib.X64.WakePh.Tcb2Call.tcb2Q_tcbOf]
  refine ⟨(· = th.st), q, ⟨th, th0, tls, (th.st.st.1.regs.get64 .r12).toNat,
    (th.st.st.1.regs.get64 .rbx).toNat, lc, hth, hs, by rw [hexe]; exact hpcS, h4, hprom, hcall, e1, htl.symm,
    rfl, rfl, by rw [hheld, hr1], by rw [hr0]; exact Spike.Lib.X64.Rt.Ti2.r01_disj hbd, hO0, hO1, rfl,
    by omega, by omega, by omega, hr0'.2, hterm, hc, hmev, htid0,
    ⟨by decide, _, by simp [Scc.Sem.wordAddr, h12l], rfl⟩,
    ⟨by decide, _, by simp [Scc.Sem.wordAddr, hbxl], rfl⟩⟩,
    fun st hst => by subst hst; exact ⟨hexe, hend, hdecl⟩,
    fun st hst => by subst hst; exact ⟨hpcS, h8'⟩, ⟨rfl, rfl⟩, hstk, fun l' hl' => hlz l' hl'⟩

variable {B : Budget} {Ab Ac : State → Prop} (cT : Loc) (Dt : State → Prop) (ls0 : Lsize) (Ctx : FragS isa)
  (frM : TermRun.Frame) (inv0 : FragS isa)

set_option hygiene false in
/-- `wakeD` at the levels `W0W`, `W1W` and `h1`'s invariant `inv1W`. -/
local notation "DH" =>
  X64.WakeOD.wakeD hp i E cT Dt ls0 (X64.WakeOPremW.W0W asm hp i E Dt Ctx ls0 frM) inv0
    (X64.WakeOPremW.W1W asm hp i E Dt Ctx ls0) (X64.WakeH1Inv.inv1W asm hp i E cT Dt Ctx ls0)

/-- **`OpenX.hCl` at `wakeD` with `inv1W`**, from `OPrem` there (`c`'s
label sized by `X64.WakeH1Inv.lsize_of`, the child's stack owned at
`inv1W`'s clone states by `X64.WakeH1Inv.own1_of`). -/
theorem hCl_W (hR1 : ∀ d s, R1 d s → X64WakeO.R1O arch (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) DH d s)
    (hO : X64WakeO.OPrem arch (Ly).Λ B asm E Ab Ac DH) :
    ∀ d s th stack tls r (th0 : TermRun.TTh) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
      (hd : Option (Nat × TermRun.Word)),
      SpawnPrem (QG hp i arch R1 μ M r0 r1) (Ly).Λ asm E 0 d s th stack tls r →
      d.1.threads = #[th] → s.ths = #[th0] → th0.σs = [] → th0.promises = [] →
      I2 (DH).ar (DH).L0 (DH).ls0 (DH).inv0 (DH).inv1 lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack →
      HeldOk2 (Ly).Λ (DH).r0 (DH).r1 th.st d.2.held → Inv1 (Ly).Λ lbl lsize ts th d.1.mem s.mem →
      ∃ (X : State → Prop) (q : TcbGG), ClonePre (Ly).Λ (DH).r0 (r1Of (Ly).lab) X lbl d s ∧
        (∀ st, X st → st.exe = (Ly).exe ∧ st.endPc = X64WakeAssemblyR.endR hp i ∧ st.decls = {}) ∧
        (∀ st, X st → st.st.2 = cloneAt (Ly).exe ∧ st.st.1.regs.get64 .r8 = tcbOf (Ly).lab q) ∧
        Q2 q ∧ th0.stack = [] ∧
        (∀ l, TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) →
          0 < lsize l) :=
  hCl_of hp i hR1 (X64WakeHClW.nodes_of hp i cT Dt ls0 Ctx frM inv0 hO).1
    (X64WakeHClW.nodes_of hp i cT Dt ls0 Ctx frM inv0 hO).2
    (fun _ h => h.1) (X64.WakeWf.noClone_of hO.h0)
    (fun l b n => X64.WakeH1Inv.cloneInv_of asm hp i E cT Dt Ctx ls0 l b n) rfl rfl (hbd_W hp i)
    (fun l b n => X64.WakeH1Inv.own1_of asm hp i E cT Dt Ctx ls0 l b n)
    (fun l b n => X64.WakeH1Inv.lsize_of asm hp i E cT Dt Ctx ls0 l b n)

end Inst

end Spike.Lib.X64WakeHClC

/-- info: 'Spike.Lib.X64WakeHClC.clone_args' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClC.clone_args

/-- info: 'Spike.Lib.X64WakeHClC.hCl_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClC.hCl_of

/-- info: 'Spike.Lib.X64WakeHClC.hCl_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeHClC.hCl_W
