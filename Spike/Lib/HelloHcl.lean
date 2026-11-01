/-
**The child after main's `clone` is out of the write abort's phase** (AArch64): the `hcl`
premise of `HelloPostAbH.tw_step_hello` / `post_abort_hello`, with main at a system call and the kernel not exited
(the call site, `HelloPostAbW.tw_step`, has both from `Handover.step_up_cases`; without them the relation's
post-exit branch pins no pc, and a `clone` decoded off a `svc` is no call, so the premise is unprovable).

At a `clone` call under the relation before the exit, main is the one thread (`RSAH`'s `PreJAH`), its state in the
fragment at the clone's pc (`HelloHClW.pc_of_cloneH`); the child's state is main's at the next cell
(`Handover.childAfter_st`, `nextPc_of_cellAt` at the clone's `svc`), the pc `.L22_wc_main.sp6 + 4·25 + 4`, which
is off every pc of `scc_rt_abort_write`'s phase (`HelloWf.siAbH_sound`, decided on the listing).

- `siAbH_clone`: the clone's next pc is off `abPcs` (decided).
- `child_pc_of_clone`: the child's pc after the clone.
- `hcl_ofR`: the premise, from the relation (`R1OH … XH`), the fragment's nodes and take site and the levels'
  statements (`h2` at `inv2H`, for `ClonePostH`'s executable facts).
-/
import Spike.Lib.A64HelloHClWR
import Spike.Lib.A64HelloRefAbT
import Spike.Lib.A64HelloChildAt

namespace Spike.Lib.HelloHcl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Entry Range)
open Scc.Sem.A64 (abi pcOf)
open Scc.Sem.Kernel (callOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.WakeA64 (Cfg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HelloPreA (clonePcH cloneAtH H0StmtH H1StmtHF H2StmtH pfxM)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloH2Inv (inv2H cloneInv2_of)
open Spike.Lib.HelloHClW (pc_of_cloneH)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.Flow.Worker.Hello.Child (hello_svcIn)
open Spike.Lib.A64.Flow.Worker.Wake.Child (svcB)

/-- **The clone's next pc is off the write abort's pcs** (`HelloWf.siAbH` at `.L22_wc_main.sp6 + 4·25`). -/
theorem siAbH_clone : Spike.Lib.A64.HelloWf.siAbH ".L22_wc_main.sp6" 25 = true := by
  simp only [Spike.Lib.A64.HelloWf.siAbH, Spike.Lib.LowerA64.labC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- **The child's pc after main's `clone`**: main's next cell (the `svc` is four bytes). -/
theorem child_pc_of_clone {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Scc.Cert.Rt.A64.Lays exe SccCode.helloProg kp) (hend : endPc = Scc.Cert.Rt.A64.endOf exe SccCode.helloProg kp)
    {x : Scc.Sem.Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {stack tls : Nat}
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hpc : t.st.st.2 = cloneAtH pfxM exe) :
    (Spike.Lib.Handover.childAfter abi x tid t stack tls).st.st.2 = cloneAtH pfxM exe + 4 := by
  have hcode := Spike.Lib.A64.Flow.code_of hp hend hello_svcIn (q := cloneAtH pfxM exe) rfl
  obtain ⟨d0, hd0⟩ : ∃ d, svcB[0]? = some d := ⟨_, rfl⟩
  have hcell : Kraken.Promising.Lower.A64.CellAt t.st d0 4 := by
    have := hcode t.st he hn 0 d0 hd0
    rw [Spike.Lib.A64.Flow.ofNat4_zero, ← hpc] at this
    exact this
  have hnext := Scc.Sem.A64.nextPc_of_cellAt hcell
  have hch : (abi.child t.st stack tls).st.2 = cloneAtH pfxM exe + 4 := by
    show Scc.Sem.A64.nextPc t.st = _
    rw [hnext, hpc]; rfl
  unfold Spike.Lib.Handover.childAfter
  split
  · exact hch
  · exact hch

section Rel

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks} {Dd : ODataH}
  {L : RuntimeLayout} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isaLSE2} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isaLSE2}
  {Start : FragS isaLSE2} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
  {Box : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop}
  {a : Int64} {ls0 : Lsize}

/-- **`tw_step_hello`'s `hcl`** (module doc), with the kernel not exited. -/
theorem hcl_ofR (hprog : L.prog = SccCode.helloProg)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hR1 : ∀ d s, R1 d s → R1OH arch L.Λ μ Dd XH d s)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ d s tid th stack tls, R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧ ¬ Spike.Lib.A64.WriteAb.Ab L.lab (Spike.Lib.Handover.childAfter abi d.2 tid th stack tls).st := by
  intro d s tid th stack tls h1R _ hth hsys hcall hex
  obtain ⟨hRS, -⟩ := hR1 _ _ h1R
  rcases hRS with hPre | ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, hk⟩, _⟩
  case inr => rw [hk] at hex; cases hex
  obtain ⟨thm, th0, _, _, _, _, _, _, hd, hthm, -, -, -, -, -, -, -, -, hI, -⟩ := hPre
  have hsz : d.1.threads.size = 1 := by rw [hthm]; rfl
  have hth' : th = thm := by
    rw [hthm] at hth
    have ht : tid = 0 := by
      have := (Array.getElem?_eq_some_iff.mp hth).1
      simp at this; omega
    subst ht; simpa using hth.symm
  subst hth'
  refine ⟨hsz, ?_⟩
  -- main is at the clone's pc; its executable facts from `ClonePostH`
  have hpc := pc_of_cloneH hN hT hCl hI hsys hcall
  rcases hI with ⟨-, -, hi⟩ | ⟨l1, b1, n1, hl1, hb1, -, -, hi⟩ | ⟨l1, b1, n1, l', b', n', -, -, -, -, -, -, hi⟩
  · exact absurd hpc (h0.2.2 _ _ _ hi)
  · exact absurd hpc ((h1 l1 b1 n1 hl1 hb1).2.2 _ _ _ hi)
  rw [hinv2] at hi
  obtain ⟨-, t, l2, ws, ⟨R, F₂, tc, k, sl, me, cA, frp, -, ⟨he, hn, -, hpcS, -⟩, -⟩, -⟩ := cloneInv2_of hi hpc
  have hpS : th.st.st.2 = cloneAtH pfxM L.exe := by rw [hpcS]; rfl
  have hendS : L.endPc = Scc.Cert.Rt.A64.endOf L.exe SccCode.helloProg L.pfx := by rw [← hprog]
  have hcp := child_pc_of_clone (hprog ▸ L.lays) hendS (x := d.2) (tid := tid) (stack := stack) (tls := tls) he hn hpS
  refine Spike.Lib.A64.WriteAb.not_ab_of_pc ?_
  rw [hcp]
  exact Spike.Lib.A64.HelloWf.siAbH_sound hlab siAbH_clone

end Rel

end Spike.Lib.HelloHcl

/-- info: 'Spike.Lib.HelloHcl.child_pc_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHcl.child_pc_of_clone

/-- info: 'Spike.Lib.HelloHcl.hcl_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloHcl.hcl_ofR
