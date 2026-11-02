/-
**The child after main's `clone` is out of the write abort's phase** (x86-64; the twin of
`Spike/Lib/HelloHcl.lean`): the `hcl` premise of `X64HelloPostAbH.tw_step_hello` / `post_abort_hello`, with main
at a system call and the kernel not exited (the call site has both from `Handover.step_up_cases`; without them the
relation's post-exit branch pins no pc).

At a `clone` call under the relation before the exit, main is the one thread (`RSAH`'s `PreJAH`), its state in the
fragment at the clone's pc (`X64HelloHClW.pc_of_cloneH`); the child's state is main's at the next cell
(`Handover.childAfter`, `nextPc_of_cellAt` at the clone's `syscall`), the pc `.Lwc_main.x25 + 94 + 2`, which is
off every pc of `scc_rt_abort_write`'s phase (`HelloWf.siAbH_sound`, decided on the listing).

- `siAbH_clone`: the clone's next pc is off `abPcs` (decided).
- `child_pc_of_clone`: the child's pc after the clone.
- `hcl_ofR`: the premise, from the relation (`R1OH … XH`), the fragment's nodes and take site and the levels'
  statements (`h2` at `inv2H`, for `ClonePostH`'s executable facts).

## Unlike AArch64

- The clone's `syscall` is 2 bytes at `.Lwc_main.x25 + 94` (`X64HelloClonePreH.cloneAtH`; AArch64 the 4-byte
  `svc` at `.L22_wc_main.sp6 + 4·25` past the prefix `pfxM`), so the child's pc is `cloneAtH exe + 2`, and
  `siAbH` takes the instruction's size.
- The layout's program is the cell list `SccCode.helloCells` and the label premise `hlab` reads `codeLabel`
  (AArch64 `helloProg`, `codeOf`).
-/
import Spike.Lib.X64HelloHClWR
import Spike.Lib.X64HelloRefAbT
import Spike.Lib.X64HelloChildAt
import Spike.Lib.X64HelloWcInv3F

namespace Spike.Lib.X64HelloHcl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (Marks Entry Range)
open Scc.Sem.X64 (abi pcOf codeLabel)
open Scc.Sem.Kernel (callOf)
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)
open Spike.Lib (Arena FragS MemSide)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64HelloPreA (clonePcH cloneAtH H0StmtH H1StmtHF)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64HelloH2Inv (inv2H cloneInv2_of)
open Spike.Lib.X64HelloHClW (pc_of_cloneH)
open Spike.Lib.X64.Flow.Worker.Hello.Child (hello_svcIn)
open Spike.Lib.X64.HelloPh.WcSp6 (x25L)

/-- **The clone's next pc is off the write abort's pcs** (`HelloWf.siAbH` at `.Lwc_main.x25 + 94`, 2 bytes). -/
theorem siAbH_clone : Spike.Lib.X64.HelloWf.siAbH x25L 94 2 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-- **The child's pc after main's `clone`**: main's next cell (the `syscall` is two bytes). -/
theorem child_pc_of_clone {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {x : Scc.Sem.Kernel.KState} {tid : Nat} {t : Thread isa} {stack tls : Nat}
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hpc : t.st.st.2 = cloneAtH exe) :
    (Spike.Lib.Handover.childAfter abi x tid t stack tls).st.st.2 = cloneAtH exe + 2 := by
  have hcell : CellAt t.st (op64 .syscall) 2 :=
    (codeAt_blockAt_lays hp he (hn.trans hend) hello_svcIn).cell0 rfl rfl hpc
  have hnext := Scc.Sem.X64.nextPc_of_cellAt hcell
  have hch : (abi.child t.st stack tls).st.2 = cloneAtH exe + 2 := by
    rw [Scc.Sem.X64.abi_child_of_cellAt hcell]
    show t.st.st.2 + Int64.ofNat 2 = _
    rw [hpc]; rfl
  unfold Spike.Lib.Handover.childAfter
  split
  · exact hch
  · exact hch

section Rel

variable {ι : Type} {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks} {Dd : ODataH}
  {L : RuntimeLayout} {ab : Option (State → Prop)} {Cl : State → Prop}
  {W0 : FragS isa} {K : State → State → Prop} {ms0 : List TermRun.Frame → MemSide isa}
  {Start : FragS isa} {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {Rd : WeakMem.AllocLabel → Nat → Nat → State → Ctl → Prop} {fr : List TermRun.Frame}
  {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
  {a : Int64} {ls0 : Lsize}

/-- **`tw_step_hello`'s `hcl`** (module doc), with the kernel not exited. -/
theorem hcl_ofR (hprog : L.prog = SccCode.helloCells)
    (hlab : ∀ l x, codeLabel Spike.Lib.X64.HelloPh.lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x)
    (hR1 : ∀ d s, R1 d s → R1OH arch L.Λ μ Dd XH d s)
    (hN : NodesA L.Λ helloSrc μ Dd.rd Dd.G Dd.own Dd.ar (IH Dd) ab Cl) (hT : TakeSiteS helloSrc μ (IH Dd))
    (hCl : ∀ s, Cl s → pcOf s = clonePcH L)
    (h0 : H0StmtH W0 K Dd.L0 ms0 L Start Dd.inv0) (h1 : H1StmtHF W1 K Dd.ar Dd.L0 ms1 L Rd Dd.inv1 fr)
    (hinv2 : Dd.inv2 = inv2H W2 K ms2 L a L.endPc Dd.L0 ls0) :
    ∀ d s tid th stack tls, R1 d s → d.1.threads.size = d.2.slots.size → d.1.threads[tid]? = some th →
      abi.atSys th.st = true → callOf abi th = some (.clone stack tls) → d.2.exited = none →
      d.1.threads.size = 1 ∧
        ¬ Spike.Lib.X64.WriteAb.Ab L.lab (Spike.Lib.Handover.childAfter abi d.2 tid th stack tls).st := by
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
  have hpS : th.st.st.2 = cloneAtH L.exe := by rw [hpcS]; rfl
  have hendS : L.endPc = endOf L.exe SccCode.helloCells L.pfx := by
    show endOf L.exe L.prog L.pfx = _; rw [hprog]
  have hcp := child_pc_of_clone (hprog ▸ L.lays) hendS (x := d.2) (tid := tid) (stack := stack) (tls := tls) he hn
    hpS
  refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
  rw [hcp]
  exact Spike.Lib.X64.HelloWf.siAbH_sound hlab siAbH_clone

end Rel

end Spike.Lib.X64HelloHcl

/-- info: 'Spike.Lib.X64HelloHcl.siAbH_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHcl.siAbH_clone

/-- info: 'Spike.Lib.X64HelloHcl.child_pc_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHcl.child_pc_of_clone

/-- info: 'Spike.Lib.X64HelloHcl.hcl_ofR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHcl.hcl_ofR
