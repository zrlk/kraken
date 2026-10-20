/-
A sequential caller of the lowered FlatHashMap `take` and `lookup`, and the
lifting of sequential procedure specs to fragment specs. ISA: AArch64.

* `mainFrag`: `main` saves the link and the arguments in callee-saved
  registers, calls `flat_take` on key `k`, keeps its result in `x25`/`x26`,
  calls `flat_lookup` on the same key and returns with the lookup's result in
  `x0`/`x1`.
* `main_spec` (**sequential** machine-founded wp, `MachineWP`, total
  correctness): `main`'s `ProcSpec` from `take_spec` and `lookup_spec` at their
  call sites (`call_proc_spec_at`), in every code that places the three
  fragments.
* `FragSpecEnvL.ofProcSpec`: **the lifting** of a placement-independent
  sequential `ProcSpec` to a `FragSpecEnvL` in any environment whose fences
  are permitted (`FenceInv (fun _ => True)`), by `ProcSpec.env` with the
  trivial invariant and `Safely.of_eventually`. Instances for the AArch64
  kit's two environments: `fenceInv_true_of_mono` (every `FenceMono` env, in
  particular `counted (EnvGCAdjA A tid pl)`) and `fenceInv_true_relPure`
  (`counted (relPure A rel)`).

Machine of the lifted statements: the executable machine's per-thread
environment semantics (`Executable.instrStepEnv`), partial correctness.
-/
import Kraken.Promising.Lower.FlatTake
import Kraken.Promising.Lower.FragSpecCalls
import Kraken.Promising.Lower.FragSpecProc
import Kraken.Promising.SLR.EnvG.AdjVCGenA64
import Kraken.Promising.SLR.EnvG.RelPureEnv

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.Promising.Lower.Flat.Whole

open Kraken.Promising.Lower.Flat Kraken.Promising.Lower.Flat.Take

/-! ## The lifting

The generic forms are `MachineWP.FragSpecEnvL.ofProcSpec` and
`MachineWP.FragSpecEnv.ofProcSpec` (`Lower/FragSpecProc.lean`); the fence
facts are `SharedEnv.FenceMono.fenceInv_true` and `SharedEnv.Skips.fenceInv_true`
(`SLR/EnvG/FenceInvTrue.lean`). The names below are kept as aliases. -/

/-- **A sequential, placement-independent `ProcSpec` is a fragment spec in
every environment whose fences are permitted**, at each value `x` of its
logical variable; the environment state is unconstrained and unread. -/
theorem FragSpecEnvL.ofProcSpec {frags : List Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], (∀ p ∈ frags, Program.PlacedIn p) →
      cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnvL env frags l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  MachineWP.FragSpecEnvL.ofProcSpec h env hI x

/-- The one-fragment form. -/
theorem FragSpecEnv.ofProcSpec {frag : Program} {l : Label} {α : Type}
    {Pre : α → Int64 → MachineData → Prop} {Post : α → Int64 → MachineData → MachineData → Prop}
    (h : ∀ [CodeEnv], Program.PlacedIn frag → cenv.ProcSpec ((_root_.Executable.labels cenv).label l) Pre Post)
    (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : α) :
    FragSpecEnv env frag l (fun ra t _ => Pre x ra t) (fun ra t _ t' _ => Post x ra t t') :=
  MachineWP.FragSpecEnv.ofProcSpec h env hI x

/-- Every fence-monotone environment permits every fence. -/
theorem fenceInv_true_of_mono (env : SharedEnv) [env.FenceMono] : env.FenceInv (fun _ => True) :=
  SharedEnv.FenceMono.fenceInv_true env

/-- `counted (relPure A rel)` permits every fence (fences skip). -/
theorem fenceInv_true_relPure (A : Kraken.Promising.Arch) (rel : Kraken.Promising.Loc → Kraken.Promising.SLR.Pred) :
    (SharedEnv.counted (SharedEnv.relPure A rel)).FenceInv (fun _ => True) :=
  SharedEnv.Skips.fenceInv_true _

/-! ## `main` -/

/-- `main`: save the link and the arguments, `take k`, keep its result,
`lookup k`, restore the link, return. One block (no internal label). -/
def mainFrag : Program := parseAArch64("
main:
  mov x19, x30
  mov x20, x0
  mov x21, x1
  mov x22, x2
  mov x23, x3
  mov x24, x4
  bl flat_take
  mov x25, x0
  mov x26, x1
  mov x0, x20
  mov x1, x21
  mov x2, x22
  mov x3, x23
  mov x4, x24
  bl flat_lookup
  mov x30, x19
  ret
")

/-- `main`'s logical variable: the table, key and counters at entry, and
`take`'s model answer (table, counters, result). -/
structure WX where
  T : Tbl
  k : Nat
  gl : Nat
  n : Nat
  T1 : Tbl
  gl1 : Nat
  n1 : Nat
  r1 : Option Nat

/-- `take`'s result as `main` keeps it: the tag in `x25`, the value in `x26`. -/
def TakeRes : Option Nat → MachineData → Prop
  | none, s => s.regs.X25 = 0
  | some y, s => s.regs.X25 = 1 ∧ s.regs.X26.toNat = y

/-- `main`'s precondition: `take`'s, the model's answer of `take` named, and
`lookup`'s table-level hypotheses on the table `take` leaves. -/
def MainPre (x : WX) (ra : Int64) (t : MachineData) : Prop :=
  TakePre (x.T, x.k, x.gl, x.n) ra t ∧ takeN x.T x.gl x.n x.k = some (x.T1, x.gl1, x.n1, x.r1)
    ∧ x.T1.Bounded x.k ∧ ProbeEnds x.T1 x.k

/-- `main`'s postcondition: `take`'s result in `x25`/`x26`, then `lookup`'s
answer on the table `take` left in `x0`/`x1`; that table in memory, every
byte outside the buffers as at entry. -/
def MainPost (x : WX) (_ra : Int64) (t₀ s : MachineData) : Prop :=
  TakeRes x.r1 s ∧ (∃ r, lookupN x.T1 x.k = some r ∧ ResRegs r s) ∧ x.T1.InMem s.dmem
    ∧ Frame x.T t₀.dmem s.dmem

/-- The spec table: one block. -/
def mainTable (x : WX) (ra : Int64) (t₀ : MachineData) : Label → MachineData → Prop
  | "main", s => s = t₀ ∧ MainPre x ra t₀
  | _, _ => False

section Spec
variable [CodeEnv]

/-- **`main`'s specification** (sequential machine, total correctness): in
every code placing `main`, `flat_take` and `flat_lookup`, entered at `main`
with `take`'s precondition and `lookup`'s table-level hypotheses on the
table `take` leaves, every run returns to `ra` with `take`'s result in
`x25`/`x26` and `lookup`'s in `x0`/`x1`. -/
theorem main_spec (hm : Program.PlacedIn mainFrag) (ht : Program.PlacedIn flatTake)
    (hl : Program.PlacedIn flatLookup) :
    cenv.ProcSpec ((_root_.Executable.labels cenv).label "main") MainPre MainPost := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := mainFrag) mainTable
    (hblocks := ?_) (hpre := fun x ra t h => ⟨rfl, h⟩)
  rintro ⟨T, k, gl, n, T1, gl1, n1, r1⟩ ra t₀
  have hc1 := call_proc_spec_at (T, k, gl, n) "flat_take" (take_spec ht)
  have hc2 := call_proc_spec_at (T1, k) "flat_lookup" (lookup_spec hl)
  cfg_cases [mainFrag]
  vcgen [hc1, hc2]
  have hh := ‹mainTable _ _ _ "main" _ ∧ _›
  simp only [mainTable, MainPre, TakePre, LookupPre, Args, Extra] at hh
  obtain ⟨⟨rfl, ⟨⟨⟨h0, h1, h2, h3, h4, hlr⟩, hmem, hb, hpe⟩, h10, h11, hgl, hn, hsep⟩, htk, hb1, hpe1⟩, -⟩ := hh
  obtain ⟨hcb, hsb, hmv, hcv⟩ := takeN_shape htk
  refine ⟨?_, fun s1 hpost => ?_⟩
  · simp only [TakePre, LookupPre, Args, Extra]
    simp [MachineData.setLr, Reg64s.setXReg, h0, h1, h2, h3, h4, h10, h11, hmem, hb, hpe, hgl, hn, hsep]
  · obtain ⟨T', gl', n', r, hr, hres, h10', h11', hin, hfr, hcs⟩ := hpost
    rw [htk] at hr
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    simp only [Callee, MachineData.setLr, Reg64s.setXReg] at hcs
    simp at hcs
    obtain ⟨hsp, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28⟩ := hcs
    vcgen [hc2]
    refine ⟨?_, fun s2 hpost2 => ?_⟩
    · simp only [LookupPre, Args]
      simp [MachineData.setLr, Reg64s.setXReg, c20, c21, c22, c23, c24, hcb, hsb, hmv, hcv, hin, hb1, hpe1]
      all_goals first | exact hin | exact ⟨h0, h1, h2, h3, h4⟩
    · obtain ⟨r2, hr2, hres2, hdm2, hcs2⟩ := hpost2
      vcgen
      simp only [Callee, MachineData.setLr, Reg64s.setXReg] at hcs2
      simp at hcs2
      have hd2 : s2.dmem = s1.dmem := hdm2
      obtain ⟨-, d19, -, -, -, -, -, d25, d26, -, -⟩ := hcs2
      refine Or.inr ⟨?_, ?_, ⟨r2, hr2, ?_⟩, ?_, ?_⟩
      · simp
        rw [d19, c19]
        first
          | exact Int64.toBitVec_inj.mp (by simpa using hlr)
          | (apply Int64.toBitVec_inj.mp; simp [hlr])
          | (cases ra; simp_all [UInt64.toInt64, Int64.ofBitVec])
      · cases r1 <;> simp only [TakeRes] <;> simp [d25, d26] <;> exact hres
      · cases r2 <;> simp [ResRegs] at hres2 ⊢ <;> exact hres2
      · show T1.InMem s2.dmem
        rw [hd2]; exact hin
      · simp only [MachineData.setLr] at hfr
        show Frame T _ s2.dmem
        rw [hd2]; exact hfr

end Spec

end Kraken.Promising.Lower.Flat.Whole
