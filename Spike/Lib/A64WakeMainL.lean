/-
**main's post-spawn controls have their label words mapped** (AArch64): the node obligations of main's post-spawn segments
(`WaitLoop.LoopW`, `Park.ParkGW`, `ParentW`, the `exit_group` tail's) at
`W := fun _ c => P c` for any control predicate `P` holding of the parent's
control `cP`, the loop's `c0` and every control past the load (`Past`):
each node's control is one of those. At `P := LabMapped lbl (K0 Λ)` they
give the third conjunct of `WakeInst.mainWR`.

- `blkW_ctl`, `nodeW_ctl`: a block (node) whose controls satisfy `P`.
- `loopW_ctl`, `parkGW_ctl`, `parentW_ctl`, `exitW0_ctl`, `exitW1_ctl`,
  `tlsW_ctl`.
- `labMapped_c0`: `LabMapped` at the loop's control, whose only label access
  is the load of the flag, from the flag's word mapped in `K0`.
- (`tlsW_mainR`, all four conjuncts at the limit load, is in
  `Spike/Lib/A64WakeMainS.lean`.)
-/
import Spike.Lib.A64WakeMainR
import Spike.Lib.WakeLabMapped

namespace Spike.Lib.A64WakeMainL

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow
open Spike.Lib.A64WakeMainSegW (ParentW exitNP)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {P : Ctl → Prop}

/-- **A block whose controls satisfy `P`.** -/
theorem blkW_ctl {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
  exact ⟨h σ c hJ, fun _ h => h⟩

/-- **A node whose controls satisfy `P`.** -/
theorem nodeW_ctl {n : ND} (h : ∀ σ c, n.J σ c → P c) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨h σ c hJ, fun _ h => h⟩

section Loop

open Spike.Lib.A64.WaitLoop

variable {pfx : String} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A x29 ra tp : BitVec 64}

/-- **`wc_waitLoop`'s controls satisfy `P`**: each is `c0` or past the
load. -/
theorem loopW_ctl (h0 : P c0) (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    LoopW (fun _ c => P c) exe endPc R F pfx c0 x e ty Rd A x29 ra tp where
  top := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  n1 := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact h0
  n2 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  entry := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  ld := nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact h0
  n4 := blkW_ctl fun _ c hJ => by
    obtain ⟨-, -, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
    · exact hP c hp
    · exact h0
  n5 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  then1 := blkW_ctl fun _ c hJ => by obtain ⟨-, -, hp, -⟩ := hJ; exact hP c hp
  else2 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  sp3 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0

/-- **The limit load's controls satisfy `P`** (the `.tls` node's control is
`c0`). -/
theorem tlsW_ctl (h0 : P c0) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label pfx c0 x e ty Rd A x29 ra tp .tls) :=
  nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact h0

/-- **The exit tail's block's controls satisfy `P`**: past the load. -/
theorem exitW0_ctl (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F
      (E c0 x e ty Rd A x29 ra tp .ret) (exitTail 8) :=
  blkW_ctl fun _ c hJ => by obtain ⟨hp, -⟩ := hJ; exact hP c hp

/-- **The exit tail's `svc` control satisfies `P`**: past the load. -/
theorem exitW1_ctl (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F (exitNP (E c0 x e ty Rd A x29 ra tp .ret)) :=
  nodeW_ctl fun _ c hJ => by obtain ⟨-, -, ⟨hp, -⟩, -⟩ := hJ; exact hP c hp

end Loop

section Park

open Spike.Lib.A64.Flow.Park

/-- **`scc_rt_park`'s controls satisfy `P`**: each is its ghost source
`c0`. -/
theorem parkGW_ctl {c0 : Ctl} {x29 ra tp : BitVec 64} (h0 : P c0) :
    ParkGW (fun _ c => P c) exe endPc R F c0 x29 ra tp where
  e := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  n1 := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  swp1 := nodeW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  n2 := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  n3 := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  wait := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  svc := nodeW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  n5 := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  swp2 := nodeW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  n6 := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0
  done := blkW_ctl fun _ _ h => by
    obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
    exact h0

end Park

/-- **The parent's controls satisfy `P`**: each is `cP`. -/
theorem parentW_ctl {cP : Ctl} {A x29 ra tp : BitVec 64} (hP : P cP) :
    ParentW (fun _ c => P c) exe endPc R F cP A x29 ra tp where
  wcb := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wcl := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wbs := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
  wsp := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP

/-- **`LabMapped` at the loop's control**: its term loads through `a`, one
word `w` with tag `0` representing the flag's address `A` (`hval`), whose
word is mapped in `K0` (`hmA`). -/
theorem labMapped_c0 {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {x : String}
    {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A : BitVec 64}
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : Scc.Sem.ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) wr ⟨A, 8⟩ = true) :
    Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c0 := by
  obtain ⟨sa0, hsa⟩ := htag
  intro sa A' hp hv wr
  cases Spike.Lib.WakeLabMapped.ptr_of_load hterm hev hsa sa hp
  rw [hsa] at hval
  obtain ⟨-, y, hy, hAy⟩ := hval
  obtain ⟨-, y', hy', hAy'⟩ := hv
  rw [hy] at hy'
  cases hy'
  have : A' = A := BitVec.eq_of_toNat_eq (by omega)
  subst this
  exact hmA wr

/-- info: 'Spike.Lib.A64WakeMainL.loopW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopW_ctl
/-- info: 'Spike.Lib.A64WakeMainL.parkGW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parkGW_ctl
/-- info: 'Spike.Lib.A64WakeMainL.parentW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parentW_ctl
/-- info: 'Spike.Lib.A64WakeMainL.labMapped_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms labMapped_c0

end Spike.Lib.A64WakeMainL
