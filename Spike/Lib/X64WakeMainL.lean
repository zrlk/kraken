/-
**main's post-spawn controls have their label words mapped** (x86-64): the x64 twin of
`Spike/Lib/A64WakeMainL.lean`. The node
obligations of main's post-spawn segments (`WaitLoop.LoopW`, `Park.ParkGW`,
`X64WakeMainSegW.ParentW`, the `exit_group` tail's) at
`W := fun _ c => P c` for any control predicate `P` holding of the parent's
control `cP`, the loop's `c0` and every control past the load (`Past`):
each node's control is one of those. At
`P := X64WakeMappedRow.LabMapped lbl (X64Consumer.K0 Λ)` they give the
`LabMapped` conjunct of the x64 `mainWR`.

- `blkW_ctl`, `nodeW_ctl`: a block (node) whose controls satisfy `P`.
- `xProW_ctl`: a prologue whose entry controls satisfy `P`.
- `loopW_ctl`, `parkGW_ctl`, `parentW_ctl`, `exitW0_ctl`, `exitW1_ctl`.
- `labMapped_c0`: `LabMapped` at the loop's control, whose only label access
  is the load of the flag, from the flag's word mapped in `K0`.

**Deviations from the A64 file.** No `tlsW_ctl`: x86-64's limit load is the
prologue's `w2` node (`xProW_ctl`).
-/
import Spike.Lib.X64WakeMainR
import Spike.Lib.X64WakeLabMapped

namespace Spike.Lib.X64WakeMainL

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64WakeMainSegW (ParentW exitN exitNP)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {P : Ctl → Prop}

/-- **A block whose controls satisfy `P`.** -/
theorem blkW_ctl {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c _ _ _ _ _ _ hJ _ _ _ _ _
  exact ⟨h σ c hJ, fun _ h => h⟩

/-- **A node whose controls satisfy `P`.** -/
theorem nodeW_ctl {n : ND} (h : ∀ σ c, n.J σ c → P c) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨-, -, -, -, σ, -, -, hJ⟩
  exact ⟨h σ c hJ, fun _ h => h⟩

/-- **A prologue's controls satisfy `P`** if its entry's do (every node
of the prologue keeps the entry's control). -/
theorem xProW_ctl {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop} (h : ∀ σ c, J σ c → P c) :
    XProW (fun _ c => P c) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J where
  w0 := blkW_ctl h
  w1 := blkW_ctl fun _ c ⟨σ, hJ, _⟩ => h σ c hJ
  w2 := nodeW_ctl fun _ c ⟨σ, hJ, _⟩ => h σ c hJ
  w3 := blkW_ctl fun _ c ⟨σ, _, hJ, _⟩ => h σ c hJ
  w4 := blkW_ctl fun _ c ⟨σ, _, hJ, _⟩ => h σ c hJ

section Loop

open Spike.Lib.X64.WaitLoop

variable {ms : MemSide isa} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A fp ra tp sp : BitVec 64}

/-- **`wc_waitLoop`'s controls satisfy `P`**: each is `c0` or past the
load. -/
theorem loopW_ctl (h0 : P c0) (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    LoopW (fun _ c => P c) ms exe endPc R F c0 x e ty Rd A fp ra tp sp where
  pro := xProW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  entry := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  ld := nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact h0
  n5 := blkW_ctl fun _ c hJ => by
    obtain ⟨-, ⟨-, hp⟩ | ⟨-, rfl⟩⟩ := hJ
    · exact hP c hp
    · exact h0
  n6 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  then1 := blkW_ctl fun _ c hJ => by obtain ⟨-, hp, -⟩ := hJ; exact hP c hp
  else2 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0
  x16 := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact h0

/-- **The exit tail's block's controls satisfy `P`**: past the load. -/
theorem exitW0_ctl (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F (exitN c0 x e ty Rd A fp ra tp sp)
      (xExit (-16) 4 4 5) :=
  blkW_ctl fun _ c hJ => by obtain ⟨hp, -⟩ := hJ; exact hP c hp

/-- **The exit tail's `syscall` control satisfies `P`**: past the load. -/
theorem exitW1_ctl (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F (exitNP (exitN c0 x e ty Rd A fp ra tp sp)) :=
  nodeW_ctl fun _ c hJ => by obtain ⟨-, -, ⟨hp, -⟩, -⟩ := hJ; exact hP c hp

end Loop

section Park

open Spike.Lib.X64.Flow.Park (ParkGW)

set_option hygiene false in
/-- A park node's control is its ghost `c0`. -/
local macro "parkC" : tactic =>
  `(tactic| (obtain rfl : _ = c0 := by first | exact h.1 | exact h.1.1 | exact h.1.1.1 | exact h.1.1.1.1
             exact h0))

/-- **`scc_rt_park`'s controls satisfy `P`**: each is its ghost source
`c0`. -/
theorem parkGW_ctl {c0 : Ctl} {rbp0 ra tp : BitVec 64} (h0 : P c0) :
    ParkGW (fun _ c => P c) exe endPc R F c0 rbp0 ra tp where
  e := blkW_ctl fun _ _ h => by parkC
  fsl := nodeW_ctl fun _ _ h => by parkC
  n1 := blkW_ctl fun _ _ h => by parkC
  xchg1 := nodeW_ctl fun _ _ h => by parkC
  n2 := blkW_ctl fun _ _ h => by parkC
  n3 := blkW_ctl fun _ _ h => by parkC
  wait := blkW_ctl fun _ _ h => by parkC
  sys := nodeW_ctl fun _ _ h => by parkC
  n5 := blkW_ctl fun _ _ h => by parkC
  xchg2 := nodeW_ctl fun _ _ h => by parkC
  n6 := blkW_ctl fun _ _ h => by parkC
  done := blkW_ctl fun _ _ h => by parkC

end Park

/-- **The parent's controls satisfy `P`**: each is `cP`. -/
theorem parentW_ctl {cP : Ctl} {A fp ra tp : BitVec 64} (hP : P cP) :
    ParentW (fun _ c => P c) exe endPc R F cP A fp ra tp where
  wts := nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wje := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wx22 := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wbs := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
  wsp := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP

/-- **`LabMapped` at the loop's control**: its term loads through `a`, one
word `w` with tag `0` representing the flag's address `A` (`hval`), whose
word is mapped in `K0` (`hmA`). -/
theorem labMapped_c0 {Λ : Scc.Sem.Layout} {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {x : String}
    {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A : BitVec 64}
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : Scc.Sem.ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) wr ⟨A, 8⟩ = true) :
    Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) c0 := by
  obtain ⟨sa0, hsa⟩ := htag
  intro sa A' hp hv wr
  cases Spike.Lib.X64WakeLabMapped.ptr_of_load hterm hev hsa sa hp
  rw [hsa] at hval
  obtain ⟨-, y, hy, hAy⟩ := hval
  obtain ⟨-, y', hy', hAy'⟩ := hv
  rw [hy] at hy'
  cases hy'
  have : A' = A := BitVec.eq_of_toNat_eq (by omega)
  subst this
  exact hmA wr

end Spike.Lib.X64WakeMainL

/-- info: 'Spike.Lib.X64WakeMainL.loopW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainL.loopW_ctl
/-- info: 'Spike.Lib.X64WakeMainL.parkGW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainL.parkGW_ctl
/-- info: 'Spike.Lib.X64WakeMainL.parentW_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainL.parentW_ctl
/-- info: 'Spike.Lib.X64WakeMainL.labMapped_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainL.labMapped_c0
