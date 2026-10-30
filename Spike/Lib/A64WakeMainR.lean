/-
**main's post-spawn states write at most once, a release write**
(AArch64): the node obligations of main's post-spawn segments
(`WaitLoop.LoopW`, `Park.ParkGW`, `ParentW`, the `exit_group` tail's) at
`W := fun s _ => RelWS s` (`Spike/Lib/A64RelWS.lean`), from the code alone:
every block is covered (its states run to `.done`), the flag's `ldar` loads,
the park's two `swpal` write once with release kind, the `svc`s fault. With
`*.and` they combine with the `mainW` obligations into the obligations of
`mainW ∧ RelWS`.

- `LoopW.and`, `loopW_relW`; `ParkGW.and`, `parkGW_relW`;
  `ParentW.and`, `parentW_relW`; `exitW0_relW`, `exitW1_relW`.
-/
import Spike.Lib.A64RelWS
import Spike.Lib.A64WakeMainSegW
import Spike.Lib.A64WakeAbOffL

namespace Spike.Lib.A64WakeMainR

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0 wake_exitIn)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64WakeMainSegW (ParentW exitNP)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## `wc_waitLoop` -/

section Loop

open Spike.Lib.A64.WaitLoop

variable {pfx : String} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A x29 ra tp : BitVec 64}

/-- **Two predicates' `LoopW` combine.** -/
theorem LoopW.and {W₁ W₂ : Frag isaLSE2} (h₁ : LoopW W₁ exe endPc R F pfx c0 x e ty Rd A x29 ra tp)
    (h₂ : LoopW W₂ exe endPc R F pfx c0 x e ty Rd A x29 ra tp) :
    LoopW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F pfx c0 x e ty Rd A x29 ra tp where
  top := h₁.top.and h₂.top
  n1 := h₁.n1.and h₂.n1
  n2 := h₁.n2.and h₂.n2
  entry := h₁.entry.and h₂.entry
  ld := h₁.ld.and h₂.ld
  n4 := h₁.n4.and h₂.n4
  n5 := h₁.n5.and h₂.n5
  then1 := h₁.then1.and h₂.then1
  else2 := h₁.else2.and h₂.else2
  sp3 := h₁.sp3.and h₂.sp3

/-- **`wc_waitLoop`'s states are in `RelWS`.** -/
theorem loopW_relW (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hcode : Code pfx c0 x e ty Rd A x29 ra tp exe endPc) :
    LoopW (fun s _ => RelWS s) exe endPc R F pfx c0 x e ty Rd A x29 ra tp where
  top := blkW_relW b0_ok hR hal hlo hhi hcode.top
  n1 := blkW_relW b1_ok hR hal hlo hhi hcode.n1
  n2 := blkW_relW b2_ok hR hal hlo hhi hcode.n2
  entry := blkW_relW b3_ok hR hal hlo hhi hcode.entry
  ld := nodeW_relW hcode.ld fun _ hc => relWS_ldar hc
  n4 := blkW_relW b4_ok hR hal hlo hhi hcode.n4
  n5 := blkW_relW b5_ok hR hal hlo hhi hcode.n5
  then1 := blkW_relW b6_ok hR hal hlo hhi hcode.then1
  else2 := blkW_relW b7_ok hR hal hlo hhi hcode.else2
  sp3 := blkW_relW b8_ok hR hal hlo hhi hcode.sp3

end Loop

/-! ## `scc_rt_park` -/

section Park

open Spike.Lib.A64.Flow.Park

variable {c0 : Ctl} {x29 ra tp : BitVec 64}

/-- **Two predicates' `ParkGW` combine.** -/
theorem ParkGW.and {W₁ W₂ : Frag isaLSE2} (h₁ : ParkGW W₁ exe endPc R F c0 x29 ra tp)
    (h₂ : ParkGW W₂ exe endPc R F c0 x29 ra tp) :
    ParkGW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F c0 x29 ra tp where
  e := h₁.e.and h₂.e
  n1 := h₁.n1.and h₂.n1
  swp1 := h₁.swp1.and h₂.swp1
  n2 := h₁.n2.and h₂.n2
  n3 := h₁.n3.and h₂.n3
  wait := h₁.wait.and h₂.wait
  svc := h₁.svc.and h₂.svc
  n5 := h₁.n5.and h₂.n5
  swp2 := h₁.swp2.and h₂.swp2
  n6 := h₁.n6.and h₂.n6
  done := h₁.done.and h₂.done

/-- **`scc_rt_park`'s states are in `RelWS`**: its two exchanges are
`swpal`, release writes. -/
theorem parkGW_relW (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -64) (hhi : 0 ≤ R.hi)
    (hcode : Code c0 x29 ra tp exe endPc) :
    ParkGW (fun s _ => RelWS s) exe endPc R F c0 x29 ra tp where
  e := blkW_relW b0_ok hR hal hlo hhi hcode.e
  n1 := blkW_relW b1_ok hR hal hlo hhi hcode.n1
  swp1 := nodeW_relW hcode.swp1 fun _ hc => relWS_swp EvTree.storeKind_rmw_acqRel_armv8 hc
  n2 := blkW_relW b2_ok hR hal hlo hhi hcode.n2
  n3 := blkW_relW b3_ok hR hal hlo hhi hcode.n3
  wait := blkW_relW b4_ok hR hal hlo hhi hcode.wait
  svc := nodeW_relW hcode.svc fun _ hc => relWS_svc hc
  n5 := blkW_relW b5_ok hR hal hlo hhi hcode.n5
  swp2 := nodeW_relW hcode.swp2 fun _ hc => relWS_swp EvTree.storeKind_rmw_acqRel_armv8 hc
  n6 := blkW_relW b6_ok hR hal hlo hhi hcode.n6
  done := blkW_relW b7_ok hR hal hlo hhi hcode.done

end Park

/-! ## The parent -/

section Parent

variable {cP : Ctl} {A x29 ra tp : BitVec 64}

/-- **Two predicates' `ParentW` combine.** -/
theorem ParentW.and {W₁ W₂ : Frag isaLSE2} (h₁ : ParentW W₁ exe endPc R F cP A x29 ra tp)
    (h₂ : ParentW W₂ exe endPc R F cP A x29 ra tp) :
    ParentW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F cP A x29 ra tp where
  wcb := h₁.wcb.and h₂.wcb
  wcl := h₁.wcl.and h₂.wcl
  wbs := h₁.wbs.and h₂.wbs
  wsp := h₁.wsp.and h₂.wsp

/-- **The parent's states are in `RelWS`**, in any valid layout of
`wakeProg`. -/
theorem parentW_relW [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
    (hend : endPc = endOf exe wakeProg kp) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80)
    (hhi : 0 ≤ R.hi) : ParentW (fun s _ => RelWS s) exe endPc R F cP A x29 ra tp := by
  have hin := wake_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, hgap⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  exact {
    wcb := blkW_relW cbP_ok hR hal hlo hhi (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := blkW_relW cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := blkW_relW bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := blkW_relW spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

end Parent

/-! ## The `exit_group` tail -/

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64}
  [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **The tail block's states are in `RelWS`.** -/
theorem exitW0_relW (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 16 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 8) := by
  have hin := wake_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact blkW_relW (exitTail_ok (lo := 0) (hi := 16) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

/-- **The tail's `svc` state is in `RelWS`.** -/
theorem exitW1_relW (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F
      (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret)) := by
  have hin := wake_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact nodeW_relW (code_of hp hend hin.2 (by
    show _ = Int64.ofBitVec ra + 4 + 4 + 4; rw [hra]; simp only [ofNat4_succ, ofNat4_zero]))
    fun _ hc => relWS_svc hc

end Exit

/-! ## The limit load (`.tls`) -/

section Tls

variable [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **`wc_waitLoop`'s limit load is in `RelWS`** (a plain `ldr`), at any
node at its pc (`seg_waitTlsW`'s `hpc`). -/
theorem tlsW_relW (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".stack_check") +
      Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n :=
  nodeW_relW (code_of hp hend Spike.Lib.A64.Flow.Worker.Wake.AbOffAt.wait_tlsCode hpc.symm) fun _ hc => relWS_ldr hc

end Tls

/-- info: 'Spike.Lib.A64WakeMainR.tlsW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tlsW_relW
/-- info: 'Spike.Lib.A64WakeMainR.loopW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms loopW_relW
/-- info: 'Spike.Lib.A64WakeMainR.parkGW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parkGW_relW
/-- info: 'Spike.Lib.A64WakeMainR.parentW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms parentW_relW
/-- info: 'Spike.Lib.A64WakeMainR.exitW0_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW0_relW
/-- info: 'Spike.Lib.A64WakeMainR.exitW1_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms exitW1_relW

end Spike.Lib.A64WakeMainR
