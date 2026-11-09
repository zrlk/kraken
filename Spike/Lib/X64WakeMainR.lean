/-
**main's post-spawn states write at most once, a release write**
(x86-64): the x64 twin of `Spike/Lib/A64WakeMainR.lean`. The
node obligations of main's post-spawn segments (`WaitLoop.LoopW`,
`Park.ParkGW`, `X64WakeMainSegW.ParentW`, the `exit_group` tail's) at
`W := fun s _ => RelWS s` (`Spike/Lib/X64RelWS.lean`), from the code alone:
every block is covered (its states run to `.done`), the loads (`movq`, the
thread-pointer `movq %fs:…`) only load, the `testq` has no event, the
park's two `xchgq` are locked RMWs (release writes under `Arch.tso`), the
`syscall`s fault. With `*.and` they combine with the `mainW` obligations
into the obligations of `mainW ∧ RelWS`.

- `access_noW`, `access_relW1`; `relWS_load`, `relWS_movfs`, `relWS_xchg`,
  `relWS_test`: per instruction (the analogs of A64's `relWS_ldr`,
  `relWS_ldar`, `relWS_swp` that `X64RelWS` leaves to this file).
- `XProW.and`, `xProW_relW`: a stack-checked prologue (from `prologueIn`).
- `LoopW.and`, `loopW_relW`; `ParkGW.and`, `parkGW_relW`;
  `ParentW.and`, `parentW_relW`; `exitW0_relW`, `exitW1_relW`.

**Deviations from the A64 file.** The code comes from the listing checks
(`waitIn`, `parentIn`, `exitIn`, `prologueIn`) at any `cells`, not from a
`Code` structure (x86-64's loop has none; the park's `Park.Code` is used);
no alignment premise (`blkW_relW` needs none on x86-64). There is no
`tlsW_relW`: x86-64's limit load is the prologue's `w2` node, covered by
`xProW_relW`.
-/
import Spike.Lib.X64RelWS
import Spike.Lib.X64WakeMainSegW

namespace Spike.Lib.X64WakeMainR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAt blockAtB codeAt_blockAt_lays code_field label_labelGapB)
open Spike.Lib.X64.WakePh.MainPost (mainX2)
open Spike.Lib.X64WakeMainSegW (ParentW exitN exitNP)

/-! ## Per instruction -/

/-- An access whose every event writes nothing writes nothing. -/
theorem access_noW {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, EvTree.NoW (k l)) : EvTree.NoW (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · exact .fault _

/-- An access whose every event writes once, a release write, does so. -/
theorem access_relW1 {σ : Type} {A : Arch} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, EvTree.RelW1 A (k l)) : EvTree.RelW1 A (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · exact .noW (.fault _)

/-- **`movq m, r`**: a load, or no event. -/
theorem relWS_load {s : State} {sz : Nat} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt s (op64 (.mov (.reg r) (.mem m))) sz) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s sz m) 8 with
  | none => exact relWS_of (exec_load hc rfl hm) (.noW (access_noW fun _ => .load fun _ => .done _))
  | some j => exact relWS_of (exec_load_mapped hc rfl hm) (.noW (.done _))

/-- **`movq %fs:m, r`**: a load, or no event. -/
theorem relWS_movfs {s : State} {sz : Nat} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt s (op64 (.movfs (.reg r) (.mem m))) sz) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (fsAddr s sz m) 8 with
  | none => exact relWS_of (exec_movfs_load hc rfl hm) (.noW (access_noW fun _ => .load fun _ => .done _))
  | some j => exact relWS_of (exec_movfs_load_mapped hc rfl hm) (.noW (.done _))

/-- **`xchgq r, m`**: one locked RMW, a release write under `tso`, or no
event. The release kind is the model's own: `exec_xchg` gives an RMW of kind
`.acqRel`, and `Arch.storeKind Arch.tso (Arch.rmwKind Arch.tso .acqRel).storeKind`
reduces to `.rel` by the definitions of `Arch.rmwKind`, `RmwKind.storeKind`
and `Arch.storeKind` (`Kraken/Promising/Basic.lean`, `Kraken/MemKinds.lean`; `decide`), no new
assumption. -/
theorem relWS_xchg {s : State} {sz : Nat} {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt s (op64 (.xchg r (.mem m))) sz) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s sz m) 8 with
  | none => exact relWS_of (exec_xchg hc rfl hm) (access_relW1 fun _ => .rmw (by decide) fun _ => .done _)
  | some j =>
    obtain ⟨s', h'⟩ := exec_xchg_mapped hc rfl hm
    exact relWS_done ⟨_, h'⟩

/-- **`testq b, a`**: no event (a choice of `AF`). -/
theorem relWS_test {s : State} {sz : Nat} {a b : Reg .W64} (hc : CellAt s (op64 (.test (.reg a) (.reg b))) sz) :
    RelWS s :=
  relWS_of (exec_test_rr hc) (.noW (.choose fun _ => .done _))

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-! ## The prologue -/

section Pro

variable {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
  {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}

/-- **Two predicates' `XProW` combine.** -/
theorem XProW.and {W₁ W₂ : Frag isa} {K : State → State → Prop}
    (h₁ : XProW W₁ K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (h₂ : XProW W₂ K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J) :
    XProW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨h₁.w0.and h₂.w0, h₁.w1.and h₂.w1, h₁.w2.and h₂.w2, h₁.w3.and h₂.w3, h₁.w4.and h₂.w4⟩

/-- **A stack-checked prologue's states are in `RelWS`** (from
`prologueIn`; the limit's load `w2` a `movq %fs:…`). -/
theorem xProW_relW [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn sc entry : Label}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hZ : 0 ≤ Z.toInt)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true) :
    XProW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim
      L zl zf z1 z2 zs ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  exact {
    w0 := blkW_relW (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hR hlo hhi
      (code_field hp hend b0 (ofNat_zero' _))
    w1 := blkW_relW (xLea_ok (lo := -8 - Z.toInt) (hi := 0) Z zl) hR hlo hhi
      (code_field hp hend b1 (by show _ = _ + 1 + 3; rw [h4, ofNat_zero']))
    w2 := nodeW_relW (code_field hp hend b2 (by show _ = _ + 1 + 3 + _; rw [h4])) fun _ hc => relWS_movfs hc
    w3 := blkW_relW (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ L z1 z2) hR hlo hhi
      (code_field hp hend b3 (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add']))
    w4 := blkW_relW (xFr_ok (lo := -8 - Z.toInt) (hi := 0) Z zs ps hps) hR hlo hhi
      (code_field hp hend b4 (by
        show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])) }

end Pro

/-! ## `wc_waitLoop` -/

section Loop

open Spike.Lib.X64.WaitLoop

variable {ms : MemSide isa} {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop}
  {A fp ra tp sp : BitVec 64}

/-- **Two predicates' `LoopW` combine.** -/
theorem LoopW.and {W₁ W₂ : Frag isa} (h₁ : LoopW W₁ ms exe endPc R F c0 x e ty Rd A fp ra tp sp)
    (h₂ : LoopW W₂ ms exe endPc R F c0 x e ty Rd A fp ra tp sp) :
    LoopW (fun s c => W₁ s c ∧ W₂ s c) ms exe endPc R F c0 x e ty Rd A fp ra tp sp where
  pro := XProW.and h₁.pro h₂.pro
  entry := h₁.entry.and h₂.entry
  ld := h₁.ld.and h₂.ld
  n5 := h₁.n5.and h₂.n5
  n6 := h₁.n6.and h₂.n6
  then1 := h₁.then1.and h₂.then1
  else2 := h₁.else2.and h₂.else2
  x16 := h₁.x16.and h₂.x16

/-- **`wc_waitLoop`'s states are in `RelWS`** (at `seg_waitLoopW`'s region
bounds; the acquire load a plain `movq` under `tso`). -/
theorem loopW_relW [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : waitIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 8 ≤ R.hi) :
    LoopW (fun s _ => RelWS s) ms exe endPc R F c0 x e ty Rd A fp ra tp sp := by
  have hin' := hin
  simp only [waitIn, Bool.and_eq_true, and_assoc] at hin'
  obtain ⟨hpro, h4, hld, h5, h6, h7, h8, h9, -⟩ := hin'
  exact {
    pro := xProW_relW hp hend hpro hR (by have : (16 : Int64).toInt = 16 := by decide
                                          omega) (by omega) (by decide) (by decide)
    entry := blkW_relW b4_ok hR hlo hhi (code_field hp hend h4 (ofNat_zero' _))
    ld := nodeW_relW (code_field hp hend hld rfl) fun _ hc => relWS_load hc
    n5 := blkW_relW b5_ok hR hlo hhi (code_field hp hend h5 rfl)
    n6 := blkW_relW b6_ok hR hlo hhi (code_field hp hend h6 rfl)
    then1 := blkW_relW b7_ok hR hlo hhi
      (Spike.Lib.X64.code_field_blockAcrossB hp hend h7 (List.take_append_drop _ _) (ofNat_zero' _))
    else2 := blkW_relW b8_ok hR hlo hhi (code_field hp hend h8 (ofNat_zero' _))
    x16 := blkW_relW b9_ok hR hlo hhi (code_field hp hend h9 (ofNat_zero' _)) }

end Loop

/-! ## `scc_rt_park` -/

section Park

open Spike.Lib.X64.Flow.Park (ParkGW)

variable {c0 : Ctl} {rbp0 ra tp : BitVec 64}

/-- **Two predicates' `ParkGW` combine.** -/
theorem ParkGW.and {W₁ W₂ : Frag isa} (h₁ : ParkGW W₁ exe endPc R F c0 rbp0 ra tp)
    (h₂ : ParkGW W₂ exe endPc R F c0 rbp0 ra tp) :
    ParkGW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F c0 rbp0 ra tp where
  e := h₁.e.and h₂.e
  fsl := h₁.fsl.and h₂.fsl
  n1 := h₁.n1.and h₂.n1
  xchg1 := h₁.xchg1.and h₂.xchg1
  n2 := h₁.n2.and h₂.n2
  n3 := h₁.n3.and h₂.n3
  wait := h₁.wait.and h₂.wait
  sys := h₁.sys.and h₂.sys
  n5 := h₁.n5.and h₂.n5
  xchg2 := h₁.xchg2.and h₂.xchg2
  n6 := h₁.n6.and h₂.n6
  done := h₁.done.and h₂.done

/-- **`scc_rt_park`'s states are in `RelWS`**: its two exchanges are
`xchgq`, locked RMWs (release writes under `tso`). -/
theorem parkGW_relW (hR : R.OK) (hlo : R.lo ≤ -56) (hhi : 8 ≤ R.hi)
    (hcode : Spike.Lib.X64.Flow.Park.Code c0 rbp0 ra tp exe endPc) :
    ParkGW (fun s _ => RelWS s) exe endPc R F c0 rbp0 ra tp where
  e := blkW_relW Spike.Lib.X64.Flow.Park.b0_ok hR hlo hhi hcode.e
  fsl := nodeW_relW hcode.fsl fun _ hc => relWS_movfs hc
  n1 := blkW_relW Spike.Lib.X64.Flow.Park.b1_ok hR hlo hhi hcode.n1
  xchg1 := nodeW_relW hcode.xchg1 fun _ hc => relWS_xchg hc
  n2 := blkW_relW Spike.Lib.X64.Flow.Park.b2_ok hR hlo hhi hcode.n2
  n3 := blkW_relW Spike.Lib.X64.Flow.Park.b3_ok hR hlo hhi hcode.n3
  wait := blkW_relW Spike.Lib.X64.Flow.Park.b4_ok hR hlo hhi hcode.wait
  sys := nodeW_relW hcode.sys fun _ hc => relWS_syscall hc
  n5 := blkW_relW Spike.Lib.X64.Flow.Park.b5_ok hR hlo hhi hcode.n5
  xchg2 := nodeW_relW hcode.xchg2 fun _ hc => relWS_xchg hc
  n6 := blkW_relW Spike.Lib.X64.Flow.Park.b6_ok hR hlo hhi hcode.n6
  done := blkW_relW Spike.Lib.X64.Flow.Park.b7_ok hR hlo hhi hcode.done

end Park

/-! ## The parent -/

section Parent

open Spike.Lib.X64.WakePh.WcClone (x21L)
open Spike.Lib.X64.WakePh.Parent

variable {cP : Ctl} {A fp ra tp : BitVec 64}

/-- **Two predicates' `ParentW` combine.** -/
theorem ParentW.and {W₁ W₂ : Frag isa} (h₁ : ParentW W₁ exe endPc R F cP A fp ra tp)
    (h₂ : ParentW W₂ exe endPc R F cP A fp ra tp) :
    ParentW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F cP A fp ra tp where
  wts := h₁.wts.and h₂.wts
  wje := h₁.wje.and h₂.wje
  wx22 := h₁.wx22.and h₂.wx22
  wbs := h₁.wbs.and h₂.wbs
  wsp := h₁.wsp.and h₂.wsp

/-- **The parent's states are in `RelWS`**, in any valid layout of cells
with `parentIn` (the test row a `testq`). -/
theorem parentW_relW [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : parentIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -64) (hhi : 16 ≤ R.hi) :
    ParentW (fun s _ => RelWS s) exe endPc R F cP A fp ra tp := by
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, -⟩, b22⟩, bbs⟩, bsp⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((_root_.Executable.labels exe).label l) b :=
    fun h s he hn => by simpa using code h s he hn
  exact {
    wts := nodeW_relW (fun s he hn => code bts s he hn) fun _ hc => relWS_test hc
    wje := blkW_relW jeB_ok hR hlo hhi (fun s he hn => code bje s he hn)
    wx22 := blkW_relW x22B_ok hR hlo hhi (fun s he hn => code0 b22 s he hn)
    wbs := blkW_relW bsB_ok hR hlo hhi (fun s he hn => code bbs s he hn)
    wsp := blkW_relW spB_ok hR hlo hhi (fun s he hn => code0 bsp s he hn) }

end Parent

/-! ## The `exit_group` tail -/

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A fp ra tp sp : BitVec 64}
  [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **The tail block's states are in `RelWS`** (`%rbp` at offset `40`, the
spill cell `24`). -/
theorem exitW0_relW (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : exitIn cells mainX2 (-16) 4 4 5 = true) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (exitN c0 x e ty Rd A fp ra tp sp)
      (xExit (-16) 4 4 5) := by
  rw [exitIn, Bool.and_eq_true] at hin
  exact blkW_relW (xExit_ok (lo := 0) (hi := 32) (-16) 4 4 5 (by decide)) hR hlo hhi
    (code_field hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat_zero']))

/-- **The tail's `syscall` state is in `RelWS`.** -/
theorem exitW1_relW (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : exitIn cells mainX2 (-16) 4 4 5 = true)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (exitNP (exitN c0 x e ty Rd A fp ra tp sp)) := by
  rw [exitIn, Bool.and_eq_true] at hin
  exact nodeW_relW (code_field hp hend hin.2 (by
    show _ = Int64.ofBitVec ra + _ + _ + _; rw [ofNat_add', ofNat_add', hra]))
    fun _ hc => relWS_syscall hc

end Exit

end Spike.Lib.X64WakeMainR

/-- info: 'Spike.Lib.X64WakeMainR.loopW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainR.loopW_relW
/-- info: 'Spike.Lib.X64WakeMainR.parkGW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainR.parkGW_relW
/-- info: 'Spike.Lib.X64WakeMainR.parentW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainR.parentW_relW
/-- info: 'Spike.Lib.X64WakeMainR.exitW0_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainR.exitW0_relW
/-- info: 'Spike.Lib.X64WakeMainR.exitW1_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainR.exitW1_relW
