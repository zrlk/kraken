/-
**No write to the worker's TCB self word at every node's states of
wake.w's worker, x86-64** (in the manner of `Spike/Lib/A64RelW1Nodes.lean`
and `Spike/Lib/A64WakeRelZ.lean`, for the x64 own-word discipline): the
fact `OwnW W s` (off a system call, every write of the instruction's event
tree is to a location other than `⟨W, 8⟩`, the word `wakeOwnX` has the
worker own) at every node's states of the thread worker's run
(`thrZA_own`) and of the child's stub (`cZA_own`). It is the
`ownInstr` obligation (`X64Consumer.Nodes.ownInstr`, `OwnTree`'s first
case) at the worker's states.

The covered blocks run to `.done` (their frame cells are the thread's
private memory, so no frame slot needs a premise), the loads, the `testq`,
the `xorl` and the `syscall`s write nothing; the three shared writes are
premises: the store of `c` at `A` (`hA : A ≠ W`), the exchange on the
permit at `B + 16` (`hB`), the tail's store at `tp + 24` (`htp`).

- `noW_writeTree`; `ownW_done`, `ownW_noW`, `ownW_movfs`, `ownW_test`,
  `ownW_fi`, `ownW_syscall`, `ownW_st`, `ownW_xchg`: per instruction.
- `nodeW_cell`, `xProW_own`: a single instruction's node (`NodeW`), a
  stack-checked prologue (`XProW`, from `prologueIn`).
- `head_own`, `wk_own`, `unpk_own`, `tail_own`, `thrZA_own`, `cZA_own`.

**Unlike AArch64** (forced by the x64 shape): there is no AArch64
counterpart of `OwnW` (the AArch64 worker owns no word the runtime
writes); the shape follows `RelZ`: `NodeZA` over byte-sized cells, the
prologues `XProW`s, the stub four nodes; the worker's TCB self word is read
by the tail's `movq %fs:0, %rax`, which writes nothing.
-/
import Spike.Lib.X64WakeRelZ

namespace Spike.Lib.X64.Flow.Worker.Wake.OwnW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (WriteTree)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays code_field label_labelGapB)
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZA wkCode thrCode thECode unpkCode wake_thrPro wake_wcPro)
open Spike.Lib.X64.WakePh (wake_childIn)
open Spike.Lib.X64.WakePh.Child (cN childN childIn CN jeB_ok chB_ok)
open Spike.Lib.X64.Flow.Worker.Wake.Child (cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.RelZW (silent_noW blkZA_done nodeZA_cell)
open Spike.Lib.X64WakeMainR (access_noW)

/-- **Off a system call, the instruction writes nothing at `⟨W, 8⟩`.** -/
def OwnW (W : BitVec 64) : Frag isa := fun s _ =>
  Scc.Sem.X64.abi.atSys s = false → ∀ tree, isa.exec s = some tree → WriteTree (fun l _ => l ≠ ⟨W, 8⟩) tree

/-! ## Per instruction -/

/-- A tree that writes nothing writes as any `G` says. -/
theorem noW_writeTree {σ : Type} {G : Loc → Val → Prop} {t : EvTree σ} (h : EvTree.NoW t) : WriteTree G t := by
  induction h with
  | done _ => trivial
  | fault _ => trivial
  | choose _ ih => exact ih
  | load _ ih => exact ih
  | fence _ ih => exact ih

variable {W : BitVec 64} {s : State} {c : Ctl}

/-- An instruction whose tree writes nothing. -/
theorem ownW_noW {t : EvTree State} (h : isa.exec s = some t) (ht : EvTree.NoW t) : OwnW W s c := by
  intro _ tree he; rw [h] at he; cases he; exact noW_writeTree ht

/-- An instruction that runs to `.done`. -/
theorem ownW_done {s' : State} (h : isa.exec s = some (.done s')) : OwnW W s c := ownW_noW h (.done _)

/-- **`movq %fs:m, r`**: a load, or no event. -/
theorem ownW_movfs {sz : Nat} {r : Reg .W64} {m : AddrExpr} (hc : CellAt s (op64 (.movfs (.reg r) (.mem m))) sz) :
    OwnW W s c := by
  cases hm : Mem.loadInt s.st.1.dmem (fsAddr s sz m) 8 with
  | none => exact ownW_noW (exec_movfs_load hc rfl hm) (access_noW fun _ => .load fun _ => .done _)
  | some j => exact ownW_done (exec_movfs_load_mapped hc rfl hm)

/-- **`testq`**: no event. -/
theorem ownW_test {sz : Nat} {a b : Reg .W64} (hc : CellAt s (op64 (.test (.reg a) (.reg b))) sz) : OwnW W s c :=
  ownW_noW (exec_test_rr hc) (.choose fun _ => .done _)

/-- **A flag-setting register instruction**: silent. -/
theorem ownW_fi {fi : FI} {z : Nat} (hc : CellAt s fi.toDir z) : OwnW W s c := by
  obtain ⟨t, ht, hs⟩ := exec_fi hc
  exact ownW_noW ht (silent_noW hs)

/-- **`syscall`**: a fault. -/
theorem ownW_syscall {sz : Nat} (hc : CellAt s (op64 .syscall) sz) : OwnW W s c :=
  ownW_noW (exec_syscall hc) (.fault _)

/-- **`movq %r, k(%b)`** at an address other than `W`: a store there, or no
event. -/
theorem ownW_st {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (stDir b k r) z) (hd : s.decls = {})
    (ha : eaddr s z (mB b k) ≠ W) : OwnW W s c := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    intro _ tree he
    rw [exec_store_agrees hc rfl hm (agrees_of_decls hd _ _)] at he
    cases he
    exact ⟨fun h => ha (congrArg Loc.addr h), fun _ => trivial⟩
  | some j => exact ownW_done (exec_store_mapped hc rfl hm)

/-- **`xchgq %r, k(%b)`** at an address other than `W`: an RMW there, or no
event. -/
theorem ownW_xchg {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (xchgDir b k r) z) (hd : s.decls = {})
    (ha : eaddr s z (mB b k) ≠ W) : OwnW W s c := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    intro _ tree he
    rw [exec_xchgG_agrees (w := .W64) hc rfl hm (agrees_of_decls hd _ _)] at he
    cases he
    exact ⟨fun _ _ _ h => ha (congrArg Loc.addr h), fun _ => trivial⟩
  | some j =>
    obtain ⟨_, hx⟩ := exec_xchgG_mapped (w := .W64) hc rfl hm
    exact ownW_done hx

/-! ## Nodes and prologues -/

section Nodes

variable {Z : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A fact of a single instruction's cell at its node** (`NodeW`). -/
theorem nodeW_cell {n : ND} {d : Directive} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (h : ∀ s c, CellAt s d z → Z s c) : NodeW Z (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, hn, -, hpc, -⟩
  exact ⟨h s c ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])), fun _ h => h⟩

/-- **`OwnW` at a stack-checked prologue's states** (from `prologueIn`; its
blocks covered, the limit's load a `movq %fs:…`). -/
theorem xProW_own [Executable.ValidLayout exe] {ms : MemSide isa} {Z lim : Int64} {L : String}
    {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop}
    {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn sc entry : Label}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    (hR : R.OK) (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi) (hZ : 0 ≤ Z.toInt)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true) :
    XProW (OwnW W) (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim
      L zl zf z1 z2 zs ps J := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  exact {
    w0 := blkZA_done (fun _ _ _ h => ownW_done h)
      (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (Int.le_refl _)) hR hlo hhi
      (code_field hp hend b0 (ofNat_zero' _))
    w1 := blkZA_done (fun _ _ _ h => ownW_done h) (xLea_ok (lo := -8 - Z.toInt) (hi := 0) Z zl) hR hlo hhi
      (code_field hp hend b1 (by show _ = _ + 1 + 3; rw [h4, ofNat_zero']))
    w2 := nodeW_cell (code_field hp hend b2 (by show _ = _ + 1 + 3 + _; rw [h4])) fun _ _ hc => ownW_movfs hc
    w3 := blkZA_done (fun _ _ _ h => ownW_done h) (xCmp_ok (lo := -8 - Z.toInt) (hi := 0) _ L z1 z2) hR hlo hhi
      (code_field hp hend b3 (by show _ = _ + 1 + 3 + _ + _; rw [h4, ofNat_add']))
    w4 := blkZA_done (fun _ _ _ h => ownW_done h) (xFr_ok (lo := -8 - Z.toInt) (hi := 0) Z zs ps hps) hR hlo hhi
      (code_field hp hend b4 (by
        show _ = _ + 1 + 3 + _ + _ + _ + _; rw [h4, ofNat_add', ofNat_add', ofNat_add'])) }

end Nodes

/-! ## wake.w's worker -/

/-- The address of `k(%b)` at a node's state, from the abstraction. -/
theorem eaddr_abs {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ) (z : Nat) (b : Reg64)
    (k : Int64) : eaddr s z (mB b k) = σ.regs.get64 b + BitVec.ofInt 64 k.toInt := by
  rw [eaddr_mB, hA.regs]

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
include hp hend

/-- Closes a covered block's obligation. -/
local macro "rb " ok:term:max code:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => ownW_done h) $ok (by assumption) (by omega) (by omega) $code)

/-- Closes an empty block's obligation. -/
local macro "rnil" : tactic => `(tactic| exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _))

/-- **`OwnW` at `scc_rt_thr_worker`'s head.** -/
theorem head_own {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : ThrHeadW.TN) :
    NodeZA (OwnW W) exe endPc R F (ThrHeadW.tN (_root_.Executable.labels exe).label J L i) (ThrHeadW.blkN i) := by
  cases i
  · rb ThrHeadW.thE_ok (thECode hp hend)
  · rnil

/-- **`OwnW` at `wc_worker`'s nodes**, in its region: its store of `c` at
`A`. -/
theorem wk_own {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -32) (hhi : 8 ≤ R.hi)
    {c1 c2 c3 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (hA : A ≠ W) (i : WkTailW.PN) :
    NodeZA (OwnW W) exe endPc R F (WkTailW.NA (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp sp i)
      (WkTailW.blkN i) := by
  have hc := wkCode hp hend (c0 := c1) (c1 := c2) (c2 := c3) (A := A) (B := B) (rbp0 := rbp0) (ra := ra) (tp := tp)
    (sp := sp)
  cases i
  · rb WkTailW.b0_ok hc.e
  · refine nodeZA_cell hc.st fun s σ c hc hd hAbs hJ => ownW_st hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    simpa using hA
  · rb WkTailW.b1_ok hc.n3
  · rnil
  · rb WkTailW.b2_ok hc.x14

/-- **`OwnW` at `scc_rt_unpark`'s nodes**, in its region: its exchange at
`B + 16`. -/
theorem unpk_own {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c2 c3 : Ctl} {B rbp1 ra1 tp : BitVec 64} (hB : B + 16#64 ≠ W) (i : Unpark.PN) :
    NodeZA (OwnW W) exe endPc R F (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i)
      (Unpark.blkN i) := by
  have hc := unpkCode hp hend (c0 := c2) (c1 := c3) (B := B) (rbp0 := rbp1) (ra := ra1) (tp := tp)
  cases i
  · rb Unpark.b0_ok hc.e
  · rb Unpark.b1_ok hc.n1
  · refine nodeZA_cell hc.xchg fun s σ c hc hd hAbs hJ => ownW_xchg hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    exact hB
  · rb Unpark.b2_ok hc.n2
  · rb Unpark.b3_ok hc.n3
  · rb Unpark.b4_ok hc.wake
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => ownW_syscall hc
  · rb Unpark.b5_ok hc.n5
  · rb Unpark.b6_ok hc.done

/-- **`OwnW` at `scc_rt_thr_worker`'s tail**: its store at `tp + 24`. -/
theorem tail_own {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c3 : Ctl} {tp sp0 : BitVec 64} (htp : tp + 24#64 ≠ W) (i : ThrTailW.PN) :
    NodeZA (OwnW W) exe endPc R F (ThrTailW.NA (_root_.Executable.labels exe).label c3 tp sp0 i)
      (ThrTailW.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp) (sp := sp0)
  cases i
  · exact nodeZA_cell hc.x12 fun _ _ _ hc _ _ _ => ownW_movfs hc
  · rb ThrTailW.b0_ok hc.n1
  · refine nodeZA_cell hc.ex fun s σ c hc hd hAbs hJ => ownW_st hc hd ?_
    rw [eaddr_abs hAbs, hJ.2.1]
    exact htp
  · rb ThrTailW.b1_ok hc.n2
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => ownW_syscall hc

/-- **`OwnW` at every node's states of the thread worker's run**, in a
region covering its frames: `c` at `A`, the permit at `B + 16` and the
TCB word at `tp + 24` are not `W`. -/
theorem thrZA_own {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -120)
    (hhi : 8 ≤ R.hi) {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} (hA : A ≠ W) (hB : B + 16#64 ≠ W)
    (htp : tp + 24#64 ≠ W) :
    ThrZA (OwnW W) exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := xProW_own hp hend wake_thrPro hR (by have : (32 : Int64).toInt = 32 := by decide
                                              omega) (by omega) (by decide) (by decide)
  head := head_own hp hend hR hlo hhi
  wpro _ _ hC _ _ := xProW_own hp hend wake_wcPro hC.ok
    (by have : (16 : Int64).toInt = 16 := by decide
        have := hC.lo; omega) (by have := hC.hi; omega) (by decide) (by decide)
  wk _ _ hC _ _ := wk_own hp hend hC.ok (by have := hC.lo; omega) hC.hi hA
  unpk _ _ _ _ _ _ _ hC _ _ := unpk_own hp hend hC.ok hC.lo hC.hi hB
  tail := tail_own hp hend hR (by omega) hhi htp

/-- **`OwnW` at the child's stub**: it writes nothing shared. -/
theorem cZA_own {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZA (OwnW W) exe endPc R F (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  have hin := wake_childIn
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt SccCode.wakeCells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  intro i
  cases i
  · exact nodeZA_cell (fun s he hn => code bts s he hn) fun _ _ _ hc _ _ _ => ownW_test hc
  · rb jeB_ok (fun s he hn => code bje s he hn)
  · exact nodeZA_cell (fun s he hn => (by simpa using code bxb s he hn :
      CodeAt s ((_root_.Executable.labels exe).label Spike.Lib.X64.WakePh.Child.chL) Spike.Lib.X64.WakePh.Child.xbp))
      fun _ _ _ hc _ _ _ => ownW_fi hc
  · rb chB_ok (fun s he hn => code bch s he hn)

end Inst

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.OwnW.thrZA_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thrZA_own

end Spike.Lib.X64.Flow.Worker.Wake.OwnW
