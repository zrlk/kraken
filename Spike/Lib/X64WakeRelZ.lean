/-
**At most one write per path, a release write, at every node's states of
wake.w's worker, x86-64** (the x64 twin of `Spike/Lib/A64WakeRelZ.lean`
and of the per-instruction half of `Spike/Lib/A64RelW1Nodes.lean`): the
fact `RelWS s` (`Spike/Lib/X64RelWS.lean`: the instruction runs, and its
event tree is `RelW1 Arch.tso`) at every node's states of the thread
worker's run (`thrZA_rel`) and of the child's stub (`cZA_rel`), from the
code alone: covered blocks run to `.done` (`blkZA_done`), the loads only
load, the store (`movq`) and the exchange (`xchgq`) are release writes
under TSO, the `syscall`s fault.

- `silent_noW`; `relWS_st`, `relWS_fi`: per instruction (the store, a
  flag-setting register instruction).
- `blkZA_done`, `nodeZA_cell`: a fact of the states of a covered block
  (they run to `.done`), of a single instruction's cell (with the node's
  invariant and abstraction at its state), at a node's states (`NodeZA`).
- `head_rel`, `wk_rel`, `unpk_rel`, `tail_rel`, `thrZA_rel`, `cZA_rel`.

**Unlike AArch64** (forced by the x64 shape): the fact is `RelWS s`
(AArch64: `RelZ`, the trees only; here the instruction also runs, which
`X64RelWS`'s lemmas give), under `Arch.tso` (a plain `movq` store is a
release store); `NodeZA` is over byte-sized cells with no alignment
premise; the prologues are `XProW`s (`X64WakeMainR.xProW_relW`); the
store, exchange, `%fs` load and `syscall` nodes are single cells
(`nodeZA_cell`); the stub is four nodes, its `testq` and `xorl` single
cells; `wc_worker`'s and the tail's nodes are `WkTailW.NA`, `ThrTailW.NA`
(`ThrZA`'s).
-/
import Spike.Lib.X64WakeMainR
import Spike.Lib.X64WakeChildNNA

namespace Spike.Lib.X64.Flow.Worker.Wake.RelZW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZA wkCode thrCode thECode unpkCode wake_thrPro wake_wcPro)
open Spike.Lib.X64.WakePh (wake_childIn)
open Spike.Lib.X64.WakePh.Child (cN childN childIn CN jeB_ok chB_ok)
open Spike.Lib.X64.Flow.Worker.Wake.Child (cBlk)
open Spike.Lib.X64WakeMainR (relWS_movfs relWS_xchg relWS_test xProW_relW)

/-! ## Per instruction -/

/-- A silent tree writes nothing. -/
theorem silent_noW {σ : Type} {P : σ → Prop} : ∀ {t : EvTree σ}, Lower.SilentTree P t → EvTree.NoW t
  | .done _, _ => .done _
  | .choose _ _, h => .choose fun i => silent_noW (h.2 i)
  | .fault _, h => h.elim
  | .load _ _ _ _, h => h.elim
  | .store _ _ _ _ _, h => h.elim
  | .rmw _ _ _ _ _, h => h.elim
  | .fence _ _, h => h.elim

/-- **`movq %r, k(%b)`**: a plain store (a release store under TSO), or no
event. -/
theorem relWS_st {s : State} {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (stDir b k r) z)
    (hd : s.decls = {}) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    exact relWS_of (exec_store_agrees hc rfl hm (agrees_of_decls hd _ _)) (.store (by decide) fun _ => .done _)
  | some j => exact relWS_of (exec_store_mapped hc rfl hm) (.noW (.done _))

/-- **A flag-setting register instruction**: silent. -/
theorem relWS_fi {s : State} {fi : FI} {z : Nat} (hc : CellAt s fi.toDir z) : RelWS s := by
  obtain ⟨t, ht, hs⟩ := exec_fi hc
  exact relWS_of ht (.noW (silent_noW hs))

/-! ## At a node's states -/

section Nodes

variable {Z : Frag isa} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}

/-- **A fact of every state that runs to `.done`, at a covered block's
states.** -/
theorem blkZA_done {lo hi : Int} {blk : List (Directive × Nat)}
    (hZ : ∀ s c s', isa.exec s = some (.done s') → Z s c) (hok : okBlk lo hi n.o blk = true) (hR : R.OK)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    NodeZA Z exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA _
  subst he
  obtain ⟨s', h⟩ := blk_exec_done hok hR hlo hhi (hcode s rfl hn) hk hA
  exact ⟨hZ _ c _ h, fun _ h => h⟩

/-- **A fact of a single instruction's cell at its node's states**, given
the node's invariant and abstraction there. -/
theorem nodeZA_cell {d : Directive} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (h : ∀ s σ c, CellAt s d z → s.decls = {} → Abs R n.o s.st.1 σ → n.J σ c → Z s c) :
    NodeZA Z exe endPc R F n [(d, z)] := by
  intro s σ c he hn hd _ _ _ hJ k hk m hA _
  have hk0 : k = 0 := by simp at hk; omega
  subst hk0
  refine ⟨h _ σ c ((hcode _ he hn).cell0 rfl rfl (by simp [cellOff])) hd ?_ hJ, fun _ h => h⟩
  exact hA

end Nodes

/-! ## wake.w's worker -/

/-- The fact. -/
abbrev RZ : Frag isa := fun s _ => RelWS s

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
include hp hend

/-- Closes a covered block's obligation. -/
local macro "rb " ok:term:max code:term:max : tactic =>
  `(tactic| exact blkZA_done (fun _ _ _ h => relWS_done ⟨_, h⟩) $ok (by assumption) (by omega) (by omega) $code)

/-- **`RelWS` at `scc_rt_thr_worker`'s head.** -/
theorem head_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -120) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} (i : ThrHeadW.TN) :
    NodeZA RZ exe endPc R F (ThrHeadW.tN (_root_.Executable.labels exe).label J L i) (ThrHeadW.blkN i) := by
  cases i
  · rb ThrHeadW.thE_ok (thECode hp hend)
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-- **`RelWS` at `wc_worker`'s nodes**, in its region. -/
theorem wk_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -32) (hhi : 8 ≤ R.hi)
    {c1 c2 c3 : Ctl} {A B rbp0 ra tp sp : BitVec 64} (i : WkTailW.PN) :
    NodeZA RZ exe endPc R F (WkTailW.NA (_root_.Executable.labels exe).label c1 c2 c3 A B rbp0 ra tp sp i)
      (WkTailW.blkN i) := by
  have hc := wkCode hp hend (c0 := c1) (c1 := c2) (c2 := c3) (A := A) (B := B) (rbp0 := rbp0) (ra := ra) (tp := tp)
    (sp := sp)
  cases i
  · rb WkTailW.b0_ok hc.e
  · exact nodeZA_cell hc.st fun _ _ _ hc hd _ _ => relWS_st hc hd
  · rb WkTailW.b1_ok hc.n3
  · exact fun _ _ _ _ _ _ _ _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)
  · rb WkTailW.b2_ok hc.x14

/-- **`RelWS` at `scc_rt_unpark`'s nodes**, in its region. -/
theorem unpk_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c2 c3 : Ctl} {B rbp1 ra1 tp : BitVec 64} (i : Unpark.PN) :
    NodeZA RZ exe endPc R F (Unpark.N (_root_.Executable.labels exe).label c2 c3 B rbp1 ra1 tp i) (Unpark.blkN i) := by
  have hc := unpkCode hp hend (c0 := c2) (c1 := c3) (B := B) (rbp0 := rbp1) (ra := ra1) (tp := tp)
  cases i
  · rb Unpark.b0_ok hc.e
  · rb Unpark.b1_ok hc.n1
  · exact nodeZA_cell hc.xchg fun _ _ _ hc _ _ _ => relWS_xchg hc
  · rb Unpark.b2_ok hc.n2
  · rb Unpark.b3_ok hc.n3
  · rb Unpark.b4_ok hc.wake
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => relWS_syscall hc
  · rb Unpark.b5_ok hc.n5
  · rb Unpark.b6_ok hc.done

/-- **`RelWS` at `scc_rt_thr_worker`'s tail.** -/
theorem tail_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {c3 : Ctl} {tp sp0 : BitVec 64} (i : ThrTailW.PN) :
    NodeZA RZ exe endPc R F (ThrTailW.NA (_root_.Executable.labels exe).label c3 tp sp0 i) (ThrTailW.blkN i) := by
  have hc := thrCode hp hend (c0 := c3) (tp := tp) (sp := sp0)
  cases i
  · exact nodeZA_cell hc.x12 fun _ _ _ hc _ _ _ => relWS_movfs hc
  · rb ThrTailW.b0_ok hc.n1
  · exact nodeZA_cell hc.ex fun _ _ _ hc hd _ _ => relWS_st hc hd
  · rb ThrTailW.b1_ok hc.n2
  · exact nodeZA_cell hc.sys fun _ _ _ hc _ _ _ => relWS_syscall hc

/-- **`RelWS` at every node's states of the thread worker's run**, in a
region covering its frames. -/
theorem thrZA_rel {R : Region} {F : MachineData → Prop} {ms : MemSide isa} (hR : R.OK) (hlo : R.lo ≤ -120)
    (hhi : 8 ≤ R.hi) {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} :
    ThrZA RZ exe endPc R F ms c0 c1 c2 c3 A B tp sp0 where
  pro := xProW_relW hp hend wake_thrPro hR (by have : (32 : Int64).toInt = 32 := by decide
                                               omega) (by omega) (by decide) (by decide)
  head := head_rel hp hend hR hlo hhi
  wpro _ _ hC _ _ := xProW_relW hp hend wake_wcPro hC.ok
    (by have : (16 : Int64).toInt = 16 := by decide
        have := hC.lo; omega) (by have := hC.hi; omega) (by decide) (by decide)
  wk _ _ hC _ _ := wk_rel hp hend hC.ok (by have := hC.lo; omega) hC.hi
  unpk _ _ _ _ _ _ _ hC _ _ := unpk_rel hp hend hC.ok hC.lo hC.hi
  tail := tail_rel hp hend hR (by omega) hhi

/-- **`RelWS` at the child's stub.** -/
theorem cZA_rel {R : Region} {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZA RZ exe endPc R F (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  have hin := wake_childIn
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt SccCode.wakeCells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  intro i
  cases i
  · exact nodeZA_cell (fun s he hn => code bts s he hn) fun _ _ _ hc _ _ _ => relWS_test hc
  · rb jeB_ok (fun s he hn => code bje s he hn)
  · exact nodeZA_cell (fun s he hn => (by simpa using code bxb s he hn :
      CodeAt s ((_root_.Executable.labels exe).label Spike.Lib.X64.WakePh.Child.chL) Spike.Lib.X64.WakePh.Child.xbp)) fun _ _ _ hc _ _ _ => relWS_fi hc
  · rb chB_ok (fun s he hn => code bch s he hn)

end Inst

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.RelZW.thrZA_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thrZA_rel

end Spike.Lib.X64.Flow.Worker.Wake.RelZW
