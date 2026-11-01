/-
**hello.w's worker store point on the target** (row 5j-k
`PassZ`, AArch64): the restatement of `A64WakePass.lean` at hello.w's
listing (`SccCode.helloProg`, `Spike/Lib/A64HelloCode.lean`). The pcs past
the worker's release store (`helloPostRuns`), the target store point
`helloPassT` (the pc is one of them), and its value at every node of the
worker's segments (`seg_wcWorkerS`'s, `seg_thrWorkerH`'s, the child's stub,
`print`'s callee nodes and the abort path), decided per pc on the listing
(`passChk`, `pcIn_iff`).

Unlike wake's, these facts do not mention the control: each node's pc is
on one side of the store point (`PB b`), whatever the source; the pairing
with the source's store point (`helloPass`, `PassZ`'s form, the frames
empty and the control at `wkUnpark` or `ret ()`) is the concrete `Z`'s,
from each node's pinned control (`pass_of_b`).

- `helloPostRuns`: `wc_worker` from the instruction after its `stlr`
  (`hello_stlrAt`) to its return, `scc_rt_unpark`, `scc_rt_thr_worker` from
  its `.sp0` to its exit; `hello_runsOk`.
- `helloPassT`: `PcIn helloPostRuns`; `HPassC c`: the source past its store;
  `helloPass s c fs`: `helloPassT s ↔ fs = [] ∧ HPassC c` (`PassZ`'s body).
- `PB b`: the pc is past the store iff `b`; `pass_at`, `nodeZ_b`, `pro_off`,
  `off_of_pcIn`: at a decided pc, a node, a prologue, a set of runs.
- `tail_b` (`tailB`), `unpk_b`, `thrT_b`, `thrE_b`, `thrPro_off`, `wcPro_off`,
  `wE_b`, `wC_b`, `print_b`, `child_b`, `abort_off`: each function's nodes.
- `pass_of_b`, `pass_off`, `pass_on`: `helloPass` from a node's side and the
  control's.
-/
import Spike.Lib.A64PcRuns
import Spike.Lib.A64HelloWorkerTCS
import Spike.Lib.A64HelloChildNN
import Spike.Lib.WorkerSrc

namespace Spike.Lib.A64.Flow.Worker.Hello.Pass

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays blockAt labelGap label_labelGap labelIdx run)
open Spike.Lib.A64.PcRuns (PcIn runsOk inRuns pcIn_iff)
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words cN childN childJ cLen pfxM)
open SccCode (helloProg)
open Spike.Lib.WorkerSrc (wkUnpark)

set_option linter.unusedSimpArgs false

/-- **The pcs past the worker's release store**: `wc_worker`'s `.sp4` from
its fourth instruction (past the `stlr`) and its `.sp6`, `scc_rt_unpark`,
`scc_rt_thr_worker`'s `.sp0` and `.halt4`. -/
def helloPostRuns : List (Label × Nat × Nat) :=
  [(".L20_wc_worker.sp4", 3, 5), (".L20_wc_worker.sp6", 0, 4), ("scc_rt_unpark", 0, 5),
    (".L11_scc_rt_unpark.0_entry", 0, 10), (".L11_scc_rt_unpark.1_wake", 0, 17),
    (".L11_scc_rt_unpark.2_done", 0, 4), (HThrTail.pfx0 ++ ".sp0", 0, 10), (HThrTail.pfx0 ++ ".halt4", 0, 1)]

theorem hello_runsOk : runsOk helloProg helloPostRuns = true := by decide +kernel

/-- The run of `wc_worker`'s `.sp4` starts two instructions before its
`stlr`. -/
theorem hello_stlrAt : blockAt helloProg ".L20_wc_worker.sp4" 2
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] = true := by decide +kernel

/-- **The target store point**: the pc is past the worker's `stlr`
(`PassZ`'s `passT`). -/
def helloPassT (s : State) : Prop := PcIn helloPostRuns s

/-- **The source is past its store**: at `wkUnpark` or `ret ()`. -/
def HPassC (c : Ctl) : Prop := c.term = wkUnpark ∨ c.term = .ret .unit

/-- **The target store point agrees with the source's** on the frames
(`PassZ`'s body at `helloPassT`). -/
def helloPass : FragS isaLSE2 := fun s c fs => (helloPassT s ↔ fs = [] ∧ HPassC c)

/-- **The pc is past the store iff `b`.** -/
def PB (b : Bool) : Frag isaLSE2 := fun s _ => (helloPassT s ↔ b = true)

/-- **The instructions `k0 .. k0 + len` after `l` are all (`b`) or none
(`!b`) past the store**, decided on the listing. -/
def passChk (l : Label) (k0 len : Nat) (b : Bool) : Bool :=
  (labelIdx helloProg l).isSome && decide (k0 + len ≤ (run helloProg l).length) &&
    (List.range len).all fun j => inRuns helloProg helloPostRuns l (k0 + j) == b

/-- A node of no instructions keeps any fragment. -/
theorem nodeZ_nil {Z : Frag isaLSE2} {exe : _root_.Executable} {n : ND} : NodeZ Z exe n 0 :=
  fun _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

/-! ## `helloPass` from the pc's side and the control's -/

/-- **`helloPass` from a side `b`** and the source's store point agreeing
with it. -/
theorem pass_of_b {s : State} {c : Ctl} {fs : List TermRun.Frame} {b : Bool} (h : PB b s c)
    (hb : fs = [] ∧ HPassC c ↔ b = true) : helloPass s c fs :=
  h.trans hb.symm

/-- **Before the store on both sides**: the pc not past it, the source not
past it on the empty stack. -/
theorem pass_off {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PB false s c)
    (hc : fs = [] → ¬ HPassC c) : helloPass s c fs :=
  pass_of_b h ⟨fun ⟨h1, h2⟩ => absurd h2 (hc h1), nofun⟩

/-- **Past the store on both sides.** -/
theorem pass_on {s : State} {c : Ctl} {fs : List TermRun.Frame} (h : PB true s c) (hfs : fs = [])
    (hc : HPassC c) : helloPass s c fs :=
  pass_of_b h ⟨fun _ => rfl, fun _ => ⟨hfs, hc⟩⟩

theorem hPassC_unpark {env : TermRun.Env} {h : Option _} : HPassC ⟨wkUnpark, env, h⟩ := .inl rfl

theorem hPassC_ret {env : TermRun.Env} {h : Option _} : HPassC ⟨.ret .unit, env, h⟩ := .inr rfl

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
include hp

/-- **The store point at a decided pc**: the instruction `k0 + k` after `l`. -/
theorem pass_at {l : Label} {k0 len : Nat} {b : Bool} (hchk : passChk l k0 len b = true) {s : State} {k : Nat}
    (hk : k < len) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0) + Int64.ofNat (4 * k)) :
    helloPassT s ↔ b = true := by
  simp only [passChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hchk
  obtain ⟨⟨hl, hlen⟩, hall⟩ := hchk
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add] at hs
  unfold helloPassT
  rw [pcIn_iff hp hello_runsOk he hl (by omega) hs, hall k hk]

/-- **The store point at a node** at the instructions `k0 ..` after `l`. -/
theorem nodeZ_b {n : ND} {len : Nat} {l : Label} {k0 : Nat} {b : Bool}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : passChk l k0 len b = true) : NodeZ (PB b) exe n len :=
  fun _ _ _ _ hk he hs _ => pass_at hp hchk hk he (hpc ▸ hs)

/-- **Before the store at a prologue** (`fn`'s label is its stack check's,
`sc`), its fifteen instructions. -/
theorem pro_off {fn sc : Label} (hg : labelGap helloProg fn sc 0 = true) (hchk : passChk sc 0 15 false = true) :
    ∀ (s : State) (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → ¬ helloPassT s := by
  intro s k hk he hs h
  have := (pass_at hp hchk hk he (by rw [hs, label_labelGap hp hg]; simp only [ofNat4_zero])).mp h
  exact Bool.false_ne_true this

/-- **Before the store on a set of runs** none of whose instructions is past
it, decided on the listing. -/
theorem off_of_pcIn {A : List (Label × Nat × Nat)} (hok : runsOk helloProg A = true)
    (hdis : A.all (fun q => (List.range q.2.2).all fun j => !inRuns helloProg helloPostRuns q.1 j) = true)
    {s : State} (he : s.exe = exe) (h : PcIn A s) : ¬ helloPassT s := by
  obtain ⟨q, hq, j, hlo, hj, hs⟩ := h
  simp only [runsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hdis
  obtain ⟨hl, hlen⟩ := hok q hq
  rw [he] at hs
  unfold helloPassT
  rw [pcIn_iff hp hello_runsOk he hl (by omega) (k := j) hs]
  · rw [hdis q hq j hj]; exact Bool.false_ne_true

/-- Closes `nodeZ_b`'s side goals: the node's pc, the decided check. -/
local macro "zb" : tactic =>
  `(tactic| first
    | (simp only [Unpark.N, Unpark.pcSvc, HelloTail.N, HelloTail.pcBl, HThrTail.N, HThrHead.tN, cN, childN,
        Body.wN, Body.wCall, PrintF.cN, ND.withTp, PrintF.FA.N, Spike.Lib.A64.PrintA.N, PrintF.pcSvc,
        Spike.Lib.A64.PrintA.pcSvc, ofNat4_succ, ofNat4_zero]; done)
    | decide +kernel)

/-- Which of `wc_worker`'s tail nodes are past the store: from the one
after the `stlr`. -/
def tailB : HelloTail.PN → Bool
  | .sp4 => false | .st => false | .n3 => true | .bl => true | .unpk => true | .sp6 => true

/-- **The store point at `wc_worker`'s tail nodes** (`seg_wcWorkerS`'s
`hZW`). -/
theorem tail_b {c0 c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} (i : HelloTail.PN) :
    NodeZ (PB (tailB i)) exe (HelloTail.N (_root_.Executable.labels exe).label c0 c1 c2 A B x29 ra tp i)
      (HelloTail.lenN i) := by
  cases i
  · exact nodeZ_b hp (l := ".L20_wc_worker.sp4") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L20_wc_worker.sp4") (k0 := 2) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L20_wc_worker.sp4") (k0 := 3) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L20_wc_worker.sp4") (k0 := 4) (by zb) (by zb)
  · exact nodeZ_nil
  · exact nodeZ_b hp (l := ".L20_wc_worker.sp6") (k0 := 0) (by zb) (by zb)

/-- **`scc_rt_unpark`'s nodes are past the store** (`hZU`). -/
theorem unpk_b {c0 c1 : Ctl} {B x29 ra tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (PB true) exe (Unpark.N (_root_.Executable.labels exe).label c0 c1 B x29 ra tp i) (Unpark.lenN i) := by
  cases i
  · exact nodeZ_b hp (l := "scc_rt_unpark") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 3) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 4) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 9) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 11) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 12) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L11_scc_rt_unpark.2_done") (k0 := 0) (by zb) (by zb)

/-- **`scc_rt_thr_worker`'s tail is past the store** (`seg_thrWorkerH`'s
`hZT`). -/
theorem thrT_b {c0 : Ctl} {tp : BitVec 64} (i : HThrTail.PN) :
    NodeZ (PB true) exe (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c0 tp i)
      (HThrTail.lenN i) := by
  cases i
  · exact nodeZ_b hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 5) (by zb) (by zb)
  · exact nodeZ_b hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 6) (by zb) (by zb)
  · exact nodeZ_b hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 8) (by zb) (by zb)

/-- **`scc_rt_thr_worker`'s `.0_entry` block is before the store** (`hZE`). -/
theorem thrE_b {J : AS → Ctl → Prop} {L : Ctl → Ctl → Prop} :
    NodeZ (PB false) exe (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label J L .e)
      HThrHead.thE.length :=
  nodeZ_b hp (l := HThrTail.pfx0 ++ ".0_entry") (k0 := 0) (by zb) (by zb)

/-- **`scc_rt_thr_worker`'s prologue is before the store** (`hz`). -/
theorem thrPro_off : ∀ (s : State) (k : Nat), k < 15 → s.exe = exe →
    s.st.2 = (_root_.Executable.labels exe).label "scc_rt_thr_worker" + Int64.ofNat (4 * k) → ¬ helloPassT s :=
  pro_off hp (sc := HThrTail.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)

/-- **`wc_worker`'s prologue is before the store** (`seg_wcWorkerS`'s `hz`). -/
theorem wcPro_off : ∀ (s : State) (k : Nat), k < 15 → s.exe = exe →
    s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat (4 * k) → ¬ helloPassT s :=
  pro_off hp (sc := ".L20_wc_worker.stack_check") (by decide +kernel) (by decide +kernel)

/-- **`wc_worker`'s `.0_entry` block is before the store** (`hZE`). -/
theorem wE_b {J : AS → Ctl → Prop} {Pr : AS → Nat → Ctl → Prop} :
    NodeZ (PB false) exe (Body.wN (_root_.Executable.labels exe).label J Pr .e) Body.wkE.length :=
  nodeZ_b hp (l := ".L20_wc_worker.0_entry") (k0 := 0) (by zb) (by zb)

/-- **`wc_worker`'s call node is before the store** (`hZC`). -/
theorem wC_b {J Kc : AS → Ctl → Prop} : NodeZ (PB false) exe (Body.wCall (_root_.Executable.labels exe).label J Kc) 1 :=
  nodeZ_b hp (l := "scc_rt_print") (k0 := 0) (by zb) (by zb)

set_option maxHeartbeats 1600000 in
/-- **`print`'s nodes are before the store** (`hZP`), any source. -/
theorem print_b {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS} (i : PrintF.PN) :
    NodeZ (PB false) exe (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i) (PrintF.FA.lenN i) := by
  cases i
  · exact nodeZ_b hp (l := "scc_rt_print") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.0_entry") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.1_loop") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.1_loop") (k0 := 4) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 1) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 5) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 6) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 13) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.2_write") (k0 := 14) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 6) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 7) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.4_chk3") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.4_chk3") (k0 := 4) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.5_adv") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.6_fail") (k0 := 0) (by zb) (by zb)
  · exact nodeZ_b hp (l := ".L9_scc_rt_print.7_done") (k0 := 0) (by zb) (by zb)

/-- **The child's stub is before the store** (`seg_childStubH`'s `hZc`). -/
theorem child_b {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (i : Child.CN) :
    NodeZ (PB false) exe (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cLen i) := by
  cases i
  · exact nodeZ_b hp (l := pfxM ++ ".sp6") (k0 := 26) (by zb) (by zb)
  · exact nodeZ_b hp (l := pfxM ++ ".child13") (k0 := 0) (by zb) (by zb)

/-- **The abort path is before the store** (`seg_wcWorkerS`'s `hZA`). -/
theorem abort_off {s : State} (he : s.exe = exe) (h : PcIn abortRuns s) : ¬ helloPassT s :=
  off_of_pcIn hp (by decide +kernel) (by decide +kernel) he h

end Inst

end Spike.Lib.A64.Flow.Worker.Hello.Pass
