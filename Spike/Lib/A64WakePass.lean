/-
**wake.w's worker store point on the target** (`WCompat.pass`, AArch64): the pcs past the worker's release store
(`wakePostRuns`, runs of instructions after labels of the listing), the
fragment `wakePass` (the pc is one of them iff the source is past its store),
and `wakePass` at every node of the child's segments (`ThrZ`, the stub's
`NodeZ`), for `seg_childPreNN` at `Z := wakePass`. The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

Every node's invariant pins its control (`c = c'`), and every node's pc is a
label of the listing plus a count of instructions; whether such a pc is past
the store is decided on the listing (`passChk`, `pcIn_iff`).

- `wakePostRuns`: `wc_worker` from the instruction after its `stlr`
  (`wake_stlrAt`) to its return, `scc_rt_unpark`, `scc_rt_thr_worker` from
  its `.sp0` (past `wc_worker`'s return) to its exit; `wake_runsOk`.
- `wakePassT`: `PcIn wakePostRuns`, the flag record's `passT`.
- `WPassC c`: the source is past its store (`wkUnpark` or `ret `), the
  right side of `WCompat.pass`; `wakePass s c`: `PcIn wakePostRuns s ↔ WPassC c`.
- `nodeZ_pass`, `pro_pass`: a node (prologue) with a decided pc check.
- `head_pass`, `wk_pass`, `unpk_pass`, `tail_pass`: each function's nodes.
- `thrZ_pass`, `cZ_pass`: `wakePass` at every node of the thread worker's
  run and of the child's stub, given which controls are past the store.
- `kidC_not`, `wc1_not`, `wkC2_pass`, `wkC3_pass`: the child's controls;
  `childThrZ`: `seg_childPreNN`'s premises at `Z := wakePass` (with
  `cZ_pass hp (kidC_not ..)`).
-/
import Spike.Lib.A64PcRuns
import Spike.Lib.A64WakeChildNN
import Spike.Lib.WorkerSrc

namespace Spike.Lib.A64.Flow.Worker.Wake.Pass

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays blockAt labelGap label_labelGap labelIdx run)
open Spike.Lib.A64.PcRuns (PcIn runsOk inRuns pcIn_iff)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN childJ cLen pfxM kidC)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.WorkerSrc (wkUnpark)

set_option linter.unusedSimpArgs false

/-- **The pcs past the worker's release store**: `wc_worker`'s `.0_entry`
from its fourth instruction (past the `stlr`) and its `.sp1`,
`scc_rt_unpark`, `scc_rt_thr_worker`'s `.sp0` and `.halt4`. -/
def wakePostRuns : List (Label × Nat × Nat) :=
  [(WkTailW.pfx0 ++ ".0_entry", 3, 5), (WkTailW.pfx0 ++ ".sp1", 0, 4), ("scc_rt_unpark", 0, 5),
    (".L11_scc_rt_unpark.0_entry", 0, 10), (".L11_scc_rt_unpark.1_wake", 0, 17),
    (".L11_scc_rt_unpark.2_done", 0, 4), (ThrTailW.pfx0 ++ ".sp0", 0, 10), (ThrTailW.pfx0 ++ ".halt4", 0, 1)]

theorem wake_runsOk : runsOk wakeProg wakePostRuns = true := by decide +kernel

/-- The run of `wc_worker`'s `.0_entry` starts right past its `stlr`. -/
theorem wake_stlrAt : blockAt wakeProg (WkTailW.pfx0 ++ ".0_entry") 2
    [.instr ⟨.W64, .STLR .W64 (.low (.reg .X9) .W64) (.low (.reg .X10) .W64)⟩] = true := by decide +kernel

/-- **The target store point**: the pc is past the worker's `stlr`
(`WCompat.pass`'s `passT`). -/
def wakePassT (s : State) : Prop := PcIn wakePostRuns s

/-- **The source is past its store** (`WCompat.pass`'s right side). -/
def WPassC (c : Ctl) : Prop := c.term = wkUnpark ∨ c.term = .ret .unit

/-- **The target store point agrees with the source's**: the pc is past the
`stlr` iff the control is past the store. -/
def wakePass : Frag isaLSE2 := fun s c => (wakePassT s ↔ WPassC c)

/-- **The instructions `k0 .. k0 + len` after `l` are all (`b`) or none
(`!b`) past the store**, decided on the listing. -/
def passChk (l : Label) (k0 len : Nat) (b : Bool) : Bool :=
  (labelIdx wakeProg l).isSome && decide (k0 + len ≤ (run wakeProg l).length) &&
    (List.range len).all fun j => inRuns wakeProg wakePostRuns l (k0 + j) == b

theorem wp_false {c : Ctl} (h : ¬ WPassC c) : WPassC c ↔ false = true := ⟨fun h' => absurd h' h, nofun⟩

theorem wp_true {c : Ctl} (h : WPassC c) : WPassC c ↔ true = true := ⟨fun _ => rfl, fun _ => h⟩

theorem kidC_not (T : Ty) (w1 w2 : TermRun.Word) : ¬ WPassC (kidC T w1 w2) := by
  simp [WPassC, kidC, wkUnpark]

theorem wc1_not (w1 w2 : TermRun.Word) : ¬ WPassC (wc1 workerTy w1 w2) := by
  simp [WPassC, wc1, workerRest, wkUnpark]

theorem wkC2_pass {env : TermRun.Env} : WPassC ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), env, none⟩ :=
  .inl rfl

theorem wkC3_pass {env : TermRun.Env} : WPassC ⟨.ret .unit, env, none⟩ := .inr rfl

/-- A node of no instructions keeps any fragment. -/
theorem nodeZ_nil {Z : Frag isaLSE2} {exe : _root_.Executable} {n : ND} : NodeZ Z exe n 0 :=
  fun _ _ _ _ hk => absurd hk (Nat.not_lt_zero _)

section Inst

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
include hp

/-- **`wakePass` at a decided pc**: the instruction `k0 + k` after `l`. -/
theorem pass_at {l : Label} {k0 len : Nat} {b : Bool} (hchk : passChk l k0 len b = true) {c : Ctl}
    (hb : WPassC c ↔ b = true) {s : State} {k : Nat} (hk : k < len) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0) + Int64.ofNat (4 * k)) :
    wakePass s c := by
  simp only [passChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq] at hchk
  obtain ⟨⟨hl, hlen⟩, hall⟩ := hchk
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add] at hs
  show wakePassT s ↔ WPassC c
  unfold wakePassT
  rw [pcIn_iff hp wake_runsOk he hl (by omega) hs, hall k hk]
  exact hb.symm

/-- **`wakePass` at a node** whose invariant pins the control to `c'`, at
the instructions `k0 ..` after `l`. -/
theorem nodeZ_pass {n : ND} {len : Nat} {l : Label} {k0 : Nat} {b : Bool}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : passChk l k0 len b = true) {c' : Ctl} (hc : ∀ σ c, n.J σ c → c = c') (hb : WPassC c' ↔ b = true) :
    NodeZ wakePass exe n len := by
  intro s σ c k hk he hs hJ
  obtain rfl := hc σ c hJ
  exact pass_at hp hchk hb hk he (hpc ▸ hs)

/-- **`wakePass` at a prologue** (`fn`'s label is its stack check's, `sc`),
before the store. -/
theorem pro_pass {fn sc : Label} (hg : labelGap wakeProg fn sc 0 = true) (hchk : passChk sc 0 11 false = true)
    {J : AS → Ctl → Prop} {c' : Ctl} (hc : ∀ σ c, J σ c → c = c') (h0 : ¬ WPassC c') :
    ∀ (s : State) σ c (k : Nat), k < 11 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → J σ c → wakePass s c := by
  intro s σ c k hk he hs hJ
  obtain rfl := hc σ c hJ
  refine pass_at hp hchk (wp_false h0) hk he ?_
  rw [hs, label_labelGap hp hg]
  simp only [ofNat4_zero]

/-- Closes `nodeZ_pass`'s side goals: the node's pc, the decided check, the
control's pin. -/
local macro "zn" : tactic =>
  `(tactic| first
    | (simp only [Unpark.N, Unpark.pcSvc, WkTailW.N, WkTailW.pcBl, ThrTailW.N, ThrHeadW.tN, cN, childN,
        ofNat4_succ, ofNat4_zero]; done)
    | decide +kernel
    | (intro σ c h
       simp only [Unpark.N, Unpark.JI, Unpark.JS, Unpark.JE, WkTailW.N, WkTailW.JI, ThrTailW.N, ThrHeadW.tN,
         thrJ, cN, childN, childJ] at h
       first | exact h.1 | exact h.1.1 | exact h | (obtain ⟨_, h⟩ := h; exact h.1)))

/-- `wakePass` at `scc_rt_thr_worker`'s head, before the store. -/
theorem head_pass {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC c0) (i : ThrHeadW.TN) :
    NodeZ wakePass exe (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0)
      (fun _ c => c = c1) i) (ThrHeadW.lenN i) := by
  cases i
  · refine nodeZ_pass hp (l := (ThrTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ ?_ (wp_false h0) <;> zn
  · exact nodeZ_nil

/-- `wakePass` at `wc_worker`'s nodes: before the store at `c1`, past it at
`c2`, `c3`. -/
theorem wk_pass {c1 c2 c3 : Ctl} {A B x29 ra tp : BitVec 64} (h1 : ¬ WPassC c1) (h2 : WPassC c2)
    (h3 : WPassC c3) (i : WkTailW.PN) :
    NodeZ wakePass exe (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp i)
      (WkTailW.lenN i) := by
  cases i
  · refine nodeZ_pass hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ ?_ (wp_false h1) <;> zn
  · refine nodeZ_pass hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 2) ?_ ?_ ?_ (wp_false h1) <;> zn
  · refine nodeZ_pass hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 3) ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 4) ?_ ?_ ?_ (wp_true h2) <;> zn
  · exact nodeZ_nil
  · refine nodeZ_pass hp (l := (WkTailW.pfx0 ++ ".sp1")) (k0 := 0) ?_ ?_ ?_ (wp_true h3) <;> zn

/-- `wakePass` at `scc_rt_unpark`'s nodes, past the store. -/
theorem unpk_pass {c2 c3 : Ctl} {B x29 ra tp : BitVec 64} (h2 : WPassC c2) (h3 : WPassC c3) (i : Unpark.PN) :
    NodeZ wakePass exe (Unpark.N (_root_.Executable.labels exe).label c2 c3 B x29 ra tp i) (Unpark.lenN i) := by
  cases i
  · refine nodeZ_pass hp (l := "scc_rt_unpark") (k0 := 0) ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 0) ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 3) ?_ ?_ ?_ (wp_true h2) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 4) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 9) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 0) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 11) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 12) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := ".L11_scc_rt_unpark.2_done") (k0 := 0) ?_ ?_ ?_ (wp_true h3) <;> zn

/-- `wakePass` at `scc_rt_thr_worker`'s tail, past the store. -/
theorem tail_pass {c3 : Ctl} {tp : BitVec 64} (h3 : WPassC c3) (i : ThrTailW.PN) :
    NodeZ wakePass exe (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (ThrTailW.lenN i) := by
  cases i
  · refine nodeZ_pass hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 0) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 5) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 6) ?_ ?_ ?_ (wp_true h3) <;> zn
  · refine nodeZ_pass hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 8) ?_ ?_ ?_ (wp_true h3) <;> zn

/-- **`wakePass` at every node of the thread worker's run**, its controls
before (`c0`, `c1`) and past (`c2`, `c3`) the store. -/
theorem thrZ_pass {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC c0) (h1 : ¬ WPassC c1)
    (h2 : WPassC c2) (h3 : WPassC c3) : ThrZ wakePass exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_pass hp (sc := ThrTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
    (fun _ _ h => h.1) h0
  head := head_pass hp h0
  wpro _ _ := pro_pass hp (sc := WkTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
    (fun _ _ h => h.1) h1
  wk _ _ := wk_pass hp h1 h2 h3
  unpk _ _ := unpk_pass hp h2 h3
  tail := tail_pass hp h3

/-- **`wakePass` at the child's stub**, before the store. -/
theorem cZ_pass {cW : Ctl} {A B tp sp0 : BitVec 64} (h0 : ¬ WPassC cW) :
    ∀ i, NodeZ wakePass exe (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cLen i) := by
  intro i
  cases i
  · refine nodeZ_pass hp (l := (pfxM ++ ".sp6")) (k0 := 14) ?_ ?_ ?_ (wp_false h0) <;> zn
  · refine nodeZ_pass hp (l := (pfxM ++ ".child9")) (k0 := 0) ?_ ?_ ?_ (wp_false h0) <;> zn

/-- **`wakePass` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakePass`): its controls after the tail call, the `split`,
the `store` and the `unpark`. -/
theorem childThrZ (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ wakePass exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_pass hp (kidC_not T w1 w2) (wc1_not w1 w2) wkC2_pass wkC3_pass

end Inst

end Spike.Lib.A64.Flow.Worker.Wake.Pass
