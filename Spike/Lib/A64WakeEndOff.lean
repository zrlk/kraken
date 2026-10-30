/-
**wake.w's worker never at the program's end** (AArch64):
the pc of every worker node's instructions is not `endOf exe wakeProg kp`,
the pc at which a thread halts (`isaLSE2.exec` is `none` there), decided
per pc on the listing by the same `abChk` checks as `AbOffW`'s (a label's
index and the instruction within its run). With `wakePass` the fragment
`wakeZE exe kp` for `seg_childPreNN`, from which `hhalt1` of
`WakeAssembly.wake_obligations` (the worker's instruction at a system call
runs: `svc` faults) follows. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `endOff_at`: `label l + 4k0 + 4k`, decided by `abChk l k0 len`, `k < len`,
  is not the program's end (`label_add_eq`, distinct sizes before).
- `EndOff exe kp`: the pc is not the program's end.
- `nodeZ_end`, `pro_end`, `head_end`, `wk_end`, `unpk_end`, `tail_end`,
  `thrZ_end`, `cZ_end`: at every node of the child's segments.
- `wakeZE`, `childThrZE`, `cZE`: `wakePass ∧ EndOff`, `seg_childPreNN`'s
  premises.
- `exec_isSome_atSvc`, `hhalt1_of`: at an `svc` off the end the instruction
  runs; for a side inside `NNZ exe endPc (wakeZE exe kp)`.
-/
import Spike.Lib.A64WakeAbOffW
import Spike.Lib.A64SvcFault

namespace Spike.Lib.A64.Flow.Worker.Wake.EndOff

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf labelGap label_labelGap labelIdx run)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN childJ cLen pfxM kidC)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Worker.Wake.Pass (wakePass)
open Spike.Lib.A64.Flow.Worker.Wake.AbOffAt (abChk)
open Spike.Lib.A64.Flow.Worker.Wake.AbOffW (nodeZ_and thrZ_and)

/-- **The pc is not the program's end.** -/
def EndOff (exe : _root_.Executable) (kp : Nat) : Frag isaLSE2 := fun s _ => s.st.2 ≠ endOf exe wakeProg kp

/-- **The worker's fragment with the end**: `wakePass` and off the end. -/
def wakeZE (exe : _root_.Executable) (kp : Nat) : Frag isaLSE2 := fun s c => wakePass s c ∧ EndOff exe kp s c

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeProg kp)
include hp

/-- **Off the end at a decided pc.** -/
theorem endOff_at {l : Label} {k0 len : Nat} (hchk : abChk l k0 len = true) {q : Int64} {k : Nat}
    (hk : k < len) (hs : q = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0) + Int64.ofNat (4 * k)) :
    q ≠ endOf exe wakeProg kp := by
  simp only [abChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨hl, hlen⟩, -⟩ := hchk
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hl
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add,
    Spike.Lib.A64.PcRuns.label_add_eq hp hi (by omega)] at hs
  obtain ⟨ins, z, hc⟩ := Spike.Lib.A64.PcRuns.run_cell hp hi (k := k0 + k) (by omega)
  obtain ⟨d, hd, -⟩ := Spike.Lib.A64.PcRuns.run_getElem? hi (k := k0 + k) (by omega)
  have hlt : i + 1 + (k0 + k) < wakeProg.length := (List.getElem?_eq_some_iff.mp hd).1
  intro he
  have heq : Kraken.Executable.addrOf exe (kp + (i + 1 + (k0 + k))) =
      Kraken.Executable.addrOf exe (wakeProg.length + kp) := by
    rw [← hs, he]; rfl
  have hsz := Kraken.Executable.sizeBefore_eq_of_addrOf_eq exe heq
  have hlt' := Spike.Lib.A64.PcRuns.sizeBefore_lt (show kp + (i + 1 + (k0 + k)) < wakeProg.length + kp by omega) hc
  have hz := hv.instr_size _ ins z hc
  omega

/-- **Off the end at a node** at the instructions `k0 ..` after `l`, decided. -/
theorem nodeZ_end {n : ND} {len : Nat} {l : Label} {k0 : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : abChk l k0 len = true) : NodeZ (EndOff exe kp) exe n len :=
  fun _ _ _ _ hk _ hs _ => endOff_at hp hchk hk (hpc ▸ hs)

/-- **Off the end at a prologue** (`fn`'s label is its stack check's, `sc`). -/
theorem pro_end {fn sc : Label} (hg : labelGap wakeProg fn sc 0 = true) (hchk : abChk sc 0 11 = true)
    {J : AS → Ctl → Prop} :
    ∀ (s : State) σ c (k : Nat), k < 11 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → J σ c → EndOff exe kp s c := by
  intro s σ c k hk _ hs _
  refine endOff_at hp hchk hk ?_
  rw [hs, label_labelGap hp hg]
  simp only [ofNat4_zero]

/-- Closes `nodeZ_end`'s side goals: the node's pc, the decided check. -/
local macro "ze" : tactic =>
  `(tactic| first
    | (simp only [Unpark.N, Unpark.pcSvc, WkTailW.N, WkTailW.pcBl, ThrTailW.N, ThrHeadW.tN, cN, childN,
        ofNat4_succ, ofNat4_zero]; done)
    | decide +kernel)

theorem head_end {c0 c1 : Ctl} {A B tp sp0 : BitVec 64} (i : ThrHeadW.TN) :
    NodeZ (EndOff exe kp) exe
      (ThrHeadW.tN ThrTailW.pfx0 (_root_.Executable.labels exe).label (thrJ c0 A B tp sp0)
        (fun _ c => c = c1) i) (ThrHeadW.lenN i) := by
  cases i
  · refine nodeZ_end hp (l := (ThrTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ <;> ze
  · exact Pass.nodeZ_nil

theorem wk_end {c1 c2 c3 : Ctl} {A B x29 ra tp : BitVec 64} (i : WkTailW.PN) :
    NodeZ (EndOff exe kp) exe
      (WkTailW.N WkTailW.pfx0 (_root_.Executable.labels exe).label c1 c2 c3 A B x29 ra tp i) (WkTailW.lenN i) := by
  cases i
  · refine nodeZ_end hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 0) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 2) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 3) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (WkTailW.pfx0 ++ ".0_entry")) (k0 := 4) ?_ ?_ <;> ze
  · exact Pass.nodeZ_nil
  · refine nodeZ_end hp (l := (WkTailW.pfx0 ++ ".sp1")) (k0 := 0) ?_ ?_ <;> ze

theorem unpk_end {c2 c3 : Ctl} {B x29 ra tp : BitVec 64} (i : Unpark.PN) :
    NodeZ (EndOff exe kp) exe (Unpark.N (_root_.Executable.labels exe).label c2 c3 B x29 ra tp i) (Unpark.lenN i) := by
  cases i
  · refine nodeZ_end hp (l := "scc_rt_unpark") (k0 := 0) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 0) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 3) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 4) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 9) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 0) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 11) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 12) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := ".L11_scc_rt_unpark.2_done") (k0 := 0) ?_ ?_ <;> ze

theorem tail_end {c3 : Ctl} {tp : BitVec 64} (i : ThrTailW.PN) :
    NodeZ (EndOff exe kp) exe (ThrTailW.N ThrTailW.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (ThrTailW.lenN i) := by
  cases i
  · refine nodeZ_end hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 0) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 5) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 6) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (ThrTailW.pfx0 ++ ".sp0")) (k0 := 8) ?_ ?_ <;> ze

/-- **Off the end at every node of the thread worker's run.** -/
theorem thrZ_end {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} :
    ThrZ (EndOff exe kp) exe c0 c1 c2 c3 A B tp sp0 where
  pro := pro_end hp (sc := ThrTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
  head := head_end hp
  wpro _ _ := pro_end hp (sc := WkTailW.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel)
  wk _ _ := wk_end hp
  unpk _ _ := unpk_end hp
  tail := tail_end hp

/-- **Off the end at the child's stub.** -/
theorem cZ_end {cW : Ctl} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (EndOff exe kp) exe (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cLen i) := by
  intro i
  cases i
  · refine nodeZ_end hp (l := (pfxM ++ ".sp6")) (k0 := 14) ?_ ?_ <;> ze
  · refine nodeZ_end hp (l := (pfxM ++ ".child9")) (k0 := 0) ?_ ?_ <;> ze

/-- **`wakeZE` at the spawned child's nodes** (`seg_childPreNN`'s `ThrZ`
premise at `Z := wakeZE exe kp`). -/
theorem childThrZE (T : Ty) (w1 w2 : TermRun.Word) (A B tp sp0 : BitVec 64) :
    ThrZ (wakeZE exe kp) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_and (Pass.childThrZ hp T w1 w2 A B tp sp0) (thrZ_end hp)

/-- **`wakeZE` at the child's stub** (`seg_childPreNN`'s stub premise). -/
theorem cZE (T : Ty) (w1 w2 : TermRun.Word) {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (wakeZE exe kp) exe (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i)
      (cLen i) :=
  fun i => nodeZ_and (Pass.cZ_pass hp (Pass.kidC_not T w1 w2) i) (cZ_end hp i)

end Inst

/-! ## `hhalt1` -/

/-- **At an `svc` off the end the instruction runs** (it faults). -/
theorem exec_isSome_atSvc {s : State} (hv : Kraken.Executable.ValidLayout s.exe)
    (ha : Scc.Sem.A64.atSvc s = true) (hne : s.st.2 ≠ s.endPc) : (isaLSE2.exec s).isSome := by
  obtain ⟨imm, sz, rest, hc⟩ := Spike.Lib.A64.SvcFault.svc_codeAt ha
  have hne' : (s.st.2 == s.endPc) = false := by simpa using hne
  rw [exec_svc (sz := sz) ⟨hv, hne', rest, hc⟩]
  rfl

/-- **`hhalt1`** for a family of states inside `NNZ exe endPc (wakeZE exe kp)`
with `endPc` the program's end. -/
theorem hhalt1_of {ι κ : Type} {Wi : ι → State → κ → Prop} {exe : _root_.Executable}
    [hv : Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat} (hend : endPc = endOf exe wakeProg kp)
    {cOf : κ → Ctl} (hW : ∀ w s c, Wi w s c → NNZ exe endPc (wakeZE exe kp) s (cOf c)) :
    ∀ w s c, Wi w s c → Scc.Sem.A64.abi.atSys s = true → (isaLSE2.exec s).isSome := by
  intro w s c h ha
  obtain ⟨⟨he, hn, -, -⟩, -, hz⟩ := hW w s c h
  exact exec_isSome_atSvc (he ▸ hv) ha (by rw [hn, hend]; exact hz)

end Spike.Lib.A64.Flow.Worker.Wake.EndOff
