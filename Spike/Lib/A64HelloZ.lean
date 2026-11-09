/-
**hello.w's worker segment's concrete control fact** (rows
5j-k `PassZ` and C4 `ZStoreOk`, AArch64): the fragment `ZH exe kp` the
worker's frame-aware segment carries (`helloDR`'s `hseg`, at
`Z := fun _ => ZH exe kp`), its two consumers' premises (`passZ_ZH`,
`zStoreOk_ZH`), and its value at every node of `seg_wcWorkerS`
(`hz`, `hZE`, `hZC`, `hZP`, `hZA`, `hZu`, `hZW`, `hZU`) and of the thread
worker's and the child's segments, decided per pc on hello.w's listing.

`ZH` is `Z0` (pc and control facts, at each node from its pc, `NodeZ`) and,
on no frame, wake's `SysSafe` (no `write` at all), which the segment keeps
from wake's `NN` leaves (`seg_wcWorkerS`'s fragment): a `NodeZ` fact cannot
see the registers, and the store phase's `svc`s (`futex`, `exit`) are told
from `print`'s `write` only by `x8`.

- `Z0 exe kp s c fs`: the store points agree (`Pass.helloPass`); on no frame
  off `scc_rt_abort_write`'s system calls (`AbW`); on a frame the control at
  no `unpark` binding (`NotUnpk`, `printF_callTCS`'s `hZu`); the pc not the
  program's end (`hhalt1`).
- `abWRuns`, `abW_pcIn`, `offChk`, `off_at`: `AbW`'s pcs as runs, a decided
  check that a node's are none of them.
- `endOff_run`, `endOff_pcIn`: a pc of a run of the listing is not its end.
- `node0F`, `node0T`, `nodeFr`, `pro0`: `Z0` at a node on no frame (before /
  past the store), on a frame, at a prologue; `pc_past`, `node0T2`, `nodeFr2`:
  a node across a return label.
- `wc_hz`, `wc_hZE`, `wc_hZC`, `wc_hZP`, `wc_hZA`, `wc_hZu`, `wc_hZW`,
  `wc_hZU`: `seg_wcWorkerS`'s premises at `Z := Z0 exe kp`.
- `thr_hz`, `thr_hZE`, `thr_hZT`, `child_hZc`: the thread worker's and the
  child's (`seg_thrWorkerH`, `seg_childStubH`).
-/
import Spike.Lib.A64HelloPass
import Spike.Lib.HelloPassH
import Spike.Lib.HelloW1StoreZ

namespace Spike.Lib.A64.Flow.Worker.Hello.Z

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap labelIdx run)
open Spike.Lib.A64.PcRuns (PcIn runsOk inRuns pcIn_iff)
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE thrJE thrJ cN childN childJ cLen pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (helloPassT HPassC helloPass PB passChk pass_at pass_of_b pass_off
  nodeZ_nil hello_runsOk)
open SccCode (helloProg)

set_option linter.unusedSimpArgs false

/-- **The control at no `unpark` binding.** -/
def NotUnpk (c : Ctl) : Prop := ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e

/-- **The worker segment's pc and control facts**: the store points agree;
on no frame off `scc_rt_abort_write`'s system calls; on a frame at no
`unpark` binding; off the program's end. -/
def Z0 (exe : _root_.Executable) (kp : Nat) : FragS isaLSE2 := fun s c fs =>
  helloPass s c fs ∧ (fs = [] → ¬ AbW exe s) ∧ (fs ≠ [] → NotUnpk c) ∧ s.st.2 ≠ endOf exe helloProg kp

/-- **The worker segment's concrete control fact**: `Z0`, and on no frame
no `write` (`seg_wcWorkerS`'s fragment). -/
def ZH (exe : _root_.Executable) (kp : Nat) : FragS isaLSE2 := fun s c fs =>
  Z0 exe kp s c fs ∧ (fs = [] → SysSafe s)

/-! ## The consumers' premises -/

/-- **Row 5j-k: `PassZ` at `ZH`.** -/
theorem passZ_ZH {exe : _root_.Executable} {kp : Nat} : HelloPassH.PassZ helloPassT (ZH exe kp) :=
  fun _ _ _ h => h.1.1

/-- **Row C4: `ZStoreOk` at `ZH`**: on no frame off the abort-write calls,
and a `write` there is no safe call. -/
theorem zStoreOk_ZH {ι : Type} {exe : _root_.Executable} {kp : Nat} :
    HelloW1Store.ZStoreOk exe (fun _ : ι => ZH exe kp) := by
  intro _ s c h _ _
  refine ⟨h.1.2.1 rfl, fun buf n ha hd => ?_⟩
  rcases h.2 rfl ha _ hd with h' | ⟨h', -⟩
  · cases h'
  · exact h' 1 buf n rfl

/-- **`printF_callTCS`'s `hZu` at `Z0`.** -/
theorem z0_unpk {exe : _root_.Executable} {kp : Nat} :
    ∀ (fr : TermRun.Frame) s c, Z0 exe kp s c [fr] → NotUnpk c :=
  fun _ _ _ h => h.2.2.1 (List.cons_ne_nil _ _)

/-! ## Runs of the listing -/

/-- **`scc_rt_abort_write`'s two system calls.** -/
def abWRuns : List (Label × Nat × Nat) :=
  [(".L16_scc_rt_abort_write.0_entry", 7, 8), ("scc_rt_abort_write_exit", 0, 1)]

theorem abWRuns_ok : runsOk helloProg abWRuns = true := by decide +kernel

/-- `AbW` is a pc of `abWRuns`. -/
theorem abW_pcIn {exe : _root_.Executable} {s : State} (he : s.exe = exe) (h : AbW exe s) : PcIn abWRuns s := by
  rcases h with h | h
  · refine ⟨(".L16_scc_rt_abort_write.0_entry", 7, 8), by simp [abWRuns], 7, Nat.le_refl _, by decide, ?_⟩
    rw [he, h]
    simp only [Spike.Lib.A64.Abort.pcSvc, Spike.Lib.A64.Abort.write, ofNat4_succ, ofNat4_zero]
  · refine ⟨("scc_rt_abort_write_exit", 0, 1), by simp [abWRuns], 0, Nat.le_refl _, by decide, ?_⟩
    rw [he, h]
    exact (ofNat4_zero _).symm

/-- **None of the instructions `k0 .. k0 + len` after `l` is in `A`**,
decided on the listing. -/
def offChk (A : List (Label × Nat × Nat)) (l : Label) (k0 len : Nat) : Bool :=
  (labelIdx helloProg l).isSome && decide (k0 + len ≤ (run helloProg l).length) &&
    (List.range len).all fun j => !inRuns helloProg A l (k0 + j)

theorem passChk_run {l : Label} {k0 len : Nat} {b : Bool} (h : passChk l k0 len b = true) :
    (labelIdx helloProg l).isSome = true ∧ k0 + len ≤ (run helloProg l).length := by
  simp only [passChk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
include hp

/-- **Off `A` at a decided pc.** -/
theorem off_at {A : List (Label × Nat × Nat)} (hok : runsOk helloProg A = true) {l : Label} {k0 len : Nat}
    (hchk : offChk A l k0 len = true) {s : State} {k : Nat} (hk : k < len) (he : s.exe = exe)
    (hs : s.st.2 = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0) + Int64.ofNat (4 * k)) :
    ¬ PcIn A s := by
  simp only [offChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hchk
  obtain ⟨⟨hl, hlen⟩, hall⟩ := hchk
  rw [Int64.add_assoc, ← Int64.ofNat_add, ← Nat.mul_add] at hs
  rw [pcIn_iff hp hok he hl (by omega) hs, hall k hk]
  exact Bool.false_ne_true

/-- **A pc of a run of the listing is not its end.** -/
theorem endOff_run {l : Label} {k : Nat} (hl : (labelIdx helloProg l).isSome = true)
    (hk : k < (run helloProg l).length) {q : Int64}
    (hs : q = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) : q ≠ endOf exe helloProg kp := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hl
  rw [Spike.Lib.A64.PcRuns.label_add_eq hp hi (by omega)] at hs
  obtain ⟨ins, z, hc⟩ := Spike.Lib.A64.PcRuns.run_cell hp hi hk
  obtain ⟨d, hd, -⟩ := Spike.Lib.A64.PcRuns.run_getElem? hi hk
  have hlt : i + 1 + k < helloProg.length := (List.getElem?_eq_some_iff.mp hd).1
  intro he
  have heq : Kraken.Executable.addrOf exe (kp + (i + 1 + k)) =
      Kraken.Executable.addrOf exe (helloProg.length + kp) := by
    rw [← hs, he]; rfl
  have hsz := Kraken.Executable.sizeBefore_eq_of_addrOf_eq exe heq
  have hlt' := Spike.Lib.A64.PcRuns.sizeBefore_lt (show kp + (i + 1 + k) < helloProg.length + kp by omega) hc
  have hz := hv.instr_size _ ins z hc
  omega

/-- **A pc of runs of the listing is not its end.** -/
theorem endOff_pcIn {A : List (Label × Nat × Nat)} (hok : runsOk helloProg A = true) {s : State}
    (he : s.exe = exe) (h : PcIn A s) : s.st.2 ≠ endOf exe helloProg kp := by
  obtain ⟨q, hq, j, -, hj, hs⟩ := h
  simp only [runsOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hl, hlen⟩ := hok q hq
  rw [he] at hs
  exact endOff_run hp hl (by omega) hs

/-- **`Z0` at a node on no frame, before the store**: its pc decided, its
controls not past the store. -/
theorem node0F {n : ND} {len : Nat} {l : Label} {k0 : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : passChk l k0 len false = true) (hab : offChk abWRuns l k0 len = true)
    (hb : ∀ σ c, n.J σ c → ¬ HPassC c) : NodeZ (fun s c => Z0 exe kp s c []) exe n len := by
  intro s σ c k hk he hs hJ
  have hs' := hpc ▸ hs
  obtain ⟨hl, hlen⟩ := passChk_run hchk
  refine ⟨pass_off (pass_at hp hchk hk he hs') fun _ => hb σ c hJ,
    fun _ h => off_at hp abWRuns_ok hab hk he hs' (abW_pcIn he h), fun h => absurd rfl h,
    endOff_run hp hl (k := k0 + k) (by omega) (by rw [hs', ofNat4_add])⟩

/-- **`Z0` at a node on no frame, past the store.** -/
theorem node0T {n : ND} {len : Nat} {l : Label} {k0 : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : passChk l k0 len true = true) (hab : offChk abWRuns l k0 len = true)
    (hb : ∀ σ c, n.J σ c → HPassC c) : NodeZ (fun s c => Z0 exe kp s c []) exe n len := by
  intro s σ c k hk he hs hJ
  have hs' := hpc ▸ hs
  obtain ⟨hl, hlen⟩ := passChk_run hchk
  refine ⟨Pass.pass_on (pass_at hp hchk hk he hs') rfl (hb σ c hJ),
    fun _ h => off_at hp abWRuns_ok hab hk he hs' (abW_pcIn he h), fun h => absurd rfl h,
    endOff_run hp hl (k := k0 + k) (by omega) (by rw [hs', ofNat4_add])⟩

/-- **`Z0` at a node on a frame** (before the store), its controls at no
`unpark` binding. -/
theorem nodeFr {fr : TermRun.Frame} {n : ND} {len : Nat} {l : Label} {k0 : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hchk : passChk l k0 len false = true) (hu : ∀ σ c, n.J σ c → NotUnpk c) :
    NodeZ (fun s c => Z0 exe kp s c [fr]) exe n len := by
  intro s σ c k hk he hs hJ
  have hs' := hpc ▸ hs
  obtain ⟨hl, hlen⟩ := passChk_run hchk
  refine ⟨pass_off (pass_at hp hchk hk he hs') fun h => absurd h (List.cons_ne_nil _ _),
    fun h => absurd h (List.cons_ne_nil _ _), fun _ => hu σ c hJ,
    endOff_run hp hl (k := k0 + k) (by omega) (by rw [hs', ofNat4_add])⟩

/-- **A node's pc past a return label**: the instruction `k` (`a ≤ k`) of a
node at `l + k0` is the instruction `k - a` after the label `m` right after
its first `a` (`labelGap`). -/
theorem pc_past {n : ND} {l m : Label} {k0 a k : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hg : labelGap helloProg l m (k0 + a) = true) (hka : a ≤ k) :
    n.pc + Int64.ofNat (4 * k) =
      (_root_.Executable.labels exe).label m + Int64.ofNat (4 * 0) + Int64.ofNat (4 * (k - a)) := by
  rw [hpc, label_labelGap hp hg, ofNat4_zero, Int64.add_assoc, Int64.add_assoc, ← Int64.ofNat_add,
    ← Int64.ofNat_add]
  exact congrArg (_ + Int64.ofNat ·) (by omega)

/-- **`node0T` across a return label**: its first `a` instructions `k0 ..`
after `l`, the rest from the label `m` right after them (`labelGap`), as
`A64WakePass.nodeZ_pass2`. -/
theorem node0T2 {n : ND} {len : Nat} {l m : Label} {k0 a : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hg : labelGap helloProg l m (k0 + a) = true)
    (hchk1 : passChk l k0 a true = true) (hchk2 : passChk m 0 (len - a) true = true)
    (hab1 : offChk abWRuns l k0 a = true) (hab2 : offChk abWRuns m 0 (len - a) = true)
    (hb : ∀ σ c, n.J σ c → HPassC c) : NodeZ (fun s c => Z0 exe kp s c []) exe n len := by
  intro s σ c k hk he hs hJ
  by_cases hka : k < a
  · exact node0T hp hpc hchk1 hab1 hb s σ c k hka he hs hJ
  · exact node0T hp (n := { n with pc := _ }) rfl hchk2 hab2 hb s σ c (k - a) (by omega) he
      (hs.trans (pc_past hp hpc hg (by omega))) hJ

/-- **`nodeFr` across a return label**, as `node0T2`. -/
theorem nodeFr2 {fr : TermRun.Frame} {n : ND} {len : Nat} {l m : Label} {k0 a : Nat}
    (hpc : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k0))
    (hg : labelGap helloProg l m (k0 + a) = true)
    (hchk1 : passChk l k0 a false = true) (hchk2 : passChk m 0 (len - a) false = true)
    (hu : ∀ σ c, n.J σ c → NotUnpk c) : NodeZ (fun s c => Z0 exe kp s c [fr]) exe n len := by
  intro s σ c k hk he hs hJ
  by_cases hka : k < a
  · exact nodeFr hp hpc hchk1 hu s σ c k hka he hs hJ
  · exact nodeFr hp (n := { n with pc := _ }) rfl hchk2 hu s σ c (k - a) (by omega) he
      (hs.trans (pc_past hp hpc hg (by omega))) hJ

/-- **`Z0` at a prologue** (`fn`'s label is its stack check's, `sc`), its
fifteen instructions, the control not past the store. -/
theorem pro0 {fn sc : Label} (hg : labelGap helloProg fn sc 0 = true) (hchk : passChk sc 0 15 false = true)
    (hab : offChk abWRuns sc 0 15 = true) {J : AS → Ctl → Prop} (hb : ∀ σ c, J σ c → ¬ HPassC c) :
    ∀ (s : State) σ c (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label fn + Int64.ofNat (4 * k) → J σ c → Z0 exe kp s c [] :=
  fun s σ c k hk he hs hJ => node0F hp (n := ⟨(_root_.Executable.labels exe).label sc, ⟨0, []⟩, J⟩) (k0 := 0)
    (ofNat4_zero _).symm hchk hab hb s σ c k hk he (by rw [hs, label_labelGap hp hg, ofNat4_zero]) hJ

/-- Closes a node's side goals: its pc, the decided checks. -/
local macro "zc" : tactic =>
  `(tactic| first
    | (simp only [Unpark.N, Unpark.pcSvc, HelloTail.N, HelloTail.pcBl, HThrTail.N, HThrHead.tN, cN, childN,
        Body.wN, Body.wCall, PrintF.cN, ND.withTp, PrintF.FA.N, Spike.Lib.A64.PrintA.N, PrintF.pcSvc,
        Spike.Lib.A64.PrintA.pcSvc, ofNat4_succ, ofNat4_zero]; done)
    | decide +kernel)

omit hv hp in
/-- A pinned control before the store. -/
theorem pinF {J : AS → Ctl → Prop} {c0 : Ctl} (hc : ∀ σ c, J σ c → c = c0) (h0 : ¬ HPassC c0) :
    ∀ σ c, J σ c → ¬ HPassC c := fun σ c h => hc σ c h ▸ h0

omit hv hp in
/-- A pinned control past the store. -/
theorem pinT {J : AS → Ctl → Prop} {c0 : Ctl} (hc : ∀ σ c, J σ c → c = c0) (h0 : HPassC c0) :
    ∀ σ c, J σ c → HPassC c := fun σ c h => hc σ c h ▸ h0

/-- Closes a node's control goal from its pinned control (`h0`). -/
local macro "zp " h0:term : tactic => `(tactic| first | exact pinF (fun _ _ h => h.1) $h0 | exact pinF (fun _ _ h => h.1.1) $h0 | exact pinF (fun _ _ h => h) $h0 | exact pinF (fun _ _ h => h.elim fun _ h => h.1) $h0 | exact pinT (fun _ _ h => h.1) $h0 | exact pinT (fun _ _ h => h.1.1) $h0 | exact pinT (fun _ _ h => h) $h0)

/-! ## `seg_wcWorkerS`'s premises -/

theorem wc_hz {c0 : Ctl} {w : Words} {x29 ra tp : BitVec 64} (h0 : ¬ HPassC c0) :
    ∀ (s : State) σ c (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat (4 * k) →
      wcJE c0 w x29 ra tp σ c → Z0 exe kp s c [] :=
  pro0 hp (sc := ".L20_wc_worker.stack_check") (by decide +kernel) (by decide +kernel) (by decide +kernel)
    fun _ _ h => h.1 ▸ h0

theorem wc_hZE {c0 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {Pr : AS → Nat → Ctl → Prop} (h0 : ¬ HPassC c0) :
    NodeZ (fun s c => Z0 exe kp s c []) exe
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e) Body.wkE.length :=
  node0F hp (l := ".L20_wc_worker.0_entry") (k0 := 0) (by zc) (by zc) (by zc) (by zp h0)

theorem wc_hZC {J Kc : AS → Ctl → Prop} (hK : ∀ σ c, Kc σ c → ¬ HPassC c) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (Body.wCall (_root_.Executable.labels exe).label J Kc) 1 :=
  node0F hp (l := "scc_rt_print") (k0 := 0) (by zc) (by zc) (by zc) fun σ c h => hK σ c h.2

omit hv hp in
/-- `print`'s nodes' controls are `Pc`'s or `Qc`'s. -/
theorem print_u {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS} (hP : ∀ k c, Pc σC k c → NotUnpk c)
    (hQ : ∀ k c, Qc σC k c → NotUnpk c) (i : PrintF.PN) :
    ∀ σ c, (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i).J σ c → NotUnpk c := by
  have r2 : ∀ {len0 k r c}, Spike.Lib.A64.PrintA.RC2 len0 (Pc σC) (Qc σC) k r c → NotUnpk c := by
    intro _ _ _ _ h; rcases h with ⟨-, -, h⟩ | ⟨-, h⟩
    · exact hP _ _ h
    · exact hQ _ _ h
  have r1 : ∀ {len0 k r c}, Spike.Lib.A64.PrintA.RC1 len0 (Pc σC) (Qc σC) k r c → NotUnpk c := by
    intro _ _ _ _ h; rcases h with ⟨-, h⟩ | h
    · exact hP _ _ h
    · exact r2 h
  have r0 : ∀ {len0 k r c}, Spike.Lib.A64.PrintA.RC0 len0 (Pc σC) (Qc σC) k r c → NotUnpk c := by
    intro _ _ _ _ h; rcases h with ⟨-, h⟩ | h
    · exact hP _ _ h
    · exact r1 h
  intro σ c h
  obtain ⟨h, -⟩ := h
  cases i
  · exact hP _ _ h.1
  · obtain ⟨k, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨⟨k, -, -, h⟩, -⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, h⟩ := h; exact r0 h
  · obtain ⟨⟨k, -, h⟩, -⟩ := h; exact r0 h
  · obtain ⟨k, -, h⟩ := h; exact r1 h
  · obtain ⟨k, -, h⟩ := h; exact r1 h
  · obtain ⟨⟨k, -, h⟩, -⟩ := h; exact r1 h
  · obtain ⟨k, -, h⟩ := h; exact r2 h
  · obtain ⟨k, -, h⟩ := h; exact r2 h
  · obtain ⟨k, -, -, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, -, -, -, h⟩ := h; exact hP _ _ h
  · obtain ⟨k, h⟩ := h; exact hQ _ _ h
  · obtain ⟨-, -, h⟩ := h; exact hP _ _ h

set_option maxHeartbeats 1600000 in
/-- **`print`'s nodes** (`hZP`), its predicates' controls at no `unpark`
binding. -/
theorem wc_hZP {fr : TermRun.Frame} {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS}
    (hP : ∀ k c, Pc σC k c → NotUnpk c) (hQ : ∀ k c, Qc σC k c → NotUnpk c) (i : PrintF.PN) :
    NodeZ (fun s c => Z0 exe kp s c [fr]) exe (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i)
      (PrintF.FA.lenN i) := by
  have hu := print_u (exe := exe) hP hQ i
  cases i
  · exact nodeFr hp (l := "scc_rt_print") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.0_entry") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.1_loop") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.1_loop") (k0 := 4) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 1) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 5) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 6) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 13) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.2_write") (k0 := 14) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 6) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.3_chk2") (k0 := 7) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.4_chk3") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.4_chk3") (k0 := 4) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.5_adv") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr hp (l := ".L9_scc_rt_print.6_fail") (k0 := 0) (by zc) (by zc) hu
  · exact nodeFr2 hp (l := ".L9_scc_rt_print.7_done") (m := ".L9_scc_rt_print.x12") (k0 := 0) (a := 3)
      (by zc) (by zc) (by zc) (by zc) hu

/-- **The abort path** (`hZA`), the abort's controls at no `unpark`
binding. -/
theorem wc_hZA {fr : TermRun.Frame} {c' : Ctl} (hu : NotUnpk c') {s : State} (he : s.exe = exe)
    (h : PcIn abortRuns s) : Z0 exe kp s c' [fr] :=
  ⟨pass_off ⟨fun hs => absurd hs (Pass.abort_off hp he h), nofun⟩
      fun h => absurd h (List.cons_ne_nil _ _),
    fun h => absurd h (List.cons_ne_nil _ _), fun _ => hu, endOff_pcIn hp (by decide +kernel) he h⟩

/-- **`wc_worker`'s tail** (`hZW`): before the store at `cw`, past it at
`c1`, `c2`. -/
theorem wc_hZW {cw c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} (hw : ¬ HPassC cw) (h1 : HPassC c1)
    (h2 : HPassC c2) (i : HelloTail.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp i)
      (HelloTail.lenN i) := by
  cases i
  · exact node0F hp (l := ".L20_wc_worker.sp4") (k0 := 0) (by zc) (by zc) (by zc) (by zp hw)
  · exact node0F hp (l := ".L20_wc_worker.sp4") (k0 := 2) (by zc) (by zc) (by zc) (by zp hw)
  · exact node0T hp (l := ".L20_wc_worker.sp4") (k0 := 3) (by zc) (by zc) (by zc) (by zp h1)
  · exact node0T hp (l := ".L20_wc_worker.sp4") (k0 := 4) (by zc) (by zc) (by zc) (by zp h1)
  · exact nodeZ_nil
  · exact node0T2 hp (l := ".L20_wc_worker.sp6") (m := ".L20_wc_worker.x7") (k0 := 0) (a := 3)
      (by zc) (by zc) (by zc) (by zc) (by zc) (by zc) (by zp h2)

set_option maxHeartbeats 800000 in
/-- **`scc_rt_unpark`'s nodes** (`hZU`), past the store. -/
theorem wc_hZU {c1 c2 : Ctl} {B x29 ra tp : BitVec 64} (h1 : HPassC c1) (h2 : HPassC c2) (i : Unpark.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp i)
      (Unpark.lenN i) := by
  cases i
  · exact node0T hp (l := "scc_rt_unpark") (k0 := 0) (by zc) (by zc) (by zc) (by zp h1)
  · exact node0T hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 0) (by zc) (by zc) (by zc) (by zp h1)
  · exact node0T hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 3) (by zc) (by zc) (by zc) (by zp h1)
  · exact node0T hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 4) (by zc) (by zc) (by zc) (by zp h2)
  · exact node0T hp (l := ".L11_scc_rt_unpark.0_entry") (k0 := 9) (by zc) (by zc) (by zc) (by zp h2)
  · exact node0T hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 0) (by zc) (by zc) (by zc) (by zp h2)
  · exact node0T hp (l := ".L11_scc_rt_unpark.1_wake") (k0 := 11) (by zc) (by zc) (by zc) (by zp h2)
  · exact node0T2 hp (l := ".L11_scc_rt_unpark.1_wake") (m := ".L11_scc_rt_unpark.x4") (k0 := 12) (a := 4)
      (by zc) (by zc) (by zc) (by zc) (by zc) (by zc) (by zp h2)
  · exact node0T2 hp (l := ".L11_scc_rt_unpark.2_done") (m := ".L11_scc_rt_unpark.x5") (k0 := 0) (a := 3)
      (by zc) (by zc) (by zc) (by zc) (by zc) (by zc) (by zp h2)

/-! ## The thread worker's and the child's premises -/

theorem thr_hz {c0 : Ctl} {w : Words} {tp sp0 : BitVec 64} (h0 : ¬ HPassC c0) :
    ∀ (s : State) σ c (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "scc_rt_thr_worker" + Int64.ofNat (4 * k) →
      thrJE c0 w tp sp0 σ c → Z0 exe kp s c [] :=
  pro0 hp (sc := HThrTail.pfx0 ++ ".stack_check") (by decide +kernel) (by decide +kernel) (by decide +kernel)
    fun _ _ h => h.1 ▸ h0

theorem thr_hZE {c0 : Ctl} {w : Words} {tp sp0 : BitVec 64} {L : Ctl → Ctl → Prop} (h0 : ¬ HPassC c0) :
    NodeZ (fun s c => Z0 exe kp s c []) exe
      (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ c0 w tp sp0) L .e) HThrHead.thE.length :=
  node0F hp (l := HThrTail.pfx0 ++ ".0_entry") (k0 := 0) (by zc) (by zc) (by zc) (by zp h0)

theorem thr_hZT {c3 : Ctl} {tp : BitVec 64} (h3 : HPassC c3) (i : HThrTail.PN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i)
      (HThrTail.lenN i) := by
  cases i
  · exact node0T hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 0) (by zc) (by zc) (by zc) (by zp h3)
  · exact node0T hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 5) (by zc) (by zc) (by zc) (by zp h3)
  · exact node0T hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 6) (by zc) (by zc) (by zc) (by zp h3)
  · exact node0T hp (l := HThrTail.pfx0 ++ ".sp0") (k0 := 8) (by zc) (by zc) (by zc) (by zp h3)

theorem child_hZc {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (h0 : ¬ HPassC cW) (i : Child.CN) :
    NodeZ (fun s c => Z0 exe kp s c []) exe (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i) (cLen i) := by
  cases i
  · exact node0F hp (l := pfxM ++ ".sp6") (k0 := 26) (by zc) (by zc) (by zc) (by zp h0)
  · exact node0F hp (l := pfxM ++ ".child13") (k0 := 0) (by zc) (by zc) (by zc) (by zp h0)

end Inst

end Spike.Lib.A64.Flow.Worker.Hello.Z
