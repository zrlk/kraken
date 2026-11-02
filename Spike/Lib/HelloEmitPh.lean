/-
**hello.w on AArch64: the worker mid-`write`** (C4,
design (a′)): mid-`write(1, …)` the target worker is at
`print`'s `svc` with `wr 1 = j` bytes out and the source worker at the emit
row's `Pw j`, where `PT1h`'s invariant conjunct (`D.Wi` at the source
worker's control) does not hold. The worker's per-thread relation becomes
`PT1hE := PT1h ∨ EmitPh`; `PT1h` stays frozen. The link `j = wr 1` and the
source's `Pw j` are in the kernel relation (`HelloKRE.Lk`, `EmitR`).

- `EmitPh`: `PT1h`'s conjuncts 2–6 in the print phase, the target worker at
  a system call with `D.Wi` at some control and frames.
- `PT1hE`: `PT1h ∨ EmitPh`; `PT1hE.wi`: its worker in `D.Wi`.
- `PartsE`: `Post` unpacked at `EmitPh` (`HelloW1.PartsH`' twin);
  `post_partsHE`: `Post` at `Q.PT1 = PT1hE D` unpacks at `PartsH` or
  `PartsE`; `PartsH.postE`, `PartsE.post`: reassembly.
- `EmitShape`: at the worker's `write(1, …)` in the
  print phase an emit row whose byte controls `Pw j` are in the print phase
  at print-phase terms.
-/
import Spike.Lib.HelloKRE

namespace Spike.Lib.HelloEmitPh

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh BufV PTermH)
open Spike.Lib.HelloSplit (workerCallH workerRestH)
open Spike.Lib.HelloKRE (EmitCl)

variable {ι : Type}

/-! ## The relation -/

/-- **The source worker's frames mid-`write`** (row 5j-wit-E): none, or
frames `fs0` with the worker's invariant at some control `c0` and the
target state `st`, or, with no frame at `D.Wi`, the frame of `print`'s call
(`u`, `workerRestH`) pushed at a local run from `c0` to the call. With no
byte out the source worker's frame run to the emit row's first byte control
(`EmitShapeF`) starts at `D.Wi` and may enter `print`
(`HelloEmitStep.emitFrS_frameRun`); with bytes out the frames are kept. -/
def EmitFrS (D : WSideH ι) (w : ι) (st : isaLSE2.State) (fs : List TermRun.Frame) : Prop :=
  fs = [] ∨ ∃ c0 fs0, D.Wi w st c0 fs0 ∧
    (fs = fs0 ∨ (fs0 = [] ∧ ∃ c', LocalRunS helloSrc c0 c' ∧ c'.term = workerCallH ∧
      fs = [⟨"u", workerRestH, c'.env, [], .unit⟩]))

/-- **A term of `print`'s or `printL`'s body** followed down
(`PrintSvc.printTerms`): `PTermT` without the prelude's terms. -/
def PTermE (e : Expr) : Prop :=
  e ∈ PrintSvc.printTerms PrintSrc.printBody ∨ e ∈ PrintSvc.printTerms HelloPrintSrcPub.printLBodyP

/-- **The worker mid-`write`**: `PT1h`'s conjuncts 2–6 in the print phase
(no type variables; the print phase with the buffer's `BufV`, a
print-phase term and no promise or no `emit` ahead; the promise facts), the target worker at a system call
with `D.Wi` at some control and frames (for the facts `WCompatH` reads off
`D.Wi` at the target state) and decoding to `write(1, buf, n)`. The source
worker's control is the emit row's `Pw j`, in `HelloKRE.Lk`. `D.Wi` at the
source worker's control is not excluded: `EmitPh` with it is `PT1h`
(`EmitPh.pt1h`), and `post_partsHE` returns `PartsE` only without it. The
source worker's frames are `EmitFrS` and its term is `print`'s or
`printL`'s (`PTermE`; for the placement, row 5j-wit-E,
`HelloPlE.hplE_of`). -/
def EmitPh (D : WSideH ι) (w : ι) (_tm : Memory) (sm : WeakMem.Memory) (t1 : Thread isaLSE2)
    (s1 : TermRun.TTh) : Prop :=
  (∃ c fs, D.Wi w t1.st c fs) ∧ abi.atSys t1.st = true ∧
    (∃ buf n, decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n)) ∧ s1.σs = [] ∧
    (PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∧ BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) sm ∧
      PTermH s1 ∧ (s1.promises = [] ∨ HelloW1.NoEmit (D.cw w) s1)) ∧
    s1.promises.length ≤ 1 ∧
    (∀ k ∈ s1.promises, D.S w ≤ k ∧ ∃ m : WeakMem.Msg, sm[k]? = some m ∧ (D.cw w).val = .loc m.loc 0) ∧
    t1.prom.Nodup ∧ EmitFrS D w t1.st s1.stack ∧ PTermE s1.term

/-- **The worker's per-thread relation with its `write`**: `PT1h`, or
mid-`write` (`EmitPh`). -/
def PT1hE (D : WSideH ι) (w : ι) (tm : Memory) (sm : WeakMem.Memory) (t1 : Thread isaLSE2)
    (s1 : TermRun.TTh) : Prop :=
  PT1h D w tm sm t1 s1 ∨ EmitPh D w tm sm t1 s1

/-- **`EmitPh` with `D.Wi` at the source worker's control is `PT1h`.** -/
theorem EmitPh.pt1h {D : WSideH ι} {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (h : EmitPh D w tm sm t1 s1) (hW : D.Wi w t1.st (Ctl.of s1) s1.stack) :
    PT1h D w tm sm t1 s1 :=
  let ⟨_, _, _, hσ, hph, hl, hk, hn, _⟩ := h
  ⟨hW, hσ, .inl hph, hl, hk, hn⟩

/-- `EmitPh`'s source frames (`EmitFrS`). -/
theorem EmitPh.frS {D : WSideH ι} {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (h : EmitPh D w tm sm t1 s1) : EmitFrS D w t1.st s1.stack :=
  h.2.2.2.2.2.2.2.2.1

/-- `EmitPh`'s source term (`PTermE`). -/
theorem EmitPh.termE {D : WSideH ι} {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (h : EmitPh D w tm sm t1 s1) : PTermE s1.term :=
  h.2.2.2.2.2.2.2.2.2

/-- **`PT1hE`'s worker is in `D.Wi`** at some control and frames (`PT1h`'s
at the source worker's, `EmitPh`'s at some). -/
theorem PT1hE.wi {D : WSideH ι} {w : ι} {tm : Memory} {sm : WeakMem.Memory} {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (h : PT1hE D w tm sm t1 s1) : ∃ c fs, D.Wi w t1.st c fs :=
  h.elim (fun h => ⟨_, _, h.1⟩) (fun h => h.1)

/-- **The link with no byte out and the worker at `PT1h`** (`HelloKRE.lk_wr0`
at `PT1h`'s `D.Wi`; the spawn's link, L-ex (ii)). -/
theorem lk_pt1h {D : WSideH ι} {w : ι} {t : Cfg} {s : TermRun.Cfg} (h0 : t.2.wr 1 = 0)
    (hp : ∀ t1 s1, t.1.threads[1]? = some t1 → s.ths[1]? = some s1 → PT1h D w t.1.mem s.mem t1 s1) :
    HelloKRE.Lk D w t s :=
  HelloKRE.lk_wr0 h0 fun t1 s1 h1 h2 => (hp t1 s1 h1 h2).1

/-! ## `Post` unpacked mid-`write` -/

/-- **`Post`'s parts mid-`write`** (`PartsH` with `EmitPh` for `PT1h`). -/
structure PartsE (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg)
    (t0 t1 : Thread isaLSE2) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat)
    (oc : Option (Nat × Nat)) : Prop where
  th : t.1.threads = #[t0, t1]
  ths : s.ths = #[s0, s1]
  core : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
    (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) t.1.mem t0 t1 s.mem s0 s1 ts
    tp sp
  preC : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views
  pt0 : Q.PT0 w t.1.mem s.mem t0 s0
  pt1 : EmitPh D w t.1.mem s.mem t1 s1
  prot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp
  kr : Q.KR w t s

variable {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout}

/-- **`Post` unpacks at `PT1hE`**: at `PartsH`, or mid-`write` at `PartsE`
without `D.Wi` at the source worker's control (with it, `EmitPh` is `PT1h`). -/
theorem post_partsHE (hpt1 : Q.PT1 = PT1hE D) {t : Cfg} {s : TermRun.Cfg} (h : Q.Post Λ t s) :
    (∃ w t0 t1 s0 s1 ts tp sp oc, PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) ∨
      ∃ w t0 t1 s0 s1 ts tp sp oc, PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc ∧
        ¬ D.Wi w t1.st (Ctl.of s1) s1.stack := by
  obtain ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, hth, hs, hcore, hp0, hp1, oc, hprot⟩, hkr⟩ := h
  simp only [WakeRel.PTw, ite_true] at hp0
  simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1] at hp1
  rcases hp1 with hp1 | hp1
  · exact .inl ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hth, hs, hcore, hp0.1, hp0.2, hp1, hprot, hkr⟩
  · by_cases hW : D.Wi w t1.st (Ctl.of s1) s1.stack
    · exact .inl ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, hth, hs, hcore, hp0.1, hp0.2, hp1.pt1h hW, hprot, hkr⟩
    · exact .inr ⟨w, t0, t1, s0, s1, ts, tp, sp, oc, ⟨hth, hs, hcore, hp0.1, hp0.2, hp1, hprot, hkr⟩, hW⟩

variable {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **`Post` from `PartsH` at `PT1hE`.** -/
theorem PartsH.postE (hpt1 : Q.PT1 = PT1hE D) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    Q.Post Λ t s := by
  refine ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, h.th, h.ths, h.core, ?_, ?_, oc, h.prot⟩, h.kr⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨h.preC, h.pt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1]
    exact .inl h.pt1

/-- **`Post` from `PartsE` at `PT1hE`.** -/
theorem PartsE.post (hpt1 : Q.PT1 = PT1hE D) (h : PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    Q.Post Λ t s := by
  refine ⟨w, ⟨t0, t1, s0, s1, ts, tp, sp, h.th, h.ths, h.core, ?_, ?_, oc, h.prot⟩, h.kr⟩
  · simp only [WakeRel.PTw, ite_true]
    exact ⟨h.preC, h.pt0⟩
  · simp only [WakeRel.PTw, Nat.one_ne_zero, ite_false, hpt1]
    exact .inr h.pt1

/-- `PartsE`'s source worker is thread 1's. -/
theorem PartsE.s1_get (h : PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : s.ths[1]? = some s1 := by
  rw [h.ths]; rfl

/-- `PartsE`'s target worker is thread 1's. -/
theorem PartsE.t1_get (h : PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : t.1.threads[1]? = some t1 := by
  rw [h.th]; rfl

/-! ## The emit row's shape -/

/-- **The source worker at control `c1`** (term and environment; its
stack, promises and views kept). -/
def atC (s1 : TermRun.TTh) (c1 : Ctl) : TermRun.TTh := { s1 with term := c1.term, env := c1.env }

/-- **At the worker's `write(1, buf, n)` in the
print phase there is an emit row at the source worker's frames**: at
`D.Wi w st (Ctl.of s1) s1.stack` with the source worker `s1` in the print
phase, byte controls `Pw` and refusal controls `Qw` with the source's local
run into `Pw 0` and the emit row's clauses (`EmitCl`). (The print phase at
the byte controls is not asked: it follows from the source's dynamics,
`HelloEmitSrc.emit_byte_src`.) -/
def EmitShape (D : WSideH ι) : Prop :=
  ∀ w st s1 buf n, D.Wi w st (Ctl.of s1) s1.stack → abi.atSys st = true →
    decode abi.nrs (abi.nr st) (abi.arg st) = some (.write 1 buf n) →
    PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 →
    ∃ Pw Qw, (∃ c', LocalRun helloSrc (Ctl.of s1) c' ∧ Pw 0 c') ∧ EmitCl D w st s1.stack buf n Pw Qw

/-- info: 'Spike.Lib.HelloEmitPh.post_partsHE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_partsHE

end Spike.Lib.HelloEmitPh
