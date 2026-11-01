/-
**hello.w's child entry at main's clone, with the flag's locative** (AArch64): `SegRP.childPX cS` (`childP` with word
3 `cS`'s locative, `seg_childPPXc`'s entry) at main's clone, the
twins of `SegR.childP_of_cloneX` / `childP_of_cloneR1X` given word 3 at `cS` (`hw3`: the spawn's argument binding,
`HelloSpawnR.words_clone`'s `hcw`).

- `childPX_of_cloneX`: `childPX cS` from `ChildPrem` at main's registers.
- `childPX_of_cloneR1X`: at the record's `r1 = r1Of L.lab` (`StackB.childB_r1Of`).
-/
import Spike.Lib.A64HelloChildX
import Spike.Lib.A64HelloWorkerSegRPX

namespace Spike.Lib.A64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words childN pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **The child after main's `clone` is in `childPX cS`, at main's registers** (`childP_of_cloneX` with word 3 at
`cS`'s locative, `hw3`), once `ChildPrem` holds there. -/
theorem childPX_of_cloneX {lbl' : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) (hal : (r1.lo + r1.size) % 16 = 0) (hsz : 272 ≤ r1.size)
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) {cS : WeakMem.Address} (hw3 : w3.val = .loc cS 0) :
    ∃ (th : Thread isaLSE2) (tls : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧ (th.st.st.1.regs.getXReg .X3).toNat = tls ∧
      (ChildPrem exe endPc kp lbl' ms
          (DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
          (wordsX th) (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)) w0 w1 w2 w3 w4 n m →
        Hello.SegRP.childPX exe endPc kp lbl' ms cS (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st
          (kidH T w0 w1 w2 w3 w4) []) := by
  obtain ⟨htop, hlo0, hsz', hR, hal', -, hhi'⟩ :=
    Spike.Lib.A64.Rt.childStub_region (lo := -272) htop hal (by decide) (by omega)
  obtain ⟨th, tls, hth, hcall, h3, hA⟩ := clonePreH_child_atX hp hend h hX htop hlo0 hsz' (kidH T w0 w1 w2 w3 w4)
  refine ⟨th, tls, hth, hcall, h3, fun hpr => ⟨rfl, ⟨childR (r1.lo + r1.size) (-272),
    _, _, _, _, T, w0, w1, w2, w3, w4, n, m⟩, ⟨FStable.dframe _ _, hR, hal', by show (-272 : Int) ≤ -272; decide,
    hhi'⟩, hpr, hw3, hA⟩⟩

/-- **`childPX_of_cloneX` at the record's handed stack** `r1Of L.lab` (inside the stack pool: `childB_r1Of`). -/
theorem childPX_of_cloneR1X {lbl' : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (L : RuntimeLayout) (hsub : (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).Sub L.Λ.stackPool)
    {Λ : Scc.Sem.Layout} {r0 : Scc.Sem.Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : ClonePreH pfxM Λ r0 (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) {cS : WeakMem.Address} (hw3 : w3.val = .loc cS 0) :
    let top := (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).lo + (Spike.Lib.A64.Rt.PreChild.r1Of L.lab).size
    ∃ (th : Thread isaLSE2) (tls : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone top tls) ∧ (th.st.st.1.regs.getXReg .X3).toNat = tls ∧
      (ChildPrem exe endPc kp lbl' ms
          (DFrame (childR top (-272)) (childAfter abi t.2 0 th top tls).st.st.1)
          (wordsX th) (BitVec.ofNat 64 tls) (BitVec.ofNat 64 top) w0 w1 w2 w3 w4 n m →
        Hello.SegRP.childPX exe endPc kp lbl' ms cS (childAfter abi t.2 0 th top tls).st (kidH T w0 w1 w2 w3 w4) []) :=
  have hB := Spike.Lib.A64.HelloPh.StackB.childB_r1Of L hsub
  childPX_of_cloneX (lbl' := lbl') (ms := ms) (kp := kp) hp hend h hX hB.1 hB.2.1 hB.2.2 T w0 w1 w2 w3 w4 n m hw3

end Spike.Lib.A64.Flow.Worker.Hello.SegR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.childPX_of_cloneX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.childPX_of_cloneX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.childPX_of_cloneR1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.childPX_of_cloneR1X
