/-
**hello.w's worker segment's entry** (row 5j-misc,
AArch64): `helloDR`'s `P` and `hseg` at `Z := fun _ => ZHR exe kp`. The
entry `childP` is the child's stub node at `[]` in some region and frame
condition, at some packet, the segment's premises (`ChildPrem`, one field
per premise) holding there; its segment is `seg_childR`'s
(`SegTCS.toZHR`).

- `ChildPrem`: `seg_childR`'s premises; `ChildD`: its data.
- `childP`, `seg_childP`.
- `SegTCS.of_imp`: a segment under a proposition.
- `childP_of_clone`: at main's `clone` (`ClonePreH`, its handed stack
  `r1`), the child after the clone, at its `tail worker`
  control, is in `childP` once `ChildPrem` holds at the clone's data.

`childP` is inhabited at the real clone state by discharging `ChildPrem`
there (`hWi`, `HelloSpawnR.HWiH`).
-/
import Spike.Lib.A64HelloWorkerSegR
import Spike.Lib.A64HelloChildAt
import Spike.Lib.Rt.A64RtChildPrem

namespace Spike.Lib.A64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloSplit (wcP)
open Spike.Lib.HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE childN pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.A64.Flow.Worker.Hello.Z (ZR ZHR)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

/-- **The child segment's premises** (`seg_childR`'s, one field per premise;
`Spike/Lib/A64HelloWorkerSegR.lean`'s module doc). -/
structure ChildPrem (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) (F : MachineData → Prop) (w : Words) (tp sp0 : BitVec 64)
    (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop where
  hlimT : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      (ms []).rt (tcbA r 8).toNat ∧ (ms []).mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA r 8, 8⟩ v → (v.setWidth 64).toNat ≤ (sp0 - (80 : Int64).toBitVec).toNat
  hlimW : ∀ x29 ra σ c, wcJE (wcP w0 w1 w2 w3 w4) w x29 ra tp σ c →
      σ.regs.SP.toBitVec = sp0 - (80 : Int64).toBitVec →
      (ms []).rt (tcbA σ.regs 8).toNat ∧ (ms []).mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, (ms []).G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat
  hm : w.w2.toNat * 8 < 2 ^ 63
  hx1 : ∀ x29 ra σ, wkJ (wcP w0 w1 w2 w3 w4) w x29 ra tp σ (wcP w0 w1 w2 w3 w4) →
      (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat = printN n m
  hwm : w1.val = .num m
  hm0 : m ≠ 0
  hwn : w2.val = .num n
  hsvc : SvcX exe endPc kp lbl ms F w tp w0 w1 w2 w3 w4 n m
  hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none
  hv : Scc.Sem.ValRep lbl w3.val w.w4.toNat
  htag : ∃ sa, w3.val = .loc sa 0
  hvu : Scc.Sem.ValRep lbl w4.val w.w5.toNat
  /- (`HelloHv012.hv012_of_clone`). The packet's slice words: the buffer locative at
  `x0`, the pair's `m`, `n` at `x2`, `x3`. -/
  hv0 : Scc.Sem.ValRep lbl w0.val w.w0.toNat
  hv1 : Scc.Sem.ValRep lbl w1.val w.w2.toNat
  hv2 : Scc.Sem.ValRep lbl w2.val w.w3.toNat
  hS : StOk (ms []) F exe endPc (w.w5 + 16#64) 1#64
  htp4 : (w.w5 + 16#64).toNat % 4 = 0
  hSx : StOk (ms []) F exe endPc (tp + 24#64) 1#64
  habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s

/-- **The child segment's data**: its region and frame condition, the
machine's six words, the thread pointer, the stack's top, the packet's type
and five words, the slice's bytes and words. -/
structure ChildD where
  R : Region
  F : MachineData → Prop
  w : Words
  tp : BitVec 64
  sp0 : BitVec 64
  T : Ty
  w0 : TermRun.Word
  w1 : TermRun.Word
  w2 : TermRun.Word
  w3 : TermRun.Word
  w4 : TermRun.Word
  n : Nat
  m : Nat

/-- The region's facts (`seg_childR`'s `hF`, `hR`, `hal`, `hlo`, `hhi`). -/
def ChildD.ok (d : ChildD) : Prop :=
  FStable d.R d.F ∧ d.R.OK ∧ d.R.base.toNat % 16 = 0 ∧ d.R.lo ≤ -272 ∧ 0 ≤ d.R.hi

/-- **The worker segment's entry** (`helloDR`'s `P`): at `[]`, the child's
stub node at some data whose premises hold. -/
def childP (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isaLSE2) : FragS isaLSE2 := fun s c fs =>
  fs = [] ∧ ∃ d : ChildD, d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m ∧
    At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4)
      d.w d.tp d.sp0) s c

/-- **A segment under a proposition.** -/
theorem SegTCS.of_imp {I : ISA} {S P Q : FragS I} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide I} {A : Prop} (h : A → SegTCS S p lbl ms P Q) :
    SegTCS S p lbl ms (fun s c fs => A ∧ P s c fs) Q :=
  (Classical.em A).elim (fun ha => (h ha).mono_pre fun _ _ _ h => h.2)
    fun hn => SegTCS.empty fun _ _ _ h => hn h.1

/-- **`helloDR`'s `hseg` at `Z := ZHR`**: from `childP`, never leaving. -/
theorem seg_childP {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.A64.abi) :
    SegTCS (fun s c fs => NNH exe endPc s ∧ ZHR exe kp s c fs) helloSrc lbl ms (childP exe endPc kp lbl ms)
      (fun _ _ _ => False) := by
  refine SegTCS.toZHR ((SegTCS.exists_pre fun d : ChildD => SegTCS.of_imp
    (A := d.ok ∧ ChildPrem exe endPc kp lbl ms d.F d.w d.tp d.sp0 d.w0 d.w1 d.w2 d.w3 d.w4 d.n d.m)
    (P := (At exe endPc d.R d.F (childN pfxM (_root_.Executable.labels exe).label
      (kidH d.T d.w0 d.w1 d.w2 d.w3 d.w4) d.w d.tp d.sp0)).at []) fun ⟨⟨hF, hR, hal, hlo, hhi⟩, h⟩ =>
      seg_childR hp hend hK hF hR hal hlo hhi h.hlimT h.hlimW h.hm h.hx1 h.hwm h.hm0 h.hwn h.hsvc.toR h.hdm h.hv
        h.htag h.hvu h.hS h.htp4 h.hSx h.habt).mono_pre ?_)
  rintro s c fs ⟨rfl, d, hok, hpr, hA⟩
  exact ⟨d, ⟨hok, hpr⟩, hA, rfl⟩

open Kraken.Promising Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover in
open Spike.Lib.HelloPreA (ClonePreH) in
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR) in
/-- **`childP` at the real clone state**: from main's state at its `clone`
(`ClonePreH`; `hX`: its runtime facts pin the executable, its end and no
declarations), the handed stack `r1` (its top below `2 ^ 64`, 16-aligned, at
least 272 bytes), the child after the clone at the control `kidH T w0 .. w4`
is in `childP` at region `childR top (-272)`, its frame condition the child's first memory, the
words `ClonePreH`'s, once `ChildPrem` holds there. -/
theorem childP_of_clone {lbl' : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) (hal : (r1.lo + r1.size) % 16 = 0) (hsz : 272 ≤ r1.size)
    (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) :
    ∃ (th : Thread isaLSE2) (tls sl0 sl1 sl2 sl3 cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
      (ChildPrem exe endPc kp lbl' ms
          (DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
          ⟨BitVec.ofNat 64 sl0, BitVec.ofNat 64 sl1, BitVec.ofNat 64 sl2, BitVec.ofNat 64 sl3,
            BitVec.ofNat 64 cA, BitVec.ofNat 64 meW⟩
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)) w0 w1 w2 w3 w4 n m →
        childP exe endPc kp lbl' ms (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st (kidH T w0 w1 w2 w3 w4) []) := by
  obtain ⟨htop, hlo0, hsz', hR, hal', -, hhi'⟩ :=
    Spike.Lib.A64.Rt.childStub_region (lo := -272) htop hal (by decide) (by omega)
  obtain ⟨th, tls, sl0, sl1, sl2, sl3, cA, meW, hth, hcall, hA⟩ :=
    Child.clonePreH_child_at hp hend h hX htop hlo0 hsz' (kidH T w0 w1 w2 w3 w4)
  refine ⟨th, tls, sl0, sl1, sl2, sl3, cA, meW, hth, hcall, fun hpr => ⟨rfl, ⟨childR (r1.lo + r1.size) (-272),
    _, _, _, _, T, w0, w1, w2, w3, w4, n, m⟩, ⟨FStable.dframe _ _, hR, hal', by show (-272 : Int) ≤ -272; decide, hhi'⟩, hpr, hA⟩⟩

end Spike.Lib.A64.Flow.Worker.Hello.SegR

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.seg_childP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.seg_childP

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.SegR.childP_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.SegR.childP_of_clone
