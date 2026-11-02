/-
**hello.w's spawned child at the concrete control fact** (x86-64; the twin of
`Spike/Lib/A64HelloWorkerSegR.lean`): the child's source controls and `print`'s `write` obligation, at
`Z := ZR exe kp` (`Z0 ∧ RelWS`, `Spike/Lib/X64HelloZR.lean`), `print`'s predicate `PrW` and the call's control
`KcW` (`Spike/Lib/X64HelloWorkerCallSrc.lean`), on the packet's five source words `w0 .. w4` (the slice's three,
the flag's, main's `ThreadId`). The source controls are the child's tail call (`kidH`), `wcP` at `print`'s call,
`wcR` at the store, `cS1` past it, `cS2` past the `unpark`.

- `kidH`, `cS1`, `cS2`; `kidH_notPass`.
- `SvcX`: `print`'s `write` segment generic in an extra fragment, the child's `hsvc` premise.
- `cN_ctl`: every state of `print`'s nodes at a call holds the source at `Pc` or `Qc`; `wcR_hZPc`: `print`'s
  nodes (`hZP`) at `PrintF.cN`, from `Z.wcR_hZP` at `Print.N`'s pcs and offsets.

## Differences from the AArch64 version

- The source is x86-64's reading `X64HelloSrc.helloSrc`, its controls `X64HelloSplit`'s.
- `SvcX` is stated at `wc_worker`'s call node `Body.wCall` over `wkJ … sp` for every region `Rw` of
  `wc_worker` (`sp := Rw.addr 0`, the frame `wkJ` reads `%rbp` against), with `PrintF.CallFC Rw` among its
  premises; `print`'s region is `R'.lo ≤ -40`, `16 ≤ R'.hi` (no alignment premise), its `write` node `.sys`
  (AArch64 `.svc`), its nodes `PrintF.cN … (-96) σC` (the return address in cell `-96`).
- `seg_childR` and `SvcX.toR` are not twinned: the child's segment is composed from
  `Child.seg_childStubSX`, `Child.seg_thrWorkerSX` and `Wk.seg_wcWorkerSX` where it is consumed.
  `SegTCS.toZHR` is not twinned either.
- `cN_ctl` and `wcR_hZPc` are new: x86-64's `Z.wcR_hZP` is stated at `Print.N`'s pcs and offsets for any
  invariant whose controls are at no `unpark` binding, AArch64's at `PrintF.cN` directly.
-/
import Spike.Lib.X64HelloWorkerTCSX
import Spike.Lib.X64HelloZR
import Spike.Lib.X64HelloWorkerCallSrc

namespace Spike.Lib.X64.Flow.Worker.Hello.SegR

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (wcP wcR)
open Spike.Lib.X64HelloWorkerCallSrc (PrW KcW)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.X64.Flow.Worker.Hello.Wk (wkJ)
open Spike.Lib.X64.Flow.Worker.Hello.Pass (HPassC)
open Spike.Lib.X64.Flow.Worker.Hello.Z (ZR NotUnpk)
open Scc.Cert.Rt.X64 (Lays endOf)
open SccCode (helloCells)

/-- **The child's control after the spawn**: `tail worker [] (var "a") []` on the packet's five words. -/
def kidH (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.tail "worker" [] (.var "a") [], [("a", T, [w0, w1, w2, w3, w4])], none⟩

/-- The control past the store: `d` bound, at the `unpark`. -/
def cS1 (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wcR w0 w1 w2 w3 w4).env, none⟩

/-- The control past the `unpark`: `ret ()`. -/
def cS2 (w0 w1 w2 w3 w4 : TermRun.Word) : Ctl :=
  ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: (cS1 w0 w1 w2 w3 w4).env, none⟩

theorem kidH_notPass (T : Ty) (w0 w1 w2 w3 w4 : TermRun.Word) : ¬ HPassC (kidH T w0 w1 w2 w3 w4) := by
  simp [HPassC, kidH, Spike.Lib.WorkerSrc.wkUnpark]

/-- `cS1` is past the store (`wcR_hZW`'s `h1`). -/
example (w0 w1 w2 w3 w4 : TermRun.Word) : HPassC (cS1 w0 w1 w2 w3 w4) := .inl rfl

/-- `cS2` is past the store (`wcR_hZW`'s `h2`). -/
example (w0 w1 w2 w3 w4 : TermRun.Word) : HPassC (cS2 w0 w1 w2 w3 w4) := .inr rfl

/-- **`print`'s `write` segment, generic in an extra fragment** (the child segment's `hsvc` premise): for every
region `Rw` of `wc_worker` and every call state of its call node on the packet's words, for every fragment `Xf`
that holds at `print`'s `write` node, the `write` is a segment inside `NNZP SysW1 (ZR ∧ Xf)` from the `sys` node
to `n5`. `Xf := True` is the `ZR`-only premise (`Wk.seg_wcWorkerSX`'s `hsvc`); a lifted fragment `ZR ∧ X`
instantiates `Xf` at `X`'s `print` nodes. Not produced here: it is carried as `ChildPrem.hsvc` up to the
child's segment's callers. -/
def SvcX (exe : _root_.Executable) (endPc : Int64) (kp : Nat) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (F : MachineData → Prop) (w : Words) (tp : BitVec 64)
    (w0 w1 w2 w3 w4 : TermRun.Word) (n m : Nat) : Prop :=
  ∀ rbp ra (Rw : Region) fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -40 → 16 ≤ R'.hi →
    FStable R' F' → (∀ m, F' m → F m) →
    PrintF.CallFC Rw (Body.wCall (_root_.Executable.labels exe).label
      (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (Rw.addr 0)) (KcW w0 w1 w2 w3 w4 n m)) F' →
    ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ (wcP w0 w1 w2 w3 w4) w rbp ra tp (Rw.addr 0))
      (KcW w0 w1 w2 w3 w4 n m)).J σC c → CallToI helloSrc c cE fr →
    ∀ Xf : Frag isa, NodeW Xf (fun _ _ => False) exe endPc R' F'
      (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m) (fun _ => PrW w0 w2 n m) (-96) σC
        .sys) →
    SegTC (NNZP SysW1 exe endPc (fun s c => ZR exe kp s c [fr] ∧ Xf s c)) helloSrc lbl (ms [fr])
      (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) (-96) σC .sys))
      (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label (fun _ => PrW w0 w2 n m)
        (fun _ => PrW w0 w2 n m) (-96) σC .n5))

/-- **`print`'s states at a call hold the source at `Pc` or `Qc`**: every node's invariant names a count `k`
with the source at `Pc σC k` or (a refused `write`) at `Qc σC k`. -/
theorem cN_ctl {lab : Label → Int64} {Pc Qc : AS → Nat → Ctl → Prop} {ko : Int} {σC σ : AS} {c : Ctl}
    {i : Print.PN} (h : (PrintF.cN lab Pc Qc ko σC i).J σ c) : ∃ k, Pc σC k c ∨ Qc σC k c := by
  obtain ⟨h, -⟩ := h
  have r2 : ∀ {k : Nat} {r : BitVec 64}, PrintA.RC2 (σC.regs.get64 .rsi).toNat (Pc σC) (Qc σC) k r c →
      ∃ k, Pc σC k c ∨ Qc σC k c := fun h => h.elim (fun h => ⟨_, .inl h.2.2⟩) fun h => ⟨_, .inr h.2⟩
  have r1 : ∀ {k : Nat} {r : BitVec 64}, PrintA.RC1 (σC.regs.get64 .rsi).toNat (Pc σC) (Qc σC) k r c →
      ∃ k, Pc σC k c ∨ Qc σC k c := fun h => h.elim (fun h => ⟨_, .inl h.2⟩) r2
  have r0 : ∀ {k : Nat} {r : BitVec 64}, PrintA.RC0 (σC.regs.get64 .rsi).toNat (Pc σC) (Qc σC) k r c →
      ∃ k, Pc σC k c ∨ Qc σC k c := fun h => h.elim (fun h => ⟨_, .inl h.2⟩) r1
  cases i
  · exact ⟨0, .inl h.1⟩
  · obtain ⟨k, -, hk⟩ := h; exact ⟨k, .inl hk⟩
  · obtain ⟨k, -, hk⟩ := h; exact ⟨k, .inl hk⟩
  · obtain ⟨k, -, -, hk⟩ := h; exact ⟨k, .inl hk⟩
  · obtain ⟨k, -, -, hk⟩ := h; exact ⟨k, .inl hk⟩
  · obtain ⟨⟨k, -, -, hk⟩, -⟩ := h; exact ⟨k, .inl hk⟩
  · obtain ⟨k, -, hk⟩ := h; exact r0 hk
  · obtain ⟨k, -, hk⟩ := h; exact r1 hk
  · obtain ⟨k, -, hk⟩ := h; exact r1 hk
  · obtain ⟨k, -, hk⟩ := h; exact r2 hk
  · obtain ⟨k, -, hk⟩ := h; exact r2 hk
  · obtain ⟨k, -, -, -, hk⟩ := h; exact ⟨_, .inl hk⟩
  · obtain ⟨k, -, -, -, hk⟩ := h; exact ⟨_, .inl hk⟩
  · obtain ⟨k, hk⟩ := h; exact ⟨k, .inr hk⟩
  · exact ⟨_, .inl h.2.2⟩

/-- **`print`'s nodes** (`hZP`) at a call's `PrintF.cN`, whose sources at `Pc` and `Qc` are at no `unpark`
binding (`Z.wcR_hZP` at `Print.N`'s pcs and offsets, which `PrintF.cN`'s share). -/
theorem wcR_hZPc {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} {endPc : Int64}
    (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp) {fr : TermRun.Frame} {R : Region}
    {F : MachineData → Prop} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) {Pc Qc : AS → Nat → Ctl → Prop}
    {ko : Int} {σC : AS} (hP : ∀ k c, Pc σC k c → NotUnpk c) (hQ : ∀ k c, Qc σC k c → NotUnpk c)
    (i : Print.PN) :
    NodeZA (fun s c => ZR exe kp s c [fr]) exe endPc R F
      (PrintF.cN (_root_.Executable.labels exe).label Pc Qc ko σC i) (PrintF.FA.blkN i) := by
  have h := Z.wcR_hZP hp hend (fr := fr) (F := F) hR hlo hhi (c0 := ⟨.ret .unit, [], none⟩)
    (rbp0 := σC.regs.rbp.toBitVec) (ra := σC.slot ko)
    (J := (PrintF.cN (_root_.Executable.labels exe).label Pc Qc ko σC i).J)
    (fun σ c hJ => (cN_ctl hJ).elim fun k h => h.elim (hP k c) (hQ k c)) i
  cases i <;> exact h

end Spike.Lib.X64.Flow.Worker.Hello.SegR

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.kidH_notPass' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegR.kidH_notPass

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SegR.wcR_hZPc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SegR.wcR_hZPc
