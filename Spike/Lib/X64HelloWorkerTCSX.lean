/-
**hello.w's `wc_worker` at depth with a fact at every landing pair, on x86-64** (the twin of
`Spike/Lib/A64HelloWorkerTCSX.lean`): the worker from its label to the tail's exit at `[]`, `print` a source call
at `[fr]` (`PrintF.printF_callTCSX`, `Spike/Lib/X64HelloPrintTCSX.lean`), every landing pair in a fragment `XL`
(`Spike/Lib/HelloSegTCSX.lean`).

The landings follow from `Z` (`hZX : Z ⊆ XL`) except two: `print`'s return landing at `[fr]` (`hXR`) and the tail's
exit at `[]` (`hXE`, `HelloTail.E`'s pairs, not in `Z`). The flat pieces are lifted by `SegTCSX.ofTC_seq` (the
prologue, no `XL` at its exit) and `SegTCSX.ofTC` (the `.entry` blocks, their exit the call node, in `XL` by `hZC`
and `hZX`; the tail, its exit by `hXE`).

- `nodeZA_at0`: a node's fact at its first cell is one at the node's states.
- `Hello.Wk.seg_wcWorkerSX`: `wc_worker` over `SegTCSX` at the fragment `SH exe endPc Z` and landings `XL`.

## Differences from the AArch64 version

- The `.entry` block is three nodes (`Body.wN`'s `.e`, `.mul`, `.e2`: `imulq` leaves the flags undefined), so the
  call state is `Body.wkC lab σ fl` for the multiply's flags `fl`: `hcall` and `hdone` are asked at every `fl`
  (`hcall` at the `.e2` edge, after `fl` is known), and `hZE` is the three nodes' `NodeZA`
  (`X64HelloZR.wcR_hZE`'s shape). `hZC` is a `NodeZA` at the call node's block `Print.x0` (`wcR_hZC`), read at
  its first cell (`nodeZA_at0`) where A64 asks `NodeW`.
- The region is `[-176, 8)` from the entry `%rsp` (A64: `[-192, 0)`, 16-byte aligned): the `.entry` blocks ask
  `-144`, the tail (`HelloTail.seg_wkTailUNN`) `-136`, and `print`'s call at `-96` asks `-96 - 8 + -72`. The
  entry `%rsp` is the region's base (`Wake.Labels.At.rspAt`), so the tail's ghost `sp` and `hZW`/`hZU` are at
  `R.addr 0`; `hZU` is `HelloTail.seg_wkTailUNN`'s (`CallerF`).
- The stack limit is a `LimOk` at `tp + 8` (as `X64WakeWorkerLabelsNNA`); the count register is `%rsi`
  (`Body.wkC_rsi_lt`, `hm`); `print`'s callee obligations are `printF_callTCSX`'s (`hsvc` at `R'.lo ≤ -40`,
  `hZP`/`hXR` at `-72`, `hZA` at `-24`, all with `16 ≤ hi`, at `cN … (-96) σC`).
- `print`'s return lands at `.x17` at the offsets knowing `%rsp` alone (`HelloTail.oP`), the tail's entry
  `HelloTail.N .e` claimed back with `%rbp` (`WaitLoop.At.rbpOf`); the kept words are checked against
  `Body.wkSl_keep`.
- The exit is `HelloTail.E` (A64 rewrites to `Wake.WkTailW.E` through `tailE_eq`).
-/
import Spike.Lib.X64HelloThrTCSX
import Spike.Lib.X64HelloPrintTCSX
import Spike.Lib.X64HelloWorkerTCS
import Spike.Lib.X64HelloWorkerSeg
import Spike.Lib.X64HelloWorkerSegNN
import Spike.Lib.X64HelloWkTailNN
import Spike.Lib.X64WakeWorkerLabelsNNA

set_option linter.unusedSimpArgs false

namespace Spike.Lib.X64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Worker
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64HelloSegTCSX
open Spike.Lib.X64.Flow.Ret0 (StOk LimOk)
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words wcJE)
open Scc.Cert.Rt.X64 (Lays endOf)

section WorkerTCSX

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z XL : FragS isa}

omit [Kraken.Executable.ValidLayout exe] in
/-- **A node's fact at its first cell** is one at the node's states (`NodeZA.toW` for a block of any length). -/
theorem nodeZA_at0 {Z0 : Frag isa} {n : ND} {blk : List (Directive × Nat)} (hne : 0 < blk.length)
    (h : NodeZA Z0 exe endPc R F n blk) : ∀ s c, At exe endPc R F n s c → Z0 s c :=
  fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => by
    have h0 := (h s σ c he hn hdc hpc hA hD hJ 0 hne s.st.1 hA (DFrame.refl _ _)).1
    rw [cellOff_zero, ← hpc] at h0
    exact h0

set_option maxHeartbeats 800000 in
open Classical in
/-- **`wc_worker`'s `.entry` blocks inside `SH exe endPc Z`**: `.e`, the flag multiply and `.e2`, from the body's
first node to `print`'s call node, at `[]`; `Z` inside `XL` (`hZX`). -/
theorem seg_wcEntrySX (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {c0 : Ctl} {w : Words} {rbp ra tp : BitVec 64} {Pr : AS → Nat → Ctl → Prop} {Kc : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -144) (hhi : 8 ≤ R.hi)
    (hcall : ∀ σ fl, wkJ c0 w rbp ra tp (R.addr 0) σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Kc (Body.wkC (_root_.Executable.labels exe).label σ fl) c')
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .e) Body.wkE1 ∧
      NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .mul)
        [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .e2) Body.wkE2)
    (hZC : NodeZA (fun s c => Z s c []) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) Spike.Lib.X64.Print.x0)
    (hZX : ∀ s c fs, Z s c fs → XL s c fs) :
    SegTCSX (SH exe endPc Z) XL p lbl ms
      ((At exe endPc R F (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .e)).at [])
      ((At exe endPc R F
        (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc)).at []) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := wkJ c0 w rbp ra tp (R.addr 0)
  let nE := Body.wN lab J0 Pr .e
  let nM := Body.wN lab J0 Pr .mul
  let n2 := Body.wN lab J0 Pr .e2
  let nC := Body.wCall lab J0 Kc
  have hZC0 : ∀ s c, At exe endPc R F nC s c → Z s c [] := nodeZA_at0 (by simp [Spike.Lib.X64.Print.x0]) hZC
  have hXC : ∀ s c, At exe endPc R F nC s c → XL s c [] := fun s c hA => hZX _ _ _ (hZC0 s c hA)
  have hE : SegTC (NNZ exe endPc fun s c => Z s c []) p lbl (ms []) (At exe endPc R F nE) (At exe endPc R F nM) :=
    (seg_ndNNA (N := fun _ : Unit => nM) (E := fun y : Empty => y.elim) (blk := Body.wkE1) (by simp [Body.wkE1])
      Body.wkE1_ok (by decide) hF hR hlo hhi (wkE1Code hp hend)
      (fun σ c hJ => ?_) hZE.1).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim
  case refine_1 =>
    refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, ?_⟩⟩
    · show lab ".Lwc_worker.entry" + 36 = (arun lab Body.wkE1 ⟨lab ".Lwc_worker.entry", Body.oB, σ⟩).pc
      rw [Body.wkE1_run]
    · show SO.le Body.oB (arun lab Body.wkE1 ⟨lab ".Lwc_worker.entry", Body.oB, σ⟩).so = true
      rw [Body.wkE1_run]; rfl
    · rfl
  have hM : SegTC (NNZ exe endPc fun s c => Z s c []) p lbl (ms []) (At exe endPc R F nM) (At exe endPc R F n2) :=
    (Wake.Child.flag_ndNNA (N := fun _ : Unit => n2) (E := fun y : Empty => y.elim) (fi := Body.wkMul) rfl
      (by decide) hF (wkMulCode hp hend)
      (fun σ c hJ fl => ?_) (NodeZA.toW hZE.2.1)).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim
  case refine_1 =>
    obtain ⟨σ0, hJ, rfl⟩ := hJ
    refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ0, fl, hJ, rfl⟩⟩
    · show lab ".Lwc_worker.entry" + 40 = lab ".Lwc_worker.entry" + 36 + Int64.ofNat 4
      rw [Int64.add_assoc]; rfl
    · rfl
  have h2E : SegTC (NNZ exe endPc fun s c => Z s c []) p lbl (ms []) (At exe endPc R F n2) (At exe endPc R F nC) :=
    (seg_ndNNA (N := fun _ : Unit => nC) (E := fun y : Empty => y.elim) (blk := Body.wkE2) (by simp [Body.wkE2])
      Body.wkE2_ok (by decide) hF hR hlo hhi (wkE2Code hp hend) (fun σ c hJ => ?_) hZE.2.2).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨y, _⟩ => y.elim
  case refine_1 =>
    obtain ⟨σ0, fl, hJ0, rfl⟩ := hJ
    obtain rfl := hJ0.1
    obtain ⟨c', hr, hK'⟩ := hcall σ0 fl hJ0
    refine ⟨c', hr, .inl ⟨(), ?_, ?_, ⟨σ0, c, fl, hJ0, (Body.wkC_eq _ _ _).symm⟩, ?_⟩⟩
    · simp only [nC, n2, Body.wCall, Body.wN]; rw [Body.wkE2_run]
    · simp only [nC, n2, Body.wCall, Body.wN]; rw [Body.wkE2_run]; rfl
    · show Kc (arun lab Body.wkE2 ⟨lab ".Lwc_worker.entry" + 40, Body.oB, _⟩).σ c'
      rw [← Body.wkC_eq]; exact hK'
  exact SegTCSX.ofTC ((hE.seq hM).seq h2E) (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2) hXC

open Classical in
/-- **`print`'s call from `wc_worker` inside `SH exe endPc Z`**: `printF_callTCSX` with `print` at `[fr]`, from the
call node back to the tail's `.x17` node at `[]`; `Z` inside `XL` (`hZX`), `print`'s return landing in `XL`
(`hXR`). -/
theorem seg_wcCallSX (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {rbp ra tp : BitVec 64}
    {Pr Qa : AS → Nat → Ctl → Prop} {Kc : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -176) (hhi : 8 ≤ R.hi)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcallI : ∀ σ c, Kc σ c → ∃ cE fr, CallToI p c cE fr)
    (hP0 : ∀ σ c cE fr, Kc σ c → CallToI p c cE fr → Pr σ 0 cE)
    (hdone : ∀ σ0 fl c cE fr c', wkJ c0 w rbp ra tp (R.addr 0) σ0 c0 →
      Kc (Body.wkC (_root_.Executable.labels exe).label σ0 fl) c → CallToI p c cE fr →
      Pr (Body.wkC (_root_.Executable.labels exe).label σ0 fl)
        ((Body.wkC (_root_.Executable.labels exe).label σ0 fl).regs.get64 .rsi).toNat c' →
      FrameRun p (c', [fr]) (cw, []))
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -40 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      SegTC (NNZP SysW1 exe endPc (fun s c => Z s c [fr])) p lbl (ms [fr])
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC .sys))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC .n5)))
    (hZC : NodeZA (fun s c => Z s c []) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) Spike.Lib.X64.Print.x0)
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      ∀ i, NodeZA (fun s c => Z s c [fr]) exe endPc R' F'
        (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC i) (PrintF.FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi → FStable RA FA →
      (∀ m, FA m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) FA →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr → ∀ k c', Qa σC k c' → AbortObl (fun s c => Z s c [fr]) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s)
    (hZu : ∀ fr s c, Z s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hZX : ∀ s c fs, Z s c fs → XL s c fs)
    (hXR : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      ∀ s c', At exe endPc R' F' (PrintF.cE (_root_.Executable.labels exe).label Pr Qa (-96) σC .ret) s c' →
        XL s c' [fr]) :
    SegTCSX (SH exe endPc Z) XL p lbl ms
      ((At exe endPc R F
        (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc)).at [])
      ((At exe endPc R F
        ⟨(HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) .e).pc,
          HelloTail.oP,
          (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) .e).J⟩).at []) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := wkJ c0 w rbp ra tp (R.addr 0)
  let nC := Body.wCall lab J0 Kc
  let nT := HelloTail.N lab cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) .e
  let nP : ND := ⟨nT.pc, HelloTail.oP, nT.J⟩
  have hZC0 : ∀ s c, At exe endPc R F nC s c → Z s c [] := nodeZA_at0 (by simp [Spike.Lib.X64.Print.x0]) hZC
  have hXC : ∀ s c, At exe endPc R F nC s c → XL s c [] := fun s c hA => hZX _ _ _ (hZC0 s c hA)
  show SegTCSX (SH exe endPc Z) XL p lbl ms ((At exe endPc R F nC).at []) ((At exe endPc R F nP).at [])
  refine (PrintF.printF_callTCSX (nC := nC) (Pc := Pr) (Qc := Qa) (Zc := fun fr s c => Z s c [fr])
    (N' := fun _ : Unit => nP) (E' := fun y : Empty => y.elim) hp hend SccCode.hello_abort hR hF
    (by show R.lo ≤ -96 - 8 + -72; omega) (by show (-96 : Int) - 8 + 16 ≤ R.hi; omega)
    (by show ((-96 : Int) - 8) % 8 = 0; decide)
    (printCode hp hend (c0 := c0) (rbp0 := rbp) (ra := ra)) (printEntry hp) rfl (fun fr => hK _)
    (fun σ c ⟨⟨σ0, c0', fl, hJ0, hσ⟩, _⟩ => hσ ▸ Body.wkC_rsi_lt lab σ0 fl (by rw [hJ0.2.2.2.1]; exact hm))
    (fun s c hA => nnzS ⟨at_nn (n := nC)
      (fun s he hn => (printCode hp hend (c0 := c0) (rbp0 := rbp) (ra := ra)).e s he hn) (by decide) s c hA,
      hZC0 s c hA⟩) hXC
    (fun _ _ _ h1 h2 => ⟨h1, h2, fun h => absurd h (List.cons_ne_nil _ _)⟩)
    (fun fr s c h => hZX _ _ _ h) hXR hZu (fun σ c hJ => hcallI σ c hJ.2)
    (fun σ c cE fr hJ hCT => hP0 σ c cE fr hJ.2 hCT) hsvc hZP hZA habt ?_).mono_post ?_
  · rintro σC c cE fr σR c' ⟨⟨σ0, c0', fl, hJ0, rfl⟩, hKc⟩ hCT hbp hfs hP hsl
    obtain rfl := hJ0.1
    refine ⟨cw, hdone σ0 fl c cE fr c' hJ0 hKc hCT hP, .inl ⟨(), ?_, ?_, ?_⟩⟩
    · show lab ".Lwc_worker.x17" = Int64.ofBitVec ((Body.wkC lab σ0 fl).slot (-96))
      rw [Body.wkC_ra lab σ0 fl (hgap hp)]
      exact (int64_ofBitVec_toBitVec _).symm
    · show SO.le HelloTail.oP ⟨-96 + 8, []⟩ = true; decide
    · obtain ⟨-, -, -, -, -, h48, h56, h8, h0, htp0, hbp0⟩ := hJ0
      obtain ⟨k8, k0, k48, k56⟩ := Body.wkSl_keep lab σ0
      have hk : ∀ k, -88 ≤ k → k < 8 → k % 8 = 0 → σR.slot k = Body.wkSl lab σ0 k := fun k h1 h2 h3 => by
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, nC, Body.wCall]; omega),
          Body.wkC_slot]
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hk _ (by decide) (by decide) (by decide), k8, h8]
      · rw [hk _ (by decide) (by decide) (by decide), k0, h0]
      · rw [hk _ (by decide) (by decide) (by decide), k48, h48]
      · rw [hk _ (by decide) (by decide) (by decide), k56, h56]
      · rw [hfs, Body.wkC_fs, htp0]
      · have := Body.wkC_rbp lab σ0 fl
        simp only [Reg64s.get64] at hbp this
        rw [hbp, this, hbp0]
  · rintro s c fs ⟨(⟨_, h⟩ | ⟨⟨⟩, -⟩), rfl⟩
    exact ⟨h, rfl⟩

open Classical in
/-- **`wc_worker` at depth inside `SH exe endPc Z`, every landing in `XL`**: the prologue, the `.entry` blocks,
`print`'s call (`printF_callTCSX`, `print` at `[fr]`) and the tail; `Z` inside `XL` (`hZX`), `print`'s return
landing in `XL` at `[fr]` (`hXR`), the tail's exit in `XL` at `[]` (`hXE`). -/
theorem seg_wcWorkerSX (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {rbp ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop} {Kc : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -176) (hhi : 8 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w rbp ra tp σ c → X σ →
      LimOk (ms []) F (tp + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec))
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ fl, wkJ c0 w rbp ra tp (R.addr 0) σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Kc (Body.wkC (_root_.Executable.labels exe).label σ fl) c')
    (hcallI : ∀ σ c, Kc σ c → ∃ cE fr, CallToI p c cE fr)
    (hP0 : ∀ σ c cE fr, Kc σ c → CallToI p c cE fr → Pr σ 0 cE)
    (hdone : ∀ σ0 fl c cE fr c', wkJ c0 w rbp ra tp (R.addr 0) σ0 c0 →
      Kc (Body.wkC (_root_.Executable.labels exe).label σ0 fl) c → CallToI p c cE fr →
      Pr (Body.wkC (_root_.Executable.labels exe).label σ0 fl)
        ((Body.wkC (_root_.Executable.labels exe).label σ0 fl).regs.get64 .rsi).toNat c' →
      FrameRun p (c', [fr]) (cw, []))
    (hK : ∀ fs, (ms fs).K = some Scc.Sem.X64.abi)
    (hsvc : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -40 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      SegTC (NNZP SysW1 exe endPc (fun s c => Z s c [fr])) p lbl (ms [fr])
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC .sys))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hS : StOk (ms []) F (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : XProW (fun s c => Z s c []) (fun _ _ => False) exe endPc R F (ms [])
      ((_root_.Executable.labels exe).label "wc_worker") 80 8 ".Lwc_worker.stk" 5 9 3 6 4 wcPs
      (fun σ c => wcJE c0 w rbp ra tp σ c ∧ X σ))
    (hZE : NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .e) Body.wkE1 ∧
      NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .mul)
        [(Body.wkMul.toDir, 4)] ∧
      NodeZA (fun s c => Z s c []) exe endPc R F
        (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Pr .e2) Body.wkE2)
    (hZC : NodeZA (fun s c => Z s c []) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) Spike.Lib.X64.Print.x0)
    (hZP : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      ∀ i, NodeZA (fun s c => Z s c [fr]) exe endPc R' F'
        (PrintF.cN (_root_.Executable.labels exe).label Pr Qa (-96) σC i) (PrintF.FA.blkN i))
    (hZA : ∀ fr (RA : Region) (FA : MachineData → Prop), RA.OK → RA.lo ≤ -24 → 16 ≤ RA.hi → FStable RA FA →
      (∀ m, FA m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) FA →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr → ∀ k c', Qa σC k c' → AbortObl (fun s c => Z s c [fr]) exe endPc RA FA c')
    (habt : ∀ fr s, s.exe = exe → s.st.2 = (_root_.Executable.labels exe).label Abort.write.exit →
      (ms [fr]).abortAt s)
    (hZu : ∀ fr s c, Z s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e)
    (hZW : ∀ i, NodeZA (fun s c => Z s c []) exe endPc R F
      (HelloTail.NA (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) i)
      (HelloTail.blkN i))
    (hZU : ∀ (R' : Region) (F' : MachineData → Prop),
      CallerF R F (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) .unpk)
        0 (-40) 8 R' F' →
      ∀ rbp1 ra1, Int64.ofBitVec ra1 = (_root_.Executable.labels exe).label ".Lwc_worker.x18" →
      ∀ i, NodeZA (fun s c => Z s c []) exe endPc R' F'
        (Unpark.N (_root_.Executable.labels exe).label c1 c2 w.w5 rbp1 ra1 tp i) (Unpark.blkN i))
    (hZX : ∀ s c fs, Z s c fs → XL s c fs)
    (hXR : ∀ fr (R' : Region) (F' : MachineData → Prop), R'.OK → R'.lo ≤ -72 → 16 ≤ R'.hi → FStable R' F' →
      (∀ m, F' m → F m) →
      PrintF.CallFC R (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc) F' →
      ∀ σC c cE, (Body.wCall (_root_.Executable.labels exe).label (wkJ c0 w rbp ra tp (R.addr 0)) Kc).J σC c →
      CallToI p c cE fr →
      ∀ s c', At exe endPc R' F' (PrintF.cE (_root_.Executable.labels exe).label Pr Qa (-96) σC .ret) s c' →
        XL s c' [fr])
    (hXE : ∀ s c, (∃ y, At exe endPc R F (HelloTail.E c2 rbp ra tp y) s c) → XL s c []) :
    SegTCSX (SH exe endPc Z) XL p lbl ms
      ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w rbp ra tp σ c ∧ X σ⟩).at [])
      (Frag.at (fun s c => ∃ y, At exe endPc R F (HelloTail.E c2 rbp ra tp y) s c) []) := by
  let lab := (_root_.Executable.labels exe).label
  let J0 := wkJ c0 w rbp ra tp (R.addr 0)
  let nE := Body.wN lab J0 Pr .e
  let nC := Body.wCall lab J0 Kc
  let nT := HelloTail.N lab cw c1 c2 w.w4 w.w5 rbp ra tp (R.addr 0) .e
  let nP : ND := ⟨nT.pc, HelloTail.oP, nT.J⟩
  have h2 : SegTCSX (SH exe endPc Z) XL p lbl ms ((At exe endPc R F nE).at []) ((At exe endPc R F nC).at []) :=
    seg_wcEntrySX hp hend hF hR (Int.le_trans hlo (by decide)) hhi hcall hZE hZC hZX
  -- the call, `print` at `[fr]`, back to `.x17` at `[]`
  have h3 : SegTCSX (SH exe endPc Z) XL p lbl ms ((At exe endPc R F nC).at []) ((At exe endPc R F nP).at []) :=
    seg_wcCallSX (cw := cw) (c1 := c1) (c2 := c2) hp hend hF hR hlo hhi hm hcallI hP0 hdone hK hsvc hZC hZP hZA
      habt hZu hZX hXR
  -- the tail, at `[]`
  have h4 : SegTCSX (SH exe endPc Z) XL p lbl ms ((At exe endPc R F nP).at [])
      (Frag.at (fun s c => ∃ y, At exe endPc R F (HelloTail.E c2 rbp ra tp y) s c) []) :=
    (SegTCSX.ofTC (HelloTail.seg_wkTailUNN (Z := fun s c => Z s c []) (ms := ms []) hF hR
      (Int.le_trans hlo (by decide)) hhi hdm ht hev hv htag hevb hvb hc1 (Labels.wkTailCode hp hend) (hK _) hS
      htp4 htu hhu hevu hvu hc2 (Labels.unpkCode hp hend (c0 := cw) (c1 := c1) (B := w.w5) (rbp0 := rbp) (ra := ra)
        (tp := tp)) (Labels.hpentry hp) (Labels.hx18 hp) hZW hZU) (fun _ _ h => nnzS h)
      (fun _ _ h => hZX _ _ _ h.2) hXE).mono_pre fun s c fs ⟨h, e⟩ => ⟨WaitLoop.At.rbpOf h fun σ c hJ => by
        show σ.regs.get64 .rbp = _
        have := hJ.2.2.2.2.2.2
        simp only [Reg64s.get64] at this ⊢
        rw [this, WaitLoop.addr0_sub8], e⟩
  -- the prologue, at `[]`, before the rest
  refine (SegTCSX.ofTC_seq (wc_prologue_segNN (Z := fun s c => Z s c []) (ms := ms []) hp hend hF hR
    (Int.le_trans hlo (by decide)) (by omega)
    (J := fun σ c => (wcJE c0 w rbp ra tp σ c ∧ X σ) ∧ σ.regs.rsp.toBitVec = R.addr 0)
    (nb := nE) rfl (by show SO.le Body.oB (oF 80) = true; decide)
    (fun σ c hJ => ?_) (Wake.Labels.XProW.monoJ hz fun _ _ h => h.1)) (fun _ _ h => nnzS h) (fun _ _ h => hZX _ _ _ h.2)
    ((h2.seq h3).seq h4)).mono_pre fun s c fs ⟨h, e⟩ => ⟨Wake.Labels.At.rspAt h, e⟩
  obtain ⟨⟨hJ, hX⟩, hsp⟩ := hJ
  have hl := hlim σ c hJ hX
  obtain ⟨rfl, hdi, hsi, hdx, hcx, h8, h9, hbp, h0, htp⟩ := hJ
  rw [htp]
  refine ⟨hl.rt, hl.mp, hl.unmapped, fun v hv => ⟨hl.room v hv, fun σ' hr hs => ?_⟩⟩
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdi]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hsi]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hdx]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, hcx]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, h8]
  · rw [hs, hr]; simp [xStSlots, xS1, upd_apply, xFrRegs, hdRegs, Reg64s.set64, Reg64s.get64, h9]
  · rw [hs]; simp [xStSlots, xS1, upd_apply, hbp]
  · rw [hs]; simp [xStSlots, xS1, upd_apply, h0]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, htp]
  · rw [hr]; simp [xFrRegs, hdRegs, Reg64s.set64, hsp]

end WorkerTCSX

end Spike.Lib.X64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcWorkerSX' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcWorkerSX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcEntrySX' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcEntrySX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcCallSX' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Wk.seg_wcCallSX
