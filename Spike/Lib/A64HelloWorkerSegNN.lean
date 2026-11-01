/-
**hello.w's `wc_worker` off the transfer sites** (`WCompatH.noSite`/`sysOkH`, AArch64): the segments of
`Spike/Lib/A64WorkerBody.lean` (`seg_wkBodyT`, `seg_wkT`) and
`Spike/Lib/A64HelloWorkerSeg.lean` (`seg_wcWorkerH`, `seg_wcWorkerHA`) inside
hello's fragment `SegTC (NNZH exe endPc Z)` (`Spike/Lib/A64HelloNN.lean`).

The proofs are the originals', with the leaves off the transfer sites: the
prologue `prologue_seg_ofNN`, the `.0_entry` block `seg_ndNN`, the fenced
`print` `PrintF.printF_callTNN` (its `write` inside `NNZP SysW1`, then
`NNZP.toH`), the tail `HelloTail.seg_wkTailUNN` (wake's `NNZ`, then
`SegTC.toH`), `print`'s abort `seg_jabort4H`. `Z` is asked per node
(`NodeZ`), at the prologue's pcs (`hz`) and along the abort path (`hZA`).

- `SegTC.seq_or`: `SegT.seq_or` over `SegTC`.
- `Body.seg_wkBodyTH`, `Body.seg_wkTH`: the head, the head then the tail.
- `Hello.Wk.wc_prologue_segNN`: `wc_prologue_seg` inside `NNZ`.
- `Hello.Wk.seg_wcWorkerHNN`, `seg_wcWorkerHANN`: `seg_wcWorkerH`,
  `seg_wcWorkerHA` inside `NNZH`.
-/
import Spike.Lib.A64HelloWorkerSeg
import Spike.Lib.A64HelloPrintNN
import Spike.Lib.A64HelloWkTailNN
import Spike.Lib.A64HelloAbortNN

set_option linter.unusedSimpArgs false

namespace Spike.Lib

open CoreLang CoreTerm Kraken.Promising

/-- **Sequencing on one branch inside `S`** (`SegT.seq_or` over `SegTC`). -/
theorem SegTC.seq_or {I : ISA} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide I} {S P Q X Y : Frag I} (h₁ : Spike.Lib.SegTC S p lbl ms P (fun s c => Q s c ∨ X s c))
    (h₂ : Spike.Lib.SegTC S p lbl ms Q Y) : Spike.Lib.SegTC S p lbl ms P (fun s c => Y s c ∨ X s c) := by
  obtain ⟨i₁, hs₁, hw₁, ho₁⟩ := h₁
  obtain ⟨i₂, hs₂, hw₂, ho₂⟩ := h₂
  refine ⟨fun s c => i₁ s c ∨ i₂ s c, fun s c h => .inl (hs₁ s c h), fun s c h => h.elim (hw₁ s c) (hw₂ s c), ?_⟩
  rintro s c (h | h)
  · exact (ho₁ s c h).mono fun s c h => by
      rcases h with h | h | h
      · exact .inl (.inl h)
      · exact .inl (.inr (hs₂ s c h))
      · exact .inr (.inr h)
  · exact (ho₂ s c h).mono fun s c h => h.elim (fun h => .inl (.inr h)) fun h => .inr (.inl h)

end Spike.Lib

namespace Spike.Lib.A64.Flow.Worker.Body

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow

section ProofH

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`seg_wkBodyT` inside `NNZH`**: the block off the transfer sites
(`seg_ndNN`, `Z` at it: `hZE`), `print` inside `NNZP SysW1`
(`PrintF.printF_callTNN`, its `write` `hsvc`, `Z` at its nodes `hZP`). -/
theorem seg_wkBodyTH (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr Qa : AS → Nat → Ctl → Prop} {x : ND}
    (hxpc : x.pc = (_root_.Executable.labels exe).label ".L20_wc_worker.sp4") (hxo : x.o = ⟨-96, []⟩)
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".L20_wc_worker.0_entry") wkE)
    (hgap : (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" =
      (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 21))
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hm : ∀ σ c, J σ c → (σ.slot (-80)).toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr (wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      SegTC (NNZP SysW1 exe endPc Z) p lbl ms
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hZE : NodeZ Z exe (wN (_root_.Executable.labels exe).label J Pr .e) wkE.length)
    (hZP : ∀ σC c, (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      ∀ i, NodeZ Z exe (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC i) (PrintF.FA.lenN i))
    (hedge : ∀ σ0 c0, J σ0 c0 → ∀ (σR : AS) c',
      Pr (wkC (_root_.Executable.labels exe).label σ0)
        (wkC (_root_.Executable.labels exe).label σ0).regs.X1.toBitVec.toNat c' →
      (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σR.slot k = wkSl σ0 k) →
      σR.regs.TPIDR_EL0 = σ0.regs.TPIDR_EL0 → x.J σR c') :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F (wN (_root_.Executable.labels exe).label J Pr .e))
      (fun s c => ∃ y, At exe endPc R F (wX (_root_.Executable.labels exe).label Qa x y) s c) := by
  let lab := (_root_.Executable.labels exe).label
  refine fn_segTS (N := wN lab J Pr) (E := wX lab Qa x) (fun i => ?_) WN.e
  cases i
  case e =>
    refine SegTC.toH (seg_ndNN (by simp [wkE]) wkE_ok (by simp [wkE, notNop]) hF hR hal hlo hhi hcodeE
      (fun σ c hJ => ?_) hZE)
    obtain ⟨c', hr, hP⟩ := hcall σ c hJ
    refine ⟨c', hr, .inl ⟨WN.call, ?_, ?_, ⟨σ, c, hJ, (wkC_eq _ _).symm⟩, ?_⟩⟩
    · simp only [wN]; rw [wkE_run]
    · simp only [wN]; rw [wkE_run]; rfl
    · show Pr (arun lab wkE ⟨lab ".L20_wc_worker.0_entry", ⟨-96, []⟩, σ⟩).σ 0 c'
      rw [← wkC_eq]; exact hP
  case call =>
    refine (PrintF.printF_callTNN (Sy := SysW1) (nC := wN lab J Pr .call) (Pc := Pr) (Qc := Qa) hR hal hF
      (by show R.lo ≤ -96 + -48; omega) (by show (-96 : Int) < R.hi; omega)
      (by show (-96 : Int) % 16 = 0; decide) hcode hentry rfl
      (fun σ c h => h.2) (fun σ c ⟨⟨σ0, c0, hJ0, hσ⟩, _⟩ => hσ ▸ wkC_x1_lt lab σ0 (hm σ0 c0 hJ0)) hsvc
      (fun _ _ _ _ _ _ _ _ σC c hJ i => (hZP σC c hJ i).toAOf (PrintF.FA.lenN_eq i)) ?_ ?_).mono_S fun _ _ h => h.toH
    · rintro σC c σR c' ⟨⟨σ0, c0, hJ0, rfl⟩, -⟩ - - htp hP hsl
      refine .inr ⟨WX.ret, ?_, ?_, ?_⟩
      · show x.pc = Int64.ofBitVec (wkC lab σ0).regs.X30.toBitVec
        rw [hxpc, wkC_eq, wkE_X30, ← hgap, int64_ofBitVec_toBitVec]
      · show x.o.le ⟨-96, []⟩ = true
        rw [hxo]; rfl
      · refine hedge σ0 c0 hJ0 σR c' hP (fun k h1 h2 h3 => ?_) (by rw [htp, wkC_tp])
        rw [hsl k ⟨h3, by omega, by omega⟩ (by simp only [Region.Off, Region.callee, wN]; omega), wkC_eq,
          wkSl_eq]
    · rintro σC c σR c' k - h4 hQ -
      exact .inr ⟨WX.abort, rfl, rfl, h4, σC, k, hQ⟩

/-- **`seg_wkT` inside `NNZH`**: `seg_wkBodyTH`, then the tail from `.sp4`
(`htail`, inside `NNZH`), via `SegTC.seq_or`. -/
theorem seg_wkTH (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {Pr Qa : AS → Nat → Ctl → Prop}
    {cw c1 c2 : Ctl} {A B x29 ra tp : BitVec 64}
    (hcodeE : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label ".L20_wc_worker.0_entry") wkE)
    (hgap : (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" =
      (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 21))
    {c0' : Ctl} {x29' ra' : BitVec 64} (hcode : PrintF.Code c0' x29' ra' exe endPc)
    (hentry : (_root_.Executable.labels exe).label ".L9_scc_rt_print.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_print" + 4 + 4 + 4 + 4 + 4 + 4)
    (hm : ∀ σ c, J σ c → (σ.slot (-80)).toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ c, J σ c → ∃ c', LocalRun p c c' ∧ Pr (wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      SegTC (NNZP SysW1 exe endPc Z) p lbl ms
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hZE : NodeZ Z exe (wN (_root_.Executable.labels exe).label J Pr .e) wkE.length)
    (hZP : ∀ σC c, (wN (_root_.Executable.labels exe).label J Pr .call).J σC c →
      ∀ i, NodeZ Z exe (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC i) (PrintF.FA.lenN i))
    (hrec : ∀ σ0 c0, J σ0 c0 → σ0.slot (-16) = x29 ∧ σ0.slot (-8) = ra ∧ σ0.slot (-64) = A ∧
      σ0.slot (-56) = B ∧ σ0.regs.TPIDR_EL0.toBitVec = tp ∧
      ∀ c', Pr (wkC (_root_.Executable.labels exe).label σ0)
        (wkC (_root_.Executable.labels exe).label σ0).regs.X1.toBitVec.toNat c' → c' = cw)
    (htail : SegTC (NNZH exe endPc Z) p lbl ms
      (At exe endPc R F (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4))
      (fun s c => ∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c)) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F (wN (_root_.Executable.labels exe).label J Pr .e))
      (fun s c => (∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c) ∨
        At exe endPc R F (wX (_root_.Executable.labels exe).label Qa
          (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4) .abort) s c) := by
  refine (seg_wkBodyTH (x := HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp .sp4)
    hF hR hal hlo hhi rfl rfl hcodeE hgap hcode hentry hm hcall hsvc hZE hZP ?_).mono_post ?_ |>.seq_or htail
  · intro σ0 c0 hJ0 σR c' hP hsl htp
    obtain ⟨h16, h8, h64, h56, htp0, hc⟩ := hrec σ0 c0 hJ0
    obtain ⟨k16, k8, k64, k56⟩ := wkSl_keep σ0
    refine ⟨hc c' hP, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsl _ (by decide) (by decide) (by decide), k16, h16]
    · rw [hsl _ (by decide) (by decide) (by decide), k8, h8]
    · rw [hsl _ (by decide) (by decide) (by decide), k64, h64]
    · rw [hsl _ (by decide) (by decide) (by decide), k56, h56]
    · rw [htp, htp0]
  · rintro s c ⟨y, h⟩
    cases y
    · exact .inl h
    · exact .inr h

end ProofH

end Spike.Lib.A64.Flow.Worker.Body

namespace Spike.Lib.A64.Flow.Worker.Hello.Wk

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

section SegNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`wc_prologue_seg` off the transfer sites** (`prologue_seg_ofNNA`), `Z`
at the prologue's states (`hz`, `ProW`; `ProW.ofPcs` from its fifteen
pcs). -/
theorem wc_prologue_segNN (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L20_wc_worker.0_entry")
    (ho : SO.le nb.o (oFr 96) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 96 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 96 σ.regs }).regs →
          σ'.slot = stSlots (-(96 : Int64).toInt) σ'.regs wcPs (frSlot σ) → nb.J σ' c)
    (hz : ProW Z (fun _ _ => False) exe endPc R F ms ((_root_.Executable.labels exe).label "wc_worker") 96 8
      ".L20_wc_worker.stack_grow" wcPs J) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofNNA hp hend hello_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hedge hz

/-- **`seg_wcWorkerH` inside `NNZH`**: the original's hypotheses, `print`'s
`write` inside `NNZP SysW1` (`hsvc`), and `Z` at the prologue's pcs (`hz`),
the `.0_entry` block (`hZE`), `print`'s nodes (`hZP`), the tail's (`hZW`)
and the unpark callee's at every return frame (`hZU`). -/
theorem seg_wcWorkerHNN (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w x29 ra tp σ c → X σ →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ, wkJ c0 w x29 ra tp σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Pr (Body.wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hdone : ∀ σ, wkJ c0 w x29 ra tp σ c0 → ∀ c',
      Pr (Body.wkC (_root_.Executable.labels exe).label σ)
        (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat c' → c' = cw)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      SegTC (NNZP SysW1 exe endPc Z) p lbl ms
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : ∀ (s : State) σ c (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat (4 * k) →
      wcJE c0 w x29 ra tp σ c → Z s c)
    (hZE : NodeZ Z exe (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e) Body.wkE.length)
    (hZP : ∀ σC c, (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      ∀ i, NodeZ Z exe (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC i) (PrintF.FA.lenN i))
    (hZW : ∀ i, NodeZ Z exe (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp i)
      (HelloTail.lenN i))
    (hZU : ∀ x29' ra' i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 w.w5 x29' ra' tp i)
      (Unpark.lenN i)) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩)
      (fun s c => (∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c) ∨
        At exe endPc R F (Body.wX (_root_.Executable.labels exe).label Qa
          (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort) s c) := by
  refine SegTC.mono_post (Q := fun s c => (∃ y, At exe endPc R F (HelloTail.E c2 x29 ra tp y) s c) ∨
      At exe endPc R F (Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort) s c) ?_
    fun s c h => h.imp_left fun ⟨y, hy⟩ => by cases y; exact ⟨.ret, tailE_eq c2 x29 ra tp ▸ hy⟩
  refine SegTC.seq (SegTC.toH (wc_prologue_segNN hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi
    (nb := Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e)
    rfl (by simp only [Body.wN]; decide) (fun σ c hJ => ?_)
    (ProW.ofPcs fun s σ c k hk he hpc hJ => hz s σ c k hk he hpc hJ.1))) ?_
  · obtain ⟨hJ, hX⟩ := hJ
    obtain ⟨h1, h2, h3, h4⟩ := hlim σ c hJ hX
    refine ⟨h1, h2, h3, fun v hv => ⟨h4 v hv, fun σ' hreg hsl => ?_⟩⟩
    obtain ⟨rfl, h0, hx1, hx2, hx3, hx4, hx5, h29, h30, htp⟩ := hJ
    simp only [Body.wN, wkJ]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [hsl, hreg, stSlots, frSlot, Spike.Lib.upd_apply, frRegs, ldStep, chkRegs, Reg64s.setRegOrZr,
        Reg64s.setRegOrZr64, Reg64s.setXReg, Reg64s.getXReg, Ret0.setXReg_TPIDR, *]
  refine Body.seg_wkTH hF hR hal hlo hhi (wkECode hp hend) (hgap hp) (printCode hp hend (c0 := c0) (x29 := x29)
    (ra := ra)) (printEntry hp) ?_ ?_ hsvc hZE hZP ?_
    (SegTC.toH (HelloTail.seg_wkTailUNN hF hR hal hlo hhi hdm ht hev hv htag hevb hvb hc1 (tailCode hp hend) hK hS
      htp4 htu hhu hevu hvu hc2 (Labels.unpkCode hp hend (c0 := cw) (c1 := c1) (B := w.w5) (x29 := x29) (ra := ra)
        (tp := tp)) (Labels.hpentry hp) (hsp6 hp) (fun i => (hZW i).toAOf (HelloTail.lenN_eq i))
        fun _ _ _ _ _ _ _ _ x29' ra' _ i => (hZU x29' ra' i).toAOf (by cases i <;> rfl)))
  · rintro σ c ⟨-, -, -, h80, -⟩
    rw [h80]; exact hm
  · rintro σ c hJ
    obtain rfl := hJ.1
    exact hcall σ hJ
  · rintro σ0 c0' hJ
    obtain rfl := hJ.1
    exact ⟨hJ.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.2.2.2.1, hJ.2.2.2.2.2.1, hJ.2.2.2.2.2.2.1,
      hJ.2.2.2.2.2.2.2.2.2, hdone σ0 hJ⟩

/-- **`seg_wcWorkerHA` inside `NNZH`**: `seg_wcWorkerHNN`, then
`seg_jabort4H` at `print`'s abort exit (`sp` at `-144`, the dispatcher
below to `-192`: `hlo`), to the return alone. `Z` along the abort path at
every state of the frame condition with the abort node's control (`hZA`);
the stub's exit at an abort site (`hab`). -/
theorem seg_wcWorkerHANN (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {c0 cw c1 c2 : Ctl} {w : Words} {x29 ra tp : BitVec 64} {X : AS → Prop}
    {Pr Qa : AS → Nat → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hlim : ∀ σ c, wcJE c0 w x29 ra tp σ c → X σ →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat)
    (hm : w.w2.toNat * 8 < 2 ^ 63)
    (hcall : ∀ σ, wkJ c0 w x29 ra tp σ c0 →
      ∃ c', LocalRun p c0 c' ∧ Pr (Body.wkC (_root_.Executable.labels exe).label σ) 0 c')
    (hdone : ∀ σ, wkJ c0 w x29 ra tp σ c0 → ∀ c',
      Pr (Body.wkC (_root_.Executable.labels exe).label σ)
        (Body.wkC (_root_.Executable.labels exe).label σ).regs.X1.toBitVec.toNat c' → c' = cw)
    (hsvc : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → (∀ m, F' m → F m) → ∀ σC c,
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      SegTC (NNZP SysW1 exe endPc Z) p lbl ms
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .svc))
        (At exe endPc R' F' (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC .n5)))
    (hdm : ∀ m, F m → Mem.loadInt m.dmem w.w4 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {wa wb : TermRun.Word}
    (ht : cw.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt cw.env a = some (ty, [wa]))
    (hv : ValRep lbl wa.val w.w4.toNat) (htag : ∃ sa, wa.val = .loc sa 0)
    (hevb : TermRun.evalAt cw.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc1 : c1 = ⟨e1, (d, .unit, []) :: cw.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (w.w5 + 16#64) 1#64) (htp4 : (w.w5 + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c1.term = .let_ x (.ext .unpark au) e) (hhu : c1.hold = none)
    (hevu : TermRun.evalAt c1.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val w.w5.toNat)
    (hc2 : c2 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c1.env, none⟩)
    (hz : ∀ (s : State) σ c (k : Nat), k < 15 → s.exe = exe →
      s.st.2 = (_root_.Executable.labels exe).label "wc_worker" + Int64.ofNat (4 * k) →
      wcJE c0 w x29 ra tp σ c → Z s c)
    (hZE : NodeZ Z exe (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e) Body.wkE.length)
    (hZP : ∀ σC c, (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .call).J σC c →
      ∀ i, NodeZ Z exe (PrintF.cN (_root_.Executable.labels exe).label Pr Qa σC i) (PrintF.FA.lenN i))
    (hZW : ∀ i, NodeZ Z exe (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp i)
      (HelloTail.lenN i))
    (hZU : ∀ x29' ra' i, NodeZ Z exe (Unpark.N (_root_.Executable.labels exe).label c1 c2 w.w5 x29' ra' tp i)
      (Unpark.lenN i))
    (hZA : ∀ σC c0', (Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort).J σC c0' →
      ∀ s, s.exe = exe → F s.st.1 → Z s c0')
    (hab : ∀ m0 σC c0', (Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort).J σC c0' →
      ∀ s c, At exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R ⟨-144, []⟩ m0 σC)
        (Abort.N (_root_.Executable.labels exe).label Abort.write c0' .ex) s c → ms.abortAt s) :
    SegTC (NNZH exe endPc Z) p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
        fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩)
      (fun s c => ∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c) :=
  ((seg_wcWorkerHNN hp hend hF hR hal (Int.le_trans hlo (by decide)) hhi hlim hm hcall hdone hsvc hdm ht hev hv
    htag hevb hvb hc1 hK hS htp4 htu hhu hevu hvu hc2 hz hZE hZP hZW hZU).mono_post fun _ _ h => h.symm).seq_or
    (seg_jabort4H (Q := fun s c => ∃ y, At exe endPc R F (Wake.WkTailW.E c2 x29 ra tp y) s c)
      (nC := Body.wX (_root_.Executable.labels exe).label Qa
        (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 w.w4 w.w5 x29 ra tp .sp4) .abort)
      hp hend SccCode.hello_abort rfl (fun σ _ h => by rw [h.1]; rfl) hF hR hal
      (by show R.lo ≤ -144 - 48; omega) (by show (-144 : Int) < R.hi; omega)
      (by show (-144 : Int) % 16 = 0; decide) hK hZA hab) |>.mono_post fun _ _ h => h.elim id id

end SegNN

end Spike.Lib.A64.Flow.Worker.Hello.Wk

/-- info: 'Spike.Lib.A64.Flow.Worker.Body.seg_wkTH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Body.seg_wkTH

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerHANN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.Wk.seg_wcWorkerHANN
