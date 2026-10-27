/-
**An `Accepted2` body's abort exits as segments with frames** (AArch64):
the overflow abort label (`abortN2`) and a buffer allocation's heap abort
(`nbX … .abort`) each do not return, so at frames `fs` each is a segment
(`SegWS`) into any fragment, inside any `W` with frames. The code facts are
discharged from the program's checks (`abortIn`, the function's
`.abort_overflow` block); the nodes' states inside `W` (`BlkW`, `NodeW`)
and the exit call at an abort site stay premises (`StubHN`, `StubON`,
`hW`).

- `StubHN`, `StubHN.stubHW`: the heap abort path's obligations without its
  code (`Abort.Disp.StubHW`'s `W` fields), and `StubHW` from them and the
  abort code (`stubHW_of_code`);
- `StubON`, `StubON.stubW`: the overflow abort path's, and
  `Abort.Local.StubW` from them and the abort code;
- `heapAbSeg2`: the heap abort exit (`Disp.seg_jabort2WS`);
- `ovfSeg2`: the overflow abort label (`Local.seg_localW` lifted to frames
  by `SegWS.liftS_noret`).
-/
import Spike.Lib.A64AbortHeapS
import Spike.Lib.A64AbortStubCode
import Spike.Lib.A64NewBuf
import Spike.Lib.LowerA64.OvfCode
import Spike.Lib.LowerA64.Node2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.A64.Flow.NewBuf (nbX allocAbortDepth)

section AbortSeg2

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {R : Region} {F : MachineData → Prop} {c0 : Ctl}

/-- **The heap abort path's obligations without its code** for one source
control `c0` in the dispatcher's region `R` and frame condition `F`: the
dispatcher's and the heap stub's nodes' states inside `W` (moved by no `K`,
the stub's `write` call among them, `hsvc`) and the exit call at an abort
site (`hab`); `Abort.Disp.StubHW` with the code fields dropped. -/
structure StubHN (W : Frag isaLSE2) (K : State → State → Prop) (ms : MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0
  dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1
  dj1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .j1) Abort.Disp.j1
  dt2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .t2) Abort.Disp.t2
  dg2 : BlkW W K exe endPc R F (Abort.Disp.DN.nd2 (_root_.Executable.labels exe).label c0 .g2) Abort.Disp.g2
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .e) Abort.b0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n1)
  sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n2) Abort.b1Heap
  hsvc : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .svc)
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .n5) Abort.b2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .ex)
  hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.heap c0 .ex) s c →
    ms.abortAt s

/-- **`StubHW` from `StubHN` and the abort code** (`stubHW_of_code`). -/
theorem StubHN.stubHW {W : Frag isaLSE2} {K : State → State → Prop} {ms : MemSide isaLSE2} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (h : StubHN W K ms exe endPc R F c0) : Abort.Disp.StubHW W K p lbl ms exe endPc R F c0 :=
  StubW.stubHW_of_code hp hend hprog hK hF h.de h.dt1 h.dj1 h.dt2 h.dg2 h.se h.sn1 h.sn1b h.sn2 h.hsvc h.sn5
    h.sex h.hab

/-- **The overflow abort path's obligations without its code** for one
source control `c0` in the callee's region `R` and frame condition `F`:
`Abort.Local.StubW` with the code fields dropped, the stub's `write` call
by its node's states inside `W` (`hsvc`). -/
structure StubON (W : Frag isaLSE2) (K : State → State → Prop) (ms : MemSide isaLSE2)
    (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop) (c0 : Ctl) : Prop where
  de : BlkW W K exe endPc R F (Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .e) Abort.Disp.d0
  dt1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .t1) Abort.Disp.t1
  dg1 : BlkW W K exe endPc R F (Abort.Disp.DN.nd1 (_root_.Executable.labels exe).label c0 .g1) Abort.Disp.g1
  se : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .e) Abort.b0
  sn1 : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .n1)
  sn1b : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .n1b)
  sn2 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .n2)
    Abort.b1Overflow
  hsvc : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .svc)
  sn5 : BlkW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .n5) Abort.b2
  sex : NodeW W K exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .ex)
  hab : ∀ s c, At exe endPc R F (Abort.N (_root_.Executable.labels exe).label Abort.overflow c0 .ex) s c →
    ms.abortAt s

/-- **`Abort.Local.StubW` from `StubON` and the abort code** (`code_disp`,
`code_stubs`, the `write` call by `seg_svc_of_stubIn`). -/
theorem StubON.stubW {W : Frag isaLSE2} {K : State → State → Prop} {ms : MemSide isaLSE2} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F)
    (h : StubON W K ms exe endPc R F c0) : Abort.Local.StubW W K p lbl ms exe endPc R F c0 := by
  have hpr := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hpr
  exact ⟨Scc.Cert.Rt.A64.Abort.code_disp hp hend hpr.2, h.de, h.dt1, h.dg1,
    Scc.Cert.Rt.A64.Abort.code_stubs hp hend hprog .overflow, h.se, h.sn1, h.sn1b, h.sn2, h.sn5, h.sex,
    StubW.seg_svc_of_stubIn hp hend hpr.1.1.1.1.1 hK hF h.hsvc, h.hab⟩

/-- **A buffer allocation's heap abort exit is a segment with frames** into
any fragment: from `nbX … .abort` (the jump to `scc_rt_abort` with
`x0 = 2`, `sp` at `-allocAbortDepth fr` in `R`) at frames `fs`, inside `W`
at `fs`, given the abort code (`hprog`) and, at each source control of the
exit, the heap abort path's obligations without code (`StubHN`) in the
dispatcher's region and frame condition (`Disp.seg_jabort2WS`'s). -/
theorem heapAbSeg2 {W : FragS isaLSE2} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isaLSE2}
    {fs : List TermRun.Frame} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {fr : Int} {pcR : Int64} {Jc : Flow.AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -allocAbortDepth fr - 48)
    (hkc : -allocAbortDepth fr < R.hi) (h16 : fr % 16 = 0) (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hstub : ∀ m0 σC c0,
      (nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr pcR Jc .abort).J σC c0 →
      StubHN (fun s c => W s c fs) K (ms fs) exe endPc (R.callee (-allocAbortDepth fr) (-48) 0)
        (fun m => F m ∧ CKept R (-allocAbortDepth fr) (-48) 0 m0 m ∧ Abs R ⟨-allocAbortDepth fr, []⟩ m0 σC) c0)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms
      ((At exe endPc R F (nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr pcR Jc .abort)).at fs) Q := by
  have h16' : (-allocAbortDepth fr) % 16 = 0 := by
    simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega
  refine Abort.Disp.seg_jabort2WS (W := fun s c => W s c fs)
    (nC := nbX (ms fs) (_root_.Executable.labels exe).label lbl R fr pcR Jc .abort) rfl
    (fun σ c hJ => by rw [hJ.1]; rfl) hF hR hal hlo hkc h16' hK (fun m0 σC c0 hJ => ?_) ms fs rfl (fun _ _ h => h) Q
  refine (hstub m0 σC c0 hJ).stubHW hp hend hprog hK ?_
  exact fstable_enter (kc := -allocAbortDepth fr) hR hF (by omega) (by decide) hkc (by decide) (by omega)
    (by decide) (by decide)

/-- **The overflow abort label of an `Accepted2` body is a segment with
frames** into any fragment: from `abortN2` (the function's
`.abort_overflow` block, its code from the check `hblk`) at frames `fs`,
inside `W` at `fs`, given the block's states inside `W` (`hW`), no `K`
moving the frame condition or the caller's cells (`hFK`, `hKR`), the abort
code (`hprog`) and, for the callee's region and frame condition at the
call and each source control of the block, the overflow abort path's
obligations without code (`StubON`; `Local.seg_localW`'s `hstub`). -/
theorem ovfSeg2 {W : FragS isaLSE2} {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isaLSE2}
    {fs : List TermRun.Frame} {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {cx : FnCtx} {fp ra : BitVec 64}
    (hblk : blockAt prog (cx.local "abort_overflow") 0 ovfBlk = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) (hkc : -(cx.frame : Int) < R.hi) (h16 : (cx.frame : Int) % 16 = 0)
    (hK : (ms fs).K = some Scc.Sem.A64.abi)
    (hW : BlkW (fun s c => W s c fs) K exe endPc R F
      (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0) Abort.Local.lb)
    (hFK : KStable K F)
    (hKR : ∀ s s', K s s' → F s.st.1 → ∀ k, R.Off k → ¬ (R.callee (-(cx.frame : Int)) (-48) 0).Off
      (k - -(cx.frame : Int)) → Mem.loadInt s'.st.1.dmem (R.addr k) 8 = Mem.loadInt s.st.1.dmem (R.addr k) 8)
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), R'.OK → R'.base.toNat % 16 = 0 → R'.lo ≤ -48 →
      0 ≤ R'.hi → FStable R' F' → KStable K F' → (∀ m, F' m → F m) →
      R' = R.callee (-(cx.frame : Int)) (-48) 0 →
      ∀ c1, (∃ σ0, (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J σ0 c1) →
      (∀ m, F' m → ∃ mC σC σ0, Abs R ⟨-(cx.frame : Int), []⟩ mC σC ∧ σC.slot = σ0.slot ∧
        (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J σ0 c1 ∧
        ∀ k, R.Off k → ¬ R'.Off (k - -(cx.frame : Int)) →
          Mem.loadInt m.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) →
      StubON (fun s c => W s c fs) K (ms fs) exe endPc R' F' c1)
    (Q : FragS isaLSE2) :
    SegWS W K p lbl ms
      ((At exe endPc R F (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0)).at fs) Q := by
  have h0 := Abort.Local.seg_localW (p := p) (lbl := lbl) (ms := ms fs) (Q := fun _ _ => False)
    (fr := (cx.frame : Int)) (pcA := (_root_.Executable.labels exe).label (cx.local "abort_overflow"))
    (JA := (abortN2 i T p lbl cx (_root_.Executable.labels exe).label fp ra c0).J)
    hF hR hal hlo hhi hkc h16 hK (ovfCode_codeAt hp hend hblk) hW hFK hKR
    (fun R' F' hR' hal' hlo' hhi' hF' hFK' hFF' hRe c1 hJ hm =>
      (hstub R' F' hR' hal' hlo' hhi' hF' hFK' hFF' hRe c1 hJ hm).stubW hp hend hprog hK hF')
  exact SegWS.liftS_noret fs h0 (fun _ _ h => h) Q

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.heapAbSeg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms heapAbSeg2

/-- info: 'Spike.Lib.LowerA64.ovfSeg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ovfSeg2

end AbortSeg2

end Spike.Lib.LowerA64
