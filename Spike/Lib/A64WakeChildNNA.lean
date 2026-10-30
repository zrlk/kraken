/-
**wake.w's spawned child off the transfer sites, `Z` at the nodes' states**
(AArch64): `seg_childStubNN` and `seg_childPreNN`
(`Spike/Lib/A64WakeChildNN.lean`) with `Z` at the states before each
instruction (`NodeZA` at the stub's nodes, `ThrZA` at the worker's), which
know the registers and the frame's cells. The proofs are the `NN` ones with
`seg_ndNNA` and `seg_thrWorkerNNA`. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `cBlk`: the stub's blocks.
- `seg_childStubNNA`, `seg_childPreNNA`; `seg_childPreNNA'` (with `cA`, `meW < 2 ^ 64`, the registers `x9`, `x10`).
-/
import Spike.Lib.A64WakeChildNN
import Spike.Lib.A64WakeWorkerLabelsNNA

namespace Spike.Lib.A64.Flow.Worker.Wake.Child

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.WakeLabels (wakeProg)

set_option linter.unusedSimpArgs false

/-- The stub's blocks, the `blk` of its nodes' `NodeZA`. -/
def cBlk : CN → List Directive
  | .cb => cb pfxM | .ch => chB

section SegNNA

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {Z : Frag isaLSE2}

/-- **`seg_childStubNNA` with `Z` at every node's states** (`NodeZA` at the
stub's, `ThrZA` at the worker's). -/
theorem seg_childStubNNA {Q : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {cW c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hlim : ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = tp →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤ (sp0 - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat)
    (hsplit : LocalRun p cW c1)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c1.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c1.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c1.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc2 : c2 = ⟨e1, (d, .unit, []) :: c1.env, none⟩)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hS : StOk ms F exe endPc (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c2.term = .let_ x (.ext .unpark au) e) (hhu : c2.hold = none)
    (hevu : TermRun.evalAt c2.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc3 : c3 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c2.env, none⟩)
    {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hSx : StOk ms F exe endPc (tp + 24#64) 1#64)
    (hZc : ∀ i, NodeZA Z exe endPc R F (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i))
    (hZ : ThrZA Z exe endPc R F ms cW c1 c2 c3 A B tp sp0) :
    SegTC (NNZ exe endPc Z) p lbl ms
      (At exe endPc R F (childN pfxM (_root_.Executable.labels exe).label cW A B tp sp0)) Q := by
  have hin := wake_stubIn
  simp only [stubIn, Bool.and_eq_true] at hin
  obtain ⟨hcb, hch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  let nT : ND := ⟨lab "scc_rt_thr_worker", ⟨0, []⟩, thrJE cW A B tp sp0⟩
  refine SegTC.seq (Q := At exe endPc R F nT) ?_
    (seg_thrWorkerNNA hp hend hF hR hal hlo hhi hlim hsplit hdm ht hev hv htag hevb hvb hc2 hK hS htp4
      htu hhu hevu hvu hc3 hret3 hSx hZ)
  refine ((fn_segTS (N := cN pfxM lab cW A B tp sp0) (E := fun _ : Unit => nT) (fun i => ?_) CN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h)
  cases i
  case cb =>
    refine seg_ndNNA (blk := cb pfxM) (by simp [cb]) cb_ok (by simp [cb, cbzD, notNop]) hF hR hal hlo hhi
      (code_of hp hend hcb (by simp only [cN, childN, ofNat4_succ, ofNat4_zero]; rfl))
      (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZc .cb)
    obtain ⟨rfl, h0, h9, h10, htp, hsp⟩ := hJ
    rw [cN, childN, cb_run, cbT_run]
    refine .inl ⟨CN.ch, ?_, rfl, ⟨_, rfl, rfl, h9, h10, htp, hsp⟩⟩
    simp only [cN, rl, Reg64s.getRegOrZr] at h0 ⊢
    simp [h0, Reg64s.getRegOrZr, Reg64s.getXReg]
    all_goals rfl
  case ch =>
    refine seg_ndNNA (blk := chB) (by simp [chB]) chB_ok (by simp [chB, notNop]) hF hR hal hlo hhi
      (code_of hp hend hch (ofNat4_zero _)) (fun σ c hJ => ⟨c, .refl c, ?_⟩) (hZc .ch)
    obtain ⟨x0, rfl, -, h9, h10, htp, hsp⟩ := hJ
    rw [cN, chB_run]
    refine .inr ⟨(), rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩ <;> simp_all

end SegNNA

open Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerBody workerTy wc1 kid_split)
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild preChild_hlim)
open Spike.Lib.A64.Flow.Ret0 (stacksA)
open Spike.Lib.A64.Rt (TcbGG tcbOf)
open Spike.Lib.A64Consumer (Own)

/-- **`seg_childPreNN` with `Z` at every node's states**: same hypotheses;
the child's segment given `ThrZA` (at the child's region and frame
condition) and `NodeZA` at the stub's nodes. -/
theorem seg_childPreNNA {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q Z : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {lab : Label → Int64} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms own lab q st)
    (hr1 : r1 = r1Of lab) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) (hal : (stacksA lab).toNat % 16 = 0)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hpw : ∃ d, p.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy)
    (T : Ty) :
    ∃ (th : Thread isaLSE2) (cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) (tcbOf lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR (r1.lo + r1.size) (-16384))
          (DFrame (childR (r1.lo + r1.size) (-16384))
            (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
          (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))
          (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          cA + 8 ≤ 2 ^ 64 → (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 (tcbOf lab q).toNat + 24#64) 1#64 →
          ThrZA Z exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) ms
            (kidC T w1 w2) (wc1 workerTy w1 w2)
            ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) ::
              ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat)
            (BitVec.ofNat 64 (r1.lo + r1.size)) →
          (∀ i, NodeZA Z exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)) i)
            (cBlk i)) →
          SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))) Q) := by
  subst hr1
  obtain ⟨th, -, tls, cA, meW, -, hth, -, hpc, -, -, hcall, -, h3, h9, h10, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  obtain ⟨h3', -, -, hA⟩ := hPC _ hXs
  have htl : tls = (tcbOf lab q).toNat := by
    rw [← h3]; exact congrArg BitVec.toNat h3'
  subst htl
  have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
    show (stacksA lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hr1e : r1Of lab = ⟨(stacksA lab).toNat + 16384, 16384⟩ := by
    rw [show r1Of lab = ⟨(r1Of lab).lo, 16384⟩ from rfl, hlo1]
  obtain ⟨htop, hlo0, hsz, hR, hal', hlo', hhi'⟩ := Spike.Lib.A64.Rt.childStub_region_stk hr1e hal hbd
  have hh : handed t.2 0 ((r1Of lab).lo + (r1Of lab).size) = some (0, r1Of lab) := by
    simp [handed, hheld]
  have hcode := code_of hp hend wake_svcIn (q := Spike.Lib.WakePreA.cloneAt pfxM exe) rfl
  have h9' : th.st.st.1.regs.X9.toBitVec = BitVec.ofNat 64 cA := by
    subst h9; show _ = BitVec.ofNat 64 th.st.st.1.regs.X9.toBitVec.toNat; simp
  have h10' : th.st.st.1.regs.X10.toBitVec = BitVec.ofNat 64 meW := by
    subst h10; show _ = BitVec.ofNat 64 th.st.st.1.regs.X10.toBitVec.toNat; simp
  have hcA : cA < 2 ^ 64 := by subst h9; exact BitVec.isLt _
  have hmW : meW < 2 ^ 64 := by subst h10; exact BitVec.isLt _
  refine ⟨th, cA, meW, hth, hcall, fun w1 w2 => ⟨?_, fun hv1 htag hv2 hc8 hcout hS htp4 hSx hZ hZc => ?_⟩⟩
  · rw [← h9', ← h10']
    exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo0 hsz
  obtain ⟨d, hdf, hb, ha, hty⟩ := hpw
  refine seg_childStubNNA hp hend (FStable.dframe _ _) hR hal' hlo' hhi'
    (preChild_hlim hA hh hbd hsz htls hout)
    (kid_split hdf hb ha hty w1 w2) ?_ (d := "d") (a := .var "c") (b := .lit 1)
    (e1 := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)) rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]) htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, ValRep])
    rfl hK hS htp4 (x := "w") (au := .var "j") (e := .ret .unit) rfl rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) rfl rfl hSx hZc hZ
  intro m hm
  rw [hm _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; exact hc8)
    (by simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA, Nat.mod_eq_of_lt htop]; omega),
    Spike.Lib.A64.Rt.childAfter_dmem hh]
  exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; unfold Range.contains; omega) (by decide)


/-- **`seg_childPreNNA` with the words' bounds**: the same segment, and
`cA`, `meW` below `2 ^ 64` (the registers' values `x9`, `x10`), so the
callers' `ValRep … cA`, `ValRep … meW` are the ones at `(BitVec.ofNat 64
cA).toNat`, `(BitVec.ofNat 64 meW).toNat`. -/
theorem seg_childPreNNA' {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q Z : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {lab : Label → Int64} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms own lab q st)
    (hr1 : r1 = r1Of lab) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) (hal : (stacksA lab).toNat % 16 = 0)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hpw : ∃ d, p.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy)
    (T : Ty) :
    ∃ (th : Thread isaLSE2) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.getXReg .X9).toNat = cA ∧ (th.st.st.1.regs.getXReg .X10).toNat = meW ∧
      callOf abi th = some (.clone (r1.lo + r1.size) (tcbOf lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR (r1.lo + r1.size) (-16384))
          (DFrame (childR (r1.lo + r1.size) (-16384))
            (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
          (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))
          (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          cA + 8 ≤ 2 ^ 64 → (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 (tcbOf lab q).toNat + 24#64) 1#64 →
          ThrZA Z exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) ms
            (kidC T w1 w2) (wc1 workerTy w1 w2)
            ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) ::
              ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat)
            (BitVec.ofNat 64 (r1.lo + r1.size)) →
          (∀ i, NodeZA Z exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)) i)
            (cBlk i)) →
          SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))) Q) := by
  subst hr1
  obtain ⟨th, -, tls, cA, meW, -, hth, -, hpc, -, -, hcall, -, h3, h9, h10, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  obtain ⟨h3', -, -, hA⟩ := hPC _ hXs
  have htl : tls = (tcbOf lab q).toNat := by
    rw [← h3]; exact congrArg BitVec.toNat h3'
  subst htl
  have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
    show (stacksA lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hr1e : r1Of lab = ⟨(stacksA lab).toNat + 16384, 16384⟩ := by
    rw [show r1Of lab = ⟨(r1Of lab).lo, 16384⟩ from rfl, hlo1]
  obtain ⟨htop, hlo0, hsz, hR, hal', hlo', hhi'⟩ := Spike.Lib.A64.Rt.childStub_region_stk hr1e hal hbd
  have hh : handed t.2 0 ((r1Of lab).lo + (r1Of lab).size) = some (0, r1Of lab) := by
    simp [handed, hheld]
  have hcode := code_of hp hend wake_svcIn (q := Spike.Lib.WakePreA.cloneAt pfxM exe) rfl
  have h9' : th.st.st.1.regs.X9.toBitVec = BitVec.ofNat 64 cA := by
    subst h9; show _ = BitVec.ofNat 64 th.st.st.1.regs.X9.toBitVec.toNat; simp
  have h10' : th.st.st.1.regs.X10.toBitVec = BitVec.ofNat 64 meW := by
    subst h10; show _ = BitVec.ofNat 64 th.st.st.1.regs.X10.toBitVec.toNat; simp
  have hcA : cA < 2 ^ 64 := by subst h9; exact BitVec.isLt _
  have hmW : meW < 2 ^ 64 := by subst h10; exact BitVec.isLt _
  refine ⟨th, cA, meW, hcA, hmW, hth, h9, h10, hcall, fun w1 w2 => ⟨?_, fun hv1 htag hv2 hc8 hcout hS htp4 hSx hZ hZc => ?_⟩⟩
  · rw [← h9', ← h10']
    exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo0 hsz
  obtain ⟨d, hdf, hb, ha, hty⟩ := hpw
  refine seg_childStubNNA hp hend (FStable.dframe _ _) hR hal' hlo' hhi'
    (preChild_hlim hA hh hbd hsz htls hout)
    (kid_split hdf hb ha hty w1 w2) ?_ (d := "d") (a := .var "c") (b := .lit 1)
    (e1 := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)) rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]) htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, ValRep])
    rfl hK hS htp4 (x := "w") (au := .var "j") (e := .ret .unit) rfl rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) rfl rfl hSx hZc hZ
  intro m hm
  rw [hm _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; exact hc8)
    (by simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA, Nat.mod_eq_of_lt htop]; omega),
    Spike.Lib.A64.Rt.childAfter_dmem hh]
  exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; unfold Range.contains; omega) (by decide)

end Spike.Lib.A64.Flow.Worker.Wake.Child
