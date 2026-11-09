/-
**wake.w's spawned child off the transfer sites on x86-64** (the x64 twin
of `Spike/Lib/A64WakeChildNN.lean`, `WCompat.noSite`): `Child.seg_child`,
`seg_childStub` and `seg_childPre` (`Spike/Lib/X64WakeChild.lean`,
`Spike/Lib/X64WakeChildPre.lean`) over `SegTC (NNZ exe endPc Z)`. The
proofs are the originals', with the leaves of `Spike/Lib/X64WakeNN.lean`
(`seg_ndNN`; here also `test_ndNN`, `flag_ndNN` for the stub's rows) and
`Labels.seg_thrWorkerNN`.

- `test_ndNN`, `flag_ndNN` (and `…NNA`): the rows `test_ndW`, `flag_ndW` at
  `W := NNZ exe endPc Z`, as `SegTC`.
- `cBlk`: the stub's nodes' blocks; `seg_childNN`: `Child.seg_child`.
- `seg_childStubNN`: `seg_childStub`, its hypotheses and a fragment `Z` at
  every node (`hZc` at the stub's, `ThrZ` at the worker's, entry
  `sp0 - 8`).
- `seg_childPreNN`: `seg_childPre`, same hypotheses and conclusion but for
  the final segment, over `SegTC (NNZ exe endPc Z)` given `Z` at every node
  (`ThrZ` at the controls of the child's `split`, `store` and `unpark`, and
  the stub's nodes).

**Unlike AArch64** (forced by the x64 shape): the stub is four nodes
(`testq`, `je`, `xorl`, the call block; AArch64: `cbz` and the call block),
two of them rows; the worker's `ThrZ` is at `sp0 - 8` (the `call`'s
return address, `thrR`); the thread pointer's load premises (`hT`, `hown`)
as in `seg_childPre`.
-/
import Spike.Lib.X64WakeChildPre
import Spike.Lib.X64WakeWorkerLabelsNN

namespace Spike.Lib.X64.Flow.Worker.Wake.Child

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NN NNZ NodeZ NodeZA notNop nodeW_nn nodeW_nnz nodeW_nnzA seg_ndNN fn_segTS)
open Spike.Lib.X64.WakePh (wake_childIn wake_wcCloneIn)
open Spike.Lib.X64.WakePh.WcClone (x21L svcB)
open Spike.Lib.X64.WakePh.Child (childN childR cE cN CN childIn tsB jeB xbp chB chL oC jeB_ok chB_ok jeB_run
  chB_run child_at)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerBody workerTy wc1 kid_split)
open Spike.Lib.X64.Flow.Worker.Wake.Labels (thrJE ThrZ seg_thrWorkerNN)
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild preChild_hlim)
open Spike.Lib.X64.Flow.Ret0 (stacksA StOk LdOk LimOk)
open Spike.Lib.X64.Rt (TcbGG tcbOf)
open Spike.Lib.X64Consumer (Own)

/-! ## The rows off the transfer sites -/

section Rows

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {Z : Frag isa}
  {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`test_ndW` off the transfer sites.** -/
theorem test_ndNN {n : ND} {a b : Reg64} {z : Nat} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(testDir a b, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ af,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, testStep a b σ af⟩ c')
    (hz : NodeZ Z exe n [(testDir a b, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (test_ndW hF hcode (nodeW_nnz (nodeW_nn hcode rfl) hz) hedge)

/-- **`test_ndW` off the transfer sites, `Z` at the node's states.** -/
theorem test_ndNNA {n : ND} {a b : Reg64} {z : Nat} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(testDir a b, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ af,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, n.o, testStep a b σ af⟩ c')
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (test_ndW hF hcode (nodeW_nnzA (nodeW_nn hcode rfl) hz) hedge)

/-- **`flag_ndW` off the transfer sites.** -/
theorem flag_ndNN {n : ND} {fi : FI} {z : Nat} (hok : fi.ok = true) (hnn : notNop fi.toDir = true)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fi.toDir, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ fl,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, fi.so n.o, fi.step σ fl⟩ c')
    (hz : NodeZ Z exe n [(fi.toDir, z)]) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (flag_ndW hok hF hcode (nodeW_nnz (nodeW_nn hcode hnn) hz) hedge)

/-- **`flag_ndW` off the transfer sites, `Z` at the node's states.** -/
theorem flag_ndNNA {n : ND} {fi : FI} {z : Nat} (hok : fi.ok = true) (hnn : notNop fi.toDir = true)
    (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fi.toDir, z)])
    (hedge : ∀ σ c, n.J σ c → ∀ fl,
      ∃ c', LocalRun p c c' ∧ Lands N E ⟨n.pc + Int64.ofNat z, fi.so n.o, fi.step σ fl⟩ c')
    (hz : NodeW Z (fun _ _ => False) exe endPc R F n) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  SegW.toTC (flag_ndW hok hF hcode (nodeW_nnzA (nodeW_nn hcode hnn) hz) hedge)

end Rows

/-! ## The stub -/

/-- The stub's nodes' blocks, the `blk` of their `NodeZ`. -/
def cBlk : CN → List (Directive × Nat)
  | .ts => tsB | .je => jeB | .xb => xbp | .ch => chB

section SegNN

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Region} {F : MachineData → Prop} {Z : Frag isa}

/-- **`Child.seg_child` off the transfer sites**: `Z` at every node. -/
theorem seg_childNN {cells : List (Directive × Nat)} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : childIn cells = true)
    {cW : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hZc : ∀ i, NodeZ Z exe (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (childN (_root_.Executable.labels exe).label cW A B tp sp0))
      (At exe endPc R F (cE (_root_.Executable.labels exe).label cW A B tp sp0)) := by
  simp only [childIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨bts, bje⟩, bxb⟩, bch⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  refine (fn_segTS (N := cN lab cW A B tp sp0) (E := fun _ : Unit => cE lab cW A B tp sp0) (fun i => ?_)
    CN.ts).mono_post fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_ndNN hF (fun s he hn => code bts s he hn) (fun σ c hJ af => ⟨c, .refl c, .inl ⟨CN.je, ?_, rfl, ?_⟩⟩)
      (hZc .ts)
    · show lab x21L + 51 = lab x21L + Int64.ofNat 48 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hS, h0⟩ := hJ
      exact ⟨hS, by rw [testStep_zf, h0]; rfl⟩
  case je =>
    refine seg_ndNN (blk := jeB) (by simp [jeB]) jeB_ok (by decide) hF hR hlo hhi (fun s he hn => code bje s he hn)
      (fun σ c hJ => ⟨c, .refl c, .inl ⟨CN.xb, ?_, rfl, hJ.1⟩⟩) (hZc .je)
    show lab chL = (arun lab jeB ⟨lab x21L + 51, oC, σ⟩).pc
    rw [jeB_run]; simp only [hJ.2, ite_true]
  case xb =>
    refine flag_ndNN (fi := .xor_rr32_self .rbp) rfl (by decide) hF
      (fun s he hn => (by simpa using code bxb s he hn : CodeAt s (lab chL) xbp)) (fun σ c hJ fl =>
        ⟨c, .refl c, .inl ⟨CN.ch, ?_, rfl, ?_, ?_⟩⟩) (hZc .xb)
    · rfl
    · obtain ⟨h0, h12, hbx, htp, hsp⟩ := hJ
      refine ⟨h0, ?_, ?_, ?_, ?_⟩ <;>
        simp (disch := decide) only [FI.step, FI.regs, Reg64s.get64_set64_ne, h12, hbx, hsp]
      simpa [FI.step, FI.regs, Reg64s.set64] using htp
    · simp only [FI.step, FI.regs, Reg64s.get64_set64_self]; rfl
  case ch =>
    refine seg_ndNN (blk := chB) (by simp [chB]) chB_ok (by decide) hF hR hlo hhi (fun s he hn => code bch s he hn)
      (fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, rfl, ?_⟩⟩) (hZc .ch)
    · show lab "scc_rt_thr_worker" = (arun lab chB ⟨lab chL + 2, oC, σ⟩).pc
      rw [chB_run]
    · obtain ⟨⟨h0, h12, hbx, htp, hsp⟩, hbp⟩ := hJ
      show cE lab cW A B tp sp0 |>.J (arun lab chB ⟨lab chL + 2, oC, σ⟩).σ c
      rw [chB_run]
      simp only [Reg64s.get64] at h12 hbx hbp hsp
      refine ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [Reg64s.get64, Reg64s.set64, h12]
      · simp [Reg64s.get64, Reg64s.set64, hbx]
      · simp [Reg64s.get64, Reg64s.set64, hbp]
      · simpa [Reg64s.set64] using htp
      · simp [Reg64s.get64, Reg64s.set64, hsp]
      · simp only [upd_apply, ite_true]
        rw [Int64.toBitVec_add, BitVec.add_assoc]; rfl

/-- **`seg_childStub` off the transfer sites**: its hypotheses and `Z` at
every node (`hZc` at the stub's, `ThrZ` at the worker's). -/
theorem seg_childStubNN {Q : Frag isa} (hp : Lays exe SccCode.wakeCells kp)
    (hend : endPc = endOf exe SccCode.wakeCells kp)
    {cW c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimW : LimOk ms F (tp + (8 : Int64).toBitVec) (sp0 - 8#64 - 48#64 - 8#64 - (16 : Int64).toBitVec))
    (hsplit : LocalRun p cW c1)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    {d : String} {a b : CoreTerm.At} {e1 : Expr} {ty tb : Ty} {w wb : TermRun.Word}
    (ht : c1.term = .let_ d (.store true a b none) e1) (hev : TermRun.evalAt c1.env a = some (ty, [w]))
    (hv : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hevb : TermRun.evalAt c1.env b = some (tb, [wb])) (hvb : ValRep lbl wb.val 1)
    (hc2 : c2 = ⟨e1, (d, .unit, []) :: c1.env, none⟩)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hS : StOk ms F (B + 16#64) 1#64) (htp4 : (B + 16#64).toNat % 4 = 0)
    {x : String} {au : CoreTerm.At} {e : Expr} {tu : Ty} {jw : TermRun.Word}
    (htu : c2.term = .let_ x (.ext .unpark au) e) (hhu : c2.hold = none)
    (hevu : TermRun.evalAt c2.env au = some (tu, [jw])) (hvu : ValRep lbl jw.val B.toNat)
    (hc3 : c3 = ⟨e, (x, ExtName.unpark.sig.2, []) :: c2.env, none⟩)
    {ar : CoreTerm.At} (hret3 : c3.term = .ret ar)
    (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0") tp tp)
    (hSx : StOk ms F (tp + 24#64) 1#64)
    (hZc : ∀ i, NodeZ Z exe (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i))
    (hZ : ThrZ Z exe cW c1 c2 c3 A B tp (sp0 - 8#64)) :
    SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc R F (childN (_root_.Executable.labels exe).label cW A B tp sp0)) Q := by
  have hlo8 : R.lo ≤ -8 := by omega
  have hhi8 : -8 < R.hi := by omega
  refine SegTC.seq (seg_childNN hp hend wake_childIn hF hR hlo hhi hZc) ?_
  refine (seg_thrWorkerNN hp hend (FStable.thrR hF hR hlo8 hhi8) (thrR_ok hR hlo8 hhi8)
    (by show R.lo + 8 ≤ -120; omega) (by show 8 ≤ R.hi + 8; omega) hlim hlimW hsplit hdm ht hev hv htag hevb
    hvb hc2 hK hS htp4 htu hhu hevu hvu hc3 hret3 hT hown hSx hZ).mono_pre fun s c h => At.toThr h ?_
  rintro σ c ⟨h1, h2, h3, -, h5, h6, -⟩
  exact ⟨h1, h2, h3, h5, h6⟩

end SegNN

/-- **`seg_childPre` off the transfer sites**: same hypotheses; the child's
segment over `SegTC (NNZ exe endPc Z)` given `Z` at its nodes (`ThrZ` at the
child's controls after the `split`, the `store` and the `unpark`; the stub's
nodes). -/
theorem seg_childPreNN {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q Z : Frag isa} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {lab : Label → Int64} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms own lab q st)
    (hr1 : r1 = r1Of lab) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hpw : ∃ d, p.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy)
    (T : Ty) :
    ∃ (th : Thread isa) (cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) (tcbOf lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR (r1.lo + r1.size) (-16384))
          (DFrame (childR (r1.lo + r1.size) (-16384))
            (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
          (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))
          (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          cA + 8 ≤ 2 ^ 64 → (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          LdOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (BitVec.ofNat 64 (tcbOf lab q).toNat) →
          OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0")
            (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (tcbOf lab q).toNat) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (BitVec.ofNat 64 (tcbOf lab q).toNat + 24#64) 1#64 →
          ThrZ Z exe (kidC T w1 w2) (wc1 workerTy w1 w2)
            ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) ::
              ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
            (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat)
            (BitVec.ofNat 64 (r1.lo + r1.size) - 8#64) →
          (∀ i, NodeZ Z exe (cN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)) i)
            (cBlk i)) →
          SegTC (NNZ exe endPc Z) p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))) Q) := by
  subst hr1
  obtain ⟨th, -, tls, cA, meW, -, hth, -, hpc, -, -, hcall, -, h8, h12, hbx, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  obtain ⟨h8', -, -, hA⟩ := hPC _ hXs
  have htl : tls = (tcbOf lab q).toNat := by
    rw [← h8]; exact congrArg BitVec.toNat h8'
  subst htl
  have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
    show (stacksA lab + 16384#64).toNat = _
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hr1e : r1Of lab = ⟨(stacksA lab).toNat + 16384, 16384⟩ := by
    rw [show r1Of lab = ⟨(r1Of lab).lo, 16384⟩ from rfl, hlo1]
  obtain ⟨htop, hlo0, hsz, hR, hlo', hhi'⟩ := Spike.Lib.X64.Rt.childStub_region_stk hr1e hbd
  have hh : handed t.2 0 ((r1Of lab).lo + (r1Of lab).size) = some (0, r1Of lab) := by
    simp [handed, hheld]
  have hcode : ∀ st : State, st.exe = exe → st.endPc = endPc →
      CodeAt st ((_root_.Executable.labels exe).label x21L + 46) svcB := fun st hse hsn =>
    codeAt_blockAt_lays hp hse (hsn.trans hend) (by
      have hw := wake_wcCloneIn
      simp only [Spike.Lib.X64.WakePh.WcClone.wcCloneIn, Bool.and_eq_true] at hw
      exact hw.2)
  have h12' : th.st.st.1.regs.get64 .r12 = BitVec.ofNat 64 cA := by
    rw [← h12]; simp
  have hbx' : th.st.st.1.regs.get64 .rbx = BitVec.ofNat 64 meW := by
    rw [← hbx]; simp
  have hcA : cA < 2 ^ 64 := by rw [← h12]; exact BitVec.isLt _
  have hmW : meW < 2 ^ 64 := by rw [← hbx]; exact BitVec.isLt _
  refine ⟨th, cA, meW, hth, hcall, fun w1 w2 => ⟨?_, fun hv1 htag hv2 hc8 hcout hS htp4 hT hown hSx hZ hZc => ?_⟩⟩
  · rw [← h12', ← hbx']
    exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo0 hsz
  obtain ⟨d, hdf, hb, ha, hty⟩ := hpw
  have hl := preChild_hlim (t := th) hA hh hbd hsz htls hout
    { th.st.st.1.regs with fsBase := UInt64.ofNat (tcbOf lab q).toNat } rfl
  obtain ⟨l1, l2, l3, l4⟩ := hl
  refine seg_childStubNN hp hend (FStable.dframe _ _) hR hlo' hhi'
    ⟨l1, l2, l3, fun v hv => ?_⟩ ⟨l1, l2, l3, fun v hv => ?_⟩
    (kid_split hdf hb ha hty w1 w2) ?_ (d := "d") (a := .var "c") (b := .lit 1)
    (e1 := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)) rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]) htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, ValRep])
    rfl hK hS htp4 (x := "w") (au := .var "j") (e := .ret .unit) rfl rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) rfl rfl hT hown hSx hZc hZ
  · have := (l4 v hv).1
    rwa [show BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - 8#64 - 8#64 - (32 : Int64).toBitVec =
      BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - (48 : Int64).toBitVec by
        rw [show (32 : Int64).toBitVec = 32#64 from rfl, show (48 : Int64).toBitVec = 48#64 from rfl]; bv_omega]
  · have := (l4 v hv).2
    rwa [show BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - 8#64 - 48#64 - 8#64 - (16 : Int64).toBitVec =
      BitVec.ofNat 64 ((r1Of lab).lo + (r1Of lab).size) - (48 : Int64).toBitVec - (32 : Int64).toBitVec by
        rw [show (32 : Int64).toBitVec = 32#64 from rfl, show (48 : Int64).toBitVec = 48#64 from rfl,
          show (16 : Int64).toBitVec = 16#64 from rfl]; bv_omega]
  intro m hm
  rw [hm _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; exact hc8)
    (by simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA, Nat.mod_eq_of_lt htop]; omega),
    Spike.Lib.X64.Rt.childAfter_dmem hh]
  exact Spike.Lib.X64.Rt.loadInt_copyRange_none (by omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; unfold Range.contains; omega) (by decide)

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Child.seg_childPreNN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_childPreNN

end Spike.Lib.X64.Flow.Worker.Wake.Child
