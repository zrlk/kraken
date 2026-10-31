/-
**wake.w on x86-64: the spawned child thread from main's `clone`** (the x64
twin of `Spike/Lib/A64WakeChildPre.lean`, the spawn's child half, composed):
from main's state at its `clone` (`Spike.Lib.X64WakePreA.ClonePre`, its
runtime facts `PreChild`: `Spike.Lib.X64.Rt.PreChild`), the child
`childAfter` gives is in `At` of the child's node (`childN`, region
`childR top (-16384)` the handed range `r1 = r1Of lab`, frame condition its
first memory outside it), and from there one segment with the thread rows to
any fragment (`seg_childStub`): its source the spawn's `tail worker [] (var
"a") []` on the argument's two words (`kidC`), the tail call and the `split`
(`Split.kid_split`) to the `store rel c 1`, then the `unpark j` and
`ret ()`.

Discharged here: the region's facts (`Rt.childStub_region_stk`), the stack
limits of both prologues (`Rt.PreChild.preChild_hlim` from `TcbArea`), the
source's controls and evaluations, the cell off the child's memory (`hdm`,
from the cell off `r1`). Left to the caller (inside the conclusion, per the
argument words `w1 w2`): the words' representations of `cA`/`meW`, the cell
off `r1`, the permit and `exited` words (`StOk`), the thread pointer's load
(`LdOk`, `OwnAt`), and outside it the layout facts of the runtime's areas
and the kernel model.

- `kidC T w1 w2`: the child's source control after the spawn.
- `thrR R`, `thrR_ok`, `dframe_thrR`, `FStable.thrR`, `At.toThr`: the
  child's region re-based at the worker thread's entry `%rsp` (8 below the
  child's: the `call`'s return address), the same addresses.
- `seg_childStub`: the child from `childN` to any fragment
  (`Child.seg_child`, then `Labels.seg_thrWorker` in `thrR R`).
- `seg_childPre`: the child thread from `ClonePre`.

**Unlike AArch64** (forced by the x64 shape):

- the stub ends in a `call` (`Child.seg_child`'s exit `cE`: `%rsp` 8 below
  the child's, the return address in the cell): the worker thread runs in
  the child's region re-based there (`thrR`), its entry `sp0 - 8`
  (AArch64's `bl` keeps `sp`).
- `seg_thrWorker` takes one limit premise per prologue (`hlim`, `hlimW`,
  `Ret0.LimOk`), both from `preChild_hlim`'s two rooms; and the thread
  pointer's load (`hT`, `hown`), left to the caller.
- no alignment premise; `ClonePre` and `childN` take no label prefix.
-/
import Spike.Lib.X64WakeChildAt
import Spike.Lib.X64WakeCloneIn
import Spike.Lib.X64WakeSplit
import Spike.Lib.X64WakeWorkerLabels
import Spike.Lib.Rt.X64RtPreChild
import Spike.Lib.X64WakePreA

namespace Spike.Lib.X64.Flow.Worker.Wake.Child

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.X64 (Lays endOf codeAt_blockAt_lays)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh (wake_childIn wake_wcCloneIn)
open Spike.Lib.X64.WakePh.WcClone (x21L svcB)
open Spike.Lib.X64.WakePh.Child (childN childR cE seg_child child_at)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerBody workerTy wc1 kid_split)
open Spike.Lib.X64.Flow.Worker.Wake.Labels (thrJE seg_thrWorker)
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild preChild_hlim)
open Spike.Lib.X64.Flow.Ret0 (stacksA StOk LdOk LimOk)
open Spike.Lib.X64.Rt (TcbGG tcbOf)
open Spike.Lib.X64Consumer (Own)

/-- **The child's source control after the spawn**: `tail worker [] (var
"a") []`, `a` bound (at `T`) to the argument's two words. -/
def kidC (T : Ty) (w1 w2 : TermRun.Word) : Ctl :=
  ⟨.tail "worker" [] (.var "a") [], [("a", T, [w1, w2])], none⟩

/-! ## The worker thread's region -/

/-- **The child's region re-based at the worker thread's entry**: based 8
below (`%rsp` after the `call`), the same addresses. -/
def thrR (R : Region) : Region := R.callee (-8) (R.lo + 8) (R.hi + 8)

theorem thrR_base {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : -8 < R.hi) :
    ((thrR R).base.toNat : Int) = R.base.toNat - 8 := by
  have := Region.callee_base (kc := -8) (lo' := R.lo + 8) (hi' := R.hi + 8) hR (by omega) (by omega) hhi
  rw [thrR, this]; omega

theorem thrR_ok {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : -8 < R.hi) : (thrR R).OK :=
  Region.callee_ok hR (by omega) (by omega) hhi (by omega)

/-- The re-based region's frame is the child's (the same addresses). -/
theorem dframe_thrR {R : Region} (hR : R.OK) (hlo : R.lo ≤ -8) (hhi : -8 < R.hi) {m m' : MachineData} :
    DFrame (thrR R) m m' ↔ DFrame R m m' := by
  have hb := thrR_base hR hlo hhi
  have e1 : (thrR R).lo = R.lo + 8 := rfl
  have e2 : (thrR R).hi = R.hi + 8 := rfl
  constructor
  · intro h a ha hd; exact h a ha (by rw [hb, e1, e2]; omega)
  · intro h a ha hd; exact h a ha (by rw [hb, e1, e2] at hd; omega)

theorem FStable.thrR {R : Region} {F : MachineData → Prop} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -8)
    (hhi : -8 < R.hi) : FStable (thrR R) F :=
  fun m m' hm hd => hF m m' hm ((dframe_thrR hR hlo hhi).1 hd)

/-- **A node at offset `-8` of the child's region is one at offset `0` of
the re-based region**, its cells shifted by 8 (`hJ`). -/
theorem At.toThr {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {pc : Int64}
    {J J' : AS → Ctl → Prop} {s : State} {c : Ctl} (h : At exe endPc R F ⟨pc, ⟨-8, []⟩, J⟩ s c)
    (hJ : ∀ σ c, J σ c → J' { σ with slot := fun k => σ.slot (-8 + k) } c) :
    At exe endPc (thrR R) F ⟨pc, ⟨0, []⟩, J'⟩ s c := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJσ⟩ := h
  refine ⟨he, hn, hd, hpc, { σ with slot := fun k => σ.slot (-8 + k) }, ⟨hA.regs, hA.zmms, hA.status, ?_, ?_⟩,
    hF, hJ σ c hJσ⟩
  · intro r k hk
    by_cases hr : r = .rsp
    · subst hr
      simp only [SO.get, ite_true, Option.some.injEq] at hk
      subst hk
      rw [thrR, Region.callee_addr, Int.add_zero]
      exact hA.so .rsp (-8) (SO.get_rsp _)
    · simp [SO.get, lk, hr] at hk
  · intro k hk
    have hk' := Region.callee_off (R := R) (kc := -8) (lo' := R.lo + 8) (hi' := R.hi + 8) (by omega) (by omega)
      (by omega) hk
    obtain ⟨j, hj, hv⟩ := hA.slot _ hk'
    exact ⟨j, by rw [thrR, Region.callee_addr]; exact hj, hv⟩

/-! ## The child's run -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Region} {F : MachineData → Prop}

/-- **The child's run is one segment with the thread rows** in any valid
layout of wake's cells, from its node past the `clone` (`childN`) to any
fragment: the stub (`Child.seg_child`: the `je` taken, `%rbp` zeroed, the
two words in `%rdi`/`%rsi`, the `call`), then the worker thread
(`Labels.seg_thrWorker` in the re-based region `thrR R`, entry `%rsp`
`sp0 - 8`; its hypotheses are this one's but for `hsplit` and the limits,
which take the stub's `cW` and `sp0 - 8`). -/
theorem seg_childStub {Q : Frag isa} (hp : Lays exe SccCode.wakeCells kp)
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
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") tp tp)
    (hSx : StOk ms F (tp + 24#64) 1#64) :
    SegT p lbl ms (At exe endPc R F (childN (_root_.Executable.labels exe).label cW A B tp sp0)) Q := by
  have hlo8 : R.lo ≤ -8 := by omega
  have hhi8 : -8 < R.hi := by omega
  refine SegT.seq (Seg.toT (seg_child hp hend wake_childIn hF hR hlo hhi)) ?_
  refine (seg_thrWorker hp hend (FStable.thrR hF hR hlo8 hhi8) (thrR_ok hR hlo8 hhi8)
    (by show R.lo + 8 ≤ -120; omega) (by show 8 ≤ R.hi + 8; omega) hlim hlimW hsplit hdm ht hev hv htag hevb
    hvb hc2 hK hS htp4 htu hhu hevu hvu hc3 hret3 hT hown hSx).mono_pre fun s c h => At.toThr h ?_
  rintro σ c ⟨h1, h2, h3, -, h5, h6, -⟩
  exact ⟨h1, h2, h3, h5, h6⟩

end Seg

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Child.seg_childStub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_childStub

/-- **The spawned child thread from main's `clone`** in any valid layout of
wake's cells: main's state at the clone (`ClonePre`, its runtime facts
`PreChild` for the labels `lab` and the TCB ghosts `q`, `r1` the second
take's range `r1Of lab`) gives its thread `th`, the cell's word `cA` and
main's `ThreadId` word `meW`, the `clone` asking for `r1`'s top and the
TCB; for any argument words `w1 w2` the child is in `At` of `childN` (region
`childR top (-16384)`, frame condition its first memory outside it), and,
the words representing `cA` (a tag-0 location) and `meW`, the cell off `r1`,
the permit word of `meW` and the child's `exited` word runtime words
(`StOk`), the thread pointer's load from the TCB's self word (`LdOk`,
`OwnAt`), the child runs as one segment with the thread rows to any
fragment `Q`. -/
theorem seg_childPre {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q : Frag isa} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
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
          OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12")
            (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (tcbOf lab q).toNat) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (BitVec.ofNat 64 (tcbOf lab q).toNat + 24#64) 1#64 →
          SegT p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
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
  refine ⟨th, cA, meW, hth, hcall, fun w1 w2 => ⟨?_, fun hv1 htag hv2 hc8 hcout hS htp4 hT hown hSx => ?_⟩⟩
  · rw [← h12', ← hbx']
    exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo0 hsz
  obtain ⟨d, hdf, hb, ha, hty⟩ := hpw
  have hl := preChild_hlim (t := th) hA hh hbd hsz htls hout
    { th.st.st.1.regs with fsBase := UInt64.ofNat (tcbOf lab q).toNat } rfl
  obtain ⟨l1, l2, l3, l4⟩ := hl
  refine seg_childStub hp hend (FStable.dframe _ _) hR hlo' hhi'
    ⟨l1, l2, l3, fun v hv => ?_⟩ ⟨l1, l2, l3, fun v hv => ?_⟩
    (kid_split hdf hb ha hty w1 w2) ?_ (d := "d") (a := .var "c") (b := .lit 1)
    (e1 := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)) rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]) htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, ValRep])
    rfl hK hS htp4 (x := "w") (au := .var "j") (e := .ret .unit) rfl rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) rfl rfl hT hown hSx
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

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.Child.seg_childPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms seg_childPre

end Spike.Lib.X64.Flow.Worker.Wake.Child
