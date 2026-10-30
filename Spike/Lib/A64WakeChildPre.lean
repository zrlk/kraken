/-
**wake.w on AArch64: the spawned child thread from main's `clone`** (hello
plan 1.2, the spawn's child half, composed): from main's state at its
`clone` (`Spike.Lib.WakePreA.ClonePre`, its runtime facts `PreChild`:
`Spike.Lib.A64.Rt.PreChild`), the child `childAfter` gives is in `At` of
the stub's node (`childN`, region `childR top (-16384)` the handed range
`r1 = r1Of lab`, frame condition its first memory outside it), and from
there one segment with the thread rows to any fragment
(`Spike.Lib.A64.Flow.Worker.Wake.Child.seg_childStub`): its source the
spawn's `tail worker [] (var "a") []` on the argument's two words (`kidC`),
the tail call and the `split` (`Split.kid_split`) to the `store rel c 1`,
then the `unpark j` and `ret `.

Discharged here: the region's facts (`Rt.childStub_region_stk`), the stack
limit (`Rt.PreChild.preChild_hlim` from `TcbArea`), the source's controls
and evaluations, the cell off the child's memory (`hdm`, from the cell off
`r1`). Left to the caller (inside the conclusion, per the argument words
`w1 w2`): the words' representations of `cA`/`meW`, the cell off `r1`, the
permit and `exited` words (`StOk`), and outside it the layout facts of the
runtime's areas and the kernel model.

- `kidC T w1 w2`: the child's source control after the spawn.
- `seg_childPre`: the child thread from `ClonePre`.
-/
import Spike.Lib.A64WakeChildAt
import Spike.Lib.A64WakeSplit
import Spike.Lib.Rt.A64RtPreChild

namespace Spike.Lib.A64.Flow.Worker.Wake.Child

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerBody workerTy wc1 kid_split)
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild preChild_hlim)
open Spike.Lib.A64.Flow.Ret0 (stacksA StOk)
open Spike.Lib.A64.Rt (TcbGG tcbOf)
open Spike.Lib.A64Consumer (Own)

/-- **The child's source control after the spawn**: `tail worker [] (var
"a") []`, `a` bound (at `T`) to the argument's two words. -/
def kidC (T : Ty) (w1 w2 : TermRun.Word) : Ctl :=
  ⟨.tail "worker" [] (.var "a") [], [("a", T, [w1, w2])], none⟩

/-- **The spawned child thread from main's `clone`** in any valid layout of
`wakeProg`: main's state at the clone (`ClonePre`, its runtime facts
`PreChild` for the labels `lab` and the TCB ghosts `q`, `r1` the second
take's range `r1Of lab`) gives its thread `th`, the cell's word `cA` and
main's `ThreadId` word `meW`, the `clone` asking for `r1`'s top and the
TCB; for any argument words `w1 w2` the child is in `At` of `childN` (region
`childR top (-16384)`, frame condition its first memory outside it), and,
the words representing `cA` (a tag-0 location) and `meW`, the cell off `r1`,
the permit word of `meW` and the child's `exited` word runtime words
(`StOk`), the child runs as one segment with the thread rows to any
fragment `Q`. -/
theorem seg_childPre {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q : Frag isaLSE2} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
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
          SegT p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
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
  refine ⟨th, cA, meW, hth, hcall, fun w1 w2 => ⟨?_, fun hv1 htag hv2 hc8 hcout hS htp4 hSx => ?_⟩⟩
  · rw [← h9', ← h10']
    exact child_at hcode he hn hd (he ▸ hpc) hh htop hlo0 hsz
  obtain ⟨d, hdf, hb, ha, hty⟩ := hpw
  refine seg_childStub hp hend (FStable.dframe _ _) hR hal' hlo' hhi'
    (preChild_hlim hA hh hbd hsz htls hout)
    (kid_split hdf hb ha hty w1 w2) ?_ (d := "d") (a := .var "c") (b := .lit 1)
    (e1 := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit)) rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]) htag rfl (by simp [TermRun.cst, Promises.TVal.mk0, ValRep])
    rfl hK hS htp4 (x := "w") (au := .var "j") (e := .ret .unit) rfl rfl rfl
    (by rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmW]) rfl rfl hSx
  intro m hm
  rw [hm _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; exact hc8)
    (by simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA, Nat.mod_eq_of_lt htop]; omega),
    Spike.Lib.A64.Rt.childAfter_dmem hh]
  exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega)
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcA]; unfold Range.contains; omega) (by decide)

end Spike.Lib.A64.Flow.Worker.Wake.Child
