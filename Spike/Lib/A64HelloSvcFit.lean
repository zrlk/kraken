/-
**hello.w's `print` buffer fits below `2^64` at the clone** (AArch64): at main's `clone`
(`ClonePreH`) the slice's buffer label `lb` is placed at main's `x9` (`SlRep`) and holds a source message at
offset `1` (`ClonePreH`'s buffer-content conjunct, `bufW 1`), so under any `MemRelP` over the source memory of a
well-formed layout `lbl lb + 16 ≤ 2^64` (`MemRelP.addr_lt` at `⟨lb, 1⟩`), hence `x9 + 13 < 2^64`.

- `x9_fit_clone`: `hsvc_clone`'s `hfit` from `MemRelP` and `Layout.WF`.
- `hsvc_cloneM`: `hsvc_clone` with `hfit` discharged.
-/
import Spike.Lib.HelloChildSvcClone

namespace Spike.Lib.HelloSvcFit

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloPreA (ClonePreH)

variable {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `x9` at the clone has 13 bytes of room**: the buffer label holds a source message at
offset `1`, so it is in bounds and placed below `2^64 - 16`. -/
theorem x9_fit_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th])
    {Λ' : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ' lbl lsize ts tm s.mem tp tq sp) (hwf : Λ'.WF) :
    th.st.st.1.regs.X9.toBitVec.toNat + 13 < 2 ^ 64 := by
  obtain ⟨th', _th0, _hd, _tls, _cA, _meW, sl0, _sl1, _sl2, _sl3, _l, ws, hth', -, -, -, -, -, -, -, h9, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsl, -, -, hbuf⟩ := h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨lb, rfl, hlb, -, -, -⟩ := hsl
  obtain ⟨j, m, hj, hm1, -, -⟩ := hbuf lb rfl 1 (by decide)
  obtain ⟨⟨m', hm', hloc⟩, -⟩ := hj
  have hmem : m' ∈ s.mem.toList := Array.mem_toList_iff.mpr (Array.mem_of_getElem? hm')
  obtain ⟨-, -, hoff⟩ := hm.lbl_mem m' hmem
  rw [hloc] at hoff
  have hx : wordAddr lbl ⟨lb, 1⟩ = some (sl0 + 8 * 1) := by simp [wordAddr, hlb]
  have := hm.addr_lt hwf hx hoff
  have h9' : th.st.st.1.regs.X9.toBitVec.toNat = sl0 := h9
  omega

/-- **`hsvc_clone` with its fit discharged** by `x9_fit_clone`. -/
theorem hsvc_cloneM (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th])
    {Λ' : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ' lbl lsize ts tm s.mem tp tq sp) (hwf : Λ'.WF) :
    let w' : Words := ⟨th.st.st.1.regs.X9.toBitVec, th.st.st.1.regs.X10.toBitVec, th.st.st.1.regs.X11.toBitVec,
      th.st.st.1.regs.X12.toBitVec, th.st.st.1.regs.X13.toBitVec, th.st.st.1.regs.X14.toBitVec⟩
    ∃ lb : WeakMem.AllocLabel, (∃ th0 hd l, s.ths = #[th0] ∧
        SpawnSrcH l [TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)]
          ⟨th0.term, th0.env, hd⟩) ∧
      w'.w0 + BitVec.setWidth 64 (w'.w1.take 32) = w'.w0 ∧
      (TermRun.cst (.loc ⟨lb, 0⟩ 0)).val = .loc ⟨lb, 0⟩ 0 ∧
      lbl lb = some (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat ∧
      (TermRun.cst (.num 13)).val = .num 13 ∧
      (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat + printN 13 2 < 2 ^ 64 ∧
      printN 13 2 < 2 ^ 63 :=
  Spike.Lib.HelloPreA.hsvc_clone h hth (x9_fit_clone h hth hm hwf)

end Spike.Lib.HelloSvcFit

/-- info: 'Spike.Lib.HelloSvcFit.x9_fit_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSvcFit.x9_fit_clone

/-- info: 'Spike.Lib.HelloSvcFit.hsvc_cloneM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloSvcFit.hsvc_cloneM
