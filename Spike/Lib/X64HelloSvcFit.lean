/-
**hello.w's `print` buffer fits below `2^64` at the clone** (x86-64; the twin of `Spike/Lib/A64HelloSvcFit.lean`):
at main's `clone` (`ClonePreH`) the slice's buffer label `lb` is placed at main's `%r12` (`SlRep`) and holds a
source message at offset `1` (`ClonePreH`'s buffer-content conjunct, `BufAtSpawn`, `bufW 1`), so under any
`MemRelP` over the source memory of a well-formed layout `lbl lb + 16 ≤ 2^64` (`MemRelP.addr_lt` at `⟨lb, 1⟩`),
hence `%r12 + 13 < 2^64`.

- `r12_fit_clone`: `hsvc_clone`'s `hfit` from `MemRelP` and `Layout.WF`.
- `hsvc_cloneM`: `hsvc_clone` with `hfit` discharged.

**Unlike AArch64**: the buffer's address is main's `%r12` (AArch64's `x9`, hence the name `r12_fit_clone` for
`x9_fit_clone`) and the child's words are `%r12`, `%rbx`, `%r13`, `%r14`, `%r15`, `%r9` (`X64HelloPreA.hsvc_clone`);
`ClonePreH` takes no label prefix and its buffer conjunct is `BufAtSpawn` at the slice's head label.
-/
import Spike.Lib.X64HelloChildSvcClone

namespace Spike.Lib.X64HelloSvcFit

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.X64HelloPreA (ClonePreH)

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **main's `%r12` at the clone has 13 bytes of room**: the buffer label holds a source message at offset `1`,
so it is in bounds and placed below `2^64 - 16`. -/
theorem r12_fit_clone (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th])
    {Λ' : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ' lbl lsize ts tm s.mem tp tq sp) (hwf : Λ'.WF) :
    (th.st.st.1.regs.get64 .r12).toNat + 13 < 2 ^ 64 := by
  obtain ⟨th', _th0, _hd, _tls, _cA, _meW, sl0, _sl1, _sl2, _sl3, _l, ws, hth', -, -, -, -, -, -, -, h12, -,
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
  have h12' : (th.st.st.1.regs.get64 .r12).toNat = sl0 := h12
  omega

/-- **`hsvc_clone` with its fit discharged** by `r12_fit_clone`. -/
theorem hsvc_cloneM (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th])
    {Λ' : Scc.Sem.Layout} {lsize : WeakMem.AllocLabel → Nat} {ts : Nat → Option Nat} {tm : Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ' lbl lsize ts tm s.mem tp tq sp) (hwf : Λ'.WF) :
    let w' : Words := ⟨th.st.st.1.regs.get64 .r12, th.st.st.1.regs.get64 .rbx, th.st.st.1.regs.get64 .r13,
      th.st.st.1.regs.get64 .r14, th.st.st.1.regs.get64 .r15, th.st.st.1.regs.get64 .r9⟩
    ∃ lb : WeakMem.AllocLabel, (∃ th0 hd l, s.ths = #[th0] ∧
        SpawnSrcH l [TermRun.cst (.loc ⟨lb, 0⟩ 0), TermRun.cst (.num 2), TermRun.cst (.num 13)]
          ⟨th0.term, th0.env, hd⟩) ∧
      w'.w0 + BitVec.setWidth 64 (w'.w1.take 32) = w'.w0 ∧
      (TermRun.cst (.loc ⟨lb, 0⟩ 0)).val = .loc ⟨lb, 0⟩ 0 ∧
      lbl lb = some (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat ∧
      (TermRun.cst (.num 13)).val = .num 13 ∧
      (w'.w0 + BitVec.setWidth 64 (w'.w1.take 32)).toNat + printN 13 2 < 2 ^ 64 ∧
      printN 13 2 < 2 ^ 63 :=
  Spike.Lib.X64HelloPreA.hsvc_clone h hth (r12_fit_clone h hth hm hwf)

end Spike.Lib.X64HelloSvcFit

/-- info: 'Spike.Lib.X64HelloSvcFit.r12_fit_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSvcFit.r12_fit_clone

/-- info: 'Spike.Lib.X64HelloSvcFit.hsvc_cloneM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloSvcFit.hsvc_cloneM
