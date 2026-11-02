/-
**hello.w's `print` system-call data at the clone** (x86-64; the twin of `Spike/Lib/HelloChildSvcClone.lean`): at
main's `clone` (`ClonePreH`), on main's `%r12`, `%rbx`, `%r13`, `%r14`, `%r15`, `%r9` as the child's words, the
packet's buffer word is a locative to the slice's buffer label `lb` (`SlRep`), which the placement puts at main's
`%r12` (`%rbx`, the slice's offset, is `0`), its count word `13`, and `print`'s count `printN 13 2` fits (`hfit`,
a premise on `%r12`).

- `hsvc_clone`: the child's `print` data at `n = 13`, `m = 2`: the packet's slice words, the buffer address
  `w0 + setWidth 64 (w1.take 32) = w0`, its label's placement, the count word and the count's bounds.

## Differences from the AArch64 version

- The child's words are main's `%r12`, `%rbx`, `%r13`, `%r14`, `%r15`, `%r9` at the clone (AArch64 `x9 .. x14`),
  the stub's registers (`Hello.Child.childJ`); `hfit` is on `%r12` (AArch64 `x9`).
- `ClonePreH` takes no label prefix (AArch64's `pfx`).
- The module imports `X64HelloClonePreH` and `X64HelloChild` directly (AArch64: through `HelloChildWords`).
-/
import Spike.Lib.X64HelloClonePreH
import Spike.Lib.X64HelloChild

namespace Spike.Lib.X64HelloPreA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH)

variable {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **The child's `print` data at the clone's words**: main's source at the `spawn` with the slice words
`[lb, 2, 13]` (`SpawnSrcH`), the buffer word `cst (loc lb)` placed at the buffer address `w'.w0 + w'.w1`'s low half
`= w'.w0`, the count word `13`, `print`'s count fitting (from `%r12 + 13 < 2^64`) and below `2^63`. -/
theorem hsvc_clone (h : ClonePreH Λ r0 r1 X lbl t s) {th : Thread isa} (hth : t.1.threads = #[th])
    (hfit : (th.st.st.1.regs.get64 .r12).toNat + 13 < 2 ^ 64) :
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
      printN 13 2 < 2 ^ 63 := by
  intro w'
  obtain ⟨th', th0, hd, _, _, _, sl0, sl1, _, _, l, ws, hth', hs, -, -, -, -, -, -, h12, hbx,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, -, hsl, -, -, -⟩ := h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨lb, rfl, hlb, rfl, -, -⟩ := hsl
  have hbx' : th.st.st.1.regs.get64 .rbx = 0#64 := BitVec.eq_of_toNat_eq hbx
  have key : ∀ a b : BitVec 64, b = 0#64 → a + BitVec.setWidth 64 (b.take 32) = a := by
    rintro a b rfl; simp [BitVec.take]
  have he : w'.w0 + BitVec.setWidth 64 (w'.w1.take 32) = w'.w0 := key _ _ hbx'
  have h12' : w'.w0.toNat = sl0 := h12
  refine ⟨lb, ⟨th0, hd, l, hs, hsrc⟩, he, rfl, ?_, rfl, ?_, by decide⟩
  · rw [he, h12']; exact hlb
  · rw [he, show printN 13 2 = 13 by decide]; exact hfit

end Spike.Lib.X64HelloPreA

/-- info: 'Spike.Lib.X64HelloPreA.hsvc_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloPreA.hsvc_clone
