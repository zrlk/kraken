/-
**hello.w's `print` `svc` data at the clone** (the data half; `HelloAssemblyI.hsvc_I`'s premises): at main's `clone`
(`ClonePreH`), on main's `x9 .. x14` as the child's words, the packet's
buffer word is a locative to the slice's buffer label `lb` (`SlRep`), which
the placement puts at main's `x9` (`x10`, the slice's offset, is `0`), its
count word `13`, and `print`'s count `printN 13 2` fits (`hfit`, a
premise on `x9`).

- `hsvc_clone`: `hsvc_I`'s `hpw`, `hl`, `hwn`, `hfit`, `hlen` at `n = 13`,
  `m = 2`, with the packet's slice words and the buffer address
  `w0 + setWidth 64 (w1.take 32) = w0`.
-/
import Spike.Lib.HelloChildWords

namespace Spike.Lib.HelloPreA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words)
open Spike.Lib.PrintSrc (printN)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)

variable {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
  {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg}

/-- **`hsvc_I`'s data at the clone's words**: main's source
at the `spawn` with the slice words `[lb, 2, 13]` (`SpawnSrcH`), the buffer
word `cst (loc lb)` (`hpw`) placed at the buffer address `w'.w0 + w'.w1`'s
low half `= w'.w0` (`hl`), the count word `13` (`hwn`), `print`'s count
fitting (`hfit` from `x9 + 13 < 2^64`, `hlen`). -/
theorem hsvc_clone (h : ClonePreH pfx Λ r0 r1 X lbl t s) {th : Thread isaLSE2} (hth : t.1.threads = #[th])
    (hfit : th.st.st.1.regs.X9.toBitVec.toNat + 13 < 2 ^ 64) :
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
      printN 13 2 < 2 ^ 63 := by
  intro w'
  obtain ⟨th', th0, hd, _, _, _, sl0, sl1, _, _, l, ws, hth', hs, -, -, -, -, -, -, h9, h10,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hsrc, -, hsl, -, -, -⟩ := h
  obtain rfl : th = th' := by
    rw [hth] at hth'
    exact List.singleton_inj.mp (congrArg Array.toList hth')
  obtain ⟨lb, rfl, hlb, rfl, -, -⟩ := hsl
  have h10' : th.st.st.1.regs.X10.toBitVec = 0#64 := BitVec.eq_of_toNat_eq h10
  have key : ∀ a b : BitVec 64, b = 0#64 → a + BitVec.setWidth 64 (b.take 32) = a := by
    rintro a b rfl; simp [BitVec.take]
  have he : w'.w0 + BitVec.setWidth 64 (w'.w1.take 32) = w'.w0 := key _ _ h10'
  have h9' : w'.w0.toNat = sl0 := h9
  refine ⟨lb, ⟨th0, hd, l, hs, hsrc⟩, he, rfl, ?_, rfl, ?_, by decide⟩
  · rw [he, h9']; exact hlb
  · rw [he, show printN 13 2 = 13 by decide]; exact hfit

end Spike.Lib.HelloPreA

/-- info: 'Spike.Lib.HelloPreA.hsvc_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloPreA.hsvc_clone
