/-
**The slice words' representations at main's registers at the clone** (x86-64; the twin of
`Spike/Lib/HelloHv012.lean`, its live part). At `ClonePreH`, the slice `ws` is `[b, m, n]` (`SlRep.valRep`) and
its words `b`, `m`, `n` are represented by main's `%r12`, `%r13`, `%r14` (`SlRep`'s first, third and fourth
numbers).

- `hv012_of_clone`: the three representations at the clone.

**Where this differs from AArch64**: `ClonePreH` is `X64HelloPreA`'s (no label prefix `pfx`) and the slice's
words are in `%r12`, `%r13`, `%r14` (A64: `x9`, `x11`, `x12`). A64's `hv012_of_clone_words` is not used by the
hello proof and has no twin.
-/
import Spike.Lib.X64HelloClonePreH

namespace Spike.Lib.X64HelloHv012

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (ValRep)
open Spike.Lib.X64WakeA64 (Cfg)
open Spike.Lib.X64HelloMainPreSrc (SpawnSrcH SlRep)
open Spike.Lib.X64HelloPreA (ClonePreH)

/-- **The slice words' representations at main's registers at the clone** (module doc). -/
theorem hv012_of_clone {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Cfg} {s : TermRun.Cfg} (h : ClonePreH Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isa) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (l : WeakMem.AllocLabel)
      (b m n : TermRun.Word), t.1.threads = #[th] ∧ s.ths = #[th0] ∧
      SpawnSrcH l [b, m, n] ⟨th0.term, th0.env, hd⟩ ∧
      ValRep lbl b.val (th.st.st.1.regs.get64 .r12).toNat ∧ ValRep lbl m.val (th.st.st.1.regs.get64 .r13).toNat ∧
      ValRep lbl n.val (th.st.st.1.regs.get64 .r14).toNat := by
  obtain ⟨th, th0, hd, tls, cA, meW, sl0, sl1, sl2, sl3, l, ws, hth, hs, -, -, -, -, -, -, h9, -, h11, h12, -, -, -,
    -, -, -, -, -, -, -, -, hS, -, hR, -⟩ := h
  obtain ⟨b, m, n, rfl, hb, hm, hn⟩ := hR.valRep
  exact ⟨th, th0, hd, l, b, m, n, hth, hs, hS, h9 ▸ hb, h11 ▸ hm, h12 ▸ hn⟩

end Spike.Lib.X64HelloHv012

/-- info: 'Spike.Lib.X64HelloHv012.hv012_of_clone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloHv012.hv012_of_clone
