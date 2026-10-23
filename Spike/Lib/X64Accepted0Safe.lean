/-
**`hsafe` for an `Accepted0` program** (x64): `safe_of_accepted0`,
`SrcSafe` at the single-thread source parameters `srcP1 arch` and every
fragment, vacuous since no reachable source thread is at a memory operation
(`reach_noMem` from `accepted0_noMem`, `Spike/Lib/Accepted0Src.lean`); the
generalization of `ret0_safe` (`Spike/Lib/X64Ret0Correct.lean`).
-/
import Spike.Lib.Accepted0Src
import Spike.Lib.SrcP1
import Spike.Lib.X64Consumer

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem Spike.Lib.Ret0Src Spike.Lib.Accepted0Src

/-- **`hsafe` for an `Accepted0` program**, at every fragment: no reachable
source thread is at a load, a store or an exchange. -/
theorem safe_of_accepted0 {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) (arch : WeakMem.Arch) (I : Inv) :
    SrcSafe (Spike.Lib.srcP1 arch) [d] I := by
  have hR := fun {tr s} (h : (SrcSem.source (Spike.Lib.srcP1 arch) [d]).Reach tr s) =>
    reach_noMem (accepted0_noMem hd) (Spike.Lib.srcP1_hooks arch) (mainInit_noMem 1) h
  constructor
  · intro tr s th hr h0 lbl lsize st hd _ x a e ty w sa ht
    have hn := (hR hr 0 th h0).1
    rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at hn <;> exact (hn.1 trivial).elim
  · intro tr s th hr h0 lbl lsize st hd _ x sa u v e hx
    have hn := (hR hr 0 th h0).1
    obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
      simp only at ht <;> rw [ht] at hn <;> exact (hn.1 trivial).elim

end Spike.Lib.X64Consumer
