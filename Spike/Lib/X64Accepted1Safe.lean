/-
**`hsafe` for a one-block `Accepted1` program** (x64), the twin of
`Spike/Lib/X64Accepted0Safe.lean`: `safe_of_accepted1main`, `SrcSafe` at the
single-thread source parameters `srcP1 arch` and every fragment, vacuous
since no reachable source thread is at a memory operation (`reach_noMem`
from `accepted1main_noMem`, `Spike/Lib/Accepted1Src.lean`).
-/
import Spike.Lib.Accepted1Src
import Spike.Lib.SrcP1
import Spike.Lib.X64Consumer

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem Spike.Lib.Ret0Src Spike.Lib.Accepted1Src

/-- **`hsafe` for a one-block `Accepted1` program**, at every fragment: no
reachable source thread is at a load, a store or an exchange. -/
theorem safe_of_accepted1main {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) (arch : WeakMem.Arch) (I : Inv) :
    SrcSafe (Spike.Lib.srcP1 arch) [d] I := by
  have hR := fun {tr s} (h : (SrcSem.source (Spike.Lib.srcP1 arch) [d]).Reach tr s) =>
    reach_noMem (accepted1main_noMem hd) (Spike.Lib.srcP1_hooks arch) (mainInit_noMem 1) h
  constructor
  · intro tr s th hr h0 lbl lsize st hd _ x a e ty w sa ht
    have hn := (hR hr 0 th h0).1
    rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at hn <;> exact (hn.1 trivial).elim
  · intro tr s th hr h0 lbl lsize st hd _ x sa u v e hx
    have hn := (hR hr 0 th h0).1
    obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
      simp only at ht <;> rw [ht] at hn <;> exact (hn.1 trivial).elim

end Spike.Lib.X64Consumer
