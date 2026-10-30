/-
**`hsafe` at any call depth for an `Accepted1` program with calls**
(AArch64), the frames twin of `Spike/Lib/A64Accepted1Safe.lean` and the
twin of `Spike/Lib/X64Accepted1SafeS.lean`: `safeS_of_accepted1`,
`SrcSafeS` at the single-thread source parameters `srcP1 arch` and every
fragment, vacuous since no reachable source thread is at a memory operation
(`reach_noMem` from `accepted1_noMem`, `Spike/Lib/Accepted1NoMem.lean`).
-/
import Spike.Lib.Accepted1NoMem
import Spike.Lib.SrcP1
import Spike.Lib.A64ConsumerS

namespace Spike.Lib.A64ConsumerS

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem Spike.Lib.Ret0Src Spike.Lib.Accepted1Src

/-- **`hsafe` at any call depth for an `Accepted1` program**, at every
fragment: no reachable source thread is at a load, a store or an exchange. -/
theorem safeS_of_accepted1 {p : Prog} (hp : Scc.Lower.Accepted1 p = true) (arch : WeakMem.Arch) (I : InvS) :
    SrcSafeS (Spike.Lib.srcP1 arch) p I := by
  have hR := fun {tr s} (h : (SrcSem.source (Spike.Lib.srcP1 arch) p).Reach tr s) =>
    reach_noMem (accepted1_noMem hp) (Spike.Lib.srcP1_hooks arch) (mainInit_noMem 1) h
  constructor
  · intro tr s th hr h0 lbl lsize st hd _ x a e ty w sa ht
    have hn := (hR hr 0 th h0).1
    rcases ht with ht | ⟨b, ht⟩ <;> rw [ht] at hn <;> exact (hn.1 trivial).elim
  · intro tr s th hr h0 lbl lsize st hd _ x sa u v e hx
    have hn := (hR hr 0 th h0).1
    obtain ⟨-, ⟨a, t, pw, μ, ht, -⟩ | ⟨b, i, t, pw, ti, iws, μ, sb, k, ht, -⟩⟩ := hx <;>
      simp only at ht <;> rw [ht] at hn <;> exact (hn.1 trivial).elim
  · intro tr s hr
    exact BoxCount.reach_boxLe (.inl (Spike.Lib.srcP1_hooks arch))
      (fun c hc => by subst hc; exact BoxCount.mainStart_boxLe 1) hr

end Spike.Lib.A64ConsumerS
