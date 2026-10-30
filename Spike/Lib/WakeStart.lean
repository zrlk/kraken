/-
**wake.w on AArch64: `Post` at the clone with the worker's relation**
(the `spawn` obligation's last step): `WakeA64.post_start`
at the empty owned words (`WakeOwn.post_startO`) and the worker's
`PT1` (`Spike/Lib/WakeW1.lean`), built at the spawn.

- `pt1_start`: the worker's relation at the spawn: the child at `Wi`, the
  spawned source thread at `wkTail` on one frame with no type variables,
  `EnvBody`, no promise (the source-promise conjunct vacuous, the target's
  promises `List.nodup_nil`).
- `post_startW`: `post_startO` with `Q.PT1 = PT1 D`, its `hPT1` from
  `pt1_start`.
-/
import Spike.Lib.WakeOwn
import Spike.Lib.WakeW1

namespace Spike.Lib.WakeStart

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.WakeT1
open Spike.Lib.WakeW1

/-- **The worker's relation at the spawn**: the child in `Wi`, the source
worker at `wkTail` on one frame with no type variables, its environment
`EnvBody`, no promise on either side. -/
theorem pt1_start {ι : Type} (D : WSide ι) (w : ι) (tm : Memory) (sm : WeakMem.Memory) {t1 : Thread isaLSE2}
    {s1 : TermRun.TTh} (hW : D.Wi w t1.st (Ctl.of s1)) (hst : s1.stack = []) (hσ : s1.σs = [])
    (ht : s1.term = wkTail) (henv : EnvBody (D.cw w) s1.env) (hp : s1.promises = []) (hp1 : t1.prom = []) :
    PT1 D w tm sm t1 s1 := by
  refine ⟨hW, hst, hσ, .inl ht, fun _ => henv, fun h => (h (.inl ht)).elim, ?_, ?_, ?_⟩
  · rw [hp]; exact Nat.zero_le _
  · intro k hk; rw [hp] at hk; cases hk
  · rw [hp1]; exact List.nodup_nil

/-- **`Post` at the clone with the worker's relation**: `post_startO` at
`Q.PT1 = PT1 D`, the spawned worker built by `pt1_start`. -/
theorem post_startW {Λ : Scc.Sem.Layout} {Q : WakeRel} {D : WSide Q.ι} (hQ : Q.own = WakeOwn.wakeOwn)
    (hQ1 : Q.PT1 = PT1 D) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isaLSE2} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hW1 : D.Wi w (childAfter abi d.2 0 th stack tls).st (Ctl.of s1)) (hst1 : s1.stack = [])
    (hσ1 : s1.σs = []) (ht1 : s1.term = wkTail) (henv1 : EnvBody (D.cw w) s1.env)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  have hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1 := by
    rw [hQ1]
    exact pt1_start D w _ _ hW1 hst1 hσ1 ht1 henv1 hsp1 childAfter_prom
  exact WakeOwn.post_startO hQ hSR h1 hs hi hp hmsgs hin hfits hG hb hown hsp0 hsp1 hs0 hs1 hfrz hfoot hj hjl
    hPT0 hPT1 hProt hKR

/-- info: 'Spike.Lib.WakeStart.post_startW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeStart.post_startW

end Spike.Lib.WakeStart
