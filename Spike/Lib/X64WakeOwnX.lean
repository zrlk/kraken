/-
**wake.w on x86-64: main owns its TCB word after the spawn**: the datum `own` of `WakeRel` at main
(thread 0) is the single
word `T` (`tcbM`) holding its address, the worker (thread 1) owns nothing.
Main's `scc_rt_park` call reads `tcbM` as an owned value (`OwnAt`, the
`hown` premise of `seg_parkCall`), so `X64WakeOwn.wakeOwn` (empty) is too
small for it; this map is its replacement for the `X` row variants.

- `wakeOwnX T`: `[(⟨T,8⟩, T.setWidth 128)]` at thread 0, `[]` at thread 1.
- `own1X`: `WCompatX.own1` (thread 1 owns nothing).
- `ownAt_const`: `OwnAt … T T` for a memory side whose own map is constantly `[(⟨T,8⟩, …)]`.
- `post_startOX`: `X64WakeA64.post_start` at `Q.own = wakeOwnX T`;
  `hsub0` from `hT0 : (⟨T,8⟩, T.setWidth 128) ∈ own₀` (the clone agreement),
  `hcov0` from `hcovT : (Q.P w).cov 0 ⟨T,8⟩` (direct at a `WakeP` instance
  with `own 0 l := l = ⟨T,8⟩`, `WakeP.wakeP_own_cov`), the others trivially.
- `hT0_ownGX`: `hT0` at `own₀ = ownGX L a s`, `s` on a pool stack (`selfOwn`).


-/
import Spike.Lib.X64WakeOwn
import Spike.Lib.X64WakeOwnPark

namespace Spike.Lib.X64WakeOwnX

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.X64WakeT1

/-- **The owned words after the spawn**: main's TCB word `T` holding its
address; the worker owns nothing. -/
def wakeOwnX {ι : Type} (T : BitVec 64) : ι → Nat → isa.State → List TermRun.Frame → List (Loc × Val) :=
  fun _ i _ _ => if i = 0 then [(⟨T, 8⟩, T.setWidth 128)] else []

@[simp] theorem wakeOwnX_zero {ι : Type} (T : BitVec 64) (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    wakeOwnX T w 0 s fs = [(⟨T, 8⟩, T.setWidth 128)] :=
  rfl

@[simp] theorem wakeOwnX_one {ι : Type} (T : BitVec 64) (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    wakeOwnX T w 1 s fs = [] :=
  rfl

/-- `WCompatX.own1`: the worker's owned words are none. -/
theorem own1X {ι : Type} (T : BitVec 64) (w : ι) (s : isa.State) : wakeOwnX T w 1 s [] = [] :=
  rfl

/-- `MemSide.own` of main's rows at `wakeOwnX`: constant in the state. -/
theorem own0X {ι : Type} (T : BitVec 64) (w : ι) (s : isa.State) :
    (fun _ => [((⟨T, 8⟩ : Loc), T.setWidth 128)]) s = wakeOwnX T w 0 s [] :=
  rfl

/-- **`OwnAt` at a constant own map**: every pc owns `T` holding `T`. -/
theorem ownAt_const {ms : MemSide isa} {exe : _root_.Executable} {endPc pc : Int64} {T : BitVec 64}
    (hown : ∀ s, ms.own s = [(⟨T, 8⟩, T.setWidth 128)]) : Spike.Lib.X64.OwnAt ms exe endPc pc T T :=
  fun s _ _ _ => (hown s) ▸ List.mem_singleton_self _

/-- **`post_start` with main owning `T`**: `X64WakeA64.post_start` at
`Q.own = wakeOwnX T`. `hT0`: the clone's own list holds `T` (the clone
agreement); `hcovT`: thread 0 covers `T`. -/
theorem post_startOX {Λ : Scc.Sem.Layout} {Q : WakeRel} {T : BitVec 64} (hQ : Q.own = wakeOwnX T) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isa} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hT0 : ((⟨T, 8⟩ : Loc), T.setWidth 128) ∈ own₀) (hcovT : (Q.P w).cov 0 ⟨T, 8⟩)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → (Q.P w).frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → (Q.P w).frz l → (Q.P w).cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → (Q.P w).foot j l → ¬ (Q.P w).cov i l)
    {j : Nat} (hj : d.1.mem.read? (Q.C w).cT j = some 0)
    (hjl : ∀ k w', j < k → d.1.mem.get? k = some w' → w'.loc ≠ (Q.C w).cT)
    (hPT0 : Q.PT0 w d.1.mem s.mem (retThread abi (parentPre abi d.2 0 th stack) r) s0)
    (hPT1 : Q.PT1 w d.1.mem s.mem (childAfter abi d.2 0 th stack tls) s1)
    (hProt : HelloProt (Q.SR w) (Q.C w) (Q.pT w) d.1.mem (retThread abi (parentPre abi d.2 0 th stack) r)
      (childAfter abi d.2 0 th stack tls) s.mem s0 s1 ts [] [])
    (hKR : Q.KR w (afterClone abi d 0 th stack tls r) s) :
    Q.Post Λ (afterClone abi d 0 th stack tls r) s := by
  refine post_start hSR h1 hs hi hp hmsgs hin hfits hG hb hown hsp0 hsp1 hs0 hs1 hfrz hfoot ?_ ?_ ?_ ?_ ?_
    hj hjl hPT0 hPT1 hProt hKR
  · intro L v h; rw [hQ] at h; simp only [wakeOwnX_zero, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hT0
  · intro L v h; rw [hQ] at h; simp at h
  · intro L v v' _ h; rw [hQ] at h; simp at h
  · intro L v h; rw [hQ] at h; simp only [wakeOwnX_zero, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hcovT
  · intro L v h; rw [hQ] at h; simp at h

/-- **The clone agreement**: `hT0` at `T = tcbM L`, for the clone's own list
`ownGX L a s` at a `selfOwn` state (main on its pool stack). -/
theorem hT0_ownGX {L : Spike.Lib.X64.Rt.RuntimeLayout} {a : BitVec 64} {s}
    (h : Spike.Lib.X64.WakePh.selfOwn L s) :
    ((⟨Spike.Lib.X64.WakePh.tcbM L, 8⟩ : Loc), (Spike.Lib.X64.WakePh.tcbM L).setWidth 128) ∈
      Spike.Lib.X64.WakePh.ownGX L a s :=
  Spike.Lib.X64.WakePh.tcbM_mem_ownGX h

end Spike.Lib.X64WakeOwnX

/-- info: 'Spike.Lib.X64WakeOwnX.own1X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.own1X

/-- info: 'Spike.Lib.X64WakeOwnX.ownAt_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.ownAt_const

/-- info: 'Spike.Lib.X64WakeOwnX.post_startOX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.post_startOX

/-- info: 'Spike.Lib.X64WakeOwnX.hT0_ownGX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.hT0_ownGX
