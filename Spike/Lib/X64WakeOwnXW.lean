/-
**wake.w on x86-64: both threads own their TCB self words after the spawn**
(X64-OwnW). This extends `X64WakeOwnX.wakeOwnX` so that the
worker (thread 1) owns its TCB's self word `⟨W, 8⟩ ↦ W`
(`W = tcbW = pinA + 104`, `Tcb2Call.tcb2Q_tcbOf`). It is the twin of main's
`⟨T, 8⟩ ↦ T` (`T = tcbM`).

The worker reads the word through `%fs:0`: the tail of `scc_rt_thr_worker`
at `.x12` (`movq %fs:0, %rax`), the `OwnAt` premise of the worker's tail
rows. So the empty thread-1 map of `wakeOwnX` is too small there.

**The handover.** Main's second `scc_rt_thread_init` writes the self word
(`.x7 + 48`, `movq %rax, (%rcx)` with `%rcx = W`). From then on, main
carries `(⟨W, 8⟩, W)` in the clone's own list `own₀` (the spawner owns it
until the clone). At the clone `inv2_start` hands it to thread 1
(`hsub1`). Main's map after the spawn does not hold it (`hdisj`: `T ≠ W`).

- `wakeOwnXW T W`: `[(⟨T,8⟩, T)]` at thread 0, `[(⟨W,8⟩, W)]` at thread 1;
  `ownConst1XW` (constant).
- `OffTcb2`, `msXW ms O T W`: a memory side owning `⟨O, 8⟩ ↦ O` whose
  runtime writes miss both self words (`msX` with both narrowings).
  - main is `msXW ms T T W` and the worker is `msXW ms W T W`;
  - `msXW_own`, `ownMpXW` (no owned word is a runtime write's target);
  - `ownAt_msXW` (`OwnAt … O O` at every pc: main's park and the worker's
    tail `%fs:0` loads);
  - `msXW_mp_of` (a runtime write off both words stays one), with
    `offTcb_add` for the words above a self word (park's `T + 16`, the
    worker's exit word `W + 24`).
- `wakeLocsXW`, `wakeLocsXW_ok`, `ownCov0XW`, `ownCov1XW`: the location data
  (`own 0 = ⟨T,8⟩`, `own 1 = ⟨W,8⟩`), its separation facts, and the cover
  facts at `wakeP`.
- `post_startOXW`: `X64WakeA64.post_start` at `Q.own = wakeOwnXW T W`, with
  `hT0`/`hW0` (both words in `own₀`), `hcovT`/`hcovW` (in each thread's cover
  set) and `hTW` (`⟨T,8⟩ ≠ ⟨W,8⟩`).

**Deviations / integration.** `wakeOwnX` and its users are unchanged:
`wakeOwnXW` is a new map beside it. Adopting it changes `X64WakeQ.hown`
 and needs the worker side's `WCompatX.own1`
(`Q.own w 1 s [] = []`) relaxed to an `own0`-style triple (constant, never a
runtime write's target, covered). This changes `WCompatX`;
`ownConst1XW`, `ownMpXW` and `ownCov1XW` discharge it at this
instance.
-/
import Spike.Lib.X64WakeOwnXInst

namespace Spike.Lib.X64WakeOwnX

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.Handover Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.X64WakeT1
open Spike.Lib.WakeP

/-! ## The owned words -/

/-- **The owned words after the spawn, both self words**: main's TCB word
`T` and the worker's `W`, each holding its address. -/
def wakeOwnXW {ι : Type} (T W : BitVec 64) : ι → Nat → isa.State → List TermRun.Frame → List (Loc × Val) :=
  fun _ i _ _ => if i = 0 then [(⟨T, 8⟩, T.setWidth 128)] else [(⟨W, 8⟩, W.setWidth 128)]

@[simp] theorem wakeOwnXW_zero {ι : Type} (T W : BitVec 64) (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    wakeOwnXW T W w 0 s fs = [(⟨T, 8⟩, T.setWidth 128)] :=
  rfl

@[simp] theorem wakeOwnXW_one {ι : Type} (T W : BitVec 64) (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    wakeOwnXW T W w 1 s fs = [(⟨W, 8⟩, W.setWidth 128)] :=
  rfl

/-- Thread 0's words of `wakeOwnXW` are `wakeOwnX`'s. -/
theorem wakeOwnXW_zero_eq {ι : Type} (T W : BitVec 64) (w : ι) (s : isa.State) (fs : List TermRun.Frame) :
    wakeOwnXW T W w 0 s fs = wakeOwnX T w 0 s fs :=
  rfl

/-- `wakeOwnXW`'s words of thread 0 are constant. -/
theorem ownConst0XW {ι : Type} (T W : BitVec 64) (w : ι) (s s' : isa.State) :
    wakeOwnXW T W w 0 s' [] = wakeOwnXW T W w 0 s [] :=
  rfl

/-- `wakeOwnXW`'s words of thread 1 are constant. -/
theorem ownConst1XW {ι : Type} (T W : BitVec 64) (w : ι) (s s' : isa.State) :
    wakeOwnXW T W w 1 s' [] = wakeOwnXW T W w 1 s [] :=
  rfl

/-! ## The memory sides -/

/-- **A memory side owning one self word `⟨O, 8⟩ ↦ O`**, its runtime writes
narrowed to words off both self words `[T, T + 8)`, `[W, W + 8)`. -/
def msXW (ms : MemSide isa) (O T W : BitVec 64) : MemSide isa :=
  { ms with
    own := fun _ => [(⟨O, 8⟩, O.setWidth 128)]
    mp := fun L w => ms.mp L w ∧ (w = true → OffTcb T L ∧ OffTcb W L) }

/-- main's memory side owns `wakeOwnXW`'s words of thread 0. -/
theorem msXW_own0 {ι : Type} (ms : MemSide isa) (T W : BitVec 64) (w : ι) (s : isa.State) :
    (msXW ms T T W).own s = wakeOwnXW T W w 0 s [] :=
  rfl

/-- The worker's memory side owns `wakeOwnXW`'s words of thread 1. -/
theorem msXW_own1 {ι : Type} (ms : MemSide isa) (T W : BitVec 64) (w : ι) (s : isa.State) :
    (msXW ms W T W).own s = wakeOwnXW T W w 1 s [] :=
  rfl

/-- **`OwnAt` at the self word**: every pc owns `O` holding `O` (main's
park, the worker's tail `%fs:0` load at `.Lscc_rt_thr_worker.x12`). -/
theorem ownAt_msXW {ms : MemSide isa} {O T W : BitVec 64} {exe : _root_.Executable} {endPc pc : Int64} :
    Spike.Lib.X64.OwnAt (msXW ms O T W) exe endPc pc O O :=
  ownAt_const fun _ => rfl

/-- **The words `k ≥ 8` bytes above a self word miss it** (no wrap-around
past `2 ^ 64`): park's `T + 16`, the worker's exit word `W + 24`. -/
theorem offTcb_add {O : BitVec 64} {k : Nat} (hk : 8 ≤ k) (hO : O.toNat + k + 8 ≤ 2 ^ 64) :
    OffTcb O ⟨O + BitVec.ofNat 64 k, 8⟩ := by
  unfold OffTcb
  right
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **A runtime write off both self words stays one of `msXW`.** -/
theorem msXW_mp_of {ms : MemSide isa} {O T W : BitVec 64} {L : Loc} (hmp : ms.mp L true)
    (hT : OffTcb T L) (hW : OffTcb W L) : (msXW ms O T W).mp L true :=
  ⟨hmp, fun _ => ⟨hT, hW⟩⟩

/-- **No owned word is a runtime write's target** under `msXW` when the
owned word is one of the two self words. -/
theorem ownMpXW {ms : MemSide isa} {O T W : BitVec 64} (hO : O = T ∨ O = W) (s : isa.State) (L : Loc) (v : Val)
    (hm : (L, v) ∈ (msXW ms O T W).own s) : ¬ (msXW ms O T W).mp L true := by
  simp only [msXW, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  rintro ⟨-, h⟩
  rcases hO with rfl | rfl
  · exact offTcb_self _ (h rfl).1
  · exact offTcb_self _ (h rfl).2

/-- (`WCompat0.ownMp0`) main never writes either self word as the runtime's. -/
theorem ownMp0XW {ι : Type} (ms : MemSide isa) (T W : BitVec 64) (w : ι) (s : isa.State) (L : Loc) (v : Val)
    (hm : (L, v) ∈ wakeOwnXW T W w 0 s []) : ¬ (msXW ms T T W).mp L true :=
  ownMpXW (.inl rfl) s L v hm

/-- (the worker's `ownMp1`) the worker never writes either self word as the
runtime's. -/
theorem ownMp1XW {ι : Type} (ms : MemSide isa) (T W : BitVec 64) (w : ι) (s : isa.State) (L : Loc) (v : Val)
    (hm : (L, v) ∈ wakeOwnXW T W w 1 s []) : ¬ (msXW ms W T W).mp L true :=
  ownMpXW (.inr rfl) s L v hm

/-! ## The location data -/

/-- **The location data with both threads owning their self words**: `⟨T, 8⟩`
main's, `⟨W, 8⟩` the worker's; each thread's other footprint words the
runtime words its memory side lets it write (`ms0` main's, `ms1` the
worker's). -/
def wakeLocsXW (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cT : Loc)
    (cS : WeakMem.Address) (ms0 ms1 : MemSide isa) (T W : BitVec 64) : WakeLocs where
  lbl := lbl
  lsize := lsize
  cT := cT
  cS := cS
  own i L := (i = 0 ∧ L = ⟨T, 8⟩) ∨ (i = 1 ∧ L = ⟨W, 8⟩)
  priv i L := if i = 0 then (msXW ms0 T T W).mp L true else (msXW ms1 W T W).mp L true

/-- **`wakeLocsXW`' separation facts**, given the two self words distinct,
outside every placed label and not the flag's word, and both memory sides'
runtime writes outside every placed label. -/
theorem wakeLocsXW_ok {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {cT : Loc}
    {cS : WeakMem.Address} {ms0 ms1 : MemSide isa} {T W : BitVec 64}
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    (hTl : ¬ InLabel lbl lsize ⟨T, 8⟩) (hWl : ¬ InLabel lbl lsize ⟨W, 8⟩) (hcT : cT ≠ ⟨T, 8⟩)
    (hmpl0 : ∀ L, ms0.mp L true → ¬ InLabel lbl lsize L)
    (hmpl1 : ∀ L, ms1.mp L true → ¬ InLabel lbl lsize L) :
    (wakeLocsXW lbl lsize cT cS ms0 ms1 T W).OK where
  disj i j l hi hj hij h := by
    simp only [wakeLocsXW] at h ⊢
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hj1 : j = 1 := by omega
      subst hj1
      rcases h with (⟨h0, -⟩ | ⟨-, h1⟩) | hp
      · exact absurd h0 (by decide)
      · exact hTW h1
      · simp only [show (1 : Nat) ≠ 0 by decide, ↓reduceIte] at hp
        exact offTcb_self T (hp.2 rfl).1
    · have hj0 : j = 0 := by omega
      subst hj0
      rcases h with (⟨-, h1⟩ | ⟨h0, -⟩) | hp
      · exact hTW h1.symm
      · exact absurd h0 (by decide)
      · simp only [↓reduceIte] at hp
        exact offTcb_self W (hp.2 rfl).2
  own_nlab i l _ h := by
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hTl
    · exact hWl
  priv_nlab i l _ h := by
    simp only [wakeLocsXW] at h
    split at h
    · exact hmpl0 _ h.1
    · exact hmpl1 _ h.1
  c_own h := by
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hcT h
    · exact absurd h (by decide)

/-- (`WCompat0.ownCov0`) **main's self word is in its cover set** at
`wakeP … (wakeLocsXW …)`. -/
theorem ownCov0XW {I : ISA} {K : Abi I} {μ : Marks} {ι : Type} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {cT : Loc} {cS : WeakMem.Address} {ms0 ms1 : MemSide isa} (T W : BitVec 64)
    (w : ι) (s : isa.State) (L : Loc) (v : Val) (hm : (L, v) ∈ wakeOwnXW T W w 0 s []) :
    (wakeP K μ (wakeLocsXW lbl lsize cT cS ms0 ms1 T W)).cov 0 L := by
  simp only [wakeOwnXW_zero, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  exact wakeP_own_cov (.inl ⟨rfl, rfl⟩)

/-- (the worker's `ownCov1`) **the worker's self word is in its cover set**
at `wakeP … (wakeLocsXW …)`. -/
theorem ownCov1XW {I : ISA} {K : Abi I} {μ : Marks} {ι : Type} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {cT : Loc} {cS : WeakMem.Address} {ms0 ms1 : MemSide isa} (T W : BitVec 64)
    (w : ι) (s : isa.State) (L : Loc) (v : Val) (hm : (L, v) ∈ wakeOwnXW T W w 1 s []) :
    (wakeP K μ (wakeLocsXW lbl lsize cT cS ms0 ms1 T W)).cov 1 L := by
  simp only [wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  exact wakeP_own_cov (.inr ⟨rfl, rfl⟩)

/-! ## The clone -/

/-- **`post_start` with both threads owning their self words**:
`X64WakeA64.post_start` at `Q.own = wakeOwnXW T W`. `hT0`, `hW0`: the
clone's own list holds both words (the spawner owns `W` from its
`scc_rt_thread_init` store on); `hcovT`, `hcovW`: each thread covers its
word; `hTW`: the words differ. -/
theorem post_startOXW {Λ : Scc.Sem.Layout} {Q : WakeRel} {T W : BitVec 64} (hQ : Q.own = wakeOwnXW T W)
    (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩) {w : Q.ι}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Cfg} {th : Thread isa} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh} {own₀ : List (Loc × Val)}
    (hSR : Q.SR w = ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩)
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv (Q.G w) d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hT0 : ((⟨T, 8⟩ : Loc), T.setWidth 128) ∈ own₀) (hW0 : ((⟨W, 8⟩ : Loc), W.setWidth 128) ∈ own₀)
    (hcovT : (Q.P w).cov 0 ⟨T, 8⟩) (hcovW : (Q.P w).cov 1 ⟨W, 8⟩)
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
  · intro L v h; rw [hQ] at h; simp only [wakeOwnXW_zero, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hT0
  · intro L v h; rw [hQ] at h; simp only [wakeOwnXW_one, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hW0
  · intro L v v' h0 h1'; rw [hQ] at h0 h1'
    simp only [wakeOwnXW_zero, wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at h0 h1'
    exact hTW (h0.1.symm.trans h1'.1)
  · intro L v h; rw [hQ] at h; simp only [wakeOwnXW_zero, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hcovT
  · intro L v h; rw [hQ] at h; simp only [wakeOwnXW_one, List.mem_singleton] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact hcovW

end Spike.Lib.X64WakeOwnX

/-- info: 'Spike.Lib.X64WakeOwnX.offTcb_add' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.offTcb_add

/-- info: 'Spike.Lib.X64WakeOwnX.ownMpXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.ownMpXW

/-- info: 'Spike.Lib.X64WakeOwnX.wakeLocsXW_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.wakeLocsXW_ok

/-- info: 'Spike.Lib.X64WakeOwnX.ownCov1XW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.ownCov1XW

/-- info: 'Spike.Lib.X64WakeOwnX.post_startOXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.post_startOXW
