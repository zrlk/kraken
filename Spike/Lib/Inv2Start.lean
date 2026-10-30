/-
**The two-thread relation established at the clone** (the
"Inv2 at the clone" part, and 1.3). ISA-generic, for any `Kernel.Abi`.

At the target `clone` (the source `spawn`'s commit point) the one-thread
facts of the parent (`Inv1` with no promise, by `prom_nil_of_clone`; every
message thread 0's; the memory in the layout, fitting, satisfying `G`; the
thread's values at most `|M|`; its owned words reading as their values)
give `Inv2Core` for the parent after its return and the child
(`Spike.Lib.Handover.afterClone`), with the spawn record at the current
memories (`T = tm.last`, `S = sm.size`): no message after the spawn, no
promise, the owned words split between the two threads (`own i ⊆ own`
before, disjoint), each thread's cover from the parent's (H1: the child
has the parent's `coh`).

- `bnd_parentPre`, `bnd_childAfter`: the two threads' values stay at most
  `n`;
- `getCoh_childAfter`, `getCoh_parent`: both have the parent's `coh`;
- `inv2Core_start`: the core at the clone;
- `threads_afterClone_one`: from one thread, the configuration after the
  clone has the two threads `#[parent, child]`;
- `inv2_start`: `Inv2` at the clone, given the per-thread relation and the
  protocol there;
- `preC_parent`: main's pre-spawn facts about the flag `c`
  (`Spike.Lib.Inv2Read.PreC`, part of main's `PT 0`) for the parent after
  the clone, when the latest write of `c` there has value `0`.
-/
import Spike.Lib.Inv2Core
import Spike.Lib.Handover
import Spike.Lib.Inv2Read

namespace Spike.Lib.Inv2Start

open Kraken.Promising Scc.Sem Scc.Sem.Kernel Spike.Lib.TwoSlot Spike.Lib.Handover Spike.Lib.Inv2Core

variable {I : ISA} {K : Abi I}

/-- Views without forwarding and exclusive records keep their coherence. -/
theorem getCoh_strip (vs : Views) (l : Loc) : ({ vs with fwdb := [], xclb := none } : Views).getCoh l = vs.getCoh l :=
  rfl

/-- Views without forwarding and exclusive records stay at most `n`. -/
theorem bnd_strip {vs : Views} {n : Nat} (h : vs.Bnd n) : Views.Bnd { vs with fwdb := [], xclb := none } n := by
  have hle := h.le
  refine ⟨⟨hle.coh, hle.vrNew, hle.vrOld, hle.vrOldNR, hle.vwNew, hle.vwOld, hle.vCAP, hle.vRel, ?_, hle.vwOldNT⟩,
    ?_, ?_⟩
  · intro l f hf; simp [Views.getFwd] at hf
  · intro l f hf; simp [Views.getFwd] at hf
  · intro t ν l hx; cases hx

section Facts

variable {d : Config I × KState} {tid : Nat} {t : Thread I} {stack tls : Nat} {r : BitVec 64}

theorem bnd_parentPre {n : Nat} (h : t.Bnd n) : (parentPre K d.2 tid t stack).Bnd n := by
  unfold parentPre; split
  · exact h
  · exact ⟨h.views, h.regs⟩

/-- **The child's values are at most `n`**: register views 0, the parent's
views without forwarding and exclusive records. -/
theorem bnd_childAfter {n : Nat} (h : t.Bnd n) : (childAfter K d.2 tid t stack tls).Bnd n := by
  have hc : (childThread K t stack tls).Bnd n := by
    refine ⟨bnd_strip h.views, ?_, ?_⟩
    · intro v hv
      simp only [childThread, Thread.init, Array.mem_replicate] at hv
      rw [hv.2]; exact Nat.zero_le _
    · intro v hv
      simp only [childThread, Thread.init, Array.mem_replicate] at hv
      rw [hv.2]; exact Nat.zero_le _
  unfold childAfter; split
  · exact hc
  · exact ⟨hc.views, hc.regs⟩

/-- **H1, on coherence**: the child's coherence views are the parent's. -/
theorem getCoh_childAfter (l : Loc) : (childAfter K d.2 tid t stack tls).views.getCoh l = t.views.getCoh l := by
  rw [childAfter_views]; rfl

theorem views_parent : (retThread K (parentPre K d.2 tid t stack) r).views = t.views := by
  rw [Scc.Sem.retThread_views, parentPre_views]

theorem prom_parent : (retThread K (parentPre K d.2 tid t stack) r).prom = t.prom := by
  rw [retThread_prom, parentPre_prom]

/-- From one thread, the threads after the clone are the parent after its
return and the child. -/
theorem threads_afterClone_one (h1 : d.1.threads = #[t]) :
    (afterClone K d 0 t stack tls r).1.threads =
      #[retThread K (parentPre K d.2 0 t stack) r, childAfter K d.2 0 t stack tls] := by
  simp only [afterClone, h1]
  rfl

end Facts

variable {Λ : Scc.Sem.Layout} {P : Inv2Params I} {G : Loc → Val → Prop}

/-- **The core at the clone.** `th` is the parent at its `clone` (no promise),
`t0`, `t1` the parent after its return and the child (any threads with the
parent's coherence, no promise and values at most `|M|`: `views_parent`,
`getCoh_childAfter`, `bnd_parentPre`, `bnd_childAfter`), `s0`, `s1` the
source threads after the spawn (no promise; their coherence views cover the
frozen source words' messages); the owned words before (`own₀`) split into
disjoint `own 0`, `own 1`, each in its thread's cover set. -/
theorem inv2Core_start {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {th t0 t1 : Thread I} {tm : Memory} {sm : WeakMem.Memory} {s0 s1 : TermRun.TTh}
    {own₀ : List (Loc × Val)} {own : Nat → List (Loc × Val)}
    (hi : Inv1 Λ lbl lsize ts th tm sm) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs tm)
    (hin : Consumer1.MemIn Λ tm) (hfits : Consumer1.MemFits tm) (hG : MemInv G tm)
    (hown : ExtRows.OwnOk own₀ tm th.prom)
    (hc0 : ∀ l, t0.views.getCoh l = th.views.getCoh l) (hc1 : ∀ l, t1.views.getCoh l = th.views.getCoh l)
    (hp0 : t0.prom = []) (hp1 : t1.prom = []) (hb0 : t0.Bnd tm.last) (hb1 : t1.Bnd tm.last)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, sm[k]? = some m → P.frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → P.frz l → P.cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → P.foot j l → ¬ P.cov i l)
    (hsub : ∀ i L v, i < 2 → (L, v) ∈ own i → (L, v) ∈ own₀)
    (hdisj : ∀ L v v', (L, v) ∈ own 0 → (L, v') ∈ own 1 → False)
    (hcov : ∀ i L v, i < 2 → (L, v) ∈ own i → P.cov i L) :
    Inv2Core Λ ⟨tm.last, sm.size, lbl, lsize⟩ P G own tm t0 t1 sm s0 s1 ts [] [] := by
  have hmem : MemRelP Λ lbl lsize ts tm sm [] [] [] := by
    have := hi.mem; rw [hp] at this; exact this
  have hcoh : CohCoversP th.views [] tm := by
    have := hi.coh; rw [hp] at this; exact this
  have hlast : ∀ k w, tm.get? k = some w → k ≤ tm.last := fun _ _ hk => Kraken.Promising.Memory.le_last_of_get? hk
  have hsize : ∀ k (m : WeakMem.Msg), sm[k]? = some m → k < sm.size := fun _ _ hk =>
    (Array.getElem?_eq_some_iff.mp hk).1
  have hownL : ∀ i, i < 2 → ExtRows.OwnOk (own i) tm [] := by
    intro i hi2 L v hL
    have := hown L v (hsub i L v hi2 hL)
    rwa [hp] at this
  refine
    { mem := hmem
      tp_prom := fun k hk => absurd hk List.not_mem_nil
      prom_tp := fun k w hk _ _ => by rw [hp0, hp1] at hk; simp at hk
      sp_prom := fun k => by rw [hsp0, hsp1]; simp
      narrow := hi.narrow
      memIn := hin
      fits := hfits
      memInv := hG
      bnd0 := hb0
      bnd1 := hb1
      cov0 := fun k w hk _ _ => by rw [hc0]; exact hcoh k w hk List.not_mem_nil
      cov1 := fun k w hk _ _ => by rw [hc1]; exact hcoh k w hk List.not_mem_nil
      frz_cov := hfrz
      frzT := fun k w hk hT _ => absurd (hlast k w hk) (Nat.not_le_of_lt hT)
      frzS := fun k m hk hS _ => absurd (hsize k m hk) (Nat.not_lt_of_le hS)
      scov0 := hs0
      scov1 := hs1
      pre_tid := fun k w hk _ => hmsgs k w hk
      post_foot := fun k w hk hT => absurd (hlast k w hk) (Nat.not_le_of_lt hT)
      foot_cov := hfoot
      own0 := by rw [hp0]; exact hownL 0 (by decide)
      own1 := by rw [hp1]; exact hownL 1 (by decide)
      own_disj := hdisj
      own_cov := hcov
      prom0 := fun k hk => by rw [hp0] at hk; cases hk
      prom1 := fun k hk => by rw [hp1] at hk; cases hk
      noProm0 := fun _ => hp0
      noProm1 := fun _ => hp1
      T_le := Nat.le_refl _
      S_le := Nat.le_refl _ }

/-- **`Inv2` at the clone**: the configuration after a `clone` of the one
thread `th` of `d` (`afterClone`, tid 0) and a source configuration of two
threads, from the parent's one-thread facts at the call, the per-thread
relation and the protocol there. The spawn record is at the current
memories. -/
theorem inv2_start {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Config I × KState} {th : Thread I} {stack tls : Nat} {r : BitVec 64}
    {s : TermRun.Cfg} {s0 s1 : TermRun.TTh}
    {own₀ : List (Loc × Val)} {own : Nat → I.State → List TermRun.Frame → List (Loc × Val)}
    {PT : Nat → Memory → WeakMem.Memory → Thread I → TermRun.TTh → Prop}
    {Prot : Memory → Thread I → Thread I → WeakMem.Memory → TermRun.TTh → TermRun.TTh →
      (Nat → Option Nat) → List Nat → List Nat → Prop}
    (h1 : d.1.threads = #[th]) (hs : s.ths = #[s0, s1])
    (hi : Inv1 Λ lbl lsize ts th d.1.mem s.mem) (hp : th.prom = []) (hmsgs : Consumer1.OwnMsgs d.1.mem)
    (hin : Consumer1.MemIn Λ d.1.mem) (hfits : Consumer1.MemFits d.1.mem) (hG : MemInv G d.1.mem)
    (hb : th.Bnd d.1.mem.last) (hown : ExtRows.OwnOk own₀ d.1.mem th.prom)
    (hsp0 : s0.promises = []) (hsp1 : s1.promises = [])
    (hs0 : ∀ k m, s.mem[k]? = some m → P.frzS m.loc → k ≤ s0.vs.coh m.loc)
    (hs1 : ∀ k m, s.mem[k]? = some m → P.frzS m.loc → k ≤ s1.vs.coh m.loc)
    (hfrz : ∀ i l, i < 2 → P.frz l → P.cov i l)
    (hfoot : ∀ i j l, i < 2 → j < 2 → i ≠ j → P.foot j l → ¬ P.cov i l)
    (hsub0 : ∀ L v, (L, v) ∈ own 0 (retThread K (parentPre K d.2 0 th stack) r).st s0.stack → (L, v) ∈ own₀)
    (hsub1 : ∀ L v, (L, v) ∈ own 1 (childAfter K d.2 0 th stack tls).st s1.stack → (L, v) ∈ own₀)
    (hdisj : ∀ L v v', (L, v) ∈ own 0 (retThread K (parentPre K d.2 0 th stack) r).st s0.stack →
      (L, v') ∈ own 1 (childAfter K d.2 0 th stack tls).st s1.stack → False)
    (hcov0 : ∀ L v, (L, v) ∈ own 0 (retThread K (parentPre K d.2 0 th stack) r).st s0.stack → P.cov 0 L)
    (hcov1 : ∀ L v, (L, v) ∈ own 1 (childAfter K d.2 0 th stack tls).st s1.stack → P.cov 1 L)
    (hPT0 : PT 0 d.1.mem s.mem (retThread K (parentPre K d.2 0 th stack) r) s0)
    (hPT1 : PT 1 d.1.mem s.mem (childAfter K d.2 0 th stack tls) s1)
    (hProt : Prot d.1.mem (retThread K (parentPre K d.2 0 th stack) r) (childAfter K d.2 0 th stack tls) s.mem
      s0 s1 ts [] []) :
    Inv2 Λ ⟨d.1.mem.last, s.mem.size, lbl, lsize⟩ P G own PT Prot (afterClone K d 0 th stack tls r).1 s := by
  refine ⟨_, _, s0, s1, ts, [], [], threads_afterClone_one h1, hs, ?_, hPT0, hPT1, hProt⟩
  refine inv2Core_start (th := th) hi hp hmsgs hin hfits hG hown (fun l => by rw [views_parent])
    (fun l => getCoh_childAfter l) (by rw [prom_parent, hp]) childAfter_prom
    (ExtThread.bnd_retThread K (bnd_parentPre hb) r) (bnd_childAfter hb) hsp0 hsp1 hs0 hs1 hfrz hfoot ?_ ?_ ?_
  · intro i L v hi2 hL
    rcases i with _ | _ | i
    · exact hsub0 L v hL
    · exact hsub1 L v hL
    · omega
  · intro L v v' h0 h1'
    exact hdisj L v v' h0 h1'
  · intro i L v hi2 hL
    rcases i with _ | _ | i
    · exact hcov0 L v hL
    · exact hcov1 L v hL
    · omega

/-- **main's pre-spawn facts about `c` at the clone** (the condition on 1.4's proposal 2: they are part of main's `PT 0` and hold at
the clone): the parent after its return has the parent's views, which
cover every message (`Inv1`, no promise), and the latest write `j` of `cT`
has value `0` (for hello: the `new z` initialisation of `c`'s cell). -/
theorem preC_parent {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ts : Nat → Option Nat} {d : Config I × KState} {th : Thread I} {stack : Nat} {r : BitVec 64}
    {sm : WeakMem.Memory} {cT : Loc} (hi : Inv1 Λ lbl lsize ts th d.1.mem sm) (hp : th.prom = []) {j : Nat}
    (hj : d.1.mem.read? cT j = some 0) (hjl : ∀ k w, j < k → d.1.mem.get? k = some w → w.loc ≠ cT) :
    Spike.Lib.Inv2Read.PreC ⟨d.1.mem.last, sm.size, lbl, lsize⟩ cT d.1.mem
      (retThread K (parentPre K d.2 0 th stack) r).views := by
  rw [views_parent]
  have hcoh : CohCoversP th.views [] d.1.mem := by
    have := hi.coh; rw [hp] at this; exact this
  exact Spike.Lib.Inv2Read.preC_start rfl hcoh hj hjl

end Spike.Lib.Inv2Start
