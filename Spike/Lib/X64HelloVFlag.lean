/-
**hello.w on x86-64: the box's flag at main's `spawn`, from the start** (`VFlagH`,
`vflagH_spawn`; hello's `X64SpawnFlag.VFlag`/`vflag_spawn` twin; the twin of `Spike/Lib/HelloVFlag.lean`).

Before the spawn, hello's source has one thread, main, at one of the stages
of `X64HelloPreTerm` (`HAt`). The box's `new` (stage 18) of the word `0`
pushes the cell's `undef` message at `⟨lbX, 0⟩` and then stores `0` there;
that store appends (`X64HelloPreTerm.alloc_flagMem`), so from stage 19 on the
box's word is a flag cell (`FlagMem`): every later message there is one of
main's promises. The later stages (publication, packet) keep memory and
promises; a promise step adds a promise. At the spawn main has no promises,
so the stored `0` is the latest source message at `c`'s word, with the
`undef` message before it (`vflagH_spawn`).

Unlike wake's `FlagC`, the stage (`HAt`) is carried in the invariant itself
(as in `X64HelloVBuf.VBufR`), so `VFlagH` needs no `VPre`; `c`'s label is
`lbX` by the stage's environment.

- `VFlagH`, `vflagH_init`, `vflagH_step`, `vflagH_run`: main's stage with
  `FlagMem` at `lbX` past the box's `new`, along source runs (vacuous once
  there are two threads).
- `pre1T_vflagH`: any hello `Pre1T` strengthened by `VFlagH`.
- `vflagH_spawn`: at `spawnTermH` with main promise-free, `c`'s label's
  latest message (`SLatestP` with no promise) holds `0`, after an earlier
  one (`X64SpawnFlag.vflag_spawn`'s shape).

## Differences from the AArch64 version

- Over the x86-64 copies of hello's source modules (`X64HelloSrc`, `X64HelloRodataSrc`, `X64HelloMainPreSrc`,
  `X64HelloPreTerm`, `X64HelloVBuf`); the stages and the proofs are A64's.
- `pre1T_vflagH` is over `X64WakePreTi.Pre1T … helloSrc` (the program parameter `p`) and
  `X64WakePreInv.Pre1T.invSrc`.
-/
import Spike.Lib.X64HelloVBuf
import Spike.Lib.X64WakePreInv

namespace Spike.Lib.X64HelloVFlag

open CoreLang CoreTerm TermRun
open WeakMem (Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.X64HelloSrc (helloSrc helloS hello_start)
open Spike.Lib.X64HelloRodataSrc
open Spike.Lib.X64HelloMainPreSrc
open Spike.Lib.X64HelloPreTerm
open Spike.Lib.X64HelloVBuf (set!_self eff_other hat_not_ext hat_spawnTerm)

/-- A promise step keeps `FlagMem` (its message is a promise). -/
theorem FlagMem.push {mem : WeakMem.Memory} {P : List Ts} {l : WeakMem.AllocLabel} (h : FlagMem mem P l)
    (m0 : WeakMem.Msg) : FlagMem (mem.push m0) (P ++ [mem.size]) l := by
  obtain ⟨i, j, hij, ⟨mi, hi, hil⟩, ⟨mj, hj, hjl, hjv⟩, hk⟩ := h
  refine ⟨i, j, hij, ⟨mi, ?_, hil⟩, ⟨mj, ?_, hjl, hjv⟩, fun k m hjk hm hl => ?_⟩
  · rw [TermMem.push_lt (TermLiveProps.lt_of_get hi)]; exact hi
  · rw [TermMem.push_lt (TermLiveProps.lt_of_get hj)]; exact hj
  · rw [Array.getElem?_push] at hm
    split at hm
    · rename_i he; subst he; exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact List.mem_append_left _ (hk k m hjk hm hl)

/-- **A step at stage `k` keeps the flag** (into stage `k + 1`): the box's
`new` makes it, later steps keep memory and promises. -/
theorem flag_step {mem mem' : WeakMem.Memory} {th th' : TTh} {k : Nat}
    (h : 19 ≤ k → FlagMem mem th.promises lbX) (he : Eff k mem th mem' th') :
    19 ≤ k + 1 → FlagMem mem' th'.promises lbX := by
  intro hk
  by_cases h18 : k = 18
  · subst h18
    exact he.2.2.2.2
  obtain ⟨rfl, hp, -⟩ := eff_other (by omega) (by omega) (by omega) h18 he
  rw [hp]
  exact h (by omega)

/-! ## Along source runs -/

/-- **The pre-spawn flag invariant**: with one thread, main is at a stage
`k` of `HAt` (label base 0, capacity 2), the box's word a flag cell
(`FlagMem` at `lbX`) past the box's `new`. -/
def VFlagH (s : Cfg) : Prop :=
  s.ths.size = 1 → ∃ th0 k wo0 wo1, s.ths[0]? = some th0 ∧ s.lbase = 0 ∧ s.cap = 2 ∧ HAt th0 k wo0 wo1 ∧
    (19 ≤ k → FlagMem s.mem th0.promises lbX)

theorem vflagH_init {arch : Arch} {s : Cfg} (h : (helloS arch).init s) : VFlagH s := by
  have h' : s = Spike.Lib.X64WakeT1.setupStartT 2 := by
    change Spike.Lib.X64WakeT1.progInitT helloSrc 2 s at h
    rw [hello_start] at h
    exact h
  subst h'
  intro _
  exact ⟨_, 0, meW, meW, rfl, rfl, rfl, hat_start, fun h => absurd h (by decide)⟩

/-- **One source step keeps `VFlagH`.** -/
theorem vflagH_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (helloS arch).step i s es s')
    (hv : VFlagH s) : VFlagH s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have h1 : s.ths.size = 1 := stepBy_size hs ▸ h1'
    obtain ⟨th0, k, wo0, wo1, h0, hb, hcap, hat, hl⟩ := hv h1
    rcases hs with ⟨hm, -⟩ | ⟨a, v, w, hi', -, -, rfl⟩
    · unfold TermRun.threadSteps at hm
      split at hm
      · simp at hm
      · rename_i th hth
        obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
        rw [h0] at hth
        cases hth
        obtain ⟨⟨mem, pairs, th'⟩, hr, rfl⟩ := List.mem_map.mp hm
        have hn : s.n = 2 := by simp [Cfg.n, hcap, h1]
        obtain ⟨wo0', wo1', hat', he⟩ := hat_tstep rfl hb hn rfl hat hr
        exact ⟨th', k + 1, wo0', wo1', set!_self h0 _, hb, hcap, hat', flag_step hl he⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      exact ⟨_, k, wo0, wo1, set!_self h0 _, hb, hcap, hat, fun hk => FlagMem.push (hl hk) _⟩
  · have := (spawnBy_size hs).1
    obtain ⟨x, f, a, T, ts, e, th, rt, ws, hth, -⟩ := hs
    have := (Array.getElem?_eq_some_iff.mp hth).1
    omega
  · obtain ⟨x, n, a, e, th, rt, ws, rs, hth, hterm, -, -, -, -, rfl⟩ := hs
    have h1 : s.ths.size = 1 := by rwa [TermExtStep.wake_size, TermExtStep.extCfg_size] at h1'
    obtain ⟨th0, k, wo0, wo1, h0, -, -, hat, -⟩ := hv h1
    obtain rfl : i = 0 := by have := (Array.getElem?_eq_some_iff.mp hth).1; omega
    rw [h0] at hth
    cases hth
    exact (hat_not_ext hat hterm).elim

/-- **`VFlagH` along source runs.** -/
theorem vflagH_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (helloS arch).Run s tr s') (hv : VFlagH s) :
    VFlagH s' := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vflagH_step hs hv)

open Spike.Lib.X64WakePreTi (Pre1T) in
/-- **`Pre1T` with `VFlagH`** (any hello `Pre1T`; no `VPre` needed, the
stage is carried by `VFlagH`). -/
theorem pre1T_vflagH {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Scc.Sem.X64.Asm} {E : Entry}
    {R1 : Spike.Lib.X64WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.X64.State → Prop}
    (O : Pre1T arch Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VFlagH s) Ab Ac helloSrc :=
  Spike.Lib.X64WakePreInv.Pre1T.invSrc O VFlagH (fun _ h => vflagH_init h) (fun _ _ _ hr hv => vflagH_run hr hv)

/-! ## At the spawn -/

/-- **The flag's latest source message at the spawn**: at main's spawn of
`s` (one thread `th0` at `spawnTermH`, promise-free, with `VFlagH`), for
`c`'s label `l`, the latest message at `⟨l, 0⟩` (no promise) holds `0`, and
an earlier message is there too. -/
theorem vflagH_spawn {s : Cfg} {th0 : TTh} {l : WeakMem.AllocLabel} {T : Ty} (hf : VFlagH s)
    (hs : s.ths = #[th0]) (ht : th0.term = spawnTermH) (hp : th0.promises = [])
    (hc : evalAt th0.env (.var "c") = some (T, [cst (.loc ⟨l, 0⟩ 0)])) :
    ∃ i j, i < j ∧ (∃ m, s.mem[i]? = some m ∧ m.loc = ⟨l, 0⟩) ∧ SLatestP s.mem [] ⟨l, 0⟩ j ∧
      ∃ m, s.mem[j]? = some m ∧ m.val = .num 0 := by
  obtain ⟨th, k, wo0, wo1, h0, -, -, hat, hfl⟩ := hf (by rw [hs]; rfl)
  rw [hs] at h0
  obtain rfl : th0 = th := by simpa using h0
  obtain rfl := hat_spawnTerm hat ht
  rw [hat.2.2.1] at hc
  simp [Spike.Lib.X64HelloPreTerm.hc, envP0, envC, evalAt, lookupE, cst, Promises.TVal.mk0] at hc
  obtain ⟨-, rfl⟩ := hc
  obtain ⟨i, j, hij, hi, ⟨m, hm, hml, hmv⟩, hk⟩ := hfl (by decide)
  rw [hp] at hk
  exact ⟨i, j, hij, hi, ⟨⟨m, hm, hml, List.not_mem_nil⟩, hk⟩, m, hm, hmv⟩

end Spike.Lib.X64HelloVFlag

/-- info: 'Spike.Lib.X64HelloVFlag.pre1T_vflagH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloVFlag.pre1T_vflagH

/-- info: 'Spike.Lib.X64HelloVFlag.vflagH_spawn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloVFlag.vflagH_spawn
