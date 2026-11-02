/-
**hello.w: coherence and the packet at main's `spawn`, from the start**
(`VPreCH`, `scovH_spawn`, `scovH_of`; hello's `X64SpawnCohSteps.VPreC`/
`scov_spawn`/`scov_of` twin).

Before the spawn, hello's source has one thread, main, at one of the stages
of `X64HelloPreTerm` (`HAt`). Every step keeps main's coherence covering the
memory (`CohC`, from `X64HelloVPre.hat_veff`); a promise step adds a promise,
so its message needs no coverage. At the spawn (`spawnTermH`) the packet `p`
is the pair of `p0` and `me`, types and words (`PBH`, read off stage 22's
environment). With main promise-free, every message of the spawned
configuration is at most both threads' coherence at its location.

Against wake's `VPreC`: the stage (`HAt`) is carried in the invariant itself
(as in `X64HelloVBuf.VBufR`), so `VPreCH` needs no `VPre`; wake's `PB` pairs
`c` and `me`, hello's `PBH` pairs `p0` (the slice and `c`) and `me`.

- `PBH`, `pbH_of_hat`: the packet at the spawn, from main's stage.
- `VPreCH`, `vpreCH_init`, `vpreCH_step`, `vpreCH_run`, `pre1T_vpreCH`: the
  invariant along source runs (vacuous once there are two threads).
- `scovH_spawn`, `scovH_of`: coherence covers the spawned configuration's
  memory for both threads.

x86-64 twin of `Spike/Lib/HelloVPreC.lean` (same names, namespaces with the `X64` prefix).

**Where this differs from AArch64**: nothing at the source level (the source semantics is ISA-free); the
packet type `pktTy` is `X64HelloSplit`'s and `Pre1T` is x86-64's (`X64WakePreTi`).
-/
import Spike.Lib.X64HelloVPre

namespace Spike.Lib.X64HelloVPreC

open CoreLang CoreTerm TermRun
open WeakMem (Ts Arch)
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.X64HelloSrc (helloSrc helloS hello_start)
open Spike.Lib.X64HelloMainPreSrc
open Spike.Lib.X64HelloSplit (pktTy)
open Spike.Lib.X64HelloPreTerm
open Spike.Lib.X64HelloVBuf (set!_self hat_not_ext hat_spawnTerm)
open Spike.Lib.X64SpawnCohSteps (CohC)
open Spike.Lib.X64HelloVPre (hat_veff)

/-- **`p` at the spawn is the pair of `p0` and `me`** (`X64SpawnCohSteps.PB`'s
twin; wake pairs `c`, hello pairs `p0`, the slice with `c`). -/
def PBH (th : TTh) : Prop :=
  th.term = spawnTermH → ∃ tp wp tm wm, lookupE th.env "p0" = some (tp, wp) ∧
    lookupE th.env "me" = some (tm, wm) ∧ lookupE th.env "p" = some (.prod tp tm, wp ++ wm)

/-- Main's stage gives `PBH` (the spawn is stage 22). -/
theorem pbH_of_hat {th : TTh} {k : Nat} {wo0 wo1 : Word} (h : HAt th k wo0 wo1) : PBH th := by
  intro ht
  obtain rfl := hat_spawnTerm h ht
  rw [h.2.2.1]
  exact ⟨_, _, _, _, rfl, rfl, by simp [hc, lookupE, pktTy]⟩

/-- **hello's pre-spawn coherence invariant**: with one thread, main is at a
stage `k` of `HAt` (label base 0, capacity 2), its coherence covers the
memory (`CohC`), and `p` is `p0`'s and `me`'s pair at the spawn (`PBH`). -/
def VPreCH (s : Cfg) : Prop :=
  s.ths.size = 1 → ∃ th0 k wo0 wo1, s.ths[0]? = some th0 ∧ s.lbase = 0 ∧ s.cap = 2 ∧ HAt th0 k wo0 wo1 ∧
    CohC s.mem th0 ∧ PBH th0

theorem vpreCH_init {arch : Arch} {s : Cfg} (h : (helloS arch).init s) : VPreCH s := by
  have h' : s = Spike.Lib.X64WakeT1.setupStartT 2 := by
    change Spike.Lib.X64WakeT1.progInitT helloSrc 2 s at h
    rw [hello_start] at h
    exact h
  subst h'
  intro _
  refine ⟨_, 0, meW, meW, rfl, rfl, rfl, hat_start, fun k m hm _ => ?_, pbH_of_hat hat_start⟩
  simp [Spike.Lib.X64WakeT1.setupStartT] at hm

/-- **One source step keeps `VPreCH`.** -/
theorem vpreCH_step {arch : Arch} {i : Nat} {s s' : Cfg} {es : List Ev} (h : (helloS arch).step i s es s')
    (hv : VPreCH s) : VPreCH s' := by
  intro h1'
  obtain ⟨-, hs, -⟩ := h
  rcases hs with hs | hs | hs
  · have h1 : s.ths.size = 1 := stepBy_size hs ▸ h1'
    obtain ⟨th0, k, wo0, wo1, h0, hb, hcap, hat, hc, -⟩ := hv h1
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
        obtain ⟨wo0', wo1', hat', -⟩ := hat_tstep rfl hb hn rfl hat hr
        exact ⟨th', k + 1, wo0', wo1', set!_self h0 _, hb, hcap, hat', (hat_veff rfl hb hn rfl hat hr).2.1 hc,
          pbH_of_hat hat'⟩
    · obtain rfl : i = 0 := by omega
      unfold TermRun.promise
      rw [h0]
      refine ⟨_, k, wo0, wo1, set!_self h0 _, hb, hcap, hat, ?_, pbH_of_hat hat⟩
      intro j m hm hj
      simp only [List.mem_append, List.mem_singleton, not_or] at hj
      rw [Array.getElem?_push] at hm
      split at hm
      · exact absurd ‹_› hj.2
      · exact hc j m hm hj.1
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

/-- **`VPreCH` along source runs.** -/
theorem vpreCH_run {arch : Arch} {s s' : Cfg} {tr : List Ev} (h : (helloS arch).Run s tr s') (hv : VPreCH s) :
    VPreCH s' := by
  induction h with
  | refl => exact hv
  | step hs _ ih =>
    obtain ⟨i, hs⟩ := hs
    exact ih (vpreCH_step hs hv)

open Kraken.Promising Kraken.Promising.X64 Scc.Sem.X64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakePreTi in
/-- **`Pre1T` with `VPreCH`** (any hello `Pre1T`; no `VPreH` needed, the
stage is carried by `VPreCH`). -/
theorem pre1T_vpreCH {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {E : Entry}
    {R1 : Spike.Lib.X64WakeA64.Cfg → TermRun.Cfg → Prop} {Ab Ac : Kraken.Promising.X64.State → Prop}
    (O : Pre1T arch Λ B asm E R1 Ab Ac helloSrc) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPreCH s) Ab Ac helloSrc :=
  Spike.Lib.X64WakePreInv.Pre1T.invSrc O VPreCH (fun _ h => vpreCH_init h) (fun _ _ _ hr hv => vpreCH_run hr hv)

/-! ## At the spawn -/

/-- **Coherence at the spawn** (`X64SpawnCohSteps.scov_spawn`'s shape): at
main's spawn of `s` (one thread `th0`, promise-free, with `VPreCH`), every
message of the spawned configuration is at most the coherence of both its
threads at its location. -/
theorem scovH_spawn {s : Cfg} {th0 : TTh} {x f : String} {e : Expr} {ts : List Ty} {T : Ty} {ws : List Word}
    (hc : VPreCH s) (hs : s.ths = #[th0]) (hp : th0.promises = []) :
    (∀ k m, (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).mem[k]? = some m →
      k ≤ (TermSpawnStep.spawnPar s 0 th0 x e).vs.coh m.loc) ∧
    (∀ k m, (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).mem[k]? = some m →
      k ≤ (TermSpawnStep.spawnKid s 0 th0 f ts T ws).vs.coh m.loc) := by
  obtain ⟨th, -, -, -, h0, -, -, -, hci, -⟩ := hc (by rw [hs]; rfl)
  obtain rfl : th0 = th := by rw [hs] at h0; simpa using h0
  have hk : ∀ k m, s.mem[k]? = some m → k ≤ th0.vs.coh m.loc := fun k m hm =>
    hci k m hm (by rw [hp]; exact List.not_mem_nil)
  exact ⟨fun k m hm => hk k m hm, fun k m hm => hk k m hm⟩

/-- `scovH_spawn` at `SpawnPre.ths`'s names (`X64SpawnCohSteps.scov_of`'s
shape): `s' = spawnCfg …` with threads `#[s0, s1]`. -/
theorem scovH_of {s s' : Cfg} {th0 s0 s1 : TTh} {x f : String} {e : Expr} {ts : List Ty} {T : Ty}
    {ws : List Word} (hc : VPreCH s) (hs : s.ths = #[th0]) (hp : th0.promises = [])
    (hs' : s' = TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws) (h2 : s'.ths = #[s0, s1]) :
    (∀ k m, s'.mem[k]? = some m → k ≤ s0.vs.coh m.loc) ∧ (∀ k m, s'.mem[k]? = some m → k ≤ s1.vs.coh m.loc) := by
  subst hs'
  have h2' : (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).ths =
      #[TermSpawnStep.spawnPar s 0 th0 x e, TermSpawnStep.spawnKid s 0 th0 f ts T ws] := by
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hs]
  have hq := h2.symm.trans h2'
  have h0' : (#[s0, s1] : Array TTh)[0]? = some s0 := rfl
  have h1' : (#[s0, s1] : Array TTh)[1]? = some s1 := rfl
  rw [hq] at h0' h1'
  obtain rfl : TermSpawnStep.spawnPar s 0 th0 x e = s0 := Option.some.inj h0'
  obtain rfl : TermSpawnStep.spawnKid s 0 th0 f ts T ws = s1 := Option.some.inj h1'
  exact scovH_spawn hc hs hp

/-- info: 'Spike.Lib.X64HelloVPreC.pre1T_vpreCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pre1T_vpreCH

/-- info: 'Spike.Lib.X64HelloVPreC.scovH_of' depends on axioms: [propext] -/
#guard_msgs in
#print axioms scovH_of

end Spike.Lib.X64HelloVPreC
