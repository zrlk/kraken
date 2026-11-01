/-
**hello.w on AArch64: main's spawn and the worker's store bound's premise**
(the twin, at `helloSrc`, of `Spike.Lib.WakeSpawnLt`'s (b)).

At main's `clone` the source configuration `s'` is main's spawn of `s` at
`spawnTermH`: `spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws` (hello's
continuation is wake's `mTail`, `HelloMainSrc.spawnTermH_eq`).

- `mainExit_spawnCfgH`, `run_spawnCfgH`: main has not returned after the
  spawn, and the spawn is a `helloS` run with the empty trace (the twins of
  `SpawnViewLtSteps.mainExit_spawnCfg` / `run_spawnCfg`);
- `hlt0_ofH`: at main's clone, from the pre-spawn relation `RSAH` (the
  process not exited), `HelloVPre.VPreH` and main's source position (at
  `spawnTermH`, `p` bound, `main` not returned): the spawn's run and
  `WakeSpawnLt.LtPre` at any label `l` (`vpreH_spawn`, `run_spawnCfgH`).
- `spawn_view_lt_mem`: `SpawnViewLt.spawn_view_lt` at any argument word of
  the child (hello's pointer word for `c` is the packet's fourth, not its
  first);
- `hview_RH`: at `HelloQ.helloQ` (any worker side `D`), a record whose flag
  is `⟨l, 0⟩`, whose source size is `s'.mem.size` and whose pointer word
  `D.cw w` is one of the child `s1`'s argument words: `mviewS s1` and
  `obS s1` are below `(SR w).S` (the twin of `WakeSpawnLt.hview_R`).
-/
import Spike.Lib.WakeSpawnLt
import Spike.Lib.HelloMainSrc
import Spike.Lib.HelloVPre
import Spike.Lib.HelloQ

namespace Spike.Lib.HelloSpawnLt

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloMainPreSrc (pktTy spawnTermH)
open Spike.Lib.WakeM0 (mTail)
open Spike.Lib.SpawnViewLt (SpawnVLt)
open Spike.Lib.SpawnViewLtSteps (EnvLt)
open Spike.Lib.WakeSpawnLt (LtPre)
open Spike.Lib.HelloVPre (VPreH vpreH_spawn)
open Spike.Lib.WorkerSrcStep (getElem?_set!_self)

/-- After hello's spawn, main is at `mTail`: it has not returned. -/
theorem mainExit_spawnCfgH {s : TermRun.Cfg} {th0 : TermRun.TTh} (h0 : s.ths[0]? = some th0)
    (ws : List TermRun.Word) :
    mainExit (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws) = [] := by
  have hs : (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws).ths[0]? =
      some (TermSpawnStep.spawnPar s 0 th0 "t" mTail) := by
    have hlt := (Array.getElem?_eq_some_iff.mp h0).1
    simp only [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT]
    rw [Array.getElem?_push]
    split
    · rename_i h; simp at h; omega
    · exact getElem?_set!_self h0 _
  unfold mainExit
  rw [hs]
  simp [TermSpawnStep.spawnPar, mTail]

/-- **hello main's spawn is a source run with the empty trace.** -/
theorem run_spawnCfgH {arch : WeakMem.Arch} {s : TermRun.Cfg} {th0 : TermRun.TTh} {rt : Ty}
    {ws : List TermRun.Word} (h0 : s.ths[0]? = some th0) (ht : th0.term = spawnTermH)
    (hp : th0.promises = []) (hcap : s.ths.size < 2)
    (hev : TermRun.evalAt th0.env (.var "p") = some (rt, ws)) (hex : mainExit s = []) :
    (helloS arch).Run s [] (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws) := by
  have hstep : (helloS arch).step 0 s [] (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws) := by
    refine ⟨hex, Or.inr (Or.inl ⟨"t", "worker", .var "p", _, [], mTail, th0, rt, ws, h0, ht, hp, hcap, hev, rfl⟩), ?_⟩
    have htr : (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws).trace = s.trace := rfl
    show [] = (srcObs traceOf _).drop (srcObs traceOf s).length
    simp only [srcObs, traceOf, htr, hex, mainExit_spawnCfgH h0, List.drop_length]
  exact LRun.step (step := fun c es c' => ∃ i, (helloS arch).step i c es c') ⟨0, hstep⟩ (LRun.refl _)

open Spike.Lib.A64ConsumerA (RSAH) in
/-- **`LtPre` at hello main's clone** (see the module doc): the pre-spawn
relation's one source thread `th0` (no promises) at `spawnTermH` with `p`
bound to `ws`, `VPreH` and `main` not returned give
the spawn's run with the empty trace to
`s' := spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws` and `LtPre s s' l pktTy`
at any label `l`. -/
theorem hlt0_ofH {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {H : State → List (Nat × Range) → Prop}
    {μ : Marks} {ar : Arena} {d : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} {arch : WeakMem.Arch}
    (hR : RSAH Λ P p G own I H μ ar d s) (hx : d.2.exited = none)
    (hV : VPreH s)
    (hpos : ∀ th0, s.ths = #[th0] → th0.term = spawnTermH ∧ ∃ rt ws, TermRun.evalAt th0.env (.var "p") = some (rt, ws))
    (hex : SrcSem.mainExit s = []) (l : WeakMem.AllocLabel) :
    ∃ (th0 : TermRun.TTh) (ws : List TermRun.Word), s.ths = #[th0] ∧
      (helloS arch).Run s [] (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws) ∧
      LtPre s (TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws) l pktTy := by
  rcases hR with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · obtain ⟨-, th0, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -, hp, -⟩ := h
    obtain ⟨ht, rt, ws, hev⟩ := hpos th0 hs
    have h0 : s.ths[0]? = some th0 := by rw [hs]; rfl
    have h1 : s.ths.size = 1 := by rw [hs]; rfl
    obtain ⟨hv, henv⟩ := vpreH_spawn hV h1 h0 ht
    refine ⟨th0, ws, hs, run_spawnCfgH h0 ht hp (by omega) hev hex, th0, _, _, _, _, ws, hs, rfl, hv ⟨l, 0⟩, ?_⟩
    exact fun w hw => henv _ (TermNoFul.lookupE_mem (env := th0.env) (x := "p") hev) w hw
  · rw [hk] at hx; cases hx

/-- **`spawn_view_lt` at any argument word**: the spawned child's store
bounds at any of its (bumped) argument words `cw` are below `n`, given
`SpawnVLt th a n` and the argument words below `n`. -/
theorem spawn_view_lt_mem {c : TermRun.Cfg} {i : Nat} {th : TermRun.TTh} {f : String} {ts : List Ty} {T : Ty}
    {ws : List TermRun.Word} {a : WeakMem.Address} {n : Nat} (h : SpawnVLt th a n)
    (hws : ∀ w ∈ ws, w.view < n ∧ w.rts < n) {cw : TermRun.Word}
    (hcw : cw ∈ ws.map (TermSpawn.bumpW (TermSpawnStep.spawnS c th).vs.vRelSt)) (k : Promises.Knobs)
    (arch : WeakMem.Arch) :
    Promises.storeMview (WorkerSrc.wTh (TermSpawnStep.spawnKid c i th f ts T ws).vs cw) (TermRun.dataE 1 WorkerSrc.one)
        [0] true < n ∧
      Promises.storeOb k arch (WorkerSrc.wTh (TermSpawnStep.spawnKid c i th f ts T ws).vs cw) a
        (TermRun.dataE 1 WorkerSrc.one) [0] < n := by
  obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hcw
  exact Spike.Lib.SpawnViewLt.store_lt k arch (Spike.Lib.SpawnViewLt.kidVLt_spawnKid h (hws w0 hw0))

open Spike.Lib.HelloQ (helloQ) in
open Spike.Lib.HelloW1 (WSideH) in
/-- **`hview` at hello main's spawn** (see the module doc): the worker's
store view and ordering bound below the record's source size. -/
theorem hview_RH {arch : WeakMem.Arch} {R1 : Spike.Lib.WakeA64.Cfg → TermRun.Cfg → Prop} {ι : Type}
    {SR : ι → Spike.Lib.Inv2Core.SpawnRec} {cT : ι → Loc} {cS : ι → WeakMem.Address} {pT : ι → Loc}
    {P : ι → Spike.Lib.Inv2Core.Inv2Params isaLSE2} {G : ι → Loc → Val → Prop} {passT : State → Prop}
    {M : Spike.Lib.WakeM0.MSide ι} {D : WSideH ι} {r0 r1 : ι → Range} {w : ι}
    {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {l : WeakMem.AllocLabel} {T T' : Ty} {wsK : List TermRun.Word}
    (hS : (SR w).S = s'.mem.size) (hcS : cS w = ⟨l, 0⟩) (hths : s'.ths = #[s0, s1])
    (env1 : s1.env = [("a", T', wsK)]) (hcw : D.cw w ∈ wsK) (hlt : LtPre s s' l T) :
    ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).mviewS s1 <
        ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).SR w).S ∧
      ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).C w).obS s1 <
        ((helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).SR w).S := by
  obtain ⟨th0, x, e, f, ts, ws, hs0, rfl, hv, hws⟩ := hlt
  have hs1 : (TermSpawnStep.spawnCfg s 0 th0 x e f ts T ws).ths[s.ths.size]? = some s1 := by
    rw [hths, hs0]; rfl
  obtain ⟨hm, hk⟩ := Spike.Lib.SpawnViewLt.spawnCfg_facts (c := s) (i := 0) (th := th0) (x := x) (e := e)
    (f := f) (ts := ts) (T := T) (ws := ws)
  rw [hk] at hs1
  cases hs1
  have hwsK : wsK = ws.map (TermSpawn.bumpW (TermSpawnStep.spawnS s th0).vs.vRelSt) := by
    simp only [TermSpawnStep.spawnKid, List.cons.injEq, Prod.mk.injEq, and_true] at env1
    exact env1.2.2.symm
  subst hwsK
  rw [show (helloQ arch R1 ι SR cT cS pT P G passT M D r0 r1).SR w = SR w from rfl, hS, hm]
  simp only [helloQ, WorkerSrc.helloC, hcS]
  exact spawn_view_lt_mem hv hws hcw Promises.Knobs.all arch

/-- info: 'Spike.Lib.HelloSpawnLt.hview_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hview_RH

/-- info: 'Spike.Lib.HelloSpawnLt.run_spawnCfgH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_spawnCfgH

/-- info: 'Spike.Lib.HelloSpawnLt.hlt0_ofH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hlt0_ofH

end Spike.Lib.HelloSpawnLt
