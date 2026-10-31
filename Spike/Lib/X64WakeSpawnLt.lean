/-
**wake.w on x86-64: the worker's store bound at main's spawn** (hello plan
1.6), the x86-64 twin of `Spike/Lib/WakeSpawnLt.lean` (`hview` of
`X64WakeSpawnR.spawn_R`).

At main's `clone` the source configuration `s'` is main's spawn of `s`
(`TermSpawnStep.spawnCfg s 0 th0 …`), the worker `s1` its child at slot 1
with argument words `[w1, w2]`. `SpawnViewLt.hview_of_spawnCfg` bounds the
worker's `store rel c 1` (`Promises.storeMview` / `storeOb` at the child's
views and the bumped word `w1`) below `s'.mem.size`, given strict view bounds
on main's thread `th0` at `c`'s address (`SpawnViewLt.SpawnVLt`, "hlt0") and
on the spawn's argument words.

- `LtPre s s' l ty1`: the per-configuration premise (the spawn's shape, `hlt0`
  at `⟨l, 0⟩` below `s.mem.size`, the argument words below it).
- `pre1T_vpre` (a): any `Pre1T … R1` strengthened by the source
  invariant `X64SpawnViewLtSteps.VPre` (`X64WakePreInv.Pre1T.invSrc` with
  `vpre_init`, `vpre_run`).
- `hlt0_of` (b): at main's clone, from the pre-spawn relation `RSAH` (the
  process not exited), `VPre` and main's source position (at `spawnTerm`,
  `p` bound, `main` not returned): the spawn's run and `LtPre` at `c`'s label
  `l` (`vpre_spawn`, `run_spawnCfg`).

**Unlike AArch64** (for now): A64's `hview_R`, stated at
`WakeWorkerR.QIR`, is not here yet; it waits on the x86-64 `WakeWorkerR`
(which waits on `WakeOkW`, `WakeWorkerX`, `WakeAssembly`, `WakeAssemblyI`)
and will be added to this file when that lands. This file imports neither.
-/
import Spike.Lib.SpawnViewLt
import Spike.Lib.X64SpawnViewLtSteps
import Spike.Lib.X64WakePreInv
import Spike.Lib.X64WakeM0
import Spike.Lib.X64ConsumerAH

namespace Spike.Lib.X64WakeSpawnLt

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.SpawnViewLt (SpawnVLt)

/-- **The per-configuration premise of `hview_R`**: `s'` is main's (slot
`0`, the only thread `th0` of `s`) spawn of `s` at the checked type `ty1`,
`th0`'s views and coherence at `c`'s address `⟨l, 0⟩` below `s.mem.size`
(`hlt0`), and the spawn's argument words' views and read timestamps below
it. -/
def LtPre (s s' : TermRun.Cfg) (l : WeakMem.AllocLabel) (ty1 : Ty) : Prop :=
  ∃ (th0 : TermRun.TTh) (x : String) (e : Expr) (f : String) (ts : List Ty) (ws : List TermRun.Word),
    s.ths = #[th0] ∧ s' = TermSpawnStep.spawnCfg s 0 th0 x e f ts ty1 ws ∧
    SpawnVLt th0 ⟨l, 0⟩ s.mem.size ∧ ∀ w ∈ ws, w.view < s.mem.size ∧ w.rts < s.mem.size

/-! ## (a) the pre-spawn obligations with `VPre` -/

open Spike.Lib.X64WakePreTi (Pre1T) in
open Spike.Lib.X64SpawnViewLtSteps (VPre vpre_init vpre_run) in
/-- **`Pre1T` with `VPre`** (generic in the entry `E` and the relation):
`VPre` holds at every source start and is kept by every source run. -/
theorem pre1T_vpre {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Scc.Sem.X64.Asm} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop} (O : Pre1T arch Λ B asm E R1 Ab Ac) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPre s) Ab Ac :=
  Spike.Lib.X64WakePreInv.Pre1T.invSrc O VPre (fun _ h => vpre_init h) (fun _ _ _ h hv => vpre_run h hv)

/-! ## (b) `hlt0` at main's clone -/

open Spike.Lib.X64ConsumerA (RSAH) in
open Spike.Lib.X64SpawnViewLtSteps (VPre spawnTerm vpre_spawn run_spawnCfg) in
/-- **`LtPre` at main's clone** (see the module doc): the pre-spawn
relation's one source thread `th0` (no promises) at the spawn term with `p`
bound to `ws`, `VPre`, and `main` not returned give the spawn's run with the
empty trace to `s' := spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws`
(`th0`, `ws` returned, `s.ths = #[th0]`) and `LtPre s s' l _` at any label
`l`; the instance takes `l` to be `c`'s (`PreR.hc`, `hw`, `hlt` share it). -/
theorem hlt0_of {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {H : State → List (Nat × Range) → Prop}
    {μ : Marks} {ar : Arena} {d : Cfg} {s : TermRun.Cfg} {arch : WeakMem.Arch}
    (hR : RSAH Λ P p G own I H μ ar d s) (hx : d.2.exited = none) (hV : VPre s)
    (hpos : ∀ th0, s.ths = #[th0] → th0.term = spawnTerm ∧ ∃ rt ws, TermRun.evalAt th0.env (.var "p") = some (rt, ws))
    (hex : SrcSem.mainExit s = []) (l : WeakMem.AllocLabel) :
    ∃ (th0 : TermRun.TTh) (ws : List TermRun.Word), s.ths = #[th0] ∧
      (wakeS arch).Run s []
        (TermSpawnStep.spawnCfg s 0 th0 "t" X64WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) ∧
      LtPre s (TermSpawnStep.spawnCfg s 0 th0 "t" X64WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) l
        (.prod (.ptr .pub .int) .tid) := by
  rcases hR with h | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · obtain ⟨-, th0, -, -, -, -, -, -, -, -, -, -, -, -, -, hs, -, hp, -⟩ := h
    obtain ⟨ht, rt, ws, hev⟩ := hpos th0 hs
    have h0 : s.ths[0]? = some th0 := by rw [hs]; rfl
    have h1 : s.ths.size = 1 := by rw [hs]; rfl
    obtain ⟨hvl, henv⟩ := vpre_spawn hV h1 h0 ht
    refine ⟨th0, ws, hs, run_spawnCfg h0 ht hp (by omega) hev hex, th0, _, _, _, _, ws, hs, rfl, hvl ⟨l, 0⟩, ?_⟩
    exact fun w hw => henv _ (TermNoFul.lookupE_mem (env := th0.env) (x := "p") hev) w hw
  · rw [hk] at hx; cases hx

end Spike.Lib.X64WakeSpawnLt

/-- info: 'Spike.Lib.X64WakeSpawnLt.pre1T_vpre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeSpawnLt.pre1T_vpre

/-- info: 'Spike.Lib.X64WakeSpawnLt.hlt0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeSpawnLt.hlt0_of
