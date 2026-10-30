/-
**wake.w on AArch64: the worker's store bound at main's spawn** (`hview` of `Spike.Lib.WakeSpawnR.spawn_R`).

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
  invariant `SpawnViewLtSteps.VPre` (`WakePreInv.Pre1T.invSrc` with
  `vpre_init`, `vpre_run`).
- `hlt0_of` (b): at main's clone, from the pre-spawn relation `RSAH` (the
  process not exited), `VPre` and main's source position (at `spawnTerm`,
  `p` bound, `main` not returned): the spawn's run and `LtPre` at `c`'s label
  `l` (`vpre_spawn`, `run_spawnCfg`).
- `hview_R`: at `WakeWorkerR.QIR` (any `ok`, executable, end and prefix), a
  record `w = recW … l … w1` (`PreR.hw`) whose source size is `s'.mem.size`
  (`SpawnPre.SR`), `s'`'s threads `#[s0, s1]` (`SpawnPre.ths`) and `s1`'s
  environment (`PreR.env1`): `QIR`'s `mviewS s1` and `obS s1` (`helloC`'s, at
  the worker's word `cwW = w1` and `cS = ⟨l, 0⟩`) are below `(SR w).S`.
-/
import Spike.Lib.WakeWorkerR
import Spike.Lib.SpawnViewLt
import Spike.Lib.SpawnViewLtSteps
import Spike.Lib.WakePreInv
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeSpawnLt

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeW1 Spike.Lib.Inv2Core
open Spike.Lib.WakeInst (Gh)
open Spike.Lib.WakeOkW (recW)
open Spike.Lib.SpawnViewLt (SpawnVLt hview_of_spawnCfg)

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

open Spike.Lib.WakePreTi (Pre1T) in
open Spike.Lib.SpawnViewLtSteps (VPre vpre_init vpre_run) in
/-- **`Pre1T` with `VPre`** (generic in the entry `E` and the relation):
`VPre` holds at every source start and is kept by every source run. -/
theorem pre1T_vpre {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {E : Entry}
    {R1 : Cfg → TermRun.Cfg → Prop} {Ab Ac : State → Prop} (O : Pre1T arch Λ B asm E R1 Ab Ac) :
    Pre1T arch Λ B asm E (fun d s => R1 d s ∧ VPre s) Ab Ac :=
  Spike.Lib.WakePreInv.Pre1T.invSrc O VPre (fun _ h => vpre_init h) (fun _ _ _ h hv => vpre_run h hv)

/-! ## (b) `hlt0` at main's clone -/

open Spike.Lib.A64ConsumerA (RSAH) in
open Spike.Lib.SpawnViewLtSteps (VPre spawnTerm vpre_spawn run_spawnCfg) in
/-- **`LtPre` at main's clone** (see the module doc): the pre-spawn
relation's one source thread `th0` (no promises) at the spawn term with `p`
bound to `ws`, `VPre`, and `main` not returned give the spawn's run with the
empty trace to `s' := spawnCfg s 0 th0 "t" mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws`
(`th0`, `ws` returned, `s.ths = #[th0]`) and `LtPre s s' l _` at any label
`l`; the instance takes `l` to be `c`'s (`PreR.hc`, `hw`, `hlt` share it). -/
theorem hlt0_of {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : Prog} {G : Loc → Val → Prop}
    {own : Spike.Lib.A64ConsumerS.OwnS} {I : Spike.Lib.A64ConsumerS.InvS} {H : State → List (Nat × Range) → Prop}
    {μ : Marks} {ar : Arena} {d : Cfg} {s : TermRun.Cfg} {arch : WeakMem.Arch}
    (hR : RSAH Λ P p G own I H μ ar d s) (hx : d.2.exited = none) (hV : VPre s)
    (hpos : ∀ th0, s.ths = #[th0] → th0.term = spawnTerm ∧ ∃ rt ws, TermRun.evalAt th0.env (.var "p") = some (rt, ws))
    (hex : SrcSem.mainExit s = []) (l : WeakMem.AllocLabel) :
    ∃ (th0 : TermRun.TTh) (ws : List TermRun.Word), s.ths = #[th0] ∧
      (wakeS arch).Run s []
        (TermSpawnStep.spawnCfg s 0 th0 "t" WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) ∧
      LtPre s (TermSpawnStep.spawnCfg s 0 th0 "t" WakeM0.mTail "worker" [] (.prod (.ptr .pub .int) .tid) ws) l
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

section
variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)

/-- **`hview` at main's spawn** (see the module doc): the worker's store
view and ordering bound below the record's source size. -/
theorem hview_R {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
    {M : WakeM0.MSide {g : Gh // ok g}} {r0 r1 : {g : Gh // ok g} → Range} {w : {g : Gh // ok g}}
    {s s' : TermRun.Cfg} {s0 s1 : TermRun.TTh} {T S : Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel} {pT : Loc} {w1 w2 : TermRun.Word} {ty1 : Ty}
    (hw : w.1 = recW T S lbl lsize l pT w1)
    (hS : ((WakeWorkerR.QIR hp i ok exe endPc kp arch R1 μ M r0 r1).SR w).S = s'.mem.size)
    (hths : s'.ths = #[s0, s1]) (env1 : s1.env = [("a", ty1, [w1, w2])]) (hlt : LtPre s s' l ty1) :
    ((WakeWorkerR.QIR hp i ok exe endPc kp arch R1 μ M r0 r1).C w).mviewS s1 <
        ((WakeWorkerR.QIR hp i ok exe endPc kp arch R1 μ M r0 r1).SR w).S ∧
      ((WakeWorkerR.QIR hp i ok exe endPc kp arch R1 μ M r0 r1).C w).obS s1 <
        ((WakeWorkerR.QIR hp i ok exe endPc kp arch R1 μ M r0 r1).SR w).S := by
  obtain ⟨th0, x, e, f, ts, ws, hs0, rfl, hv, hws⟩ := hlt
  rw [hS]
  have hs1 : (TermSpawnStep.spawnCfg s 0 th0 x e f ts ty1 ws).ths[s.ths.size]? = some s1 := by
    rw [hths, hs0]; rfl
  have h := hview_of_spawnCfg hv hws hs1 env1 Promises.Knobs.all arch
  have hcw : w.1.cwW = w1 := by rw [hw]; rfl
  have hcS : w.1.cS = ⟨l, 0⟩ := by rw [hw]; rfl
  have hcw' : (WakeWorkerR.wakeDR hp i ok exe endPc kp).cw w = w1 := hcw
  simp only [WakeWorkerR.QIR, WakeQ.wakeQ, WorkerSrc.helloC, hcw', hcS]
  exact h

end

/-- info: 'Spike.Lib.WakeSpawnLt.pre1T_vpre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pre1T_vpre

/-- info: 'Spike.Lib.WakeSpawnLt.hlt0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hlt0_of

/-- info: 'Spike.Lib.WakeSpawnLt.hview_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hview_R

end Spike.Lib.WakeSpawnLt
