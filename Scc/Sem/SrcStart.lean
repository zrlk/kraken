/-
**The source start, discharged**: the premises of
`Scc/Sem/PubFree.lean`'s `srcTyped_spawn_of_noPublish` at the start the
source instance uses (`SrcSem.mainInit cap`: `mainStart`, one thread entering
`main` on a unit argument, empty memory, capacity `cap`), so that for a
concrete program they are `decide` obligations.

- **The start.** `mainStart_shape`: `mainStart`'s one thread; `initShape_main`:
  TermInit's `InitShape` (empty memory and pairs, box fence on, no promises,
  empty stack, zero views, the entry typed by `TermInit.entryOK_of`), from the
  checker accepting `main`'s entry (`EntryChk`); hence `startOKX_main`
  (`StartOKX`: `SysInvO`, `AllNoProm`, `ViewInv`, `PWFall`, through
  `TermMain.initOK_of` and `A9SpawnFinal.startOKX_of_initOK`),
  `runScope_main` (`TermInit.runDRF_spawn`) and `runPF_main`.
- **The knobs.** `storeDepRts_all`: `Promises.Knobs.all` sets `storeDepRts`.
- **The runs.** `source_run_spawn`: with no extern hook, a run of
  `source P p` is a `StepsG … (Spawn p k arch cap)` run.
- **Typing.** `SrcChecks p r`: the checks on the program (`checkProg`,
  `ProgScopeOKW`, `ProgPubFree`, `main`'s entry at return type `r`), each
  decidable; `srcTyped_of_init`: every configuration `source P p` reaches is
  `SrcTyped`, the shape `Sim.transfer` consumes.
-/
import Scc.Sem.PubFree
import Scc.Sem.SrcExt

namespace Scc.Sem.SrcStart

open CoreLang CoreTerm CoreTyping TermRun TermSound TermMain TermSpawnStep TermInit
open Scc.Sem.PubFree

/-- The context `main`'s entry is checked in: the argument `a : unit`,
return type `r`. -/
def mainCx (r : Ty) : Cx := { vars := [("a", .unit, true)], ret := r }

/-- The entry term of `mainStart`. -/
def mainTerm : Expr := .tail "main" [] (.var "a") []

/-- **The checker accepts `main`'s entry** at return type `r`, and the
entry context's types are in scope. -/
structure EntryChk (p : Prog) (r : Ty) : Prop where
  chk : check p (mainCx r) mainTerm = .ok ()
  tv : TermTv.TvOK (mainCx r)

/-- **`main`'s entry context is in scope** when the return type is (a
Boolean test, `decide` for a concrete `r`). -/
theorem tvOK_mainCx {r : Ty} (h : (TermClose.tb 0 r && TermTv.mg r && TermTv.noIallV r) = true) : TermTv.TvOK (mainCx r) := by
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, ?_, h.1.1, ?_, ?_, ?_, h.1.2, h.2⟩ <;> simp [mainCx, TermClose.tb, TermTv.mg, Cx.opaqueOK]

/-- `mainStart` with capacity `cap`. -/
def start (cap : Nat) : Cfg := { SrcSem.mainStart with cap := cap }

/-- `start cap` has one thread, `mainStart`'s. -/
theorem start_ths {cap i : Nat} {th : TTh} (h : (start cap).ths[i]? = some th) :
    i = 0 ∧ th = { term := mainTerm, env := [("a", .unit, [])] } := by
  simp only [start, SrcSem.mainStart] at h
  match i, h with
  | 0, h => simp at h; exact ⟨rfl, h.symm⟩

/-- **`start cap` has TermInit's initial shape**, given the checker accepts
`main`'s entry. -/
theorem initShape_main {p : Prog} {r : Ty} {cap : Nat} (hc : EntryChk p r) : InitShape p (start cap) where
  mem := rfl
  pairs := rfl
  bf := rfl
  thr i th h := by
    obtain ⟨rfl, rfl⟩ := start_ths h
    refine ⟨rfl, rfl, rfl, entryOK_of (t := .unit) (r := r) (ws := []) rfl rfl rfl hc.chk hc.tv rfl
      (Lay_etok_unit rfl) rfl rfl⟩
  vs0 i th h := by
    obtain ⟨rfl, rfl⟩ := start_ths h
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro e he w hw
    simp only [List.mem_singleton] at he
    subst he
    cases hw
  envNoLoc i th h := by
    obtain ⟨rfl, rfl⟩ := start_ths h
    intro e he w hw
    simp only [List.mem_singleton] at he
    subst he
    cases hw
  tid0 i th h := by
    obtain ⟨rfl, rfl⟩ := start_ths h
    rfl
  tys0 i th h := by
    obtain ⟨rfl, rfl⟩ := start_ths h
    rfl

/-- **`StartOKX` at the start**: `SysInvO`, no promises, `ViewInv`, `PWFall`
(`initOK_of`, `startOKX_of_initOK`). -/
theorem startOKX_main {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {r : Ty} {cap : Nat}
    (hc : EntryChk p r) : A9SpawnFinal.StartOKX p k arch Init (start cap) :=
  A9SpawnFinal.startOKX_of_initOK (initOK_of (initShape_main hc) trivial)

/-- **`RunScope` at the start** (`runDRF_spawn`: `unit` and no type
arguments are `drf`). -/
theorem runScope_main {cap : Nat} : TermScope.RunScope (start cap) :=
  runDRF_spawn fun i th h => by
    obtain ⟨rfl, rfl⟩ := start_ths h
    exact ⟨"main", [], .unit, [], rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **`RunPF` at the start**: one thread at a `tail`, no stack. -/
theorem runPF_main {cap : Nat} : RunPF (start cap) :=
  runPF_init fun i th h => by
    obtain ⟨rfl, rfl⟩ := start_ths h
    exact ⟨"main", [], .var "a", [], rfl, rfl⟩

/-- **The source's knobs set `storeDepRts`.** -/
theorem storeDepRts_all : Promises.Knobs.all.storeDepRts = true := rfl

/-- **With no extern hook, the runs of `source P p` are runs with spawns** at
capacity `P.cap`. -/
theorem source_run_spawn {P : SrcSem.SrcParams} {p : Prog} (hP : P.hooks = SrcSem.SrcHooks.none)
    {c c' : Cfg} {tr : List Ev} (h : (SrcSem.source P p).Run c tr c') :
    StepsG p P.k P.arch (Spawn p P.k P.arch P.cap) c c' :=
  (SrcSem.source_run_stepsG h).mono fun _ _ ⟨_, hs⟩ =>
    hs.elim (fun h => h.spawn) (fun h => by rw [hP] at h; exact h.elim)

/-- **The checks on a program** that the source typing needs: the checker,
the scope check, no `publish`, and `main`'s entry at return type `r`. Each is
decidable for a concrete program (`SrcChecks.of_decide`). -/
structure SrcChecks (p : Prog) (r : Ty) : Prop where
  checked : checkProg p = .ok ()
  scope : TermScope.ProgScopeOKW p = true
  noPub : ProgPubFree p
  entry : EntryChk p r

/-- The checks from five Boolean tests (`decide` on each). -/
theorem SrcChecks.of_decide {p : Prog} {r : Ty}
    (h1 : (checkProg p matches .ok ()) = true) (h2 : TermScope.ProgScopeOKW p = true)
    (h3 : (p.all fun d => PubFree.pubFree d.body) = true) (h4 : (check p (mainCx r) mainTerm matches .ok ()) = true)
    (h5 : (TermClose.tb 0 r && TermTv.mg r && TermTv.noIallV r) = true) : SrcChecks p r := by
  refine ⟨?_, h2, h3, ⟨?_, tvOK_mainCx h5⟩⟩
  · revert h1; cases checkProg p with
    | ok u => intro; rfl
    | error _ => intro h; cases h
  · revert h4; cases check p (mainCx r) mainTerm with
    | ok u => intro; rfl
    | error _ => intro h; cases h

/-- **Every configuration the source reaches is typed**, for a program
passing `SrcChecks`, with the source's default knobs, the `main` start and no
extern hook: the invariant `Sim.transfer` takes. -/
theorem srcTyped_of_init {p : Prog} {r : Ty} (hp : SrcChecks p r) {P : SrcSem.SrcParams}
    (hk : P.k = Promises.Knobs.all) (hi : P.init = SrcSem.mainInit P.cap) (hh : P.hooks = SrcSem.SrcHooks.none) :
    ∀ tr s, (SrcSem.source P p).Reach tr s → SrcTyped p s := by
  rintro tr s ⟨s0, h0, hr⟩
  change P.init s0 at h0
  rw [hi] at h0
  subst h0
  have hr' := source_run_spawn hh hr
  have hks : P.k.storeDepRts = true := by rw [hk]; rfl
  exact srcTyped_spawn_of_noPublish (Init := .zero) hp.checked hp.scope runScope_main hp.noPub runPF_main hks
    (startOKX_main hp.entry) hr'

/-! ## End-to-end tests -/

/-- A publish-free `main`: it returns its unit argument. -/
def mainD : Decl where
  name := "main"; idx := []; arg := "a"
  argTy := .unit
  retTy := .unit
  body := .ret (.var "a")

/-- A one-block program and its checks, each by `decide`. -/
theorem srcChecks_main : SrcChecks [mainD] .unit :=
  SrcChecks.of_decide (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The source parameters of the test: AArch64's model, four threads. -/
def testP : SrcSem.SrcParams := { arch := .arm, cap := 4, init := SrcSem.mainInit 4 }

/-- **End to end**: every configuration the test program reaches is typed. -/
theorem srcTyped_main : ∀ tr s, (SrcSem.source testP [mainD]).Reach tr s → SrcTyped [mainD] s :=
  srcTyped_of_init srcChecks_main rfl rfl rfl

/-- **A program with `publish` is rejected**: WeakCore's `leakD` publishes,
so the checks fail whatever the return type. -/
theorem not_srcChecks_leak (r : Ty) : ¬ SrcChecks [mainD, leakD] r :=
  fun h => absurd h.noPub (by decide)

end Scc.Sem.SrcStart
