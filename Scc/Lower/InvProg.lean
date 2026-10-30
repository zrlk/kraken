import Scc.Lower.Inv

/-!
# The whole-program lowering of `Accepted0` programs

For a program in `Accepted0` (one code block `main(u : Unit) : Int` with a
straight-line body), the lowering `lowerWithMarks` gives the runtime
functions (fixed by the layout and the entry shape; they do not depend on
the body) followed by exactly one user function, `func0 main r` for the
body's closed form `r` (`Scc/Lower/Inv.lean`), and one placement trace,
`marks0`. There are no thread trampolines (nothing is spawned) and no
externs.

* `rtFuncs`, `progOf`: the runtime functions and the program around the user
  functions, as `lowerWithMarks` builds them;
* `checkedOf_accepted0`: the frontend's checked program of an `Accepted0`
  program (entry `main(Unit) : Int`, no externs);
* `lowerWithMarks_accepted0`: the whole-program statement;
* `lowerIR_accepted0`: the same for `lowerIR` (what `lowerAll` lowers);
  the statement on `lowerAll`'s IR is per ISA (`Scc/Lower/InvA64.lean`,
  `lowerAll_accepted0_a64`), as the two ISAs' emitters cannot be imported
  together.
-/

open CoreLang CoreTerm
open Scc.IR

namespace Scc.Lower.Inv

/-- **The runtime functions** `lowerWithMarks` puts first, for architecture
`arch` (on AArch64 `scc_rt_print`'s write is fenced, `Runtime.printF`),
layout `lay`, entry shape `entry` and `setupWords` words of setup result. -/
def rtFuncs (arch : Arch) (lay : Layout) (entry : Frontend.Entry) (setupWords : Nat) :
    Except String (List Func) :=
  [Runtime.startF lay, Runtime.mainThreadF entry setupWords, Runtime.allocF lay,
    Runtime.allocF lay Names.allocTcb Names.pinned Names.pinnedNext (Runtime.pinnedBytes lay) .threads false,
    Runtime.threadReserveF lay,
    Runtime.threadInitF lay, Runtime.stackTakeF lay, Runtime.stackReleaseF lay, Runtime.growF lay,
    Runtime.printF (fence := arch == .arm), Runtime.parkF, Runtime.unparkF, Runtime.abortF] ++
    Runtime.abortKinds.map Runtime.abortKindF |>.mapM id

/-- **The program** `lowerWithMarks` builds from runtime functions `rt`
and further functions `fs` (thread trampolines, then user functions). -/
def progOf (lay : Layout) (rt fs : List Func) : IR.Program :=
  { funcs := rt ++ fs, data := Runtime.data lay, start := Names.start, abortFn := Names.abort,
    growth := some { grow := Names.grow, release := Names.stackRelease } }

/-- An `Accepted0` body spawns nothing. -/
theorem spawnedE_body0 : ∀ (e : Expr) (scope : List String), body0 scope e = true → spawnedE e = [] := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro scope hb
    cases op with
    | atom a =>
      simp only [body0, Bool.and_eq_true] at hb
      simp only [spawnedE]; exact ih _ hb.2
    | add a b =>
      simp only [body0, Bool.and_eq_true] at hb
      simp only [spawnedE]; exact ih _ hb.2
    | _ => simp [body0] at hb
  | ret a => intro _ _; rfl
  | _ => intro scope hb; simp [body0] at hb

/-- `main` is no extern. -/
theorem externOf_main {d : Decl} (h : d.name = "main") : Frontend.externOf d = none := by
  simp [Frontend.externOf, h]

/-- **The checked program of an `Accepted0` program**: entry `main(Unit) :
Int`, no externs. -/
theorem checkedOf_accepted0 {d : Decl} (hd : Accepted0 [d] = true) :
    checkedOf [d] = .ok { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } := by
  obtain ⟨hn, ht, hi, ha, hr, -⟩ := accepted0_decl hd
  simp [checkedOf, Frontend.entryOf, Frontend.externs, externOf_main hn, hn, ht, hi, ha, hr,
    Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **The whole-program lowering of an `Accepted0` program**: the runtime
functions, then `func0 main r` for the body's closed form `r`; the trace of
`main` is `marks0`. -/
theorem lowerWithMarks_accepted0 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    (hheap : cfg.layout.heapBytes < 2 ^ 32) {rt : List Func}
    (hrt : rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 = .ok rt) :
    ∃ r, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } =
        .ok (progOf cfg.layout rt [func0 (Names.user "main") r], [(Names.user "main", marks0 d)]) := by
  obtain ⟨hn, -, -, -, -, hbody⟩ := accepted0_decl hd
  obtain ⟨r, hr, hl⟩ := lowerDeclMarks_accepted0 [d] [] cfg.layout.obj none hd
  refine ⟨r, hr, ?_⟩
  have hsp : spawnedE d.body = [] := spawnedE_body0 _ _ hbody
  have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
  unfold rtFuncs at hrt
  simp only [lowerWithMarks, hh, ite_false, List.any_nil, Bool.not_false, List.filter_cons_of_pos,
    List.filter_nil, List.mapM_cons, List.mapM_nil, hl, List.flatMap_cons, List.flatMap_nil, hsp,
    List.append_nil, List.eraseDups_nil,
    hrt, bind, Except.bind, pure, Except.pure, hn]
  rfl

/-- A successful `lowerWithMarks` of an `Accepted0` program is the one of
`lowerWithMarks_accepted0`: its runtime functions exist and the arena is
below 4 GiB. -/
theorem lowerWithMarks_accepted0_ok (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {x : IR.Program × List (Sym × Array (Node × Point))}
    (h : lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } =
      .ok x) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      x = (progOf cfg.layout rt [func0 (Names.user "main") r], [(Names.user "main", marks0 d)]) := by
  have hheap : cfg.layout.heapBytes < 2 ^ 32 := by
    refine Nat.lt_of_not_ge fun hc => ?_
    unfold lowerWithMarks at h
    simp only [hc, ↓reduceIte] at h
    cases h
  cases hrt : rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 with
  | error e =>
    exfalso
    obtain ⟨hn, -, -, -, -, hbody⟩ := accepted0_decl hd
    obtain ⟨r, -, hl⟩ := lowerDeclMarks_accepted0 [d] [] cfg.layout.obj none hd
    have hsp : spawnedE d.body = [] := spawnedE_body0 _ _ hbody
    have hh : ¬ (cfg.layout.heapBytes ≥ 2 ^ 32) := by omega
    unfold rtFuncs at hrt
    simp only [lowerWithMarks, hh, ite_false, List.any_nil, Bool.not_false, List.filter_cons_of_pos,
      List.filter_nil, List.mapM_cons, List.mapM_nil, hl, List.flatMap_cons, List.flatMap_nil, hsp,
      List.append_nil, List.eraseDups_nil,
    hrt, bind, Except.bind, pure, Except.pure, hn] at h
    cases h
  | ok rt =>
    obtain ⟨r, hr, hl⟩ := lowerWithMarks_accepted0 cfg hd hheap hrt
    rw [hl] at h
    cases h
    exact ⟨r, rt, hr, rfl, rfl⟩

/-- **The lowering `lowerAll` starts from, on an `Accepted0` program**: the
runtime functions, then `func0 main r`; the trace of `main` is `marks0`. -/
theorem lowerIR_accepted0 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {l : Lowered} (hl : lowerIR cfg [d] = .ok l) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.arch cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      l.ir = progOf cfg.layout rt [func0 (Names.user "main") r] ∧
      l.marks = [(Names.user "main", marks0 d)] := by
  unfold lowerIR at hl
  rw [checkedOf_accepted0 hd] at hl
  simp only [bind, Except.bind] at hl
  cases hb : stackBudget cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } with
  | error e => rw [hb] at hl; cases hl
  | ok b =>
    rw [hb] at hl
    cases hw : lowerWithMarks cfg { prog := [d], entry := ⟨.unit, true⟩, externs := [], adds := [] } with
    | error e => simp only [hw] at hl; cases hl
    | ok x =>
      obtain ⟨r, rt, hr, hrt, rfl⟩ := lowerWithMarks_accepted0_ok cfg hd hw
      simp only [hw] at hl
      cases hl
      exact ⟨r, rt, hr, hrt, rfl, rfl⟩

/-! ## The main-thread runtime function -/

/-- `n` fresh registers named after `hint` from the state's counter. -/
theorem mapM_fresh (hint : String) :
    ∀ (l : List Nat) (s : BState), l.mapM (fun _ => fresh hint) s =
      .ok ((List.range l.length).map (fun i => regName hint (s.next + i)),
        { s with next := s.next + l.length })
  | [], s => rfl
  | a :: l, s => by
    rw [List.mapM_cons, bind_ok (fresh_eq _ _), bind_ok (mapM_fresh hint l _)]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    show Except.ok _ = _
    congr 2
    · simp only [Nat.add_zero, List.cons.injEq, true_and]
      apply List.map_congr_left; intro i _; simp [Function.comp, Nat.add_assoc, Nat.add_comm 1]
    · simp [Nat.add_assoc, Nat.add_comm 1]

/-- `emit` outside a call's source point: the instruction joins the open
block. -/
theorem emit_cur (i : Inst) {s : BState} {l : Label} {is : Array Inst}
    (hc : s.cur = some (l, is)) (hh : s.here = none) :
    emit i s = .ok ((), { s with cur := some (l, is.push i) }) := by
  unfold emit
  rw [bind_ok (modify_eq _ _)]
  simp only [hc]
  cases i <;> simp [hh] <;> rfl

/-- The setup-word registers of the main-thread runtime function. -/
def mainDs (entry : Frontend.Entry) (sw : Nat) : List Reg :=
  (List.range (mainSetup entry sw)).map (regName "s")

/-- The arguments the main-thread runtime function passes `main`. -/
def mainArgs (entry : Frontend.Entry) (sw : Nat) : List Operand :=
  match entry.arg with
  | .unit => []
  | .tid => [.reg "tcb"]
  | .setupTid => (mainDs entry sw).map .reg ++ [.reg "tcb"]

/-- The instructions of the main-thread runtime function: the setup call
(with a setup block), the call of `main`, `exit_group` of its result (or 0). -/
def mainInsts (entry : Frontend.Entry) (sw : Nat) : List Inst :=
  let n := mainSetup entry sw
  (if entry.arg == .setupTid then [.call (mainDs entry sw) (Names.user "rodata") []] else []) ++
  (if entry.retInt then
    [.call [regName "v" n] (Names.user "main") (mainArgs entry sw),
     .syscall (regName "r" (n + 1)) .exitGroup [.reg (regName "v" n)]]
  else
    [.call [] (Names.user "main") (mainArgs entry sw),
     .syscall (regName "r" n) .exitGroup [imm 0]])

/-- **The main-thread runtime function** in closed form. -/
def mainThread0 (entry : Frontend.Entry) (sw : Nat) : Func :=
  { name := Names.mainThread, params := ["tcb"], checkStack := true,
    blocks := [⟨"entry", mainInsts entry sw, .unreachable⟩], heapRegs := ["tcb"], scalarRegs := [] }

set_option maxHeartbeats 1000000 in
theorem mainThreadF_eq (entry : Frontend.Entry) (sw : Nat) :
    Runtime.mainThreadF entry sw = .ok (mainThread0 entry sw) := by
  obtain ⟨arg, ret⟩ := entry
  have hm : markHeap "tcb" ({} : BState) = .ok ((), { heapRegs := #["tcb"] }) := by
    unfold markHeap; rw [modify_eq]; simp [hasReg_eq]
  have e1 : (Frontend.EntryArg.unit == .setupTid) = false := rfl
  have e2 : (Frontend.EntryArg.tid == .setupTid) = false := rfl
  have e3 : (Frontend.EntryArg.setupTid == .setupTid) = true := rfl
  unfold Runtime.mainThreadF buildFunc buildFuncMarks
  cases arg <;> cases ret <;>
  · simp only [StateT.run, ite_true, ite_false, pure_bind, Bool.false_eq_true]
    repeat (first
      | rw [bind_ok hm] | rw [bind_ok (mapM_fresh _ _ _)] | rw [bind_ok (emit_cur _ rfl rfl)]
      | rw [bind_ok (fresh_eq _ _)] | rw [terminate_eq _ rfl])
    simp only [Nat.zero_add, List.length_range]
    simp [mainThread0, mainInsts, mainSetup, mainDs, mainArgs, Functor.map, Except.map, e1, e2, e3]

end Scc.Lower.Inv
