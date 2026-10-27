import Spike.Lib.Src.Hello1Out
import Scc.Lower.Spec2
import Spike.Lib.HookOK
import Spike.Lib.Src.ImmIn2

/-!
**An `Accepted2` program never exits through an extern** (ISA-neutral): the
generic form of `Hello1Out`'s `hello1o_noExit`. No `Accepted2` block has an
exit extern or a spawn, no start of `progInit` has one, so under WeakCore's
output hook no reachable configuration's event trace has an exit, and
`srcP1o arch p`'s hook is accepted by the consumers (`HookOK`).

- `noS_of_body2`, `noS_of_decl2`, `noS_of_decls2`, `noExitOp_of_accepted2`:
  no `ExitOp` in an `Accepted2` program;
- `StartNoExit`, `startNoExit_one`, `progInit_startNoExit`: the starts;
- `noExit_of_progNoS`, `noExit_hook_of_accepted2`: every reachable
  configuration;
- `usesWc_srcP1o`, `hookOK_srcP1o`: `HookOK (srcP1o arch p) p`;
- `progInit_of_setupOf_some`, `progInit_of_setupOf_none`: `progInit` by the
  setup block (before it, or at `main`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem Scc.Lower

/-- An `Accepted2` body has no exit extern and no spawn (`body2` admits neither). -/
theorem noS_of_body2 {cx : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {e : Expr}
    (h : body2 cx cs bufs scope e = true) : NoS ExitOp e := by
  fun_induction body2 cx cs bufs scope e <;> simp_all [NoS, ExitOp]
  case case6 ih =>
    obtain ⟨-, h⟩ := h
    split at h
    · simp only [Bool.and_eq_true] at h; exact ih _ h.2
    · cases h

/-- An `Accepted2` block's body has none: the extern's and the loop's models by text, the others by
`body2`. -/
theorem noS_of_decl2 {earlier : List String} {setup : Option Ty} {ext : Bool} {d : Decl}
    (h : decl2 earlier setup ext d = true) : NoS ExitOp d.body := by
  unfold decl2 at h
  split at h
  · simp only [Bool.and_eq_true] at h
    rw [Scc.Frontend.declIs_eq h.1]
    simp [NoS, ExitOp, Scc.Frontend.printExtD, Scc.Frontend.printBody]
  split at h
  · rw [Scc.Frontend.declIs_eq h]
    simp [NoS, ExitOp, Scc.Frontend.printLoopD, Scc.Frontend.printLBody, Scc.Frontend.printAdv,
      Scc.Frontend.printNext]
  split at h
  · simp only [main2, Bool.and_eq_true] at h; exact noS_of_body2 h.2
  split at h
  · split at h
    · simp only [setup2, Bool.and_eq_true] at h; exact noS_of_body2 h.2
    · simp only [plain2, Bool.and_eq_true] at h; exact noS_of_body2 h.2
  · simp only [plain2, Bool.and_eq_true] at h; exact noS_of_body2 h.2

/-- The blocks of `decls2` have none. -/
theorem noS_of_decls2 {setup : Option Ty} {ext : Bool} :
    ∀ {earlier : List String} {p : Prog}, decls2 earlier setup ext p = true → ProgNoS ExitOp p
  | _, [], _ => by intro d hd; cases hd
  | _, d :: ds, h => by
    simp only [decls2, Bool.and_eq_true] at h
    intro d' hd'
    rcases List.mem_cons.1 hd' with rfl | hd'
    · exact noS_of_decl2 h.1
    · exact noS_of_decls2 h.2 d' hd'

/-- **No block of an `Accepted2` program has an exit extern or a spawn.** -/
theorem noExitOp_of_accepted2 {p : Prog} (h : Accepted2 p = true) : ProgNoS ExitOp p := by
  simp only [Accepted2, Bool.and_eq_true] at h
  exact noS_of_decls2 h.1.1.1.1.1.1.1.2

/-- A start with no exit operation in its threads and no exit in its trace. -/
def StartNoExit (c : Cfg) : Prop := CfgNoS ExitOp c ∧ ∀ x, Event.exit x ∉ c.trace

/-- A one-thread start at a term with no exit operation and an empty stack. -/
theorem startNoExit_one {mem : WeakMem.Memory} {th : TTh} {cap : Nat} (ht : NoS ExitOp th.term)
    (hs : th.stack = []) : StartNoExit { mem := mem, ths := #[th], cap := cap } := by
  refine ⟨fun j th0 hj => ?_, fun x hx => by simp at hx⟩
  rcases j with _ | j
  · simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
    subst hj
    exact ⟨ht, by simp [hs]⟩
  · simp at hj

/-- **Every start of `progInit`** has no exit operation and no exit. -/
theorem progInit_startNoExit {p : Prog} {cap : Nat} {c : Cfg} (h : SrcSem.progInit p cap c) : StartNoExit c := by
  have key : SrcSem.progInit p cap = SrcSem.mainInit cap ∨ SrcSem.progInit p cap = SrcSem.tidInit cap ∨
      SrcSem.progInit p cap = SrcSem.setupInit cap ∨ SrcSem.progInit p cap = fun _ => False := by
    unfold SrcSem.progInit
    split
    · split <;> simp
    · simp
  rcases key with e | e | e | e <;> rw [e] at h
  · subst h; exact startNoExit_one (by simp [NoS]) rfl
  · obtain ⟨meW, rfl⟩ := h; exact startNoExit_one (by simp [NoS]) rfl
  · obtain ⟨meW, rfl⟩ := h; exact startNoExit_one (by simp [SrcSem.setupTerm, NoS, ExitOp]) rfl
  · exact h.elim

/-- **No reachable configuration has an exit in its trace**, under WeakCore's
output hook, for a program with no exit operation, from starts with none. -/
theorem noExit_of_progNoS {P : SrcSem.SrcParams} {p : Prog} (hp : ProgNoS ExitOp p)
    (hU : SrcOutProto.UsesWc P p) (hinit : ∀ c, P.init c → StartNoExit c) {tr : List Ev} {s : Cfg}
    (h : (SrcSem.source P p).Reach tr s) : ∀ x, Event.exit x ∉ s.trace := by
  obtain ⟨s0, h0, hr⟩ := h
  have H : StartNoExit s0 := hinit s0 h0
  clear h0
  suffices StartNoExit s from this.2
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact ⟨cfgNoS_threadB hp H.1 hs, by erw [TermArchE.threadSteps_trace hs]; exact H.2⟩
      · exact ⟨cfgNoS_promB H.1, by erw [TermArchE.promise_trace]; exact H.2⟩
    · exfalso
      obtain ⟨x, f, a, T, ts, e, th, -, -, hth, hterm, -⟩ := hs
      have := (H.1 _ _ hth).1
      rw [hterm] at this
      exact this.1 trivial
    · rw [hU] at hs
      obtain ⟨x, n, a, e, th1, rt, ws, rs, h1, hterm, -, -, -, -, rfl⟩ := hs
      have hn : n ≠ .exitEv := by
        rintro rfl
        have := (H.1 _ _ h1).1
        rw [hterm] at this
        exact this.1 trivial
      refine ⟨cfgNoS_wakeB _ _ _ _ (cfgNoS_extB h1 hterm H.1 ws rs), fun y hy => ?_⟩
      erw [TermExtStep.wake_trace, TermExtStep.extCfg_trace] at hy
      rcases List.mem_append.1 hy with hy | hy
      · exact H.2 y hy
      · exact events_noExit hn ws rs y hy

/-- **An `Accepted2` program's hook trace has no exit**, from `progInit`'s starts. -/
theorem noExit_hook_of_accepted2 {P : SrcSem.SrcParams} {p : Prog} (hA : Accepted2 p = true)
    (hU : SrcOutProto.UsesWc P p) (hinit : ∀ c, P.init c → SrcSem.progInit p P.cap c) :
    ∀ tr s, (SrcSem.source P p).Reach tr s → ∀ x, Ev.exit x ∉ P.hooks.trace s :=
  fun _ _ h => Spike.Lib.PrintSrc.noExit_hook hU
    (noExit_of_progNoS (noExitOp_of_accepted2 hA) hU (fun c hc => progInit_startNoExit (hinit c hc)) h)

/-- **`srcP1o`'s hook is WeakCore's.** -/
theorem usesWc_srcP1o (arch : WeakMem.Arch) (p : Prog) : SrcOutProto.UsesWc (SrcSem.srcP1o arch p) p := rfl

/-- **`srcP1o` of an `Accepted2` program has an accepted hook** (`HookOK.wc`). -/
theorem hookOK_srcP1o {p : Prog} (hA : Accepted2 p = true) (arch : WeakMem.Arch) :
    HookOK (SrcSem.srcP1o arch p) p :=
  .wc (usesWc_srcP1o arch p) (noExit_hook_of_accepted2 hA (usesWc_srcP1o arch p) fun _ h => h)

/-- **With a setup block, the start is before it.** -/
theorem progInit_of_setupOf_some {p : Prog} {s : Ty} (h : setupOf p = some s) (cap : Nat) :
    SrcSem.progInit p cap = SrcSem.setupInit cap := by
  unfold setupOf at h
  unfold SrcSem.progInit
  split at h
  · rename_i d hd
    rw [hd]
    split at h
    · rename_i s' ht; dsimp only; rw [ht]
    · cases h
  · cases h

/-- **Without a setup block, an `Accepted2` program starts at `main`.** -/
theorem progInit_of_setupOf_none {p : Prog} (hA : Accepted2 p = true) (h : setupOf p = none) (cap : Nat) :
    SrcSem.progInit p cap = SrcSem.mainInit cap := by
  simp only [Accepted2, Bool.and_eq_true] at hA
  have hD := hA.1.1.1.1.1.1.1.2
  rw [h] at hD
  have hm := hA.1.1.1.1.1.1.1.1.2
  unfold SrcSem.progInit
  cases hf : p.find? (·.name == "main") with
  | none =>
    obtain ⟨d, hd, hn⟩ := List.any_eq_true.1 hm
    exact absurd hn (by simp only [List.find?_eq_none] at hf; exact hf d hd)
  | some d =>
    have hdp := List.mem_of_find?_eq_some hf
    have hdn : d.name = "main" := by simpa using List.find?_some hf
    obtain ⟨E, hE⟩ := decl2_of_decls2 hD d hdp
    have hpe : isPrintExt d = false := by simp [isPrintExt, hdn]
    unfold decl2 at hE
    have hnp : ¬ (hasPrint p = true ∧ "main" = "printL") := by simp
    simp only [hpe, hdn, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, main2, Bool.and_eq_true,
      beq_iff_eq, hnp] at hE
    simp only [hE.1.2]

/-- info: 'Spike.Lib.LowerNode.hookOK_srcP1o' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hookOK_srcP1o

/-- info: 'Spike.Lib.LowerNode.progInit_of_setupOf_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms progInit_of_setupOf_none

end Spike.Lib.LowerNode
