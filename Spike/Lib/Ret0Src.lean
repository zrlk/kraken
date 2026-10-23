/-
**`ret0.w`'s source side**, for both ISAs (`Spike/Lib/A64Ret0Correct.lean`,
`Spike/Lib/X64Ret0Correct.lean`):

- `ret0Src`: the program, the frontend's of `Scc/Test/ret0.w` (checked in
  `Spike/Test/A64Ret0Correct.lean`); `ret0P`: its source parameters;
- `reach_noMem`: on every reachable configuration of `source P p`, for a
  program `p` with no load, store, exchange or spawn (`MemOp`) and no extern
  step, no thread has one: WeakCore's `NoS` invariant (`tstep_noS`,
  `Spike`-side restatements of `cfgNoS_thread`/`no_spawn` for this `bad`).
  This makes each ISA's `SrcSafe` vacuous for `ret0Src`.
-/
import WeakCore.SpawnNoSpawn
import Scc.Sem.SrcExt

namespace Spike.Lib.Ret0Src

open CoreLang CoreTerm
open Scc.Sem

/-! ## The source program -/

/-- `main`'s body in `ret0.w`: `let x = 40; let y = x + 2; ret y`. -/
def ret0Body : Expr :=
  .let_ "x" (.atom (.lit 40)) (.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")))

/-- **`ret0.w`'s source program**: one code block, `main(u : Unit) : Int`. -/
def ret0Src : Prog :=
  [{ name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := ret0Body }]

/-- **The source parameters**: the memory model `arch`, one thread, the
`main` start, no extern step. -/
def ret0P (arch : WeakMem.Arch) : SrcSem.SrcParams where
  arch := arch
  cap := 1
  init := SrcSem.mainInit 1

theorem ret0P_hooks (arch : WeakMem.Arch) : (ret0P arch).hooks = SrcSem.SrcHooks.none := rfl

theorem ret0P_init (arch : WeakMem.Arch) : (ret0P arch).init { SrcSem.mainStart with cap := (ret0P arch).cap } :=
  rfl

/-! ## No memory operation in the source (`hsafe`) -/

section NoMem

open A9NoSpawn TermRun

/-- **The operations the source safety concerns**, with `spawn`: a load, a
store, an exchange (of a cell or a buffer slot), a spawn. -/
def MemOp : Op → Prop
  | .load .. | .store .. | .xchg .. | .xchgAt .. | .spawn .. => True
  | _ => False

theorem cfgNoS_thread_mem {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {c c' : Cfg} {i : Nat}
    (hp : ProgNoS MemOp p) (hc : CfgNoS MemOp c) (h : c' ∈ threadSteps p k arch c i) :
    CfgNoS MemOp c' := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; cases h
  | some th =>
    rw [hth] at h
    simp only [List.mem_map] at h
    obtain ⟨⟨mem', pairs', th'⟩, hr, rfl⟩ := h
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact tstep_noS (g := gOf p k arch c i) hp (hc i th hth) hr
    · exact hc j th0 hj

theorem cfgNoS_prom_mem {c : Cfg} {i : Nat} {a : WeakMem.Address} {v : WeakMem.Val} {w : WeakMem.Ts}
    (hc : CfgNoS MemOp c) : CfgNoS MemOp (promise c i a v w) := by
  unfold promise
  cases hth : c.ths[i]? with
  | none => exact hc
  | some th =>
    intro j th0 hj
    rcases getElem?_set!_or hj with rfl | hj
    · exact hc i th hth
    · exact hc j th0 hj

/-- A configuration free of `MemOp` has no spawn step. -/
theorem no_spawnBy_mem {cap i : Nat} {c c' : Cfg} (hc : CfgNoS MemOp c) (h : SrcSem.SpawnBy cap i c c') :
    False := by
  obtain ⟨x, f, a, T, ts, e, th, -, -, hth, hterm, -⟩ := h
  have := (hc _ _ hth).1
  rw [hterm] at this
  exact this.1 trivial

/-- **Every reachable source configuration is free of `MemOp`**, for a
program whose code blocks are, from `main`'s start, without extern steps. -/
theorem reach_noMem {P : SrcSem.SrcParams} {p : Prog} (hp : ProgNoS MemOp p)
    (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : ∀ c, P.init c → CfgNoS MemOp c) {tr : List Ev}
    {s : Cfg} (h : (SrcSem.source P p).Reach tr s) : CfgNoS MemOp s := by
  obtain ⟨s0, h0, hr⟩ := h
  have H := hinit s0 h0
  clear h0
  induction hr with
  | refl => exact H
  | step hs _ ih =>
    obtain ⟨i, -, hs, -⟩ := hs
    apply ih
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hs, -⟩ | ⟨a, v, w, -, -, -, rfl⟩
      · exact cfgNoS_thread_mem hp H hs
      · exact cfgNoS_prom_mem H
    · exact (no_spawnBy_mem H hs).elim
    · rw [hP] at hs; exact hs.elim

theorem ret0Src_noMem : ProgNoS MemOp ret0Src := by
  intro d hd
  simp only [ret0Src, List.mem_singleton] at hd
  subst hd
  simp [ret0Body, NoS, MemOp]

theorem mainInit_noMem (cap : Nat) : ∀ c, SrcSem.mainInit cap c → CfgNoS MemOp c := by
  rintro c rfl j th hj
  simp only [SrcSem.mainStart] at hj
  have : j = 0 := by
    rcases j with _ | j
    · rfl
    · simp at hj
  subst this
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hj
  subst hj
  exact ⟨trivial, by simp⟩

end NoMem

end Spike.Lib.Ret0Src
