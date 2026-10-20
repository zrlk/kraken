import WeakCore.TermStep

/-!
# TermZf: the ghost label set `G.zf` is inert

`G.zf` (iniop) is a proof-only ghost: `TermStep.EFoot` reads it through `IniFixZ`, and nothing
in the machine does.  Every function of `TermRun` that takes a `G` computes the same result at
`{ g with zf := Z }` as at `g`, whatever `Z` is.  The run-level relations (`threadSteps`, `promise`,
`Solo`, `Certified`) take no `G` at all: they build theirs with `gOf`, which has no ghost labels.
-/

namespace TermZf
open CoreLang CoreTerm TermRun
open WeakMem (Memory Ts AllocLabel)

theorem gOf_zf (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (c : Cfg) (i : Nat) :
    (gOf p k arch c i).zf = fun _ => False := rfl

theorem tstep_zf (g : G) (Z : AllocLabel → Prop) (mem : Memory) (pairs : List Ts) (th : TTh) :
    tstep { g with zf := Z } mem pairs th = tstep g mem pairs th := rfl

theorem evalOp_zf (g : G) (Z : AllocLabel → Prop) (env : Env) (σs : List Ty) (s : St) (o : Op) :
    evalOp { g with zf := Z } env σs s o = evalOp g env σs s o := rfl

theorem injM_zf (g : G) (Z : AllocLabel → Prop) (s : St) (t : Ty) (j : Nat) (q : List Word) :
    injM { g with zf := Z } s t j q = injM g s t j q := rfl

theorem projM_zf (g : G) (Z : AllocLabel → Prop) (s : St) (t : Ty) (ws : List Word) :
    projM { g with zf := Z } s t ws = projM g s t ws := rfl

theorem enter_zf (g : G) (Z : AllocLabel → Prop) (th : TTh) (f : String) (ts : List Ty) (a : At) :
    enter { g with zf := Z } th f ts a = enter g th f ts a := rfl

theorem callFrame_zf (g : G) (Z : AllocLabel → Prop) (th : TTh) (f : String) (ts : List Ty) (x : String)
    (e : Expr) : callFrame { g with zf := Z } th f ts x e = callFrame g th f ts x e := rfl

/-- `threadSteps` (hence `Solo`, `Certified`) is the same with any ghost labels on its `gOf`. -/
theorem threadSteps_zf (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (c : Cfg) (i : Nat)
    (Z : AllocLabel → Prop) :
    threadSteps p k arch c i = match c.ths[i]? with
      | none => []
      | some th => (tstep { gOf p k arch c i with zf := Z } c.mem c.pairs th).map fun (mem, pairs, th') =>
          { c with mem := mem, pairs := pairs, ths := c.ths.set! i th' } := rfl

/-- The thread invariant's memory side, the box fence and `PAx` do not read the ghost labels, so a
hypothesis stated at `g` serves at `{ g with zf := Z }` (the inertness point). -/
theorem MemInv_zf (g : G) (Z : AllocLabel → Prop) (E : TermSound.TEnv) (s : St) :
    TermStep.MemInv { g with zf := Z } E s ↔ TermStep.MemInv g E s := Iff.rfl

theorem boxFence_zf (g : G) (Z : AllocLabel → Prop) : ({ g with zf := Z } : G).boxFence = g.boxFence := rfl

theorem PAx_zf (g : G) (Z : AllocLabel → Prop) (mem : Memory) (pairs : List Ts) (th : TTh) :
    TermStep.PAx { g with zf := Z } mem pairs th ↔ TermStep.PAx g mem pairs th := Iff.rfl

end TermZf

#print axioms TermZf.gOf_zf
#print axioms TermZf.tstep_zf
#print axioms TermZf.evalOp_zf
#print axioms TermZf.injM_zf
#print axioms TermZf.projM_zf
#print axioms TermZf.enter_zf
#print axioms TermZf.callFrame_zf
#print axioms TermZf.threadSteps_zf
#print axioms TermZf.MemInv_zf
#print axioms TermZf.boxFence_zf
#print axioms TermZf.PAx_zf
#print axioms TermStep.IniFixZ_of
#print axioms TermStep.EFoot.iniFixZ
