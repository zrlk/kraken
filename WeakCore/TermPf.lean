import WeakCore.TermStep

/-!
# TermPf: the ghost frontier labels `G.pf` are inert

`G.pf` (EFoot tags, PfrTag) is a proof-only ghost: `TermStep.EFoot` reads it through `PfrG`, and
nothing in the machine does.  Every function of `TermRun` that takes a `G` computes the same result
at `{ g with pf := P }` as at `g`, whatever `P` is; `gOf` sets it to `fun _ => True`.  The thread
invariant's memory side, the box fence, `PAx` and `ThInvM` do not read it either, so a hypothesis
stated at `g` serves at `{ g with pf := P }`.
-/

namespace TermPf
open CoreLang CoreTerm TermRun
open WeakMem (Memory Ts AllocLabel)

theorem gOf_pf (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (c : Cfg) (i : Nat) :
    (gOf p k arch c i).pf = fun _ => True := rfl

theorem tstep_pf (g : G) (P : AllocLabel → Prop) (mem : Memory) (pairs : List Ts) (th : TTh) :
    tstep { g with pf := P } mem pairs th = tstep g mem pairs th := rfl

theorem evalOp_pf (g : G) (P : AllocLabel → Prop) (env : Env) (σs : List Ty) (s : St) (o : Op) :
    evalOp { g with pf := P } env σs s o = evalOp g env σs s o := rfl

theorem injM_pf (g : G) (P : AllocLabel → Prop) (s : St) (t : Ty) (j : Nat) (q : List Word) :
    injM { g with pf := P } s t j q = injM g s t j q := rfl

theorem projM_pf (g : G) (P : AllocLabel → Prop) (s : St) (t : Ty) (ws : List Word) :
    projM { g with pf := P } s t ws = projM g s t ws := rfl

theorem enter_pf (g : G) (P : AllocLabel → Prop) (th : TTh) (f : String) (ts : List Ty) (a : At) :
    enter { g with pf := P } th f ts a = enter g th f ts a := rfl

theorem callFrame_pf (g : G) (P : AllocLabel → Prop) (th : TTh) (f : String) (ts : List Ty) (x : String)
    (e : Expr) : callFrame { g with pf := P } th f ts x e = callFrame g th f ts x e := rfl

/-- `threadSteps` (hence `Solo`, `Certified`) is the same with any ghost frontier labels on its `gOf`. -/
theorem threadSteps_pf (p : Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) (c : Cfg) (i : Nat)
    (P : AllocLabel → Prop) :
    threadSteps p k arch c i = match c.ths[i]? with
      | none => []
      | some th => (tstep { gOf p k arch c i with pf := P } c.mem c.pairs th).map fun (mem, pairs, th') =>
          { c with mem := mem, pairs := pairs, ths := c.ths.set! i th' } := rfl

theorem MemInv_pf (g : G) (P : AllocLabel → Prop) (E : TermSound.TEnv) (s : St) :
    TermStep.MemInv { g with pf := P } E s ↔ TermStep.MemInv g E s := Iff.rfl

theorem boxFence_pf (g : G) (P : AllocLabel → Prop) : ({ g with pf := P } : G).boxFence = g.boxFence := rfl

theorem PAx_pf (g : G) (P : AllocLabel → Prop) (mem : Memory) (pairs : List Ts) (th : TTh) :
    TermStep.PAx { g with pf := P } mem pairs th ↔ TermStep.PAx g mem pairs th := Iff.rfl

theorem ThInvM_pf (p : Prog) (g : G) (P : AllocLabel → Prop) (mem : Memory) (pairs : List Ts) (th : TTh) :
    TermStep.ThInvM p { g with pf := P } mem pairs th ↔ TermStep.ThInvM p g mem pairs th := Iff.rfl

end TermPf

#print axioms TermPf.gOf_pf
#print axioms TermPf.tstep_pf
#print axioms TermPf.evalOp_pf
#print axioms TermPf.injM_pf
#print axioms TermPf.projM_pf
#print axioms TermPf.enter_pf
#print axioms TermPf.callFrame_pf
#print axioms TermPf.threadSteps_pf
#print axioms TermPf.MemInv_pf
#print axioms TermPf.boxFence_pf
#print axioms TermPf.PAx_pf
#print axioms TermPf.ThInvM_pf
#print axioms TermStep.PfrG_of
#print axioms TermStep.PfrG_refl
#print axioms TermStep.EFoot.pfrG
#print axioms TermStep.RiniArr_of
#print axioms TermStep.RiniArr_refl
#print axioms TermStep.EFoot.riniArr
#print axioms TermStep.ArrAt_of_buf
