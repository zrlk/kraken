/-
# USem — the UnElab machine

UnElab's small-step machine over nested terms, defined **by running the core**: no case of `TermRun.tstep` is
copied.

* `focus v e`: the leftmost-innermost nested operation of `e` all of whose operands are atoms (as a core `Op`,
  via `setAts`), and `e` with that operation replaced by the atom `v` (the design's `focus` + `plug`; the one-hole
  context is implicit).  Operands are visited left to right, innermost first: the order of `elabArgs`.
* `layer k e`: the first core instruction of `elabT k e`, as a `ULayer`: a `let x = o` with its U continuation
  and counter (`letOp`: a nested operation, named `tmp k`, or a `let` whose operands are atoms); a head form with
  the sentinels `S0`/`S1` in its continuation slots, with the U continuations and their counter (`head`); `ret`;
  `tail`.
* `ustep`: a non-call `letOp` and every `head` are stepped by **`tstep` on the sentinel term** (`coreView`), and
  the result is mapped back (`backTh`; `pickU` chooses the U continuation the sentinel result names: `uDispatch`).
  `call`/`callc`/`tail` (`uEnter`/`uCallFrame`: the callee starts at its U body with counter 0, the frame saves the
  caller's counter) and `ret` (pops a `UFrame`, restoring its counter) are written against `U` (design (iii)).
* Configurations: `UCfg` is `Cfg` over `UTTh`; promise, extern and spawn moves are defined **through the core
  functions** (`promise`, `extCfg`, `spawnPar`, `spawnKid`) on the images, with the U term, counter and stack put
  back; the step relations `USolo` … `StepsU` have the core rules' shapes.
* `toCoreTh`/`toCoreCfg`: elaborate the term at the thread's counter and each frame body at the frame's counter;
  everything else is copied.  `UElabSim` proves the machine equal to the core's on these images (T2).
-/
import WeakCore.UTstep
import WeakCore.UnElab
import WeakCore.TermExtStep

set_option linter.unusedSimpArgs false

namespace UnElab
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep
open WeakMem (Memory Ts VState AllocLabel Address Val Arch)

/-! ## Focus -/

/-- An operand's atom (`()` for a nested operation: never used on one). -/
def atomOf : UArg → At
  | .at a => a
  | .op _ _ => .unit

mutual
/-- The first innermost operation of an operand whose operands are atoms, replaced by `v`. -/
def peelArg (v : At) : UArg → Option (Op × UArg)
  | .at _ => none
  | .op h args =>
      match peelArgs v args with
      | some r => some (r.1, .op h r.2)
      | none => some (setAts h (args.map atomOf), .at v)

/-- The same over operands, left to right. -/
def peelArgs (v : At) : List UArg → Option (Op × List UArg)
  | [] => none
  | a :: rest =>
      match peelArg v a with
      | some r => some (r.1, r.2 :: rest)
      | none => (peelArgs v rest).map fun r => (r.1, a :: r.2)
end

/-- **`focus`** (with `plug`): the leftmost-innermost nested operation whose operands are atoms, and the term with
it replaced by `v`.  `none` iff every operand of the head form is an atom. -/
def focus (v : At) : UExpr → Option (Op × UExpr)
  | .let_ x h args e => (peelArgs v args).map fun r => (r.1, .let_ x h r.2 e)
  | .split a p q e => (peelArg v a).map fun r => (r.1, .split r.2 p q e)
  | .unpack a i x e => (peelArg v a).map fun r => (r.1, .unpack r.2 i x e)
  | .unpackT a al x e => (peelArg v a).map fun r => (r.1, .unpackT r.2 al x e)
  | .region a rn pn tn e => (peelArg v a).map fun r => (r.1, .region r.2 rn pn tn e)
  | .openPub a rn pn cn e => (peelArg v a).map fun r => (r.1, .openPub r.2 rn pn cn e)
  | .case a x e₁ y e₂ => (peelArg v a).map fun r => (r.1, .case r.2 x e₁ y e₂)
  | .ifnull a e₁ x e₂ => (peelArg v a).map fun r => (r.1, .ifnull r.2 e₁ x e₂)
  | .parity a kn ev od => (peelArg v a).map fun r => (r.1, .parity r.2 kn ev od)
  | .ifeq a b yes no => (peelArgs v [a, b]).map fun r =>
      (r.1, .ifeq (r.2.getD 0 (.at .unit)) (r.2.getD 1 (.at .unit)) yes no)
  | .cas acq rel w e v' t ok fail => (peelArgs v [w, e, v']).map fun r =>
      (r.1, .cas acq rel (r.2.getD 0 (.at .unit)) (r.2.getD 1 (.at .unit)) (r.2.getD 2 (.at .unit)) t ok fail)
  | .casp acq rel w e0 e1 v0 v1 t ok fail => (peelArgs v [w, e0, e1, v0, v1]).map fun r =>
      (r.1, .casp acq rel (r.2.getD 0 (.at .unit)) (r.2.getD 1 (.at .unit)) (r.2.getD 2 (.at .unit))
        (r.2.getD 3 (.at .unit)) (r.2.getD 4 (.at .unit)) t ok fail)
  | .ret a => (peelArg v a).map fun r => (r.1, .ret r.2)
  | .tail f is a ts => (peelArg v a).map fun r => (r.1, .tail f is r.2 ts)

/-! ## Layers -/

/-- The rest of a pattern after one split bound its component to `b`. -/
def wrap (b : String) : UPat → UExpr → UExpr
  | .bind _, e => e
  | .pair p q, e => .split (.at (.var b)) p q e

/-- The first core instruction of an elaborated term. -/
inductive ULayer
  /-- `let x = o`, then the U term `e` at counter `j` -/
  | letOp (x : String) (o : Op) (j : Nat) (e : UExpr)
  /-- a head form `h` with sentinels `S0`/`S1` in its continuation slots, the U continuations at counter `j` -/
  | head (h : Expr) (conts : List UExpr) (j : Nat)
  | ret (a : At)
  | tail (f : String) (is : List String) (a : At) (ts : List Ty)

/-- The layer of a term whose head operands are atoms (`focus = none`). -/
def headLayer (k : Nat) : UExpr → ULayer
  | .let_ x h args e => .letOp (binder x k).1 (setAts h (args.map atomOf)) (binder x k).2 e
  | .split a p q e =>
      .head (.split (atomOf a) (patBinder p k).1 (patBinder q (patBinder p k).2).1 S0)
        [wrap (patBinder p k).1 p (wrap (patBinder q (patBinder p k).2).1 q e)] (patBinder q (patBinder p k).2).2
  | .unpack a i x e => .head (.unpack (atomOf a) i x S0) [e] k
  | .unpackT a al x e => .head (.unpackT (atomOf a) al x S0) [e] k
  | .region a rn pn tn e => .head (.region (atomOf a) rn pn tn S0) [e] k
  | .openPub a rn pn cn e => .head (.openPub (atomOf a) rn pn cn S0) [e] k
  | .case a x e₁ y e₂ => .head (.case (atomOf a) x S0 y S1) [e₁, e₂] k
  | .ifnull a e₁ x e₂ => .head (.ifnull (atomOf a) S0 x S1) [e₁, e₂] k
  | .parity a kn ev od => .head (.parity (atomOf a) kn S0 S1) [ev, od] k
  | .ifeq a b yes no => .head (.ifeq (atomOf a) (atomOf b) S0 S1) [yes, no] k
  | .cas acq rel w e v t ok fail => .head (.cas acq rel (atomOf w) (atomOf e) (atomOf v) t S0 S1) [ok, fail] k
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      .head (.casp acq rel (atomOf w) (atomOf e0) (atomOf e1) (atomOf v0) (atomOf v1) t S0 S1) [ok, fail] k
  | .ret a => .ret (atomOf a)
  | .tail f is a ts => .tail f is (atomOf a) ts

/-- **The layer of `e` at counter `k`**: a focused nested operation is bound to `tmp k`; otherwise the head. -/
def layer (k : Nat) (e : UExpr) : ULayer :=
  match focus (.var (tmp k)) e with
  | some r => .letOp (tmp k) r.1 (k + 1) r.2
  | none => headLayer k e

/-- The core continuation a sentinel result term names (`S1` → the second, anything else → the first). -/
def pickE (es : List Expr) : Expr → Expr
  | .ret (.var s) => if s = "#1" then es.getD 1 (.ret .unit) else es.getD 0 (.ret .unit)
  | _ => es.getD 0 (.ret .unit)

/-- The U continuation a sentinel result term names (`uDispatch`). -/
def pickU (es : List UExpr) : Expr → UExpr
  | .ret (.var s) => if s = "#1" then es.getD 1 (.ret (.at .unit)) else es.getD 0 (.ret (.at .unit))
  | _ => es.getD 0 (.ret (.at .unit))

/-- The core term a layer stands for. -/
def ULayer.core : ULayer → Expr
  | .letOp x o j e => .let_ x o (elabT j e)
  | .head h conts j => mapHead (pickE (conts.map (elabT j))) h
  | .ret a => .ret a
  | .tail f is a ts => .tail f is a ts

/-! ## Threads -/

structure UFrame where
  x    : String
  body : UExpr
  env  : Env
  σs   : List Ty
  ty   : Ty
  /-- the caller's counter, restored by `ret` -/
  ctr  : Nat

structure UTTh where
  term     : UExpr
  env      : Env
  σs       : List Ty := []
  stack    : List UFrame := []
  vs       : VState := WeakMem.VState.init
  promises : List Ts := []
  nalloc   : Nat := 0
  undefs   : Nat := 0
  tidLbl   : Option AllocLabel := none
  /-- (D4) the park permit (the core's `TTh.permit`); copied by `toCoreTh`/`backTh` -/
  permit   : Option Ts := none
  /-- the block's temporary counter: the next anonymous binder is `tmp ctr` -/
  ctr      : Nat := 0

def toCoreFr (f : UFrame) : Frame := ⟨f.x, elabT f.ctr f.body, f.env, f.σs, f.ty⟩

/-- **The core image of a thread**: the term elaborated at the thread's counter, each frame body at its own. -/
def toCoreTh (th : UTTh) : TTh :=
  { term := elabT th.ctr th.term, env := th.env, σs := th.σs, stack := th.stack.map toCoreFr, vs := th.vs,
    promises := th.promises, nalloc := th.nalloc, undefs := th.undefs, tidLbl := th.tidLbl,
    permit := th.permit }

/-- The core thread `tstep` is run on: `th`'s core fields, term `t`, no stack. -/
def coreView (th : UTTh) (t : Expr) : TTh :=
  { term := t, env := th.env, σs := th.σs, stack := [], vs := th.vs, promises := th.promises,
    nalloc := th.nalloc, undefs := th.undefs, tidLbl := th.tidLbl,
    permit := th.permit }

/-- A core result read back: its core fields, the U term `e` at counter `j`, `th`'s stack. -/
def backTh (th : UTTh) (t : TTh) (e : UExpr) (j : Nat) : UTTh :=
  { term := e, env := t.env, σs := t.σs, stack := th.stack, vs := t.vs, promises := t.promises,
    nalloc := t.nalloc, undefs := t.undefs, tidLbl := t.tidLbl, permit := t.permit, ctr := j }

def uIsDone (th : UTTh) : Bool :=
  match th.term, th.stack with
  | .ret (.at _), [] => true
  | _, _ => false

/-- Enter U block `f` (design (iii), against `U`): its U body, counter 0. -/
def uEnter (U : UProg) (th : UTTh) (f : String) (ts : List Ty) (a : At) : Option UTTh := do
  let d ← U.find? (·.name == f)
  let (_, ws) ← evalAt th.env a
  let σs' := (ts.map (close th.σs)).reverse
  pure { th with term := d.body, env := [(d.arg, close σs' d.argTy, ws)], σs := σs', ctr := 0 }

/-- The frame a call to `f` pushes, returning into `x` and the U term `e` at counter `j`. -/
def uCallFrame (U : UProg) (th : UTTh) (f : String) (ts : List Ty) (x : String) (e : UExpr) (j : Nat) :
    Option UFrame := do
  let d ← U.find? (·.name == f)
  pure ⟨x, e, th.env, th.σs, close (ts.map (close th.σs)).reverse d.retTy, j⟩

/-- **One step of one UnElab thread**: every outcome.  Non-call operations and head forms run the core
`tstep` on the sentinel term; calls, `tail` and `ret` are written against `U`. -/
def ustep (U : UProg) (g : G) (mem : Memory) (pairs : List Ts) (th : UTTh) :
    List (Memory × List Ts × UTTh) :=
  match layer th.ctr th.term with
  | .letOp x (.call f _ a ts) j e =>
      ol (((uCallFrame U th f ts x e j).bind fun fr =>
          uEnter U { th with stack := fr :: th.stack } f ts a).map fun th' => (mem, pairs, th'))
  | .letOp x (.callc f a) j e =>
      match evalAt th.env f with
      | some (tf, [w]) =>
          match w.val with
          | .num i =>
              match U[i]? with
              | some d =>
                  ol (((uCallFrame U th d.name [] x e j).bind fun fr =>
                      uEnter U { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a).map
                    fun th' => (mem, pairs, th'))
              | none => []
          | _ => []
      | _ => []
  | .letOp x o j e =>
      (tstep g mem pairs (coreView th (.let_ x o S0))).map fun r => (r.1, r.2.1, backTh th r.2.2 e j)
  | .head h conts j =>
      (tstep g mem pairs (coreView th h)).map fun r =>
        (r.1, r.2.1, backTh th r.2.2 (pickU conts r.2.2.term) j)
  | .ret a =>
      match th.stack, evalAt th.env a with
      | f :: rest, some (_, ws) =>
          [(mem, pairs, { th with term := f.body, env := (f.x, f.ty, ws) :: f.env, σs := f.σs, stack := rest,
                                  ctr := f.ctr })]
      | _, _ => []
  | .tail f _ a ts => ol ((uEnter U th f ts a).map fun th' => (mem, pairs, th'))

/-! ## Configurations -/

structure UCfg where
  mem      : Memory
  pairs    : List Ts := []
  ths      : Array UTTh
  lbase    : Nat := 0
  boxFence : Bool := true
  cap      : Nat := 0
  trace    : List Event := []

/-- **The core image of a configuration**: every thread's image; memory, pairs, `lbase`, `boxFence`, `cap` and the
trace are copied. -/
def toCoreCfg (c : UCfg) : Cfg :=
  { mem := c.mem, pairs := c.pairs, ths := c.ths.map toCoreTh, lbase := c.lbase, boxFence := c.boxFence,
    cap := c.cap, trace := c.trace }

/-- The step's surroundings: the core's, for the elaborated program (`pS := elabProg U`). -/
def gU (U : UProg) (k : Promises.Knobs) (arch : Arch) (c : UCfg) (i : Nat) : G :=
  gOf (elabProg U) k arch (toCoreCfg c) i

def uThreadSteps (U : UProg) (k : Promises.Knobs) (arch : Arch) (c : UCfg) (i : Nat) : List UCfg :=
  match c.ths[i]? with
  | none => []
  | some th =>
      (ustep U (gU U k arch c i) c.mem c.pairs th).map fun r =>
        { c with mem := r.1, pairs := r.2.1, ths := c.ths.set! i r.2.2 }

/-- A promise of thread `i`, through the core's `promise` on the image. -/
def uPromise (c : UCfg) (i : Nat) (a : Address) (v : Val) (w : Ts) : UCfg :=
  match c.ths[i]? with
  | none => c
  | some th =>
      let d := promise (toCoreCfg c) i a v w
      { c with mem := d.mem,
               ths := c.ths.set! i { th with promises := ((d.ths[i]?).map (·.promises)).getD th.promises } }

/-- The extern move of thread `i` (at `let x = ext n a`, then the U term `e` at counter `j`), through the core's
`extCfg` on the image with a sentinel continuation. -/
def uExtCfg (c : UCfg) (i : Nat) (th : UTTh) (x : String) (n : ExtName) (e : UExpr) (j : Nat) (ws rs : List Word) :
    UCfg :=
  let d := extCfg (toCoreCfg c) i (toCoreTh th) x n S0 ws rs
  { c with ths := c.ths.set! i (backTh th ((d.ths[i]?).getD (toCoreTh th)) e j), trace := d.trace }

/-- (D4) U thread `j` gets a permit carrying `v`, joined with any permit it holds (no such thread: unchanged):
`setPermit` on the U side. -/
def uSetPermit (c : UCfg) (j : Nat) (v : Ts) : UCfg :=
  match c.ths[j]? with
  | some th => { c with ths := c.ths.set! j { th with permit := some (max (th.permit.getD 0) v) } }
  | none => c

/-- (D4) `wake` on the U side: `unpark t` by thread `i` with release view `v` gives the thread `t` names (read on the
core image) a permit carrying `v`, or view 0 if it is `i` itself (program order already orders its own accesses). -/
def uWake (c : UCfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) : UCfg :=
  match n, ws with
  | .unpark, [t] => match thrOfTid (toCoreCfg c) t with | some j => uSetPermit c j (if j = i then 0 else v) | none => c
  | _, _ => c

theorem setPermit_elab (c : UCfg) (j : Nat) (v : Ts) :
    toCoreCfg (uSetPermit c j v) = setPermit (toCoreCfg c) j v := by
  unfold uSetPermit setPermit
  rw [show (toCoreCfg c).ths[j]? = (c.ths[j]?).map toCoreTh by simp [toCoreCfg]]
  cases c.ths[j]? with
  | none => rfl
  | some th =>
    simp only [Option.map_some, toCoreCfg, Array.set!, Array.map_setIfInBounds]
    rfl

/-- (D4) `uWake` changes at most one thread, and only its permit. -/
theorem uWake_get (c : UCfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) (j : Nat) :
    (uWake c i v n ws).ths[j]? = c.ths[j]? ∨
      ∃ th u, c.ths[j]? = some th ∧ (uWake c i v n ws).ths[j]? = some { th with permit := some u } := by
  unfold uWake
  split
  · split
    · rename_i k _
      unfold uSetPermit
      cases h : c.ths[k]? with
      | none => exact Or.inl rfl
      | some th =>
        dsimp only
        simp only [Array.set!, Array.getElem?_setIfInBounds]
        by_cases hkj : k = j
        · subst hkj
          have hk : k < c.ths.size := (Array.getElem?_eq_some_iff.mp h).1
          exact Or.inr ⟨th, max (th.permit.getD 0) (if k = i then 0 else v), h, by simp [hk]⟩
        · exact Or.inl (by simp [hkj])
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem uWake_size (c : UCfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) :
    (uWake c i v n ws).ths.size = c.ths.size := by
  unfold uWake
  split
  · split
    · unfold uSetPermit; split <;> simp [Array.set!]
    · rfl
  · rfl

/-- (D4) `uWake` is `wake` on the core image. -/
theorem wake_elab (c : UCfg) (i : Nat) (v : Ts) (n : ExtName) (ws : List Word) :
    toCoreCfg (uWake c i v n ws) = wake (toCoreCfg c) i v n ws := by
  cases n <;> try rfl
  rcases ws with _ | ⟨t, _ | ⟨_, _⟩⟩ <;> try rfl
  simp only [uWake, wake]
  cases thrOfTid (toCoreCfg c) t with
  | none => rfl
  | some j => exact setPermit_elab c j _

def uExtSteps (c : UCfg) (i : Nat) : List UCfg :=
  match c.ths[i]? with
  | some th =>
      match layer th.ctr th.term with
      | .letOp x (.ext n a) j e =>
          if ExtNeedsNoProm n (toCoreTh th) then [] else
          match evalAt th.env a with
          | some (_, ws) => (n.resultsL i ws c.trace).map (uExtCfg c i th x n e j ws ·)
          | none => []
      | _ => []
  | none => []

/-- A core thread with no stack read back at the U term `e`, counter 0 (a spawned child). -/
def fromCore0 (t : TTh) (e : UExpr) : UTTh :=
  { term := e, env := t.env, σs := t.σs, stack := [], vs := t.vs, promises := t.promises,
    nalloc := t.nalloc, undefs := t.undefs, tidLbl := t.tidLbl, permit := t.permit, ctr := 0 }

/-- The spawn move of thread `i`, through the core's `spawnPar`/`spawnKid` on the image. -/
def uSpawnCfg (c : UCfg) (i : Nat) (th : UTTh) (x : String) (e : UExpr) (j : Nat) (f : String) (ts : List Ty)
    (T : Ty) (ws : List Word) : UCfg :=
  let par := backTh th (spawnPar (toCoreCfg c) i (toCoreTh th) x S0) e j
  let kid := fromCore0 (spawnKid (toCoreCfg c) i (toCoreTh th) f ts T ws) (.tail f [] (.at (.var "a")) ts)
  { c with ths := (c.ths.set! i par).push kid }

def uNoPromises (c : UCfg) (i : Nat) : Bool := (c.ths[i]?.map (·.promises.isEmpty)).getD true

/-- Steps of thread `i` alone, promises included (`Solo`'s rules). -/
inductive USolo (U : UProg) (k : Promises.Knobs) (arch : Arch) (i : Nat) : UCfg → UCfg → Prop
  | refl (c) : USolo U k arch i c c
  | thread {c c' c''} : c' ∈ uThreadSteps U k arch c i → USolo U k arch i c' c'' → USolo U k arch i c c''
  | prom {c c''} (a v w) : w < c.mem.size → USolo U k arch i (uPromise c i a v w) c'' → USolo U k arch i c c''
  | ext {c c' c''} : c' ∈ uExtSteps c i → USolo U k arch i c' c'' → USolo U k arch i c c''

def UCertified (U : UProg) (k : Promises.Knobs) (arch : Arch) (c : UCfg) (i : Nat) : Prop :=
  ∃ c', USolo U k arch i c c' ∧ uNoPromises c' i = true

/-- The machine step (`Step`'s rules). -/
inductive UStep (U : UProg) (k : Promises.Knobs) (arch : Arch) : UCfg → UCfg → Prop
  | thread {c c'} (i) : c' ∈ uThreadSteps U k arch c i → UCertified U k arch c' i → UStep U k arch c c'
  | prom {c} (i a v w) : i < c.ths.size → w < c.mem.size → UCertified U k arch (uPromise c i a v w) i →
      UStep U k arch c (uPromise c i a v w)

/-- The spawn step (`Spawn`'s rule), at a spawn layer. -/
inductive USpawn (U : UProg) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : UCfg → UCfg → Prop
  | mk {c : UCfg} (i : Nat) (x f : String) (a : At) (T : Ty) (ts : List Ty) (j : Nat) (e : UExpr) (th : UTTh)
      (rt : Ty) (ws : List Word) :
      c.ths[i]? = some th → layer th.ctr th.term = .letOp x (.spawn f a T ts) j e → th.promises = [] →
      c.ths.size < cap → evalAt th.env a = some (rt, ws) →
      USpawn U k arch cap c (uSpawnCfg c i th x e j f ts T ws)

/-- The extern step (`Ext`'s rule), at an extern layer. -/
inductive UExt (U : UProg) (k : Promises.Knobs) (arch : Arch) : UCfg → UCfg → Prop
  | mk {c : UCfg} (i : Nat) (x : String) (n : ExtName) (a : At) (j : Nat) (e : UExpr) (th : UTTh) (rt : Ty)
      (ws rs : List Word) :
      c.ths[i]? = some th → layer th.ctr th.term = .letOp x (.ext n a) j e →
      (ExtNeedsNoProm n (toCoreTh th) → th.promises = []) → evalAt th.env a = some (rt, ws) →
      n.Admits i ws c.trace rs →
      UCertified U k arch (uExtCfg c i th x n e j ws rs) i → UExt U k arch c (uWake (uExtCfg c i th x n e j ws rs) i (relView th.vs) n ws)

/-- Runs of machine steps and steps of an extra relation (`StepsG`'s rules). -/
inductive StepsGU (U : UProg) (k : Promises.Knobs) (arch : Arch) (Sp : UCfg → UCfg → Prop) : UCfg → UCfg → Prop
  | refl (c : UCfg) : StepsGU U k arch Sp c c
  | step {c c' c'' : UCfg} : (UStep U k arch c c' ∨ Sp c c') → StepsGU U k arch Sp c' c'' →
      StepsGU U k arch Sp c c''

/-- Runs of machine steps, spawns and extern steps (`StepsE`'s shape). -/
abbrev StepsU (U : UProg) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : UCfg → UCfg → Prop :=
  StepsGU U k arch (fun c c' => USpawn U k arch cap c c' ∨ UExt U k arch c c')

end UnElab

#print axioms UnElab.ustep
#print axioms UnElab.uThreadSteps
#print axioms UnElab.uExtCfg
#print axioms UnElab.uSpawnCfg
