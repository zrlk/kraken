/-
# Robust — crash-robustness of protocols, and the local-token discipline

A protocol (`CoreLang.Proto`) is a state graph: which values a word may hold,
which moves are legal, and who may make them.  Checking it can establish
*safety* (no legal sequence of moves reaches a bad state) and *non-stuckness*
(from every reachable state some participant has a legal move).  This file
asks the second question in the presence of a participant that stops: a
handler that crashes, a thread that is killed, a client that walks away.

**Held states block.**  A state that does not hold the region is *held*: only
the thread with its token may leave it.  If that thread dies, nobody may, and
every other participant waits for ever.  So a protocol with no held state is
*crash-free* (`Robustness.free`); one whose held states exist but are all
straight-line *windows* — code between a `cas` in and a `store` out, with no
call in between, which is what a crash-recovery argument can be scoped to —
is *windowed* (`.windowed`); any other is *blocking*.

**Repeating values fool `cas`.**  (The graph analysis itself lives in
`CoreTerm`, before `pwf`, so that a protocol may *claim* `robust` or
`norepeat` and be refused by the checker if the claim is false.)  Separately, a `cas` out of a shared state
succeeds whenever the word's value is the one it expects, even if the word
has moved on and come back (ABA).  `noRepeat P` says no shared state can be
re-entered at a value it had.  It is weaker than `monotone` (§4.4 rule 6),
which forbids re-entering *any* state: a lock `0 → 1 → 0` repeats; a seqlock
`2k → 2k+1 → 2k+2` does not.

**Livelock is beyond this.**  An adversary that keeps making *legal* moves
(taking and giving back a shared state for ever) can starve an honest
participant without any state being stuck; every state of the graph is fine.
Ruling that out needs an assumption on the scheduler or the adversary
(fairness), not on the protocol, and is not attempted here.

## The local-token discipline

A protocol declared `local` (`Proto.isLocal`, written `; local` in the
protocol syntax) opts in to the window rule, which a second pass over an
accepted block enforces (`localDecl`):

1. a local token in a taken state is never passed to, or returned from, a
   block (`checkDeclL` refuses the signature);
2. while a variable holds one, the block makes no `call`/`callc` and does not
   `tail` (the window is straight-line; branches are fine);
3. a local token is consumed only by a `store` on its own word, or
   restructured within the block (renamed, paired, injected, split, borrowed);
   it is never stored into memory, packed, or passed;
4. at `ret` none is held.

The pass is separate from `CoreTerm.check`, so the proven checker
(`CoreTyping.checkDecl_sound`) is untouched, and a program without a local
protocol passes it trivially: nothing changes for anyone who does not opt in.
`Scope.branches` supplies the checker's context at each point.

Build: LEAN_PATH=build lean -o build/Robust.olean Robust.lean
(after Scope.olean)
-/
import WeakCore.Scope
open CoreLang CoreTerm

namespace Robust

/-! ## §1. Classifying a protocol -/

inductive Robustness
  | free | windowed | blocking
  deriving DecidableEq, Repr

/-- What a participant that stops in a held state does to everyone else. -/
def robustness (P : Proto) : Robustness :=
  if (heldStates P).isEmpty then .free
  else if P.isLocal then .windowed
  else .blocking

def Robustness.text : Robustness → String
  | .free => "crash-free (no held state: nobody's death leaves the word stuck)"
  | .windowed => "windowed (held states are straight-line windows of one block: local)"
  | .blocking => "blocking (a participant that dies in a held state leaves the word stuck)"

/-- The one-line report a document prints. -/
def report (P : Proto) : String :=
  (robustness P).text ++ "; " ++
  (if noRepeat P then "no shared state repeats a value (a cas out of it is never fooled)"
   else "a shared state can repeat a value (ABA: a cas out of it may be fooled)")

-- The library protocols.  The mutex blocks and repeats (`0 → 1 → 0`); the
-- seqlock blocks (a writer that dies mid-write spins every reader for ever)
-- but never repeats; the claim is terminal, so it blocks nobody.
#guard robustness mutexP == .blocking && !noRepeat mutexP
#guard robustness seqP == .blocking && noRepeat seqP
#guard robustness claimP == .blocking && noRepeat claimP
-- A seqlock whose writer steps back repeats.
#guard !noRepeat badSeqP
-- The identity lock (the locking-scheme example's `Ident`): `busy(k)` is held and blocking;
-- `0 → busy → 0` is a wild cycle, so `0` repeats, and `armed(k) → busy(k) →
-- armed(k)` is a cycle of net change 0, so `armed` repeats too.
#guard robustness identP == .blocking && repeats identP 0 && repeats identP 1
#guard robustness { identP with isLocal := true } == .windowed
-- A counter that only goes up is free and never repeats, and may claim both.
def upP : Proto := { clauses := [⟨1, 0, true⟩], trans := [(0, 0, 1)] }
#guard pwf upP && robustness upP == .free && noRepeat upP
#guard pwf { upP with robust := true, norepeat := true }
-- ... and one that goes both ways repeats.
#guard !noRepeat { upP with trans := [(0, 0, 1), (0, 0, -1)] }
-- `cycleΔ` finds the lowest cycle, not the first: `0 → 1 → 0` nets +1 but
-- `0 → 2 → 0` nets 0.
def twoCyc : Proto := { clauses := [⟨3, 0, true⟩, ⟨3, 1, false⟩, ⟨3, 2, false⟩],
                        trans := [(0, 1, 0), (1, 0, 1), (0, 2, 0), (2, 0, 0)] }
#guard cycleΔ twoCyc 0 == some (some 0) && repeats twoCyc 0

/-! ## §2. The local-token discipline -/

/-- Does the type contain a token of a local protocol in a taken state? -/
def hasLocalTok (t : Ty) : Bool :=
  (takenOf 0 t).any fun (P, i) => P.isLocal && i.isSome

/-- The variables of `cx` holding one: live, or lent out. -/
def localHolders (cx : Cx) : List String :=
  cx.vars.filterMap fun (y, t, b) =>
    if (b || cx.lent.contains y) && hasLocalTok t then some y else none

/-- The immediate subterms, in `Scope.branches`'s order. -/
def subs : Expr → List Expr
  | .let_ _ _ b | .split _ _ _ b | .unpack _ _ _ b | .unpackT _ _ _ b | .region _ _ _ _ b
  | .openPub _ _ _ _ b => [b]
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂
  | .cas _ _ _ _ _ _ e₁ e₂ | .casp _ _ _ _ _ _ _ _ e₁ e₂ => [e₁, e₂]
  | .ret _ | .tail _ _ _ _ => []

/-- Is the op a call (the window must be straight-line)? -/
def isCallOp : Op → Bool
  | .call .. | .callc .. => true
  | _ => false

/-- Rule 3's test of the tokens a `let` gives up: only a store on the token's
own word consumes it, and a constructor may only repackage it into `x`. -/
def goneOK (cx c' : Cx) (x : String) (op : Op) : Bool :=
  let held' := localHolders c'
  match (localHolders cx).filter (fun y => !held'.contains y) with
  | [] => true
  | gone =>
      match op with
      | .store _ _ _ (some (.var z)) => gone == [z]
      | .atom _ | .pair .. | .inl .. | .inr .. => held'.contains x
      | _ => false

/-- Run `a`, then `b` if `a` succeeded. -/
def seqM (a b : M Unit) : M Unit :=
  match a with
  | .ok _ => b
  | .error e => .error e

/-- Walk a branch whose context the checker computed; a branch the checker
refused (`none`) has nothing to add. -/
def onBr (o : Option (Option Cx)) (f : Cx → M Unit) : M Unit :=
  match o with
  | some (some c) => f c
  | _ => pure ()

/-- Rules 2–4 along one block.  Where the checker's context is unknown the
checker itself has refused the block, so there is nothing to add.  Structural:
one arm per constructor, each recursing on a subterm named by the pattern, so
the definition is total and its equations are available to proofs
(`TermLocal.walkT_sound`). -/
def walk (p : Prog) (bn : String) : Cx → Expr → M Unit
  | cx, .let_ x op b =>
      if isCallOp op && !(localHolders cx).isEmpty then
        throw s!"{bn}: a call while {(localHolders cx).headD ""} holds a local token (the window must be straight-line)"
      else
        match Scope.branches p cx (.let_ x op b) with
        | [some c] =>
            if goneOK cx c x op then walk p bn c b
            else throw s!"{bn}: {((localHolders cx).filter (fun y => !(localHolders c).contains y)).headD ""} holds a local token, which may not leave its block (only a store on its own word consumes it)"
        | _ => pure ()
  | cx, .ret _ =>
      if (localHolders cx).isEmpty then pure ()
      else throw s!"{bn}: {(localHolders cx).headD ""} still holds a local token at the block's end"
  | cx, .tail .. =>
      if (localHolders cx).isEmpty then pure ()
      else throw s!"{bn}: a tail call while {(localHolders cx).headD ""} holds a local token (the window must be straight-line)"
  -- Binders restructure a value within the block: rule 3 allows them.
  | cx, .split a x y b => onBr (Scope.branches p cx (.split a x y b))[0]? (walk p bn · b)
  | cx, .unpack a i x b => onBr (Scope.branches p cx (.unpack a i x b))[0]? (walk p bn · b)
  | cx, .unpackT a α x b => onBr (Scope.branches p cx (.unpackT a α x b))[0]? (walk p bn · b)
  | cx, .region a r q t b => onBr (Scope.branches p cx (.region a r q t b))[0]? (walk p bn · b)
  | cx, .openPub a r q c b => onBr (Scope.branches p cx (.openPub a r q c b))[0]? (walk p bn · b)
  | cx, .case a x e₁ y e₂ =>
      seqM (onBr (Scope.branches p cx (.case a x e₁ y e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.case a x e₁ y e₂))[1]? (walk p bn · e₂))
  | cx, .ifnull a e₁ y e₂ =>
      seqM (onBr (Scope.branches p cx (.ifnull a e₁ y e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.ifnull a e₁ y e₂))[1]? (walk p bn · e₂))
  | cx, .parity a k e₁ e₂ =>
      seqM (onBr (Scope.branches p cx (.parity a k e₁ e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.parity a k e₁ e₂))[1]? (walk p bn · e₂))
  | cx, .ifeq a b e₁ e₂ =>
      seqM (onBr (Scope.branches p cx (.ifeq a b e₁ e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.ifeq a b e₁ e₂))[1]? (walk p bn · e₂))
  | cx, .cas acq rel w e v t e₁ e₂ =>
      seqM (onBr (Scope.branches p cx (.cas acq rel w e v t e₁ e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.cas acq rel w e v t e₁ e₂))[1]? (walk p bn · e₂))
  | cx, .casp acq rel w e0 e1 v0 v1 t e₁ e₂ =>
      seqM (onBr (Scope.branches p cx (.casp acq rel w e0 e1 v0 v1 t e₁ e₂))[0]? (walk p bn · e₁))
        (onBr (Scope.branches p cx (.casp acq rel w e0 e1 v0 v1 t e₁ e₂))[1]? (walk p bn · e₂))

/-- Rules 1–4 for one block. -/
def localDecl (p : Prog) (d : Decl) : M Unit := do
  if hasLocalTok d.argTy then throw s!"{d.name}: a local token cannot be passed to a block"
  if hasLocalTok d.retTy then throw s!"{d.name}: a local token cannot be returned from a block"
  walk p d.name (Scope.start d) d.body

/-- The checker, then the local-token discipline. -/
def checkDeclL (p : Prog) (d : Decl) : M Unit := do
  checkDecl p d
  localDecl p d

def checkProgL (p : Prog) : M Unit := p.forM (checkDeclL p)

/-! ### Relabelling a protocol

To ask "would these blocks pass if `P` were declared local?" without
restating them, map the protocol through every type a program mentions:
in signatures, in `mkWord`, in the type arguments of calls, injections,
packs and `zero`.  Nothing else in a program names a protocol. -/

def mapTy (f : Proto → Proto) : Ty → Ty
  | .prod a b     => .prod (mapTy f a) (mapTy f b)
  | .sum a b      => .sum (mapTy f a) (mapTy f b)
  | .code a b k   => .code (mapTy f a) (mapTy f b) k
  | .array i t    => .array i (mapTy f t)
  | .ptr μ t      => .ptr μ (mapTy f t)
  | .ptrOpt μ t   => .ptrOpt μ (mapTy f t)
  | .loc μ t      => .loc μ (mapTy f t)
  | .word r P     => .word r (f P)
  | .tok r st     => .tok r (st.map fun (P, i) => (f P, i))
  | .mu t         => .mu (mapTy f t)
  | .tex κ t      => .tex κ (mapTy f t)
  | .iall t       => .iall (mapTy f t)
  | .iex t        => .iex (mapTy f t)
  | .refine t ψ   => .refine (mapTy f t) ψ
  | t             => t

def mapOp (f : Proto → Proto) : Op → Op
  | .inl o a          => .inl (mapTy f o) a
  | .inr o a          => .inr (mapTy f o) a
  | .null μ t         => .null μ (mapTy f t)
  | .fold a t         => .fold a (mapTy f t)
  | .newBuf n t       => .newBuf n (mapTy f t)
  | .mkWord r P v tk  => .mkWord r (f P) v tk
  | .pack a w t       => .pack a w (mapTy f t)
  | .packT a σ t      => .packT a (mapTy f σ) (mapTy f t)
  | .call g is a ts   => .call g is a (ts.map (mapTy f))
  | .spawn g a T ts   => .spawn g a (mapTy f T) (ts.map (mapTy f))
  | .zero t           => .zero (mapTy f t)
  | op                => op

def mapExpr (f : Proto → Proto) : Expr → Expr
  | .let_ x op e        => .let_ x (mapOp f op) (mapExpr f e)
  | .split a x y e      => .split a x y (mapExpr f e)
  | .unpack a i x e     => .unpack a i x (mapExpr f e)
  | .unpackT a α x e    => .unpackT a α x (mapExpr f e)
  | .region a r p t e   => .region a r p t (mapExpr f e)
  | .openPub a r p c e  => .openPub a r p c (mapExpr f e)
  | .case a x e₁ y e₂   => .case a x (mapExpr f e₁) y (mapExpr f e₂)
  | .ifnull a e₁ x e₂   => .ifnull a (mapExpr f e₁) x (mapExpr f e₂)
  | .parity a k e₁ e₂   => .parity a k (mapExpr f e₁) (mapExpr f e₂)
  | .ifeq a b e₁ e₂     => .ifeq a b (mapExpr f e₁) (mapExpr f e₂)
  | .cas acq rel w e v t ok fail => .cas acq rel w e v t (mapExpr f ok) (mapExpr f fail)
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      .casp acq rel w e0 e1 v0 v1 t (mapExpr f ok) (mapExpr f fail)
  | .ret a              => .ret a
  | .tail g is a ts     => .tail g is a (ts.map (mapTy f))

def mapDecl (f : Proto → Proto) (d : Decl) : Decl :=
  { d with argTy := mapTy f d.argTy, retTy := mapTy f d.retTy, body := mapExpr f d.body }

/-- The program with `P` declared local. -/
def localise (P : Proto) (p : Prog) : Prog :=
  p.map (mapDecl fun Q => if Q == P then { Q with isLocal := true } else Q)

#guard (localise mutexP mutexLib).any (fun d => hasLocalTok d.retTy) &&
       !(localise seqP mutexLib).any (fun d => hasLocalTok d.retTy)
-- `lock` returns its token, so the mutex cannot be local; `unlock`'s caller holds one.
#guard rejects (checkProgL (localise mutexP mutexLib)) "cannot be returned from a block"

/-! ### Tests: the identity lock as a local protocol

`identL` is the locking-scheme example's `Ident` with the flag: free `0`, armed `2k+2`
(shared: parked for handler `k`), busy `2k+3` (held by `k`).  A handler's
window is `cas 0 → busy(k)` … `store busy(k) → 0`. -/

def identL : Proto := { identP with isLocal := true }
def hcell : Ty := cell identL .int

/-- The window, straight-line: accepted. -/
def winD : Decl where
  name := "win"; idx := ["r"]; arg := "m"
  argTy := hcell; retTy := .unit
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 3) "t"
      (lets [("u", .store true (v "w") (.lit 0) (some (v "t")))] (.ret .unit))
      (.ret .unit))

/-- A call inside the window: refused by the discipline (the checker is fine with it). -/
def winCallD : Decl := { winD with
  name := "winCall"
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 3) "t"
      (lets [("z", .call "win" ["r"] (v "m")), ("u", .store true (v "w") (.lit 0) (some (v "t")))]
        (.ret .unit))
      (.ret .unit)) }

/-- Returning the token, as `lock` does: refused at the signature. -/
def lockLD : Decl where
  name := "lockL"; idx := ["r"]; arg := "m"
  argTy := hcell
  retTy := .tok (.var 0) (some (identL, .lit 3))
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 3) "t"
      (.ret (v "t"))
      (.tail "lockL" ["r"] (v "m")))

/-- The token into memory: refused (rule 3). -/
def winStoreD : Decl := { winD with
  name := "winStore"
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 3) "t"
      (lets [("c", .new (v "t"))] (.ret .unit))
      (.ret .unit)) }

/-- Paired and split again, then released: accepted (restructuring). -/
def winPairD : Decl := { winD with
  name := "winPair"
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 3) "t"
      (lets [("q", .pair (v "t") (.lit 1))]
        (.split (v "q") "t2" "one"
          (lets [("u", .store true (v "w") (.lit 0) (some (v "t2")))] (.ret .unit))))
      (.ret .unit)) }

def localLib : Prog := [winD, winCallD, lockLD, winStoreD, winPairD]

-- The checker accepts all five; the discipline is what tells them apart.
#guard accepts (checkProg localLib)
#guard accepts (checkDeclL localLib winD)
#guard accepts (checkDeclL localLib winPairD)
#guard rejects (checkDeclL localLib winCallD) "the window must be straight-line"
#guard rejects (checkDeclL localLib lockLD) "cannot be returned from a block"
#guard rejects (checkDeclL localLib winStoreD) "may not leave its block"
-- Without the flag, the same blocks pass the second pass: nothing changes.
#guard accepts (checkProgL mutexLib) && accepts (checkProgL seqLib) &&
       accepts (checkProgL (claimLib .int)) && accepts (checkProgL pcLib)

end Robust
