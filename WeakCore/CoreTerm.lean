/-
# CoreTerm — the term layer's statics  (T1a)

Companion to `CoreLang.lean`, which it imports.  This file is the **checker**:
syntax in A-normal form, a typing context with an affine part, and the rules
for protocol words, regions and torn reads.  It is what decides that `Mutex`
and `SeqLock` are *library code*: §6 writes both, and each is accepted, and
every hazard in §4.4 and row 20 is written as a variant that is rejected **for
the stated reason**.

What this file is not, stated plainly:
  * It is the checker, not the definition.  The declarative judgement is
    `CoreTyping.lean`'s (T1b, decision B), with `checkProg_sound`: every
    program this checker accepts has a derivation.  Completeness is not
    claimed — the judgement's index reasoning is semantic, the checker's is a
    decision procedure for a fragment.
  * The semantics is `TermRun.lean`'s (T2): these terms run on the promise
    machine.  `TermSound.lean` proves one-step theorems about runs (T3).
  * `∀` only as a code block's prenex type parameters (row 18).  Type
    existentials (`packT`/`unpackT`, closures) are *uniform*: the variable is
    guarded, and opaque inside an unpack, so the erased witness decides no
    layout.
  * The 64-bit ceiling on a version measure (§4.4 rule 6) is not checked:
    index arithmetic here is over ℕ.

Build:  LEAN_PATH=build lean CoreTerm.lean   (after CoreLang.olean)
-/

import WeakCore.CoreLang

/-! ## Type tests moved here from TermScope / TermWrapDefs / TermClose: the `spawn`
rule (`checkOp`) uses them.  Same names, one definition each. -/

namespace TermScope
open CoreLang

/-- A mode that is not a region mode. -/
def drfM : Mode → Bool
  | .rgn _ => false
  | _ => true

/-- **Deep region- and `∀`-freedom**: no region mode and no index-`∀` node
anywhere in the type (also under references, code signatures and binders).
The region half is T1's interim scope; the `∀` half is ProgIall (T2): no
program annotation has an `iall`, so no runtime type does. -/
def drf : Ty → Bool
  | .prod a b => drf a && drf b
  | .sum a b => drf a && drf b
  | .code a b _ => drf a && drf b
  | .array _ t => drf t
  | .ptr μ t => drfM μ && drf t
  | .ptrOpt μ t => drfM μ && drf t
  | .loc μ t => drfM μ && drf t
  | .mu t => drf t
  | .tex _ t => drf t
  | .iall _ => false
  | .iex t => drf t
  | .refine t _ => drf t
  | _ => true

/-- (A1) Does a value of `t` carry a word or token key?  `VRR`'s keyed leaves (`word`, `word2`,
`tok`, `tok2`, `tokE`, `share`), through the components and binders `VRR` passes its resource up
through.  `env k`: the answer for type variable `k` (a `mu`-bound variable answers with its `mu`,
the least fixpoint, i.e. the body read with the variable key-free; other type variables are
instantiated by checked arguments and answer `false`).  Stops at references, code and arrays. -/
def rcarE (env : List Bool) : Ty → Bool
  | .word _ _ | .word2 _ _ | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ => true
  | .prod a b | .sum a b => rcarE env a || rcarE env b
  | .tvar k => env.getD k false
  | .mu t => rcarE (rcarE (false :: env) t :: env) t
  | .tex _ t => rcarE (false :: env) t
  | .iall t | .iex t | .refine t _ => rcarE env t
  | _ => false

/-- (A1) `rcarE` of a closed type (or at type parameters / opaque variables: key-free). -/
def rcar (t : Ty) : Bool := rcarE [] t

/-- (A1) **No key-carrying wrapper**, deep (also under references, code and binders), with
`rcarE env` deciding what a type variable carries. -/
def wrapOKE (env : List Bool) : Ty → Bool
  | .sum a b => !rcarE env a && !rcarE env b && wrapOKE env a && wrapOKE env b
  | .iex t | .refine t _ => !rcarE env t && wrapOKE env t
  | .tex _ t => !rcarE (false :: env) t && wrapOKE (false :: env) t
  | .mu t => wrapOKE (rcarE (false :: env) t :: env) t
  | .prod a b | .code a b _ => wrapOKE env a && wrapOKE env b
  | .array _ t | .ptr _ t | .ptrOpt _ t | .loc _ t | .iall t => wrapOKE env t
  | _ => true

def wrapOK (t : Ty) : Bool := wrapOKE [] t

/-- (A1) A type argument or type witness: `wrapOK` and key-free. -/
def argOK (t : Ty) : Bool := wrapOK t && !rcar t

end TermScope

namespace TermClose
open CoreLang

/-- Type variables all bound below `c`. -/
def tb (c : Nat) : Ty → Bool
  | .tvar k      => k < c
  | .prod a b    => tb c a && tb c b
  | .sum a b     => tb c a && tb c b
  | .code a b _  => tb c a && tb c b
  | .array _ t   => tb c t
  | .ptr _ t     => tb c t
  | .ptrOpt _ t  => tb c t
  | .loc _ t     => tb c t
  | .mu t        => tb (c + 1) t
  | .tex _ t     => tb (c + 1) t
  | .iall t      => tb c t
  | .iex t       => tb c t
  | .refine t _  => tb c t
  | _            => true

end TermClose

namespace TermTv
open CoreLang

/-- Every `μ` body in the type is guarded (CoreLang's `unguarded`). -/
def mg : Ty → Bool
  | .mu t        => !t.unguarded 0 && mg t
  | .prod a b    => mg a && mg b
  | .sum a b     => mg a && mg b
  | .code a b _  => mg a && mg b
  | .array _ t   => mg t
  | .ptr _ t     => mg t
  | .ptrOpt _ t  => mg t
  | .loc _ t     => mg t
  | .tex _ t     => mg t
  | .iall t      => mg t
  | .iex t       => mg t
  | .refine t _  => mg t
  | _            => true

/-- (T2, option ii, corrected (A)) No `∀` node at a position `AtOff`/`IallOK`
traverse (not through references or code signatures).  (P1) Also what a
frame's return type keeps (`TvOK`), so that a plain value of it carries
resources (`VR_VRR`). -/
def noIallV : Ty → Bool
  | .iall _ => false
  | .prod a b | .sum a b => noIallV a && noIallV b
  | .array _ t | .mu t | .tex _ t | .iex t | .refine t _ => noIallV t
  | _ => true

end TermTv

namespace CoreTerm

open CoreLang

/-! ## §1. The index arithmetic the checker decides

Linear forms over index variables with ℕ coefficients, and facts that define a
variable as a linear form.  That is all the refinement the rules need: parity
(`c = 2k` or `2k+1`), equality after a re-check, and matching a value against a
protocol's state families. -/

/-- `const + Σ coef·var`, coefficients positive, sorted by variable. -/
structure Lin where
  const : Nat
  coefs : List (Nat × Nat)
  deriving DecidableEq, Repr

namespace Lin
def ofConst (n : Nat) : Lin := ⟨n, []⟩
def ofVar (k : Nat) : Lin := ⟨0, [(k, 1)]⟩
def ins (k c : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(k, c)]
  | (k', c') :: rest =>
      if k == k' then (k, c + c') :: rest
      else if k < k' then (k, c) :: (k', c') :: rest
      else (k', c') :: ins k c rest
def add (a b : Lin) : Lin :=
  ⟨a.const + b.const, b.coefs.foldl (fun acc p => ins p.1 p.2 acc) a.coefs⟩
def scale (n : Nat) (a : Lin) : Lin :=
  if n == 0 then ofConst 0 else ⟨n * a.const, a.coefs.map fun p => (p.1, n * p.2)⟩
/-- `(a - off) / s` as a linear form, when it is one. -/
def divSub (a : Lin) (s off : Nat) : Option Lin :=
  if s == 0 then (if a.coefs.isEmpty && a.const == off then some (ofConst 0) else none)
  else if a.const ≥ off && (a.const - off) % s == 0 && a.coefs.all (fun p => p.2 % s == 0)
  then some ⟨(a.const - off) / s, a.coefs.map fun p => (p.1, p.2 / s)⟩
  else none
def toIdx (a : Lin) : Idx :=
  a.coefs.foldl (fun acc p => .add acc (if p.2 == 1 then .var p.1 else .smul p.2 (.var p.1)))
    (.lit a.const)
def asVar? : Lin → Option Nat
  | ⟨0, [(k, 1)]⟩ => some k
  | _ => none
/-- `v + 1` for one variable `v`: a modulus `rem` can bound below (`v := k + d`). -/
def succVar? : Lin → Option Nat
  | ⟨1, [(v, 1)]⟩ => some v
  | _ => none
def mentions (a : Lin) (k : Nat) : Bool := a.coefs.any (·.1 == k)
/-- `s·u`, one variable and no constant. -/
def single? : Lin → Option (Nat × Nat)
  | ⟨0, [(u, s)]⟩ => some (u, s)
  | _ => none
/-- `(s+1)·u`: a positive multiple of one variable, so zero only at `u = 0`. -/
def zeroVar? : Lin → Option Nat
  | ⟨0, [(u, _ + 1)]⟩ => some u
  | _ => none
def coefOf (a : Lin) (k : Nat) : Nat := ((a.coefs.find? (·.1 == k)).map (·.2)).getD 0
/-- `b − a`, clipped at zero: exact whenever `a ≤ b` coefficientwise. -/
def diff (b a : Lin) : Lin :=
  ⟨b.const - a.const, (b.coefs.map fun p => (p.1, p.2 - a.coefOf p.1)).filter (·.2 > 0)⟩
/-- `a ≤ b` at every valuation, by exhibiting `b = a + d` for a linear form `d`.
The test is the equation, so a bad `diff` can only make it fail. -/
def leB (a b : Lin) : Bool := Lin.add a (b.diff a) == b
end Lin

/-- Index variable `k` is defined as the term. -/
abbrev Facts := List (Nat × Idx)

/-- One level of normalisation: a variable with a defining fact is handed to
`k`, which is where the fuel goes. -/
def normWith (fs : Facts) (k : Idx → Option Lin) : Idx → Option Lin
  | .lit n => some (.ofConst n)
  | .var v =>
      match fs.lookup v with
      | none => some (.ofVar v)
      | some t => k t
  | .add a b => do pure (Lin.add (← normWith fs k a) (← normWith fs k b))
  | .sub _ _ => none
  | .smul n a => (normWith fs k a).map (Lin.scale n)

/-- Structural in `fuel`, then in the index, so that the kernel can evaluate
it: `CoreTyping` proves the library programs well typed by `decide`. -/
def norm (fs : Facts) : Nat → Idx → Option Lin
  | 0     => normWith fs fun _ => none
  | f + 1 => normWith fs (norm fs f)

/-! ## §2. Protocols: well-formedness, states, transitions, version measure -/

def enumFrom {α : Type} : List α → Nat → List (Nat × α)
  | [], _ => []
  | a :: as, i => (i, a) :: enumFrom as (i + 1)

/-- The one state family `a` belongs to, and its parameter `k`. -/
def classify (P : Proto) (a : Lin) : Option (Nat × Lin) :=
  match (enumFrom P.clauses 0).filterMap
          (fun (n, c) => (a.divSub c.scale c.off).map fun k => (n, k)) with
  | [m] => some m
  | _   => none

/-- A transition, checked as an equation between linear forms either way
round, so a count going down needs no subtraction: `k = k' + |dk|`.  A wild
move needs no equation at all. -/
def pstep (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) : Bool :=
  P.trans.any (fun (a, b, dk) => a == c && b == c' &&
    (if 0 ≤ dk then k' == k.add (.ofConst dk.toNat) else k == k'.add (.ofConst (-dk).toNat))) ||
  P.wild.contains (c, c')

/-- §4.4 rule 6: every transition strictly increases the word's value, for
every parameter, so no state is ever re-entered.  `sb·(k+dk)+ob > sa·k+oa` for
all `k` iff `sb ≥ sa` and `sb·dk + ob > oa`.  A wild move relates every `k` to
every `k'`: `sb·k'+ob > sa·k+oa` for all of them iff `sa = 0` and `ob > oa`. -/
def monotone (P : Proto) : Bool :=
  (P.trans.all fun (a, b, dk) =>
    match P.clauses[a]?, P.clauses[b]? with
    | some ca, some cb =>
        decide (0 ≤ dk) && cb.scale ≥ ca.scale && (cb.scale : Int) * dk + cb.off > ca.off
    | _, _ => false) &&
  P.wild.all fun (a, b) =>
    match P.clauses[a]?, P.clauses[b]? with
    | some ca, some cb => ca.scale == 0 && cb.off > ca.off
    | _, _ => false

/-- Do two state families share a value?  Two arithmetic progressions meet iff
the gcd of their steps divides the difference of their offsets. -/
def overlap (a b : Clause) : Bool :=
  match a.scale, b.scale with
  | 0, 0 => a.off == b.off
  | 0, s => a.off ≥ b.off && (a.off - b.off) % s == 0
  | s, 0 => b.off ≥ a.off && (b.off - a.off) % s == 0
  | s, t => ((a.off : Int) - b.off) % (Nat.gcd s t : Int) == 0

/-! ### Crash-robustness and repeating values (the claims `robust`, `norepeat`)

A state that does not hold the region is *held*: only the token's holder may
leave it, and if that thread stops, nobody may.  A protocol with no held
state is *crash-free*.  Separately, a `cas` out of a shared state succeeds
whenever the value is the one expected, even if the word moved on and came
back (ABA); `noRepeat` says no shared state is re-entered at a value it had.
Both are decided on the protocol's graph, and a protocol that *claims* either
(`Proto.robust`, `Proto.norepeat`) and fails it is not well formed. -/

/-- The held states: those that do not hold the region. -/
def heldStates (P : Proto) : List Nat :=
  (enumFrom P.clauses 0).filterMap fun (i, c) => if c.holds then none else some i

/-- The net parameter change along a walk: `some d`, or `none` after a wild
move (any change at all). -/
abbrev Δ := Option Int

def addΔ : Δ → Δ → Δ
  | some a, some b => some (a + b)
  | _, _ => none

/-- `a` is at most `b`; a wild walk is below every net change. -/
def leΔ : Δ → Δ → Bool
  | none, _ => true
  | some _, none => false
  | some a, some b => decide (a ≤ b)

def minΔ : Option Δ → Option Δ → Option Δ
  | none, x => x
  | x, none => x
  | some a, some b => some (if leΔ a b then a else b)

def edges (P : Proto) : List (Nat × Nat × Δ) :=
  P.trans.map (fun (a, b, d) => (a, b, some d)) ++ P.wild.map fun (a, b) => (a, b, none)

/-- One round of relaxation: the lowest net change over walks one move longer. -/
def relax (P : Proto) (dist : Array (Option Δ)) : Array (Option Δ) :=
  (edges P).foldl (init := dist) fun d (a, b, w) =>
    match d[a]? with
    | some (some da) => d.modify b fun old => minΔ old (some (addΔ da w))
    | _ => d

/-- The lowest net parameter change over cycles through state `s` (walks of at
most `n + 1` moves, which includes every simple cycle), or `none` if there is
no cycle.  Bellman–Ford without the negative-cycle stop: a negative cycle is
exactly what we are looking for. -/
def cycleΔ (P : Proto) (s : Nat) : Option Δ :=
  let n := P.clauses.length
  let d0 : Array (Option Δ) := (Array.range n).map fun i => if i == s then some (some 0) else none
  let d := (List.range (n + 1)).foldl (fun d _ => relax P d) d0
  (edges P).foldl (init := none) fun acc (a, b, w) =>
    if b != s then acc else
    match d[a]? with
    | some (some da) => minΔ acc (some (addΔ da w))
    | _ => acc

/-- Can state `s` be re-entered at a value it had?  Yes if some cycle returns
to it with the parameter not strictly grown: a wild move on the way, a net
change `≤ 0`, or no parameter at all (`scale = 0`: any cycle repeats). -/
def repeats (P : Proto) (s : Nat) : Bool :=
  match cycleΔ P s, P.clauses[s]? with
  | none, _ => false
  | some none, _ => true
  | some (some w), some cl => cl.scale == 0 || decide (w ≤ 0)
  | some (some _), none => true

/-- No shared state is ever re-entered at a value it had.  Weaker than
`monotone`, which forbids re-entering *any* state: the mutex `0 → 1 → 0`
repeats; the seqlock `2k → 2k+1 → 2k+2` does not. -/
def noRepeat (P : Proto) : Bool :=
  (enumFrom P.clauses 0).all fun (i, c) => !c.holds || !repeats P i

/-- An epoch protocol is exactly the counter: one shared clause `k!`, one move
`0->0(+1)`, nothing lent, no wild move, not ghost, not local. -/
def epochOK (P : Proto) : Bool :=
  P.clauses == [⟨1, 0, true⟩] && P.trans == [(0, 0, 1)] && P.wild.isEmpty &&
  P.lends.isEmpty && P.lendsDown.isEmpty && !P.ghost && !P.isLocal

/-- A `ticket` protocol is exactly the held counter `<k ; 0->0+1>`: one state,
held, every value, and the one move `+1`. -/
def ticketOK (P : Proto) : Bool :=
  P.clauses == [⟨1, 0, false⟩] && P.trans == [(0, 0, 1)] && P.wild.isEmpty &&
  P.lends.isEmpty && P.lendsDown.isEmpty && !P.ghost && !P.isLocal && !P.epoch

/-- What a fetch-add of 1 on an epoch counter returns: the old value `e` and
the token of the epoch it entered, `Tok[r, P, e + 1]`, under an existential
for `e` -- the counter's value is whatever the hardware read.  (`r` is shifted
under the new index binder.) -/
def fetchEpochTy (r : Idx) (P : Proto) : Ty :=
  .iex (.prod (.intS (.var 0)) (.tokE (r.shift 0) (.word P) (.add (.var 0) (.lit 1))))

/-- A fetch-add of `d` on a protocol word nobody ever holds: every family is
shared and lends nothing, and from every family `c` some listed move
`(c, c', dk)` is exactly `+d` on the value at every parameter `k` -- the same
scale, `off + d = scale·dk + off'`, and `dk ≥ 0` (so the new parameter
`k + dk` is a parameter at every `k`; a move down would leave the family at
small `k`, e.g. `<2k!, 2k+7!>` with `0 -> 1` at `dk = -3` takes `0` to `1`).
Then whatever state the word was in,
it was shared, the new state is shared, and nothing changes hands: the result
is the old value as a plain `Int`.  (A counter with a held state, or one that
lends, needs `cas`, which knows which state it left.) -/
def fetchOK (P : Proto) (d : Nat) : Bool :=
  !P.ghost && !P.epoch && P.lends.isEmpty && P.lendsDown.isEmpty &&
  (enumFrom P.clauses 0).all fun (c, cl) =>
    cl.holds && P.trans.any fun (a, b, dk) =>
      a == c && 0 ≤ dk && match P.clauses[b]? with
        | some cl' => cl'.scale == cl.scale && ((cl.off : Int) + d == (cl'.scale : Int) * dk + cl'.off)
        | none => false

/-- The declared recovery targets (`Proto.recover`) are moves out of a held
family into a shared one that lends nothing (a lending family's parameter
counts shares, which a recovery cannot create), at most one per held family,
and a ghost protocol (no runtime word) declares none. -/
def recoverOK (P : Proto) : Bool :=
  P.recover.all (fun (h, s) =>
    (match P.clauses[h]? with | some cl => !cl.holds | none => false) &&
    (match P.clauses[s]? with | some cl => cl.holds | none => false) &&
    !P.lends.contains s && !P.lendsDown.contains s) &&
  (P.recover.map Prod.fst).eraseDups.length == P.recover.length &&
  (P.recover.isEmpty || !P.ghost)

/-- States are disjoint (a value determines its state, and so what the word
holds), transitions name real states, recovery targets are held-to-shared
(`recoverOK`), lending states hold, and the claims `robust` (no held state),
`norepeat`, `epoch` and `ticket` hold if made.  (`recoverOK` shares a conjunct
with the wild moves, so the positions of the other conjuncts, which proofs
project, are unchanged.) -/
def pwf (P : Proto) : Bool :=
  (enumFrom P.clauses 0).all (fun (i, a) =>
    (enumFrom P.clauses 0).all fun (j, b) => j ≤ i || !overlap a b) &&
  P.trans.all (fun (a, b, _) => a < P.clauses.length && b < P.clauses.length) &&
  (P.wild.all (fun (a, b) => a < P.clauses.length && b < P.clauses.length) && recoverOK P) &&
  P.lends.all (fun c => match P.clauses[c]? with | some cl => cl.holds | none => false) &&
  P.lendsDown.all (fun c => !P.lends.contains c &&
    match P.clauses[c]? with | some cl => cl.holds | none => false) &&
  (!P.robust || (heldStates P).isEmpty) && (!P.norepeat || noRepeat P) &&
  (!P.epoch || epochOK P) && (!P.ticket || ticketOK P)

/-- The owner word of a ticket lock: `<k ; 0->0+1 ; ticket>`. -/
def ticketOwnerP : Proto :=
  { clauses := [⟨1, 0, false⟩], trans := [(0, 0, 1)], ticket := true }

#guard pwf ticketOwnerP
#guard !pwf { ticketOwnerP with clauses := [⟨1, 0, true⟩] }
#guard !pwf { ticketOwnerP with trans := [(0, 0, 2)] }
#guard !pwf { ticketOwnerP with epoch := true }

/-- The epoch counter of a worked locking-scheme example (not included): `<<k! ; 0->0(+1) ; robust, epoch>>`. -/
def epochCounterP : Proto :=
  { clauses := [⟨1, 0, true⟩], trans := [(0, 0, 1)], robust := true, epoch := true }

#guard pwf epochCounterP
#guard !pwf { epochCounterP with trans := [(0, 0, 2)] }
#guard !pwf { epochCounterP with trans := [] }
#guard !pwf { epochCounterP with clauses := [⟨1, 0, false⟩] }
#guard !pwf { epochCounterP with isLocal := true }
#guard !pwf { epochCounterP with wild := [(0, 0)] }

/-- How a `cas` between holding states moves the read shares: `+1` lends one
(`acq`), `-1` takes one back (`rel`), `0` none.  Inside a lending family the
count is `k + 1`, so entering one needs `k' = 0` and leaving one `k = 0`; two
different lending families are not related. -/
def shareMoveUp (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) : Option Int :=
  match P.lends.contains c, P.lends.contains c' with
  | false, false => some 0
  | true, true =>
      if c != c' then none
      else if k' == k.add (.ofConst 1) then some 1
      else if k == k'.add (.ofConst 1) then some (-1)
      else if k == k' then some 0 else none
  | false, true => if k' == .ofConst 0 then some 1 else none
  | true, false => if k == .ofConst 0 then some (-1) else none

/-- The same for a counting-down family: `k + 1 → k` lends (`+1`), `k → k + 1`
gives back (`-1`), and nothing enters or leaves. -/
def shareMoveDown (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) : Option Int :=
  if c == c' && P.lendsDown.contains c then
    if k == k'.add (.ofConst 1) then some 1
    else if k' == k.add (.ofConst 1) then some (-1)
    else if k == k' then some 0 else none
  else none

def shareMove (P : Proto) (c : Nat) (k : Lin) (c' : Nat) (k' : Lin) : Option Int :=
  if P.lendsDown.contains c || P.lendsDown.contains c' then shareMoveDown P c k c' k'
  else shareMoveUp P c k c' k'

#guard pwf mutexP && pwf seqP
-- The claims: the mutex is neither crash-free nor repeat-free; the seqlock
-- is repeat-free but a stopped writer blocks every reader.
#guard !pwf { mutexP with robust := true } && !pwf { mutexP with norepeat := true }
#guard pwf { seqP with norepeat := true } && !pwf { seqP with robust := true }
#guard noRepeat seqP && !noRepeat mutexP
#guard monotone seqP && !monotone mutexP
-- `2k` and `3k` meet at 0 and 6: which state is 6 in?  Refused.
#guard !pwf ⟨[⟨2, 0, true⟩, ⟨3, 0, false⟩], [], false, [], [], [], false, false, false, false, false, []⟩
#guard pwf ⟨[⟨4, 0, true⟩, ⟨4, 2, false⟩], [], false, [], [], [], false, false, false, false, false, []⟩
-- A seqlock whose writer steps back (`2k+1 → 2k`) has no version measure.
def badSeqP : Proto := ⟨[⟨2, 0, true⟩, ⟨2, 1, false⟩], [(0, 1, 0), (1, 0, 0)], false, [], [], [], false, false, false, false, false, []⟩
#guard pwf badSeqP && !monotone badSeqP && !noRepeat badSeqP
-- Wild moves (E1): a lock whose owner's identity `k` is in the value.  Free
-- `0`, armed `2k+2` (holds: parked for `k`), busy `2k+3` (held by `k`).
-- `0 → busy(*)` chooses `k`; `busy(*) → 0` forgets it.
def identP : Proto := { clauses := [⟨0, 0, true⟩, ⟨2, 2, true⟩, ⟨2, 3, false⟩],
                        trans := [(2, 1, 0), (1, 2, 0)], wild := [(0, 2), (2, 0)] }
#guard pwf identP && !monotone identP
#guard pstep identP 0 (.ofConst 0) 2 (.ofVar 3) && pstep identP 2 (.ofVar 3) 0 (.ofConst 0)
-- ... and the parameter is kept by the ordinary moves, not by the wild ones.
#guard pstep identP 2 (.ofVar 3) 1 (.ofVar 3) && !pstep identP 2 (.ofVar 3) 1 (.ofVar 4)
#guard !pstep identP 1 (.ofVar 3) 0 (.ofConst 0)
-- Monotone only out of a parameterless family, upward.
#guard monotone { identP with trans := [], wild := [(0, 2)] }
#guard !monotone { identP with trans := [], wild := [(2, 0)] }
#guard !monotone { identP with trans := [], wild := [(1, 2)] }
#guard !pwf { identP with wild := [(0, 3)] }
-- Recovery targets: `busy(k) → 0` (the example's reclaim) or `→ armed(k')`;
-- not into a held state, not out of a shared one, one per held state.
#guard pwf { identP with recover := [(2, 0)] } && pwf { identP with recover := [(2, 1)] }
#guard !pwf { identP with recover := [(2, 2)] } && !pwf { identP with recover := [(0, 1)] }
#guard !pwf { identP with recover := [(2, 0), (2, 1)] } && !pwf { identP with recover := [(2, 3)] }

/-! ### Pair protocols  (CoreLang's `Proto2`: two words, one access)

The same notions for a pair.  A value `(a₀, a₁)` is classified by matching
each half's pattern and checking the clause's relation between the two
parameters; a transition moves each parameter by its delta, or forgets it.
Two families are decided disjoint exactly when their halves have the same
slopes — the parameters are then determined up to a shift, and the two
relations are compared — and conservatively ("they overlap") otherwise. -/

/-- `k₁ ⋈ k₀ + d`, between linear forms: `eq` decided, `le`/`ge` soundly
(`Lin.leB`).  A negative `d` is moved to the other side, so both sides stay
natural. -/
def rel2Holds (rel : Rel2) (k0 k1 : Lin) : Bool :=
  match rel with
  | .free => true
  | .eq d => if 0 ≤ d then k1 == k0.add (.ofConst d.toNat) else k1.add (.ofConst (-d).toNat) == k0
  | .le d => if 0 ≤ d then Lin.leB k1 (k0.add (.ofConst d.toNat)) else Lin.leB (k1.add (.ofConst (-d).toNat)) k0
  | .ge d => if 0 ≤ d then Lin.leB (k0.add (.ofConst d.toNat)) k1 else Lin.leB k0 (k1.add (.ofConst (-d).toNat))

/-- The relation with its constant moved by `δ`. -/
def rel2Shift (δ : Int) : Rel2 → Rel2
  | .free => .free
  | .eq d => .eq (d + δ)
  | .le d => .le (d + δ)
  | .ge d => .ge (d + δ)

/-- Can both hold of one pair of parameters?  Exact. -/
def rel2Compat : Rel2 → Rel2 → Bool
  | .free, _ | _, .free => true
  | .eq d, .eq e => d == e
  | .eq d, .le e | .le e, .eq d => d ≤ e
  | .eq d, .ge e | .ge e, .eq d => e ≤ d
  | .le d, .ge e | .ge e, .le d => e ≤ d
  | .le _, .le _ | .ge _, .ge _ => true

/-- Do two pair families share a value?  Each half must (`overlap`); then, with
equal nonzero slopes, `b`'s parameters are `a`'s shifted by the offsets'
difference, and the relations must be compatible under that shift. -/
def overlap2 (a b : Clause2) : Bool :=
  overlap ⟨a.s0, a.o0, true⟩ ⟨b.s0, b.o0, true⟩ && overlap ⟨a.s1, a.o1, true⟩ ⟨b.s1, b.o1, true⟩ &&
  (a.s0 == 0 || a.s1 == 0 || a.s0 != b.s0 || a.s1 != b.s1 ||
    rel2Compat a.rel (rel2Shift (((a.o0 : Int) - b.o0) / a.s0 - ((a.o1 : Int) - b.o1) / a.s1) b.rel))

/-- Does `(a₀, a₁)` match family `n`?  Both halves, then the relation. -/
def pairMatch (a0 a1 : Lin) (n : Nat) (cl : Clause2) : Option (Nat × Lin × Lin) :=
  match a0.divSub cl.s0 cl.o0, a1.divSub cl.s1 cl.o1 with
  | some k0, some k1 => if rel2Holds cl.rel k0 k1 then some (n, k0, k1) else none
  | _, _ => none

/-- The one family `(a₀, a₁)` belongs to, with both parameters. -/
def classify2 (P : Proto2) (a0 a1 : Lin) : Option (Nat × Lin × Lin) :=
  match (enumFrom P.clauses 0).filterMap (fun (n, c) => pairMatch a0 a1 n c) with
  | [m] => some m
  | _ => none

/-- One half of a move: `some d` is the equation `k' = k + d` (either way
round, as `pstep`), `none` forgets the parameter. -/
def halfStep (d : Option Int) (k k' : Lin) : Bool :=
  match d with
  | none => true
  | some d => if 0 ≤ d then k' == k.add (.ofConst d.toNat) else k == k'.add (.ofConst (-d).toNat)

def pstep2 (P : Proto2) (c : Nat) (k0 k1 : Lin) (c' : Nat) (k0' k1' : Lin) : Bool :=
  P.trans.any fun (a, b, d0, d1) => a == c && b == c' && halfStep d0 k0 k0' && halfStep d1 k1 k1'

def heldStates2 (P : Proto2) : List Nat :=
  (enumFrom P.clauses 0).filterMap fun (i, c) => if c.holds then none else some i

/-- A pair state the protocol can leave. -/
def exits2 (P : Proto2) (c : Nat) : Bool := P.trans.any (·.1 == c)

/-- An epoch pair: every state shared, half 0 the bare parameter `k` in every
clause, and every move changes half 0 by `0` or `+1` (never wild). -/
def epochOK2 (P : Proto2) : Bool :=
  !P.clauses.isEmpty &&
  P.clauses.all (fun c => c.holds && c.s0 == 1 && c.o0 == 0) &&
  P.trans.all fun (_, _, d0, _) => d0 == some 0 || d0 == some 1

/-- Well-formed: families pairwise disjoint (as decided by `overlap2`), moves
between named families, and the `robust` and `epoch` claims true if made. -/
def pwf2 (P : Proto2) : Bool :=
  (enumFrom P.clauses 0).all (fun (i, a) =>
    (enumFrom P.clauses 0).all fun (j, b) => j ≤ i || !overlap2 a b) &&
  P.trans.all (fun (a, b, _, _) => a < P.clauses.length && b < P.clauses.length) &&
  (!P.robust || (heldStates2 P).isEmpty) && (!P.epoch || epochOK2 P)

/-- Does this move of an epoch pair bump the epoch?  Half 0 is the bare
parameter, so the move is `+1` on it exactly when `k₀' = k₀ + 1`. -/
def bump2 (P : Proto2) (k0 k0' : Lin) : Bool := P.epoch && halfStep (some 1) k0 k0'

/-- The epoch lock of a worked locking-scheme example (not included), design (b), as an epoch pair `(e, busy)`:
acquire `(e, 0) -> (e+1, 1)` and reclaim `(e, 1) -> (e+1, 1)` issue the new
epoch's token; release `(e, 1) -> (e, 0)` issues nothing.  Every state is
shared, so it is `robust`. -/
def epochLockP : Proto2 :=
  { clauses := [⟨1, 0, 0, 0, .free, true⟩, ⟨1, 0, 0, 1, .free, true⟩],
    trans := [(0, 1, some 1, some 0), (1, 0, some 0, some 0), (1, 1, some 1, some 0)],
    robust := true, epoch := true }
#guard pwf2 epochLockP
#guard !pwf2 { epochLockP with clauses := [⟨1, 0, 0, 0, .free, true⟩, ⟨1, 0, 0, 1, .free, false⟩] }
#guard !pwf2 { epochLockP with trans := [(0, 1, some 1, some 0), (1, 0, some (-1), some 0)] }
#guard !pwf2 { epochLockP with trans := [(0, 1, none, some 0)] }
#guard !pwf2 { epochLockP with clauses := [⟨2, 0, 0, 0, .free, true⟩, ⟨2, 1, 0, 1, .free, true⟩] }
#guard bump2 epochLockP (.ofVar 0) ((Lin.ofVar 0).add (.ofConst 1))
#guard !bump2 epochLockP (.ofVar 0) (.ofVar 0)

/-- A ticket lock's pair `(next, owner)`: free when they agree, held while the
owner is behind.  Taking a ticket is `casp (k, k) → (k+1, k)`; handing over is
`stp (k+1, k) → (k+1, k+1)`.  (Acquiring by *observing* `owner = my ticket`
is not a protocol move; see the notes.) -/
def ticketP : Proto2 :=
  { clauses := [⟨1, 0, 1, 0, .eq 0, true⟩, ⟨1, 0, 1, 0, .le (-1), false⟩],
    trans := [(0, 1, some 1, some 0), (1, 0, some 0, some 1)] }
/-- An epoch-stamped value `(epoch, value)`: one shared family; every `casp`
bumps the epoch and chooses the value, so it is `robust`. -/
def epochP : Proto2 :=
  { clauses := [⟨1, 0, 1, 0, .free, true⟩], trans := [(0, 0, some 1, none)], robust := true }
#guard pwf2 ticketP && pwf2 epochP
-- `owner ≤ next` meets `owner = next`: refused.
#guard !pwf2 { ticketP with clauses := [⟨1, 0, 1, 0, .eq 0, true⟩, ⟨1, 0, 1, 0, .le 0, false⟩] }
#guard !pwf2 { ticketP with robust := true }
#guard classify2 ticketP (.ofVar 3) (.ofVar 3) == some (0, .ofVar 3, .ofVar 3)
#guard classify2 ticketP ((Lin.ofVar 3).add (.ofConst 2)) (.ofVar 3) ==
  some (1, (Lin.ofVar 3).add (.ofConst 2), .ofVar 3)
#guard (classify2 ticketP (.ofVar 3) (.ofVar 4)).isNone      -- `owner > next`: in no state
#guard pstep2 ticketP 0 (.ofVar 3) (.ofVar 3) 1 ((Lin.ofVar 3).add (.ofConst 1)) (.ofVar 3)
#guard !pstep2 ticketP 0 (.ofVar 3) (.ofVar 3) 1 ((Lin.ofVar 3).add (.ofConst 1)) (.ofVar 4)
#guard pstep2 epochP 0 (.ofVar 3) (.ofVar 4) 0 ((Lin.ofVar 3).add (.ofConst 1)) (.ofConst 7)
-- Different slopes with a relation: conservatively overlapping.
#guard overlap2 ⟨2, 0, 1, 0, .eq 0, true⟩ ⟨1, 0, 1, 0, .eq 5, false⟩
-- Offsets shift the relation: `(k, k | k1 = k0)` and `(k+1, k | k1 = k0+1)` are the
-- same values (both say "the halves agree"); with `k1 = k0` the second is "a1 = a0 - 1".
#guard overlap2 ⟨1, 0, 1, 0, .eq 0, true⟩ ⟨1, 1, 1, 0, .eq 1, false⟩
#guard !overlap2 ⟨1, 0, 1, 0, .eq 0, true⟩ ⟨1, 1, 1, 0, .eq 0, false⟩

/-! ## §3. Syntax: A-normal form, closure-free, named variables

Term variables are names and may not be shadowed.  Index variables are named
where they are bound (`unpack`, `region`, `parity`, a load of a protocol word)
and referred to by name at calls and `pack`; inside types they are de Bruijn,
as in the type layer. -/

inductive At
  | var (x : String)
  | lit (n : Nat)
  | unit
  deriving Repr, DecidableEq

inductive Fence
  | ld | st | full
  deriving Repr, DecidableEq

/-- Binary operations on fixed-width integers.  `div`/`rem` truncate toward
zero; `x / 0 = 0` and `x % 0 = x`; everything wraps.  No undefined results. -/
inductive FOp | add | sub | mul | div | rem | and | or | xor | shl | shr
  deriving DecidableEq, Repr
/-- Comparisons on fixed-width integers, by their signed or unsigned value: `Int` 0 or 1. -/
inductive FCmp | eq | ne | lt | le
  deriving DecidableEq, Repr
inductive FOp1 | not | neg
  deriving DecidableEq, Repr

/-- Binary 64-bit word operations (operands are reduced mod 2⁶⁴).  `mulhi` is the
high word of the 128-bit product; `msb16 lo hi` gathers the top bit of each of the
16 bytes of `lo:hi` (`pmovmskb`). -/
inductive BitOp
  | and | or | xor | shl | shr | wadd | wsub | wmul | mulhi | msb16
  deriving Repr, DecidableEq

/-- Unary 64-bit word operations; `ctz 0 = 64`. -/
inductive BitOp1
  | not | ctz | popcnt
  deriving Repr, DecidableEq

/-- The fetch-ops: one atomic read-modify-write whose write is the value read
combined with the operand, and whose result is the value read (`LDADD` and
friends; `lock xadd`).  `WeakMem.RmwKind` is the machine's view of the same
list, plus the swap and the compare (`TermRun.FetchOp.kind` maps one to the
other). -/
inductive FetchOp
  | add | or | and | xor
  deriving Repr, DecidableEq

def FetchOp.name : FetchOp → String
  | .add => "add" | .or => "or" | .and => "and" | .xor => "xor"

/-- (E1) The trusted extern steps: a closed set; every other extern is a model body.
The device-stream arms. -/
inductive ExtName
  | emit | current | exitEv
  | park | unpark                                   -- (D4) machine externs; were prelude `ret ()` bodies
  | mmioR (w : Wd) (acc : RegAcc) (mo : Mo)            -- register read: an event; value = the device's last write
  | mmioW (w : Wd) (acc : RegAcc) (mo : Mo)            -- register write: an event
  | regAt (n : Nat) (w : Wd) (acc : RegAcc) (stride : Nat) (taken : List Nat) (k : Nat)   -- static split: (reg k, rest)
  | devRecv (w : Wd) | devWrite (w : Wd) | devChoice (w : Wd) | devIrq | devOut (w : Wd)   -- device decls only
  deriving DecidableEq, Repr
def ExtName.sig : ExtName → Ty × Ty
  | .emit => (.fix false .w8, .unit)
  | .current => (.unit, .tid)
  | .exitEv => (.int, .unit)
  | .park => (.unit, .unit)
  | .unpark => (.tid, .unit)
  | .mmioR w acc _ => (.opq (.reg w acc), .prod (.opq (.reg w acc)) (.fix false w))
  | .mmioW w acc _ => (.prod (.opq (.reg w acc)) (.fix false w), .opq (.reg w acc))
  | .regAt n w acc st tk k => (.opq (.blk n w acc st tk), .prod (.opq (.reg w acc)) (.opq (.blk n w acc st (k :: tk))))
  | .devRecv w => (.opq (.reg w .wo), .fix false w)
  | .devWrite w => (.prod (.opq (.reg w .ro)) (.fix false w), .unit)
  | .devChoice w => (.unit, .fix false w)
  | .devIrq => (.opq .irq, .unit)
  | .devOut w => (.fix false w, .unit)
/-- Admissible names (the `.ext` typing arm requires `n.ok`): access and ordering agree; a split index is fresh and in range; the stride is a multiple of the register width in bytes (so every split handle is aligned when the base is, user). -/
def ExtName.ok : ExtName → Bool
  | .mmioR _ acc mo => acc.canRead && mo != .rel
  | .mmioW _ acc mo => acc.canWrite && mo != .acq
  | .regAt n w _ st tk k => k < n && !tk.contains k && Wd.bits w / 8 ≤ st && st % (Wd.bits w / 8) = 0   -- in range, fresh, width fits and divides the stride
  | _ => true
/-- Device-only externs: callable from a `device` decl only (`checkDecl`). -/
def ExtName.deviceOnly : ExtName → Bool
  | .devRecv _ | .devWrite _ | .devChoice _ | .devIrq | .devOut _ => true
  | _ => false
/-- (rev 2o, E5 correction) Externs a READ-ONLY restricted body may use: see T6. -/
def ExtName.pure : ExtName → Bool
  | .mmioR _ .ro _ => true
  | .regAt .. => true
  | _ => false

def _root_.CoreLang.RegAcc.name : RegAcc → String | .ro => "ro" | .wo => "wo" | .rw => "rw"
def _root_.CoreLang.Mo.name : Mo → String | .plain => "plain" | .rel => "rel" | .acq => "acq"

/-- The surface spelling of an extern (the parser's arm, `Syntax.lean`). -/
def ExtName.name : ExtName → String
  | .emit => "emit" | .current => "current" | .exitEv => "exitEv"
  | .park => "park" | .unpark => "unpark"
  | .mmioR w acc mo => s!"mmioRead[{w.bits}, {acc.name}, {mo.name}]"
  | .mmioW w acc mo => s!"mmioWrite[{w.bits}, {acc.name}, {mo.name}]"
  | .regAt n w acc st tk k => s!"regAt[{n}, {w.bits}, {acc.name}, {st}, {tk}, {k}]"
  | .devRecv w => s!"devRecv[{w.bits}]" | .devWrite w => s!"devWrite[{w.bits}]"
  | .devChoice w => s!"devChoice[{w.bits}]" | .devIrq => "devIrq" | .devOut w => s!"devOut[{w.bits}]"

inductive Op
  | atom (a : At)
  | pair (a b : At)
  | inl (other : Ty) (a : At)
  | inr (other : Ty) (a : At)
  | add (a b : At)
  | sub (a b : At)                          -- `a − b`, only where `b ≤ a` is provable
  | new (a : At)                            -- allocate and initialise: `Ptr own τ`
  | null (μ : Mode) (target : Ty)           -- `Ptr? μ target`; the only null there is
  | fold (a : At) (target : Ty)             -- a reference to `τ[μα.τ/α]` as one to `μα.τ`
  | publish (a : At)                        -- `Ptr own τ → Ptr pub τ`; emits the release
  | intoRgn (r : String) (a : At)           -- `Ptr own τ → Ptr (rgn r) τ`: moves into region `r`; emits the release
  | newBuf (n : At) (τ : Ty)                -- `n` slots: `Buf own τ n n` if `τ` is Zeroable, else `Buf own τ n 0`
  | idx (b i : At)                          -- locative to an initialised slot of a buffer
  | bufInit (b i v : At)                    -- write slot `i = ini`: `ini` grows by one
  | fld (i : Nat) (a : At)                  -- locative to a pair's component
  | load (acq : Bool) (a : At)
  | store (rel : Bool) (a v : At) (tok : Option At)
  | fence (f : Fence)
  | mkWord (r : String) (P : Proto) (v : At) (tok : At)
  | pack (a : At) (w : String) (target : Ty)
  | packT (a : At) (σ : Ty) (target : Ty)   -- a type existential, witness `σ` (erased at runtime)
  | validate (x : String)
  | call (f : String) (is : List String) (a : At) (ts : List Ty := [])
  | borrow (s : Cap) (t : At)               -- lend a token (`bor`/`rd`) or read share (`rd`): `Cap s r`
  | endBorrow (t : At)                      -- take it back; the second-class capabilities go
  | xchg (a v : At)                         -- swap `v` into an exclusively held cell; the old value
  | fnptr (f : String)                      -- a monomorphic code block as a `code` value
  | callc (f a : At)                        -- call through a `code` value
  | rem (a n : At)                          -- `a mod n`: an index provably below `n`
  | nameI (a : At)                          -- name an integer's index: a `let` for indices
  | xchgAt (b i v : At)                     -- swap `v` into slot `i` of an own buffer; the old value
  | loadAt (b i : At)                       -- read a copyable slot of an own buffer, keeping the buffer
  | bits (o : BitOp) (a b : At)             -- 64-bit word arithmetic on plain integers
  | bit1 (o : BitOp1) (a : At)              -- unary 64-bit word ops
  | vmatch (lo hi b : At)                   -- 16-lane byte compare: bit i set iff byte i of lo:hi = b
  | band (a m : At)                         -- `a & m` for `m = v`: an index provably ≤ `v`
  | zero (τ : Ty)                           -- the zero value of a Zeroable type
  | loadAtF (b i : At) (p : List Nat)       -- `loadAt` of one component (field path `p`) of a slot
  | xchgAtF (b i : At) (p : List Nat) (v : At) -- `xchgAt` of one component of a slot
  | freeze (t : At)                         -- spend a fresh region token for good: `Cap frz r`
  | cvt (sg : Bool) (w : Wd) (a : At)       -- an integer (`Int`, `fix`, `lanes`) to `fix sg w`, wrapping
  | toInt (a : At)                          -- an unsigned `fix`, or a `lanes` word, as a plain `Int`
  | asLanes (sg : Bool) (w : Wd) (a : At)   -- an `Int`'s low 64 bits as a `lanes sg w` word
  | fop (o : FOp) (a b : At)                -- `fix sg w` arithmetic, wrapping
  | fcmp (o : FCmp) (a b : At)              -- `fix sg w` comparison: `Int` 0/1
  | fop1 (o : FOp1) (a : At)
  | lane (a j : At)                         -- lane `j mod 64/w` of a `lanes` word
  | setLane (a j v : At)                    -- the `lanes` word with lane `j mod 64/w` replaced by `v`
  | ldl (b i : At)                          -- lane `i` (`< n·64/w`) of an own buffer of `lanes`
  | stl (b i v : At)                        -- store lane `i` of an own buffer of `lanes` (a sub-word store)
  | ldlw (b wi j : At)                      -- lane `j mod 64/w` of word `wi` (`< n`) of an own buffer of `lanes`
  | stlw (b wi j v : At)                    -- store it (a sub-word store)
  | mkWord2 (r : String) (P : Proto2) (v0 v1 : At) (tok : At)  -- a protocol pair, born shared: `Pair[r, P]`
  | ldp (acq : Bool) (a : At) (n0 n1 : String)  -- observe a pair: `Int[n0] × Int[n1]`, two fresh indices
  | stp (rel : Bool) (a v0 v1 : At) (tok : At)  -- the holder's store to a pair: a protocol move
  | mkEPair (r : String) (P : ECounter) (v0 v1 : At)  -- an epoch-fenced payload pair `EPair[r, P]`, born `(v0, v1)`
  | mkTicket (r : String) (N P : Proto) (v : At) (tok : At)  -- a ticket lock: dispenser `Word[r, N]` and owner `Word[r, P]`, both at `v`
  | claim (a : At) (tok : At)               -- acquisition by observation: ticket `tok`, owner `a` seen at ticket − 1
  | fetch (o : FetchOp) (acq rel : Bool) (a v : At)  -- atomic `old ⊕ v` into a cell or protocol word; the old value
  | spawn (f : String) (a : At) (T : Ty) (ts : List Ty := [])  -- start thread `f` on a copy of `a` at the checked type `T`: `ThreadId` (the child's index); several args: a pair
  | ext (n : ExtName) (a : At)              -- (E1) a trusted extern on `a : n.sig.1`, result `n.sig.2`: a configuration step (`TermExtStep.Ext`)
  deriving Repr

inductive Expr
  | let_ (x : String) (op : Op) (e : Expr)
  | split (a : At) (x y : String) (e : Expr)
  | unpack (a : At) (i x : String) (e : Expr)
  | unpackT (a : At) (α x : String) (e : Expr)  -- a type existential: `α` is opaque in `e`
  | region (a : At) (r p t : String) (e : Expr)
  | openPub (a : At) (r p c : String) (e : Expr)  -- `Ptr pub τ` as `Ptr (rgn r) τ` with `Cap pub r`
  | case (a : At) (x : String) (e₁ : Expr) (y : String) (e₂ : Expr)
  | ifnull (a : At) (isNull : Expr) (x : String) (nonNull : Expr)  -- `Ptr?`'s case analysis
  | parity (a : At) (k : String) (even odd : Expr)
  | ifeq (a b : At) (yes no : Expr)
  | cas (acq rel : Bool) (w e v : At) (t : String) (ok fail : Expr)
  | casp (acq rel : Bool) (w e0 e1 v0 v1 : At) (t : String) (ok fail : Expr)  -- `cas` on a pair
  | ret (a : At)
  | tail (f : String) (is : List String) (a : At) (ts : List Ty := [])
  deriving Repr

def lets : List (String × Op) → Expr → Expr
  | [], e => e
  | (x, op) :: rest, e => .let_ x op (lets rest e)

inductive DeclKind | plain | device | restricted (fuel stack : Nat) deriving DecidableEq, Repr

structure Decl where
  name  : String
  tparams : List Kind := [] -- prenex type parameters, outermost first (§3.11, row 18)
  idx   : List String       -- index parameters, outermost first
  arg   : String
  argTy : Ty
  retTy : Ty
  body  : Expr
  kind : DeclKind := .plain   -- `device`: may call device-only externs; `restricted`: REFUSED by this bundle's checker

abbrev Prog := List Decl

/-! ## §4. Types the rules consult -/

/-- May a value of this type be used at most once?  `Ty.affineIn`, now in the
type layer because a kind can assert its negation (`copy`); `ke` gives the
kinds of the code block's type parameters. -/
def affine (ke : KEnv) (t : Ty) : Bool := Ty.affineIn ke t

/-- Row 20's former reading of `own` inside a region.  Since D1 a region cell
type has no `own` component (`region`/`intoRgn` require `noOwnIn`), so on every
admissible cell type `adapt r u = u`; the rules keep their text. -/
def adapt (r : Idx) : Ty → Ty
  | .ptr .own t    => .ptr (.rgn r) t
  | .ptrOpt .own t => .ptrOpt (.rgn r) t
  | .loc .own t    => .loc (.rgn r) t
  | .prod a b      => .prod (adapt r a) (adapt r b)
  | .sum a b       => .sum (adapt r a) (adapt r b)
  | .array i t     => .array i (adapt r t)
  | .iex t         => .iex (adapt (r.shift 0) t)
  | .iall t        => .iall (adapt (r.shift 0) t)
  | .tex κ t       => .tex κ (adapt r t)
  | .refine t ψ    => .refine (adapt r t) ψ
  | .mu t          => .mu (adapt r t)
  | t              => t

def wordOf : Ty → Option (Idx × Proto)
  | .ptr _ (.word r P) => some (r, P)
  | .loc _ (.word r P) => some (r, P)
  | _ => none

def word2Of : Ty → Option (Idx × Proto2)
  | .ptr _ (.word2 r P) => some (r, P)
  | .loc _ (.word2 r P) => some (r, P)
  | _ => none

def epairOf : Ty → Option (Idx × ECounter)
  | .ptr _ (.epair r P) => some (r, P)
  | .loc _ (.epair r P) => some (r, P)
  | _ => none

/-- A well-formed epoch counter of either shape. -/
def pwfE : ECounter → Bool
  | .word P => pwf P && P.epoch
  | .pair P => pwf2 P && P.epoch

/-- A reference to something `ldp` reads whole: a protocol pair or an epoch pair. -/
def pairRef (t : Ty) : Bool := (word2Of t).isSome || (epairOf t).isSome

/-- The region a token (of either shape) holds. -/
def tokRgn : Ty → Option Idx
  | .tok r _ => some r
  | .tok2 r _ _ _ => some r
  | _ => none

def cellOf : Ty → Option (Mode × Ty)
  | .ptr μ t => some (μ, t)
  | .loc μ t => some (μ, t)
  | _ => none

/-- One unrolling of an (iso-)recursive type; anything else is left alone.
`fld` looks through it, and `fold` is its inverse on references. -/
def unfold1 : Ty → Ty
  | .mu t => Ty.substT 0 (.mu t) t
  | t     => t

/-- A fixed-width integer type's signedness and width. -/
def fixOf : Ty → Option (Bool × Wd)
  | .fix sg w => some (sg, w)
  | _ => none

/-- A `lanes` word's lane signedness and width. -/
def lanesOf : Ty → Option (Bool × Wd)
  | .lanes sg w => some (sg, w)
  | _ => none

/-- `some (some i)` for `Int(i)`, `some none` for `Int`. -/
def intOf : Ty → Option (Option Idx)
  | .intS i     => some (some i)
  | .int        => some none
  | .refine t _ => intOf t
  | _           => none

/-- Types `cvt` reads: any integer. -/
def cvtSrc (t : Ty) : Bool := (intOf t).isSome || (fixOf t).isSome || (lanesOf t).isSome

/-- Types `toInt` reads: an unsigned `fix` or a `lanes` word. -/
def toIntSrc : Ty → Bool
  | .fix false _ => true
  | .lanes _ _ => true
  | _ => false

/-- The component of a pair type at field path `p` (`0` = first, `1` = second). -/
def compTy : Ty → List Nat → Option Ty
  | t, []                 => some t
  | .prod a _, 0 :: p     => compTy a p
  | .prod _ b, 1 :: p     => compTy b p
  | _, _                  => none

/-! ### Instantiating index parameters -/

def shiftN : Nat → Idx → Idx
  | 0, i => i
  | n + 1, i => Idx.shift 0 (shiftN n i)

def instI (us : List Idx) (d : Nat) : Idx → Idx
  | .lit n    => .lit n
  | .var k    => if k < d then .var k else
                   match us[k - d]? with
                   | some u => shiftN d u
                   | none   => .var (k - us.length)
  | .add i j  => .add (instI us d i) (instI us d j)
  | .sub i j  => .sub (instI us d i) (instI us d j)
  | .smul n i => .smul n (instI us d i)

def instM (us : List Idx) (d : Nat) : Mode → Mode
  | .rgn r => .rgn (instI us d r)
  | μ      => μ

def instP (us : List Idx) (d : Nat) : Pred → Pred
  | .tt      => .tt
  | .le i j  => .le (instI us d i) (instI us d j)
  | .eq i j  => .eq (instI us d i) (instI us d j)
  | .and p q => .and (instP us d p) (instP us d q)
  | .ini i   => .ini (instI us d i)

/-- Replace index variables `0 … n-1` (at depth `d`) by `us`. -/
def instT (us : List Idx) (d : Nat) : Ty → Ty
  | .intS i       => .intS (instI us d i)
  | .prod a b     => .prod (instT us d a) (instT us d b)
  | .sum a b      => .sum (instT us d a) (instT us d b)
  | .code a b k   => .code (instT us d a) (instT us d b) k
  | .array i t    => .array (instI us d i) (instT us d t)
  | .ptr μ t      => .ptr (instM us d μ) (instT us d t)
  | .ptrOpt μ t   => .ptrOpt (instM us d μ) (instT us d t)
  | .loc μ t      => .loc (instM us d μ) (instT us d t)
  | .word r P     => .word (instI us d r) P
  | .tok r st     => .tok (instI us d r) (st.map fun (P, i) => (P, instI us d i))
  | .word2 r P    => .word2 (instI us d r) P
  | .tok2 r P i j => .tok2 (instI us d r) P (instI us d i) (instI us d j)
  | .epair r P    => .epair (instI us d r) P
  | .tokE r P e   => .tokE (instI us d r) P (instI us d e)
  | .share r      => .share (instI us d r)
  | .cap c r      => .cap c (instI us d r)
  | .mu t         => .mu (instT us d t)
  | .tex κ t      => .tex κ (instT us d t)
  | .iall t       => .iall (instT us (d + 1) t)
  | .iex t        => .iex (instT us (d + 1) t)
  | .refine t ψ   => .refine (instT us d t) (instP us d ψ)
  | t             => t

/-! ## §5. The context and the rules -/

/-- Where a torn read is in §4.4's sequence: read, fenced, re-checked. -/
inductive Phase
  | opn
  | fenced
  | rechecked (v : Idx)
  deriving Repr, DecidableEq

/-- `x :~ τ @ (w, s, φ)`: a context entry, not a type (§4.4). -/
structure Torn where
  x  : String
  ty : Ty
  w  : String
  s  : Idx
  φ  : Phase

structure Cx where
  inames   : List String := []                  -- index variables, innermost first
  facts    : Facts := []
  vars     : List (String × Ty × Bool) := []    -- `false`: an affine value, used
  saws     : List (String × Idx × Bool) := []   -- `Saw(w, n)`, and whether ordered
  torn     : List Torn := []
  unsealed : List Idx := []                     -- regions taken, not yet `fence st`
  ke       : KEnv := []                         -- the block's type parameters, innermost first
  opq      : List Nat := []                     -- type variables bound by `unpackT`: opaque
  lent     : List String := []                  -- tokens and shares lent by `borrow`
  ret      : Ty

abbrev M := Except String

/-- Type variable `k` occurs in `t` only under a reference (`Ptr`, `Ptr?`,
`Loc`) — possibly inside a `Code` type, but not bare in one.  The term layer's
uniformity rule for a type existential, and its opacity rule inside an unpack:
the witness is erased, so no layout, and nothing a value's meaning depends on,
may depend on it.  Stricter than CoreLang's guard (`unguarded`), which also
counts `Code` as a guard: `Code(α, τ)` is one word, but calling it needs an `α`
by value, which a client of the package can never hold. -/
def _root_.CoreLang.Ty.guardT (k : Nat) : Ty → Bool
  | .tvar j      => j != k
  | .ptr _ _ | .ptrOpt _ _ | .loc _ _ => true
  | .code a b _  => a.guardT k && b.guardT k
  | .prod a b    => a.guardT k && b.guardT k
  | .sum a b     => a.guardT k && b.guardT k
  | .array _ t   => t.guardT k
  | .mu t        => t.guardT (k + 1)
  | .tex _ t     => t.guardT (k + 1)
  | .iall t      => t.guardT k
  | .iex t       => t.guardT k
  | .refine t _  => t.guardT k
  | _            => true

namespace Cx

/-- A new index variable, `var 0`; everything else moves up one. -/
def push (cx : Cx) (n : String) : Cx :=
  { cx with
    inames   := n :: cx.inames
    facts    := cx.facts.map fun (k, t) => (k + 1, t.shift 0)
    vars     := cx.vars.map fun (x, t, b) => (x, t.shiftI 0, b)
    saws     := cx.saws.map fun (w, s, o) => (w, s.shift 0, o)
    torn     := cx.torn.map fun tn =>
                  { tn with ty := tn.ty.shiftI 0, s := tn.s.shift 0,
                            φ := match tn.φ with
                                 | .rechecked v => .rechecked (v.shift 0)
                                 | p => p }
    unsealed := cx.unsealed.map (Idx.shift 0)
    ret      := cx.ret.shiftI 0 }

/-- A new opaque type variable of kind `κ` (`unpackT`), `tvar 0`; every type in
the context moves up one. -/
def pushT (cx : Cx) (κ : Kind) : Cx :=
  { cx with
    ke    := some κ :: cx.ke
    opq   := 0 :: cx.opq.map (· + 1)
    vars  := cx.vars.map fun (x, t, b) => (x, t.shiftT 0, b)
    torn  := cx.torn.map fun tn => { tn with ty := tn.ty.shiftT 0 }
    ret   := cx.ret.shiftT 0 }

def norm (cx : Cx) (i : Idx) : Option Lin := CoreTerm.norm cx.facts (cx.facts.length + 1) i

def eqI (cx : Cx) (a b : Idx) : Bool :=
  a == b || match cx.norm a, cx.norm b with
            | some x, some y => x == y
            | _, _ => false

/-- The constant an index is under the facts, if it is one. -/
def constIdx (cx : Cx) (j : Idx) : M Nat :=
  match cx.norm j with
  | some l => if l.coefs.isEmpty then pure l.const else throw "the index is not a known constant"
  | none => throw "the index is not a known constant"

/-- `a ≤ b` under the facts.  Sound, not complete: no case splits. -/
def leI (cx : Cx) (a b : Idx) : Bool :=
  a == b || match cx.norm a, cx.norm b with
            | some x, some y => Lin.leB x y
            | _, _ => false

def ltI (cx : Cx) (a b : Idx) : Bool := cx.leI (.add a (.lit 1)) b

def find (cx : Cx) (x : String) : M (Ty × Bool) :=
  match cx.vars.find? (·.1 == x) with
  | some (_, t, b) => pure (t, b)
  | none => throw s!"unbound variable {x}"

/-- The type of an atom, without using it up. -/
def peek (cx : Cx) : At → M Ty
  | .lit n => pure (.intS (.lit n))
  | .unit  => pure .unit
  | .var x => do
      let (t, b) ← cx.find x
      if !b then throw s!"{x} was already used (affine)"
      pure t

/-- The type of an atom, using it up if it is affine. -/
def use (cx : Cx) (a : At) : M (Ty × Cx) := do
  let t ← cx.peek a
  match a with
  | .var x =>
      if affine cx.ke t then
        pure (t, { cx with vars := cx.vars.map fun (y, u, b) => if y == x then (y, u, false) else (y, u, b) })
      else pure (t, cx)
  | _ => pure (t, cx)

/-- Every opaque type variable is guarded in `t`. -/
def opaqueOK (cx : Cx) (t : Ty) : Bool := cx.opq.all fun k => t.guardT k

def bind (cx : Cx) (x : String) (t : Ty) : M Cx := do
  if cx.vars.any (·.1 == x) || cx.torn.any (·.x == x) then
    throw s!"{x} is already bound (no shadowing)"
  if !cx.opaqueOK t then
    throw s!"{x} would hold a value whose layout depends on an unpacked type"
  if !t.arrFree then
    throw s!"{x} would hold an array by value (an array lives behind a Loc)"
  pure { cx with vars := (x, t, true) :: cx.vars }

def posOf (n : String) : List String → Nat → Option Nat
  | [], _ => none
  | m :: ms, i => if m == n then some i else posOf n ms (i + 1)

def idx (cx : Cx) (n : String) : M Idx :=
  match posOf n cx.inames 0 with
  | some i => pure (.var i)
  | none   => throw s!"unbound index variable {n}"

def hasTok (cx : Cx) (r : Idx) : Bool :=
  cx.vars.any fun (_, t, b) => b && match tokRgn t with
    | some s => cx.eqI r s
    | none => false

/-- A live epoch token `Tok[r, P, e]`.  Affine, and used by looking, not by
consuming: one token fences every write of its epoch. -/
def hasTokE (cx : Cx) (r : Idx) (P : ECounter) (e : Idx) : Bool :=
  cx.vars.any fun (_, t, b) => b && match t with
    | .tokE r' Q e' => cx.eqI r r' && Q == P && cx.eqI e e'
    | _ => false

/-- A live read share of `r`. -/
def isShareOf (cx : Cx) (r : Idx) : String × Ty × Bool → Bool
  | (_, .share s, true) => cx.eqI r s
  | _ => false

def hasShare (cx : Cx) (r : Idx) : Bool := cx.vars.any (cx.isShareOf r)

def shareOf (cx : Cx) (r : Idx) : Option String := (cx.vars.find? (cx.isShareOf r)).map (·.1)

/-- A capability for `r`; with `w`, one that licenses writes. -/
def isCapOf (cx : Cx) (r : Idx) (w : Bool) : String × Ty × Bool → Bool
  | (_, .cap c q, true) => cx.eqI r q && (!w || c.writes)
  | _ => false

def hasCap (cx : Cx) (r : Idx) (w : Bool) : Bool := cx.vars.any (cx.isCapOf r w)

/-- A `bor` capability for `r`: lent from a token, so this thread's alone. -/
def isBorOf (cx : Cx) (r : Idx) : String × Ty × Bool → Bool
  | (_, .cap c q, true) => c == .bor && cx.eqI r q
  | _ => false

def hasBor (cx : Cx) (r : Idx) : Bool := cx.vars.any (cx.isBorOf r)

/-- Keep `e` iff the first entry named `e.1` is not second-class (on a context without
shadowing, which `bind` guarantees, this is just `!e.2.1.secondClass`). -/
def firstOK (vars : List (String × Ty × Bool)) (e : String × Ty × Bool) : Bool :=
  match vars.find? (·.1 == e.1) with
  | some e0 => !e0.2.1.secondClass
  | none => true

/-- `endBorrow y`: `y` is live again, and every second-class capability goes
(conservatively, whatever its region).  An entry goes iff the first entry under its name is
second-class (`firstOK`); without shadowing, which `bind` guarantees, that is every
second-class entry. -/
def endCx (cx : Cx) (y : String) : Cx :=
  { cx with
    lent := cx.lent.erase y
    vars := (cx.vars.filter (firstOK cx.vars)).map fun (z, t, b) =>
      if z == y then (z, t, true) else (z, t, b) }

def sealedR (cx : Cx) (r : Idx) : Bool := !cx.unsealed.any (cx.eqI r ·)

end Cx

/-- The regions whose tokens a value carries, outside every binder. -/
def toksOf : Ty → List Idx
  | .tok r _     => [r]
  | .tok2 r _ _ _ => [r]
  | .prod a b    => toksOf a ++ toksOf b
  | .sum a b     => toksOf a ++ toksOf b
  | .refine t _  => toksOf t
  | _            => []

/-- §4.4 rule 7 across code blocks.  `unsealed` is local to a block, so a token
for a region taken from an observable state may not leave it — by `ret`, a
call, or `pack` — before `fence st`: the receiver would write without the
fence. -/
def noLeak (cx : Cx) (t : Ty) : M Unit :=
  if (toksOf t).any (fun r => !cx.sealedR r) then
    throw "a token leaves its code block before fence st (§4.4 rule 7)"
  else pure ()

/-- The false branch of `s·u = 0`: then `u ≥ 1`, so `u = u' + 1` for a fresh
`u'`.  An equality fact, so the facts stay equalities. -/
def nzCx (cx : Cx) (u : Nat) : Cx :=
  let c := cx.push "_nz"
  { c with facts := (u + 1, .add (.var 0) (.lit 1)) :: c.facts }

/-- `ifeq`'s true branch when one side is `(s+1)·u` and the other `0`: `u = 0`. -/
def zeroVar (ni nj : Lin) : Option Nat :=
  if nj == .ofConst 0 then ni.zeroVar? else if ni == .ofConst 0 then nj.zeroVar? else none

/-- The context for `ifeq`'s false branch, given the operands' normal forms. -/
def noCx (cx : Cx) (ni nj : Lin) : Cx :=
  if nj == .ofConst 0 then
    match ni.single? with | some (u, _) => nzCx cx u | none => cx
  else if ni == .ofConst 0 then
    match nj.single? with | some (u, _) => nzCx cx u | none => cx
  else cx

def ieqD (cx : Cx) (d : Nat) (i j : Idx) : Bool := i == j || (d == 0 && cx.eqI i j)

def meqD (cx : Cx) (d : Nat) : Mode → Mode → Bool
  | .own, .own => true
  | .pub, .pub => true
  | .rgn r, .rgn s => ieqD cx d r s
  | _, _ => false

/-- Two `ini` refinements with equal bounds (other predicates: syntactically). -/
def iniEq (cx : Cx) (d : Nat) : Pred → Pred → Bool
  | .ini i, .ini j => ieqD cx d i j
  | _, _ => false

/-- Type equality, using the facts for index terms outside every binder and
syntax under them.  Conservative: it can only fail to equate. -/
def tyEq (cx : Cx) : Nat → Ty → Ty → Bool
  | d, .intS i, .intS j => ieqD cx d i j
  | d, .prod a b, .prod a' b' => tyEq cx d a a' && tyEq cx d b b'
  | d, .sum a b, .sum a' b' => tyEq cx d a a' && tyEq cx d b b'
  | d, .code a b k, .code a' b' k' => k == k' && tyEq cx d a a' && tyEq cx d b b'
  | d, .array i t, .array j u => ieqD cx d i j && tyEq cx d t u
  | d, .ptr μ t, .ptr ν u => meqD cx d μ ν && tyEq cx d t u
  | d, .ptrOpt μ t, .ptrOpt ν u => meqD cx d μ ν && tyEq cx d t u
  | d, .loc μ t, .loc ν u => meqD cx d μ ν && tyEq cx d t u
  | d, .word r P, .word s Q => ieqD cx d r s && P == Q
  | d, .word2 r P, .word2 s Q => ieqD cx d r s && P == Q
  | d, .tok2 r P i j, .tok2 s Q i' j' => ieqD cx d r s && P == Q && ieqD cx d i i' && ieqD cx d j j'
  | d, .epair r P, .epair s Q => ieqD cx d r s && P == Q
  | d, .tokE r P e, .tokE s Q e' => ieqD cx d r s && P == Q && ieqD cx d e e'
  | d, .share r, .share s => ieqD cx d r s
  | d, .cap c r, .cap c' s => c == c' && ieqD cx d r s
  | d, .tok r i, .tok s j => ieqD cx d r s && match i, j with
      | none, none => true
      | some (P, a), some (Q, b) => P == Q && ieqD cx d a b
      | _, _ => false
  | d, .mu t, .mu u => tyEq cx d t u
  | d, .tex κ t, .tex κ' u => κ == κ' && tyEq cx d t u
  | d, .iall t, .iall u => tyEq cx (d + 1) t u
  | d, .iex t, .iex u => tyEq cx (d + 1) t u
  | d, .refine t ψ, .refine u χ => (ψ == χ || iniEq cx d ψ χ) && tyEq cx d t u
  | _, a, b => a == b

/-- Subsumption: `Int(i) ≤ Int`, refinements may be forgotten.  (An `own`
reference no longer coerces to a region reference: `intoRgn` does that, with
its fence — D1.) -/
def sub (cx : Cx) (σ τ : Ty) : Bool :=
  tyEq cx 0 σ τ ||
  match σ, τ with
  | .intS _, .int => true
  -- §3.7: knowing more slots initialised is a subtype of knowing fewer.
  | .refine t (.ini i), .refine u (.ini j) =>
      (tyEq cx 0 t u && cx.leI j i) || sub cx t (.refine u (.ini j))
  | .refine t _, u => sub cx t u
  | .ptr μ t, .ptrOpt ν u => meqD cx 0 μ ν && tyEq cx 0 t u
  | .prod a b, .prod a' b' => sub cx a a' && sub cx b b'
  | .sum a b, .sum a' b' => sub cx a a' && sub cx b b'
  | .cap c r, .cap c' s => c.le c' && ieqD cx 0 r s
  -- (M1, T1) a restricted function is a plain function, and fits a larger budget slot
  | .code a b (.restricted _ _), .code a' b' .plain => tyEq cx 0 a a' && tyEq cx 0 b b'
  | .code a b (.restricted f s), .code a' b' (.restricted f' s') =>
      decide (f ≤ f') && decide (s ≤ s') && tyEq cx 0 a a' && tyEq cx 0 b b'
  | _, _ => false

/-- An integer type of unknown index (`Int`). -/
def plainIntT (t : Ty) : Bool :=
  match intOf t with
  | some none => true
  | _ => false

/-- (E1) `ThreadId`. -/
def tidOf : Ty → Bool
  | .tid => true
  | _ => false

/-- `ifeq` on plain integers: both operands integers, at least one of unknown
index; or (E1) two `ThreadId`s.  Nothing can be recorded, so both branches see the
context unchanged. -/
def plainEq (cx : Cx) (a b : At) : Bool :=
  match cx.peek a, cx.peek b with
  | .ok ta, .ok tb =>
      ((intOf ta).isSome && (intOf tb).isSome && (plainIntT ta || plainIntT tb)) || (tidOf ta && tidOf tb)
  | _, _ => false

/-- An ordered observation `Saw(w, m)` of word `w` with `m + 1 = j`: what
`claim` needs of the owner word for ticket `j`. -/
def sawFor (cx : Cx) (w : String) (j : Idx) : Option Idx :=
  (cx.saws.find? fun p => p.1 == w && p.2.2 && cx.eqI (.add p.2.1 (.lit 1)) j).map (·.2.1)

def intIdx (cx : Cx) (a : At) : M Idx := do
  match intOf (← cx.peek a) with
  | some (some i) => pure i
  | _ => throw "expected an integer of known index"

def classifyM (cx : Cx) (P : Proto) (i : Idx) : M (Nat × Lin) := do
  let a ← match cx.norm i with
    | some a => pure a
    | none => throw "index outside the decidable fragment"
  match classify P a with
  | some m => pure m
  | none => throw "the value is in no single state of the protocol (is its parity known?)"

def clauseM (P : Proto) (c : Nat) : M Clause :=
  match P.clauses[c]? with
  | some cl => pure cl
  | none => throw "no such state"

def classify2M (cx : Cx) (P : Proto2) (i0 i1 : Idx) : M (Nat × Lin × Lin) := do
  let a0 ← match cx.norm i0 with
    | some a => pure a
    | none => throw "index outside the decidable fragment"
  let a1 ← match cx.norm i1 with
    | some a => pure a
    | none => throw "index outside the decidable fragment"
  match classify2 P a0 a1 with
  | some m => pure m
  | none => throw "the pair is in no single state of the protocol (is the relation between its halves known?)"

def clause2M (P : Proto2) (c : Nat) : M Clause2 :=
  match P.clauses[c]? with
  | some cl => pure cl
  | none => throw "no such state"

/-- The taken tokens a value carries, through every binder: protocol and state.
`d` is the number of index binders passed; a state that mentions one of them has
no name outside the value and is reported as `none` (a token in an existential
package, say `Tok[a, Lock, k]` under `∃a`), otherwise it is lowered to the
outside.  A packed handle is still a handle: without this a token could be
dropped by packing it first. -/
def takenOf (d : Nat) : Ty → List (Proto × Option Idx)
  | .tok _ (some (P, i)) =>
      [(P, if (List.range d).any i.mentions then none
           else some ((List.range d).foldl (fun j _ => j.lower 0) i))]
  | .prod a b | .sum a b => takenOf d a ++ takenOf d b
  | .refine t _ | .mu t | .tex _ t => takenOf d t
  | .iall t | .iex t => takenOf (d + 1) t
  | _ => []

/-- A state the protocol can leave: a transition or a wild move from clause `c`. -/
def exits (P : Proto) (c : Nat) : Bool :=
  P.trans.any (·.1 == c) || P.wild.any (·.1 == c)

/-- A token is *linear* when its region can be given back — its state has a
move out — and then a block may not end (`ret`, `tail`) still holding it: it
must be consumed, by a release, a store into memory, a return, or a call.  A
token whose state is terminal (a claim), and a fresh region's `Tok[r]`, are
affine: there is nothing to give back, as with own memory.  A token is held if
its variable is live, or lent (`borrow` without `endBorrow`); tokens in pairs,
sums and packages all count.  A state the context cannot classify, or cannot
name (it mentions a packed index), is taken to be linear.  The machine does not need any of this (a dropped token
only leaves a region held for ever), so the rule is not part of `Typed`: it is
a liveness check, not a safety one. -/
def linear (cx : Cx) (s : Proto × Option Idx) : Bool :=
  match s.2 with
  | none => true
  | some i =>
    match classifyM cx s.1 i with
    | .ok (c, _) => exits s.1 c
    | .error _ => true

/-- `takenOf` for pair tokens. -/
def taken2Of (d : Nat) : Ty → List (Proto2 × Option (Idx × Idx))
  | .tok2 _ P i j =>
      let low (i : Idx) : Idx := (List.range d).foldl (fun j _ => j.lower 0) i
      [(P, if (List.range d).any i.mentions || (List.range d).any j.mentions then none
           else some (low i, low j))]
  | .prod a b | .sum a b => taken2Of d a ++ taken2Of d b
  | .refine t _ | .mu t | .tex _ t => taken2Of d t
  | .iall t | .iex t => taken2Of (d + 1) t
  | _ => []

def linear2 (cx : Cx) (s : Proto2 × Option (Idx × Idx)) : Bool :=
  match s.2 with
  | none => true
  | some (i, j) =>
    match classify2M cx s.1 i j with
    | .ok (c, _, _) => exits2 s.1 c
    | .error _ => true

def noDrop (cx : Cx) : M Unit :=
  match cx.vars.find? (fun (y, t, b) =>
      (b || cx.lent.contains y) &&
      ((takenOf 0 t).any (linear cx) || (taken2Of 0 t).any (linear2 cx))) with
  | some (y, _, _) => throw s!"{y} still holds a token at the block's end (a token that can be given back must be)"
  | none => pure ()

/-- The first success of `f` along `l`; otherwise the last failure's reason
(`why` if there was none).  A loop-free `for … return`, so that proofs about
the checker can induct on it. -/
def firstOk {α β : Type} (f : α → M β) : List α → String → M β
  | [], why => throw why
  | a :: as, _ =>
      match f a with
      | .ok b => .ok b
      | .error why => firstOk f as why

/-- Whether this observation `(w, s, ordered)` licenses a torn read of `r`. -/
def licenceOf (cx : Cx) (r : Idx) : String × Idx × Bool → M (String × Idx)
  | (w, s, _) => do
      let (t, _) ← cx.find w
      match wordOf t with
      | none => throw "torn read: the observation is not of a protocol word"
      | some (r', P) =>
          if !cx.eqI r r' then throw "torn read: the observation is of another region's word"
          else if !monotone P then
            throw "torn read: the protocol has no version measure (§4.4 rule 6)"
          else match classifyM cx P s with
            | .ok (c, _) =>
                match P.clauses[c]? with
                | some cl =>
                    if cl.holds then pure (w, s)
                    else throw "torn read: the observed state does not hold the region"
                | none => throw "no such state"
            | .error _ => throw "torn read: the observed state is not determined (is its parity known?)"

/-- §4.4 rule 2: which observation, if any, licenses a torn read of region `r`.
The reasons are distinct so that each rejected program says why. -/
def tornLicence (cx : Cx) (r : Idx) : M (String × Idx) := do
  let onR := cx.saws.filter fun (w, _, _) =>
    match cx.vars.find? (·.1 == w) with
    | some (_, t, _) => match wordOf t with
        | some (r', _) => cx.eqI r r'
        | none => false
    | none => false
  if onR.isEmpty then
    throw "load from a region without its token, and no observation of its word"
  let ordered := onR.filter (·.2.2)
  if ordered.isEmpty then
    throw "torn read: the observation is not ordered before it (load[acq], or fence ld)"
  firstOk (licenceOf cx r) ordered ""

def phaseFence : Phase → Phase
  | .opn => .fenced
  | p => p

def Prog.find (p : Prog) (f : String) : M Decl :=
  match p.find? (·.name == f) with
  | some d => pure d
  | none => throw s!"no code block {f}"

/-! ### Instantiating type parameters (§3.11, row 18: prenex, kinded) -/

def shiftTN : Nat → Ty → Ty
  | 0, t => t
  | n + 1, t => Ty.shiftT 0 (shiftTN n t)

def shiftIN : Nat → Ty → Ty
  | 0, t => t
  | n + 1, t => Ty.shiftI 0 (shiftIN n t)

/-- Replace type variables `0 … n-1` by `σs` (`σs[0]` for variable 0) at once,
having crossed `c` type binders and `d` index binders.  Simultaneous, so a
`σ` that mentions the caller's own type variables is not substituted into. -/
def substTs (σs : List Ty) (c d : Nat) : Ty → Ty
  | .tvar k      => if k < c then .tvar k else
                      match σs[k - c]? with
                      | some σ => shiftIN d (shiftTN c σ)
                      | none   => .tvar (k - σs.length)
  | .prod a b    => .prod (substTs σs c d a) (substTs σs c d b)
  | .sum a b     => .sum (substTs σs c d a) (substTs σs c d b)
  | .code a b k  => .code (substTs σs c d a) (substTs σs c d b) k
  | .array i t   => .array i (substTs σs c d t)
  | .ptr μ t     => .ptr μ (substTs σs c d t)
  | .ptrOpt μ t  => .ptrOpt μ (substTs σs c d t)
  | .loc μ t     => .loc μ (substTs σs c d t)
  | .mu t        => .mu (substTs σs (c + 1) d t)
  | .tex κ t     => .tex κ (substTs σs (c + 1) d t)
  | .iall t      => .iall (substTs σs c (d + 1) t)
  | .iex t       => .iex (substTs σs c (d + 1) t)
  | .refine t ψ  => .refine (substTs σs c d t) ψ
  | t            => t

/-- §3.11's `Kind.admits`, open: `σ` may mention the caller's own type
parameters, which answer from their kinds.  This is the check at every use of
a prenex `∀(α : κ)`. -/
def admitsIn (cx : Cx) (κ : Kind) (σ : Ty) : Bool :=
  let ke := cx.ke
  (σ.wf ke.length cx.inames.length && σ.arrFree) && Ty.sharedOKIn ke σ && !σ.secondClass &&
  (!κ.zero   || zeroableIn [] ke σ) &&
  (!κ.insens || !Ty.sensitiveIn ke σ) &&
  (!κ.share  || Ty.coupledOKIn ke σ) &&
  (!κ.noOwn  || Ty.noOwnIn ke σ) &&
  (!κ.copy   || !Ty.affineIn ke σ) &&
  (!κ.noWord || Ty.wordFreeIn ke σ) &&
  match σ with
  | .tvar k => match ke[k]? with
      | some (some κ') => κ'.atom.implies κ.atom
      | _ => false
  | _ => κ.atom.holds (σ.width.bind Idx.closed)

/-- The callee's signature at these index and type arguments.  Index
parameters first: after `instT` the signature is in the caller's index scope,
which is the scope the type arguments were written in. -/
def instantiate (cx : Cx) (d : Decl) (is : List String) (ts : List Ty := []) :
    M (Ty × Ty) := do
  if is.length != d.idx.length then throw s!"{d.name}: wrong number of index arguments"
  if ts.length != d.tparams.length then throw s!"{d.name}: wrong number of type arguments"
  for (κ, σ) in d.tparams.zip ts do
    if !admitsIn cx κ σ then
      throw s!"{d.name}: a type argument does not have its parameter's kind"
    -- An instance is laid out at its type arguments; an unpacked type has none.
    if !cx.opaqueOK σ then
      throw s!"{d.name}: a type argument exposes an unpacked type"
  let us ← is.mapM cx.idx
  let σs := ts.reverse
  pure (substTs σs 0 0 (instT us.reverse 0 d.argTy), substTs σs 0 0 (instT us.reverse 0 d.retTy))

/-- D1: what a region cell may hold.  No `own` reference (the cell is shared
memory whose writes the token gates; an `own` reference inside it would be read
out without the fence that hides its placeholders), and shareable inside, as
behind `publish`.  Unlike `publish`, no `coupledOK` at the top: a type variable
needs only `noOwn`, not `share`. -/
def rgnCellOK (ke : KEnv) (u : Ty) : Bool := Ty.noOwnIn ke u && Ty.sharedOKIn ke u

/-- `Buf μ τ n k`, which is `{ν : Loc μ (Array n τ) | ini ν ≥ k}` (§3.7). -/
def bufOf : Ty → Option (Mode × Idx × Ty × Idx)
  | .refine (.loc μ (.array n τ)) (.ini k) => some (μ, n, τ, k)
  | _ => none

/-- `fold`'s check: a reference to one unrolling of the μ-type `τ` targets. -/
def foldOk (cx : Cx) : Ty → Ty → Bool
  | .ptr μ u, .ptr ν (.mu s)       => meqD cx 0 μ ν && tyEq cx 0 u (unfold1 (.mu s))
  | .ptrOpt μ u, .ptrOpt ν (.mu s) => meqD cx 0 μ ν && tyEq cx 0 u (unfold1 (.mu s))
  | .loc μ u, .loc ν (.mu s)       => meqD cx 0 μ ν && tyEq cx 0 u (unfold1 (.mu s))
  | _, _ => false

/-- What `borrow s` lends from a value of this type: its region. -/
def lendOf (cx : Cx) (c : Cap) : Ty → M Idx
  | .tok r _ | .tok2 r _ _ _ =>
      match c with
      | .pub => throw "borrow lends bor or rd, not pub"
      | .bor => if cx.sealedR r then pure r
                else throw "borrow: the region is waiting for fence st (§4.4 rule 7)"
      | .rd => pure r
      | .frz => throw "borrow lends bor or rd, not frz: freeze makes frz"
  | .share r =>
      match c with
      | .rd => pure r
      | _ => throw "borrow: a read share lends only rd"
  | _ => throw "borrow needs a token or a read share"

def codeOf : Ty → Option (Ty × Ty)
  | .code σ τ _ => some (σ, τ)
  | _ => none

def varOf : At → M String
  | .var y => pure y
  | _ => throw "expected a variable"

/-- The cell type a plain `cas` works on: a `pub` cell, or a region cell under a
capability that writes. -/
def casCellTy (cx : Cx) (tw : Ty) : M Ty :=
  match cellOf tw with
  | some (.pub, u) => pure u
  | some (.rgn r, u) =>
      if cx.hasCap r true then pure u else throw "cas on a region cell needs a capability that writes"
  | _ => throw "cas needs a protocol word or a pub cell"

/-- Why a plain store or exchange is refused at a cell that may hold a word. -/
def wordCellMsg : String :=
  "a plain store or exchange into a cell that may hold a protocol word (a type variable there needs kind noWord or copy)"

/-- The cell an `xchg` works on, as (the type a new value may have, the type
of what comes out).  `xchg` is a plain load then store, so the cell must be
held exclusively: an own cell, or a region cell under its sealed token or a
`bor` capability.  Not published memory, nor a `pub` capability: two racing
exchanges would both take the old value, duplicating an affine one. -/
def xchgCell (cx : Cx) (t : Ty) : M (Ty × Ty) :=
  match wordOf t with
  | some _ => throw "xchg on a protocol word: use store or cas"
  | none =>
  match cellOf t with
  | some (.own, u) =>
      if !Ty.wordFreeIn cx.ke u then throw wordCellMsg else pure (u, u)
  | some (.rgn r, u) =>
      if !Ty.wordFreeIn cx.ke u then throw wordCellMsg else
      -- What comes out is `adapt r u`: an `own` cell in a region may hold a
      -- region alias (F2).  A type variable could be `own` at an instance,
      -- where `adapt` would not see it, so it must be `noOwn`.
      if !Ty.noOwnIn cx.ke (adapt r u) then
        throw "xchg in a region: a type variable that may be own could come out as an alias"
      else if (cx.hasTok r && cx.sealedR r) || cx.hasBor r then pure (u, adapt r u)
      else throw "xchg on a region cell needs its sealed token or a bor capability"
  | some (.pub, _) => throw "xchg on published memory: racing exchanges would duplicate the old value"
  | none => throw "xchg needs a reference"

/-- A tail call `tail f is a ts` (the rule of `check`'s `.tail`; also the callee check of `spawn`). -/
def tailCheck (p : Prog) (cx : Cx) (f : String) (is : List String) (a : At) (ts : List Ty) : M Unit := do
      let d ← p.find f
      let (at_, rt) ← instantiate cx d is ts
      let (t, cx) ← cx.use a
      noLeak cx t
      noDrop cx
      if !sub cx t at_ then throw s!"tail call {f}: argument type mismatch"
      if !sub cx rt cx.ret then throw s!"tail call {f}: return type mismatch"

/-- The rule for one operation: the context after `let x = op`. -/
def checkOp (p : Prog) (cx : Cx) (x : String) : Op → M Cx
  | .atom a => do
      let (t, cx) ← cx.use a
      cx.bind x t
  | .pair a b => do
      let (t, cx) ← cx.use a
      let (u, cx) ← cx.use b
      cx.bind x (.prod t u)
  | .inl τ a => do
      if !τ.wf cx.ke.length 0 then throw "inl: the other arm must be closed"
      let (t, cx) ← cx.use a
      cx.bind x (.sum t τ)
  | .inr τ a => do
      if !τ.wf cx.ke.length 0 then throw "inr: the other arm must be closed"
      let (t, cx) ← cx.use a
      cx.bind x (.sum τ t)
  | .add a b => do
      let t ← cx.peek a
      let u ← cx.peek b
      match intOf t, intOf u with
      | some (some i), some (some j) => cx.bind x (.intS (.add i j))
      | some _, some _ => cx.bind x .int
      | _, _ => throw "add needs integers"
  | .sub a b => do
      -- No wrap-around: the difference must be provably nonnegative, and is then
      -- a linear form again (`toIdx`), so no `Idx.sub` reaches the facts.
      let t ← cx.peek a
      let u ← cx.peek b
      match intOf t, intOf u with
      | some (some i), some (some j) =>
          match cx.norm i, cx.norm j with
          | some ni, some nj =>
              if Lin.leB nj ni then cx.bind x (.intS (ni.diff nj).toIdx)
              else throw "sub: the difference is not provably nonnegative"
          | _, _ => throw "sub: index outside the decidable fragment"
      | _, _ => throw "sub needs integers of known value"
  | .new a => do
      let (t, cx) ← cx.use a
      if t.secondClass then throw "new: a second-class capability cannot be stored"
      cx.bind x (.ptr .own t)
  | .publish a => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u =>
          if Ty.sharedOKIn cx.ke (.ptr .pub u) then cx.bind x (.ptr .pub u)
          else throw "publish: the target is not shareable (rows 16, 17)"
      | .refine (.loc .own (.array n u)) (.ini k) =>
          if Ty.sharedOKIn cx.ke (.loc .pub (.array n u)) then
            cx.bind x (.refine (.loc .pub (.array n u)) (.ini k))
          else throw "publish: the target is not shareable (rows 16, 17)"
      | _ => throw "publish needs an own reference"
  | .intoRgn rn a => do
      -- `publish` with a region-mode result: the fence hides the placeholders,
      -- the region's token gates every later write.  No token is needed here.
      let r ← cx.idx rn
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u =>
          if rgnCellOK cx.ke u then cx.bind x (.ptr (.rgn r) u)
          else throw "intoRgn: the target is not shareable (rows 16, 17): build it inside the region"
      | .refine (.loc .own (.array n u)) (.ini k) =>
          if rgnCellOK cx.ke (.array n u) then
            cx.bind x (.refine (.loc (.rgn r) (.array n u)) (.ini k))
          else throw "intoRgn: the target is not shareable (rows 16, 17): build it inside the region"
      | _ => throw "intoRgn needs an own reference or an own buffer"
  | .newBuf n τ => do
      if !τ.wf cx.ke.length cx.inames.length then throw "newBuf: the element type is not well formed"
      if τ.secondClass then throw "newBuf: a second-class capability cannot be stored"
      if !cx.opaqueOK τ then throw "newBuf: the slots' layout depends on an unpacked type"
      if !τ.arrFree then throw "newBuf: a slot cannot hold an array by value (an array lives behind a Loc)"
      let k ← intIdx cx n
      let ini : Idx := if zeroableIn [] cx.ke τ then k else .lit 0
      cx.bind x (.refine (.loc .own (.array k τ)) (.ini ini))
  | .idx b i => do
      let t ← cx.peek b
      let (μ, n, u, k) ← match bufOf t with
        | some c => pure c
        | none => throw "idx needs a buffer"
      let j ← intIdx cx i
      if !cx.ltI j n then throw "idx: the index is not provably below the capacity"
      if !cx.ltI j k then throw "idx: the slot is not provably initialised"
      -- T3c-5 D4: the slot's address is `j * size u`, computed from the runtime
      -- type, where an unpacked witness is erased: `u` must not depend on one.
      if !cx.opaqueOK u then throw "idx: the slots' layout depends on an unpacked type"
      -- As with `fld`: a locative into an `own` buffer is a second owner.
      let cx ← if μ == .own then (·.2) <$> cx.use b else pure cx
      cx.bind x (.loc μ u)
  | .bufInit b i v => do
      let (t, cx) ← cx.use b
      let (n, u, k) ← match bufOf t with
        | some (.own, n, u, k) => pure (n, u, k)
        | some _ => throw "bufInit needs an own buffer"
        | none => throw "bufInit needs a buffer"
      let j ← intIdx cx i
      if !cx.eqI j k then throw "bufInit: the slot is not the next uninitialised one"
      if !cx.ltI k n then throw "bufInit: the buffer is full"
      let (tv, cx) ← cx.use v
      if !sub cx tv u then throw "bufInit: the value does not have the element type"
      cx.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
  | .null μ τ => do
      let t := Ty.ptrOpt μ τ
      if !t.wf cx.ke.length cx.inames.length then throw "null: the target is not well formed"
      cx.bind x t
  | .fold a τ => do
      if !τ.wf cx.ke.length cx.inames.length then throw "fold: the target is not well formed"
      let (t, cx) ← cx.use a
      if foldOk cx t τ then cx.bind x τ
      else throw "fold: the reference's target is not one unrolling of the μ-type"
  | .fld i a => do
      let t ← cx.peek a
      let (μ, u) ← match cellOf t with
        | some c => pure c
        | none => throw "fld needs a reference"
      let (c1, c2) ← match unfold1 u with
        | .prod c1 c2 => pure (c1, c2)
        | _ => throw "fld needs a reference to a pair"
      -- T3c-5 D4: field 1 sits after field 0, whose size is computed from the
      -- runtime type, where an unpacked witness is erased.
      if !(i == 0 || cx.opaqueOK c1) then
        throw "fld: the field's offset depends on an unpacked type"
      -- A locative into an `own` allocation is a second owner: it uses the first up.
      let cx ← if μ == .own then (·.2) <$> cx.use a else pure cx
      cx.bind x (.loc μ (if i == 0 then c1 else c2))
  | .load acq a => do
      let t ← cx.peek a
      match wordOf t, a with
      | some (_, P), .var w =>
          if P.ghost then throw "a ghost word has no runtime value to load"
          -- Observing a protocol word: a fresh index for its value, and
          -- `Saw(w, n)`.  It is also the re-check of every fenced torn read on `w`.
          let cx := cx.push x
          let n : Idx := .var 0
          let cx := { cx with
            saws := (w, n, acq) :: cx.saws
            torn := cx.torn.map fun (tn : Torn) =>
              if tn.w == w && tn.φ == Phase.fenced then { tn with φ := .rechecked n } else tn }
          cx.bind x (.intS n)
      | some _, _ => throw "a protocol word must be named by a variable"
      | none, _ =>
      match cellOf t with
      | none => throw "load needs a reference"
      | some (.own, u) =>
          if affine cx.ke u then throw "load would duplicate an affine value" else cx.bind x u
      | some (.pub, u) =>
          if affine cx.ke u then throw "load would duplicate an affine value"
          else if Ty.sensitiveIn cx.ke u && !acq then throw "load: a view-sensitive type needs acq (§3.8)"
          else cx.bind x u
      | some (.rgn r, u) =>
          let u' := adapt r u
          if cx.hasTok r || cx.hasShare r then
            if affine cx.ke u' then throw "load would duplicate an affine value" else cx.bind x u'
          else if cx.hasCap r false then
            if Ty.sensitiveIn cx.ke u' && !acq then
              throw "load under a capability: a view-sensitive type needs acq (§3.8)"
            else if affine cx.ke u' then throw "load would duplicate an affine value"
            else cx.bind x u'
          else do
            let (w, s) ← tornLicence cx r
            if cx.vars.any (·.1 == x) || cx.torn.any (·.x == x) then
              throw s!"{x} is already bound (no shadowing)"
            pure { cx with torn := ⟨x, u', w, s, .opn⟩ :: cx.torn }
  | .store rel a v tok => do
      let t ← cx.peek a
      match wordOf t with
      | some (r, P) =>
          let tk ← match tok with
            | some tk => pure tk
            | none => throw "a store to a protocol word needs the region's token"
          let (tt, cx) ← cx.use tk
          -- The new token keeps the old one's region index, not the word's: the
          -- two are equal, but `unsealed` is keyed by the token's, and a token
          -- re-indexed here would leave it (CoreTyping's `HoldsSealed`).
          let (r', i) ← match tt with
            | .tok r' (some (Q, i)) =>
                if !cx.eqI r r' then throw "the token is for another region"
                else if Q != P then throw "the token is for another protocol"
                else pure (r', i)
            | _ => throw "a store to a protocol word needs a taken token"
          let j ← intIdx cx v
          let (c, k) ← classifyM cx P i
          let (c', k') ← classifyM cx P j
          let cl ← clauseM P c
          let cl' ← clauseM P c'
          if cl.holds then throw "store from a shared state: use cas"
          if !pstep P c k c' k' then throw "not a transition of the protocol"
          if cl'.holds then
            if !rel && !P.ghost then throw "giving the region back needs rel"
            cx.bind x .unit
          else if P.ticket then
            -- The ticket lock's release: the next state is held by the next
            -- ticket's holder, who claims it on seeing this store.
            if !rel then throw "handing the lock on needs rel"
            cx.bind x .unit
          else cx.bind x (.tok r' (some (P, j)))
      | none =>
      match cellOf t with
      | none => throw "store needs a reference"
      | some (μ, u) => do
          if !Ty.wordFreeIn cx.ke u then throw wordCellMsg
          let (tv, cx) ← cx.use v
          match μ with
          | .own =>
              if sub cx tv u then cx.bind x .unit else throw "store: the value does not have the cell's type"
          | .pub =>
              if !sub cx tv u then throw "store: the value does not have the cell's type"
              else if Ty.sensitiveIn cx.ke u && !rel then throw "store: a view-sensitive type needs rel (§3.8)"
              else cx.bind x .unit
          | .rgn r =>
              if cx.hasTok r then
                if !cx.sealedR r then
                  throw "store into a region taken from an observable state before fence st (§4.4 rule 7)"
                else if sub cx tv u || sub cx tv (adapt r u) then cx.bind x .unit
                else throw "store: the value does not have the cell's type"
              else if cx.hasCap r true then
                if Ty.sensitiveIn cx.ke u && !rel then
                  throw "store under a capability: a view-sensitive type needs rel (§3.8)"
                else if sub cx tv u || sub cx tv (adapt r u) then cx.bind x .unit
                else throw "store: the value does not have the cell's type"
              else throw "store into a region without its token"
  | .fence f => do
      let cx := if f != .st then
          { cx with torn := cx.torn.map fun (tn : Torn) => { tn with φ := phaseFence tn.φ }
                    saws := cx.saws.map fun (w, s, _) => (w, s, true) }
        else cx
      let cx := if f != .ld then { cx with unsealed := [] } else cx
      cx.bind x .unit
  | .mkWord rn P v tk => do
      let r ← cx.idx rn
      if !pwf P then throw "the protocol is not well formed (states overlap, a move names no state, a lending state does not hold, a robust/norepeat/epoch claim fails, or a recovery target is not held -> shared)"
      let (tt, cx) ← cx.use tk
      match tt with
      | .tok r' none => if !cx.eqI r r' then throw "the token is for another region"
      | .tok _ (some _) => throw "a word is born from a fresh region token, not a taken one"
      | _ => throw "mkWord needs a region token"
      let j ← intIdx cx v
      let (c, _) ← classifyM cx P j
      let cl ← clauseM P c
      if P.ghost then
        -- Born taken: nothing at run time could arbitrate a later take.
        if cl.holds then throw "a ghost word is born in a state that does not hold its region"
        cx.bind x (.prod (.word r P) (.tok r (some (P, j))))
      else
        if !cl.holds then throw "a word is born in a state that holds its region"
        cx.bind x (.word r P)
  | .mkWord2 rn P v0 v1 tk => do
      let r ← cx.idx rn
      if !pwf2 P then throw "the pair protocol is not well formed (states overlap, a move names no state, or a robust/epoch claim fails)"
      let (tt, cx) ← cx.use tk
      match tt with
      | .tok r' none => if !cx.eqI r r' then throw "the token is for another region"
      | .tok _ (some _) => throw "a pair is born from a fresh region token, not a taken one"
      | _ => throw "mkWord2 needs a region token"
      let j0 ← intIdx cx v0
      let j1 ← intIdx cx v1
      let (c, _, _) ← classify2M cx P j0 j1
      let cl ← clause2M P c
      if !cl.holds then throw "a pair is born in a state that holds its region"
      cx.bind x (.word2 r P)
  | .ldp _ a n0 n1 => do
      let t ← cx.peek a
      if pairRef t then
        match a with
        | .var _ =>
            -- Observing a pair (a protocol pair or an epoch pair): two fresh
            -- indices, one per half.  No `Saw` and no torn-read re-check: a
            -- pair is read whole, in one single-copy-atomic access, and
            -- licenses no torn read (so taking it never needs §4.4 rule 7's
            -- fence either).
            let cx := (cx.push n0).push n1
            cx.bind x (.prod (.intS (.var 1)) (.intS (.var 0)))
        | _ => throw "a protocol pair must be named by a variable"
      else throw "ldp needs a reference to a protocol pair"
  | .stp rel a v0 v1 tok => do
      let t ← cx.peek a
      match word2Of t with
      | none => throw "stp needs a reference to a protocol pair"
      | some (r, P) =>
          let (tt, cx) ← cx.use tok
          let (r', i0, i1) ← match tt with
            | .tok2 r' Q i0 i1 =>
                if !cx.eqI r r' then throw "the token is for another region"
                else if Q != P then throw "the token is for another protocol"
                else pure (r', i0, i1)
            | _ => throw "a store to a protocol pair needs its taken token"
          let j0 ← intIdx cx v0
          let j1 ← intIdx cx v1
          let (c, k0, k1) ← classify2M cx P i0 i1
          let (c', k0', k1') ← classify2M cx P j0 j1
          let cl ← clause2M P c
          let cl' ← clause2M P c'
          if cl.holds then throw "stp from a shared state: use casp"
          if !pstep2 P c k0 k1 c' k0' k1' then throw "not a transition of the pair protocol"
          if cl'.holds then
            if !rel then throw "giving the region back needs rel"
            cx.bind x .unit
          else cx.bind x (.tok2 r' P j0 j1)
  | .mkEPair rn P v0 v1 => do
      -- An epoch pair holds nothing: it is a `pub` cell `(epoch, value)` whose
      -- writes are fenced by the epoch tokens of `Word[r, P]`.  No token is
      -- needed to make one, only that `P` is an epoch counter.
      let r ← cx.idx rn
      if !pwfE P then throw "mkEPair needs a well-formed epoch protocol"
      let _ ← intIdx cx v0
      let _ ← intIdx cx v1
      cx.bind x (.epair r P)
  | .mkTicket rn N P v tk => do
      -- A ticket lock from the region's token: the dispenser `Word[r, N]`, an
      -- epoch counter whose `cas n -> n+1` issues the ticket `Tok[r, N, n+1]`,
      -- and the owner `Word[r, P]`, a held counter born at the same value with
      -- nobody holding its token: the holder of ticket `n+1` claims it on
      -- seeing the owner at `n`.  The region token is consumed, so a region
      -- has one dispenser, and a ticket names its own lock.
      let r ← cx.idx rn
      if !(pwf N && N.epoch) then throw "mkTicket needs an epoch counter for its dispenser"
      if !(pwf P && P.ticket) then throw "mkTicket needs a ticket protocol for its owner"
      let (tt, cx) ← cx.use tk
      match tt with
      | .tok r' none => if !cx.eqI r r' then throw "the token is for another region"
      | .tok _ (some _) => throw "a ticket lock is born from a fresh region token, not a taken one"
      | _ => throw "mkTicket needs a region token"
      let _ ← intIdx cx v
      cx.bind x (.prod (.word r N) (.word r P))
  | .claim a tk => do
      -- Acquisition by observation.  Ticket `j` is unique (the dispenser issues
      -- each value once); the owner leaves `j - 1` only by the store of the
      -- thread holding `Tok[r, P, j - 1]`, which only this claim can produce;
      -- so an observation of the owner at `j - 1`, however old, is current.
      -- No instruction: the load was the observation.
      let t ← cx.peek a
      match wordOf t, a with
      | some (r, P), .var w =>
          if !P.ticket then throw "claim needs the owner word of a ticket lock"
          let (tt, cx) ← cx.use tk
          let j ← match tt with
            | .tokE r' _ j => if !cx.eqI r r' then throw "the ticket is for another region" else pure j
            | _ => throw "claim needs a ticket (the dispenser's epoch token)"
          match sawFor cx w j with
          | some m => cx.bind x (.tok r (some (P, m)))
          | none => throw "claim: no ordered observation of the owner at ticket - 1 (load acq, or fence ld)"
      | some _, _ => throw "a protocol word must be named by a variable"
      | none, _ => throw "claim needs a reference to a protocol word"
  | .fetch o acq rel a v => do
      -- A fetch-op never fails, so unlike `cas` it is an operation, not a
      -- branch, and it yields the value it read.
      let tw ← cx.peek a
      match wordOf tw with
      | none =>
          -- A plain `Int` cell, `pub` or under a writing capability, as `cas`:
          -- the cell's type is invariant and nothing is duplicated.
          let u ← casCellTy cx tw
          if u != .int then throw "fetch needs an Int cell or a protocol word"
          let (tv, cx) ← cx.use v
          if !sub cx tv .int then throw "fetch: the operand is not an Int"
          cx.bind x .int
      | some (r, P) =>
          if o != .add then throw "a fetch on a protocol word must be add: a protocol's moves are increments"
          let j ← intIdx cx v
          if P.epoch then
            -- The counter: `e -> e + 1` enters epoch `e + 1` and yields its
            -- token with `e`, whatever `e` the hardware read.
            if !acq then throw "entering an epoch needs acq"
            if !cx.eqI j (.lit 1) then throw "an epoch counter advances by 1"
            cx.bind x (fetchEpochTy r P)
          else
            let d ← cx.constIdx j
            if !cx.eqI j (.lit d) then throw "fetch on a protocol word: the operand must be a known constant"
            if !fetchOK P d then
              throw "fetch: not a +d move between shared states from every family of the protocol (or it lends)"
            cx.bind x .int
  | .pack a wn τ => do
      let w ← cx.idx wn
      let body ← match τ with
        | .iex b => pure b
        | _ => throw "pack targets an index existential"
      -- The target may mention the index variables in scope (a region the
      -- package's cells live in, D1): `instI` keeps them in place.
      if !τ.wf cx.ke.length cx.inames.length then
        throw "pack: the target must be well formed in the index scope"
      let (t, cx) ← cx.use a
      noLeak cx t
      if sub cx t (instT [w] 0 body) then cx.bind x τ
      else throw "pack: the value does not match the target at the witness"
  | .packT a σ τ =>
      match τ with
      | .tex κ body => do
          if !body.guardT 0 then
            throw "pack: the package's variable must occur only under a reference"
          if !τ.wf cx.ke.length 0 then throw "pack: the target must be closed"
          if !admitsIn cx κ σ then throw "pack: the witness does not have the variable's kind"
          let (t, cx) ← cx.use a
          noLeak cx t
          if sub cx t (Ty.substT 0 σ body) then cx.bind x τ
          else throw "pack: the value does not match the target at the witness"
      | _ => throw "pack at a type targets a type existential"
  | .validate y => do
      match cx.torn.find? (·.x == y) with
      | none => throw s!"{y} is not a torn read"
      | some tn =>
          match tn.φ with
          | .rechecked v =>
              if !cx.eqI v tn.s then
                throw "validate: the re-check is not known to equal the observed state"
              else if affine cx.ke tn.ty then throw "validate would duplicate an affine value"
              else cx.bind x tn.ty
          | .fenced => throw "validate: the word was not re-read after the fence"
          | .opn => throw "validate: no fence ld between the torn read and the re-check"
  | .call f is a ts => do
      let d ← p.find f
      let (at_, rt) ← instantiate cx d is ts
      let (t, cx) ← cx.use a
      noLeak cx t
      if !sub cx t at_ then throw s!"call {f}: argument type mismatch"
      cx.bind x rt
  | .borrow c a => do
      let y ← varOf a
      let t ← cx.peek a
      let r ← lendOf cx c t
      let (_, c₁) ← cx.use a
      { c₁ with lent := y :: c₁.lent }.bind x (.cap c r)
  | .cvt sg w a => do
      let ta ← cx.peek a
      if !cvtSrc ta then throw "cvt needs an integer"
      cx.bind x (.fix sg w)
  | .toInt a => do
      let ta ← cx.peek a
      if !toIntSrc ta then
        throw "toInt needs an unsigned fix or a lanes word (a signed one: cvt it, or test fcmp lt first)"
      cx.bind x .int
  | .asLanes sg w a => do
      let ta ← cx.peek a
      if (intOf ta).isNone then throw "asLanes needs an Int"
      cx.bind x (.lanes sg w)
  | .fop _ a b => do
      let ta ← cx.peek a
      let tb ← cx.peek b
      match fixOf ta with
      | none => throw "fop needs fixed-width integers"
      | some p =>
          if fixOf tb != some p then throw "fop: the operands have different fixed-width types"
          cx.bind x (.fix p.1 p.2)
  | .fcmp _ a b => do
      let ta ← cx.peek a
      let tb ← cx.peek b
      match fixOf ta with
      | none => throw "fcmp needs fixed-width integers"
      | some p =>
          if fixOf tb != some p then throw "fcmp: the operands have different fixed-width types"
          cx.bind x .int
  | .fop1 _ a => do
      let ta ← cx.peek a
      match fixOf ta with
      | none => throw "fop1 needs a fixed-width integer"
      | some p => cx.bind x (.fix p.1 p.2)
  -- The lane within a word is taken mod `64/w` at run time (a shift count, as
  -- the hardware masks it): no bound to prove, and nothing to go wrong.
  | .lane a j => do
      let ta ← cx.peek a
      match lanesOf ta with
      | none => throw "lane needs a lanes word"
      | some p => do
          let tj ← cx.peek j
          if (intOf tj).isNone then throw "lane: the lane number must be an Int"
          cx.bind x (.fix p.1 p.2)
  | .setLane a j v => do
      let ta ← cx.peek a
      match lanesOf ta with
      | none => throw "setLane needs a lanes word"
      | some p => do
          let tj ← cx.peek j
          if (intOf tj).isNone then throw "setLane: the lane number must be an Int"
          let tv ← cx.peek v
          if fixOf tv != some p then throw "setLane: the value is not the lane's type"
          cx.bind x (.lanes p.1 p.2)
  | .ldlw b wi j => do
      let t ← cx.peek b
      match bufOf t with
      | none => throw "ldlw needs a buffer"
      | some (μ, n, u, k) =>
          if μ != .own then throw "ldlw works on own buffers; use idx, load and lane on a shared one"
          match lanesOf u with
          | none => throw "ldlw needs a buffer of lanes"
          | some p => do
              let jw ← intIdx cx wi
              if !cx.ltI jw n then throw "ldlw: the word is not provably below the capacity"
              if !cx.ltI jw k then throw "ldlw: the word is not provably initialised"
              let tj ← cx.peek j
              if (intOf tj).isNone then throw "ldlw: the lane number must be an Int"
              cx.bind x (.fix p.1 p.2)
  | .stlw b wi j v => do
      let t ← cx.peek b
      match bufOf t with
      | none => throw "stlw needs a buffer"
      | some (μ, n, u, k) =>
          if μ != .own then
            throw "stlw works on own buffers only: a sub-word store never touches memory another thread can see"
          match lanesOf u with
          | none => throw "stlw needs a buffer of lanes"
          | some p => do
              let jw ← intIdx cx wi
              if !cx.ltI jw n then throw "stlw: the word is not provably below the capacity"
              if !cx.ltI jw k then throw "stlw: the word is not provably initialised"
              let tj ← cx.peek j
              if (intOf tj).isNone then throw "stlw: the lane number must be an Int"
              let tv ← cx.peek v
              if fixOf tv != some p then throw "stlw: the value is not the lane's type"
              cx.bind x .unit
  | .ldl b i => do
      let t ← cx.peek b
      match bufOf t with
      | none => throw "ldl needs a buffer"
      | some (μ, n, u, k) =>
          if μ != .own then throw "ldl works on own buffers; use idx, load and lane on a shared one"
          match lanesOf u with
          | none => throw "ldl needs a buffer of lanes"
          | some p => do
              let j ← intIdx cx i
              if !cx.ltI j (.smul p.2.lanes n) then throw "ldl: the lane is not provably below the capacity"
              if !cx.ltI j (.smul p.2.lanes k) then throw "ldl: the lane is not provably initialised"
              cx.bind x (.fix p.1 p.2)
  | .stl b i v => do
      let t ← cx.peek b
      match bufOf t with
      | none => throw "stl needs a buffer"
      | some (μ, n, u, k) =>
          if μ != .own then
            throw "stl works on own buffers only: a sub-word store never touches memory another thread can see"
          match lanesOf u with
          | none => throw "stl needs a buffer of lanes"
          | some p => do
              let j ← intIdx cx i
              if !cx.ltI j (.smul p.2.lanes n) then throw "stl: the lane is not provably below the capacity"
              if !cx.ltI j (.smul p.2.lanes k) then throw "stl: the lane is not provably initialised"
              let tv ← cx.peek v
              if fixOf tv != some p then throw "stl: the value is not the lane's type"
              cx.bind x .unit
  | .freeze a => do
      let (tt, cx) ← cx.use a
      match tt with
      | .tok r none =>
          if !cx.sealedR r then throw "freeze: the region is waiting for fence st (§4.4 rule 7)"
          cx.bind x (.cap .frz r)
      | .tok _ (some _) => throw "freeze needs a fresh region token, not a taken one"
      | _ => throw "freeze needs a region token"
  | .endBorrow a => do
      let y ← varOf a
      if !cx.lent.contains y then throw "endBorrow: nothing is lent from this variable"
      (cx.endCx y).bind x .unit
  | .xchg a v => do
      let t ← cx.peek a
      let (u, o) ← xchgCell cx t
      let (tv, cx) ← cx.use v
      if !(sub cx tv u || sub cx tv o) then throw "xchg: the value does not have the cell's type"
      cx.bind x o
  | .fnptr f => do
      let d ← p.find f
      if !(d.tparams.isEmpty && d.idx.isEmpty) then
        throw s!"fnptr {f}: only a monomorphic code block has a code pointer"
      cx.bind x (.code d.argTy d.retTy (match d.kind with | .restricted f s => .restricted f s | _ => .plain))
  | .callc f a => do
      let tf ← cx.peek f
      match codeOf tf with
      | some (σ, τ) => do
          let (t, cx) ← cx.use a
          noLeak cx t
          if !sub cx t σ then throw "callc: argument type mismatch"
          cx.bind x τ
      | none => throw "callc needs a code value"
  | .rem a n => do
      -- `k = a mod n` with `n = v + 1`: fresh `d` then `k`, and `v := k + d`, so
      -- `k < n` is a linear fact.  One `rem` per modulus variable per block.
      let ta ← cx.peek a
      if (intOf ta).isNone then throw "rem needs an integer"
      let j ← intIdx cx n
      match (cx.norm j).bind Lin.succVar? with
      | none => throw "rem: the modulus must be v + 1 for an undetermined index variable v"
      | some v =>
          let c := (cx.push (x ++ "_d")).push x
          { c with facts := (v + 2, .add (.var 0) (.var 1)) :: c.facts }.bind x (.intS (.var 0))
  | .nameI a => do
      let j ← intIdx cx a
      let c := cx.push x
      { c with facts := (0, j.shift 0) :: c.facts }.bind x (.intS (.var 0))
  | .xchgAt b i v => do
      -- By value: no locative is made, so the buffer is only looked at.
      let t ← cx.peek b
      let (n, u, k) ← match bufOf t with
        | some (.own, n, u, k) => pure (n, u, k)
        | some _ => throw "xchgAt works on own buffers; use idx on a shared one"
        | none => throw "xchgAt needs a buffer"
      if !Ty.wordFreeIn cx.ke u then throw wordCellMsg
      let j ← intIdx cx i
      if !cx.ltI j n then throw "xchgAt: the index is not provably below the capacity"
      if !cx.ltI j k then throw "xchgAt: the slot is not provably initialised"
      let (tv, cx) ← cx.use v
      if !sub cx tv u then throw "xchgAt: the value does not have the element type"
      cx.bind x u
  | .loadAt b i => do
      let t ← cx.peek b
      let (n, u, k) ← match bufOf t with
        | some (.own, n, u, k) => pure (n, u, k)
        | some _ => throw "loadAt works on own buffers; use idx on a shared one"
        | none => throw "loadAt needs a buffer"
      let j ← intIdx cx i
      if !cx.ltI j n then throw "loadAt: the index is not provably below the capacity"
      if !cx.ltI j k then throw "loadAt: the slot is not provably initialised"
      if affine cx.ke u then throw "loadAt would duplicate an affine value: use xchgAt"
      cx.bind x u
  | .bits _ a b => do
      let ta ← cx.peek a
      let tb ← cx.peek b
      match intOf ta, intOf tb with
      | some _, some _ => cx.bind x .int
      | _, _ => throw "bits needs integers"
  | .bit1 _ a => do
      let ta ← cx.peek a
      match intOf ta with
      | some _ => cx.bind x .int
      | none => throw "bit1 needs an integer"
  | .vmatch lo hi b => do
      let t1 ← cx.peek lo
      let t2 ← cx.peek hi
      let t3 ← cx.peek b
      match intOf t1, intOf t2, intOf t3 with
      | some _, some _, some _ => cx.bind x .int
      | _, _, _ => throw "vmatch needs integers"
  | .band a m => do
      -- `k = a & m` with `m = v`: fresh `d` then `k`, and `v := k + d`, so `k ≤ m`
      -- is a linear fact.  One `band` (or `rem`) per mask variable per block.
      let ta ← cx.peek a
      if (intOf ta).isNone then throw "band needs an integer"
      let j ← intIdx cx m
      match (cx.norm j).bind Lin.asVar? with
      | none => throw "band: the mask must be an undetermined index variable"
      | some v =>
          let c := (cx.push (x ++ "_d")).push x
          { c with facts := (v + 2, .add (.var 0) (.var 1)) :: c.facts }.bind x (.intS (.var 0))
  | .zero τ => do
      if !τ.wf cx.ke.length cx.inames.length then throw "zero: the type is not well formed"
      if τ.secondClass then throw "zero: a second-class capability has no zero"
      if !zeroableIn [] cx.ke τ then throw "zero: the type is not Zeroable"
      cx.bind x τ
  | .loadAtF b i p => do
      let t ← cx.peek b
      let (n, u, k) ← match bufOf t with
        | some (.own, n, u, k) => pure (n, u, k)
        | some _ => throw "loadAtF works on own buffers"
        | none => throw "loadAtF needs a buffer"
      match compTy u p with
      | none => throw "loadAtF: bad field path"
      | some c => do
        if !cx.opaqueOK u then throw "loadAtF: the slots' layout depends on an unpacked type"
        let j ← intIdx cx i
        if !cx.ltI j n then throw "loadAtF: the index is not provably below the capacity"
        if !cx.ltI j k then throw "loadAtF: the slot is not provably initialised"
        if affine cx.ke c then throw "loadAtF would duplicate an affine value: use xchgAtF"
        cx.bind x c
  | .xchgAtF b i p v => do
      let t ← cx.peek b
      let (n, u, k) ← match bufOf t with
        | some (.own, n, u, k) => pure (n, u, k)
        | some _ => throw "xchgAtF works on own buffers"
        | none => throw "xchgAtF needs a buffer"
      match compTy u p with
      | none => throw "xchgAtF: bad field path"
      | some c => do
        if !cx.opaqueOK u then throw "xchgAtF: the slots' layout depends on an unpacked type"
        if !Ty.wordFreeIn cx.ke c then throw wordCellMsg
        let j ← intIdx cx i
        if !cx.ltI j n then throw "xchgAtF: the index is not provably below the capacity"
        if !cx.ltI j k then throw "xchgAtF: the slot is not provably initialised"
        let (tv, cx) ← cx.use v
        if !sub cx tv c then throw "xchgAtF: the value does not have the component type"
        cx.bind x c
  | .spawn f a T ts => do
      -- A trusted runtime spawn: a new thread runs `tail f [] a' ts` on a copy `a'` of
      -- `a`, at the checked type `T` (the child's entry type; the step uses `T`, not the runtime
      -- type).  v1 transfers nothing: copyable, index- and type-closed, region-free, key-free in
      -- wrappers (A1's `KidOK`); the callee is checked as the child's whole body.
      let (t, cx) ← cx.use a
      if !sub cx t T then throw "spawn: the argument does not have the stated type"
      if affine cx.ke t || affine cx.ke T then throw "spawn: the argument must be copyable (v1 passes no ownership)"
      if !T.wf cx.ke.length 0 || !ts.all (·.wf cx.ke.length 0) then
        throw "spawn: the argument type and type arguments must be index-closed"
      if !TermClose.tb 0 T || !ts.all (TermClose.tb 0) then
        throw "spawn: the argument type and type arguments must be closed"
      if !TermScope.drf T || !ts.all TermScope.drf then throw "spawn: no region type may cross to the child"
      if !TermScope.wrapOK T || !ts.all TermScope.argOK then
        throw "spawn: a key-carrying wrapper or type argument may not cross to the child"
      let d ← p.find f
      let (_, rt) ← instantiate { vars := [("a", T, true)], ret := .unit } d [] ts
      tailCheck p { vars := [("a", T, true)], ret := rt } f [] (.var "a") ts
      -- the child's frame invariant (`TvOK`) at its entry context: a closed, guarded, `∀`-free return type
      if !(TermClose.tb 0 rt && TermTv.mg rt && TermTv.noIallV rt) then
        throw "spawn: the callee's return type must be closed, guarded and without a value-position ∀"
      cx.bind x .tid
  | .ext n a => do
      -- (E1) A trusted extern step (`TermExtStep.Ext`): no memory, no fence; `emit`/`exitEv` record an event.
      let (t, cx) ← cx.use a
      if !n.ok then throw s!"{n.name}: inadmissible extern"
      if !sub cx t n.sig.1 then throw s!"{n.name}: the argument does not have the extern's type"
      cx.bind x n.sig.2

/-- The success context of a `cas` between holding states, given `shareMove`:
bind `t`, and lend a read share (`+1`, by `acq`) or take one back (`-1`, by
`rel`, consuming a live share of the region). -/
def lendCx (cx : Cx) (acq rel : Bool) (r : Idx) (mo : Option Int) (t : String) : M Cx :=
  match mo with
  | none => throw "not a move of the lending protocol"
  | some m =>
    if m == 0 then cx.bind t .unit
    else if m == 1 then
      if !acq then throw "taking a read share needs acq" else cx.bind t (.share r)
    else if m == -1 then
      if !rel then throw "giving a read share back needs rel"
      else match cx.shareOf r with
        | none => throw "giving a read share back needs one"
        | some y => do
            let (_, c₁) ← cx.use (.var y)
            c₁.bind t .unit
    else throw "not a move of the lending protocol"

/-- The rule for a term.  Every path ends in `ret` or a tail call, so branches
are checked independently and never merged; an affine value left unused is
dropped, which is what affine means. -/
def check (p : Prog) (cx : Cx) : Expr → M Unit
  | .let_ x op e => do
      let cx ← checkOp p cx x op
      check p cx e
  | .split a x y e => do
      let (t, cx) ← cx.use a
      match t with
      | .prod u v => do
          let cx ← cx.bind x u
          let cx ← cx.bind y v
          check p cx e
      | _ => throw "split needs a pair"
  | .unpack a i x e => do
      let (t, cx) ← cx.use a
      match t with
      | .iex b => do
          let cx ← (cx.push i).bind x b
          check p cx e
      | _ => throw "unpack needs an index existential"
  | .unpackT a _ x e => do
      let (t, cx) ← cx.use a
      match t with
      | .tex κ b => do
          if !b.guardT 0 then
            throw "unpack: the package's variable must occur only under a reference"
          let cx ← (cx.pushT κ).bind x b
          check p cx e
      | _ => throw "unpack at a type needs a type existential"
  | .region a rn pn tn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .own u => do
          -- D1: a region cell is a published cell whose writes the token gates,
          -- so its type is shareable (no `own` inside) and opening it fences.
          if !rgnCellOK cx.ke u then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          check p cx e
      | .refine (.loc .own (.array n u)) (.ini k) => do
          -- An own buffer can be opened as a region directly: the region's
          -- pointer is the buffer's locative, its initialized prefix fixed.
          if !rgnCellOK cx.ke (.array n u) then
            throw "region: the cell type is not shareable (rows 16, 17): an own reference inside a region must be moved in with intoRgn"
          let cx := cx.push rn
          let cx ← cx.bind pn (.refine (.loc (.rgn (.var 0)) ((Ty.array n u).shiftI 0)) ((Pred.ini k).shift 0))
          let cx ← cx.bind tn (.tok (.var 0) none)
          check p cx e
      | _ => throw "region needs an own reference or an own buffer"
  | .openPub a rn pn cn e => do
      let (t, cx) ← cx.use a
      match t with
      | .ptr .pub u => do
          let cx := cx.push rn
          let cx ← cx.bind pn (.ptr (.rgn (.var 0)) (u.shiftI 0))
          let cx ← cx.bind cn (.cap .pub (.var 0))
          check p cx e
      | _ => throw "openPub needs a pub reference"
  | .case a x e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .sum u v => do
          check p (← cx.bind x u) e₁
          check p (← cx.bind y v) e₂
      | _ => throw "case needs a sum"
  | .ifnull a e₁ y e₂ => do
      let (t, cx) ← cx.use a
      match t with
      | .ptrOpt μ u => do
          check p cx e₁
          check p (← cx.bind y (.ptr μ u)) e₂
      | _ => throw "ifnull needs a nullable reference"
  | .parity a k ev od => do
      let i ← intIdx cx a
      let v ← match (cx.norm i).bind Lin.asVar? with
        | some v => pure v
        | none => throw "parity: the index is not a free variable, so there is nothing to refine"
      let cx := cx.push k
      check p { cx with facts := (v + 1, .smul 2 (.var 0)) :: cx.facts } ev
      check p { cx with facts := (v + 1, .add (.smul 2 (.var 0)) (.lit 1)) :: cx.facts } od
  | .ifeq a b yes no =>
      if plainEq cx a b then do check p cx yes; check p cx no
      else do
      let i ← intIdx cx a
      let j ← intIdx cx b
      match cx.norm i, cx.norm j with
      | some ni, some nj =>
          if ni == nj then check p cx yes
          else
            match ni.asVar?, nj.asVar? with
            | some v, _ =>
                if nj.mentions v then throw "ifeq: cannot record the equality"
                check p { cx with facts := (v, nj.toIdx) :: cx.facts } yes
            | _, some v =>
                if ni.mentions v then throw "ifeq: cannot record the equality"
                check p { cx with facts := (v, ni.toIdx) :: cx.facts } yes
            | _, _ =>
                match zeroVar ni nj with
                | some u => check p { cx with facts := (u, .lit 0) :: cx.facts } yes
                | none => throw "ifeq: cannot record the equality"
          check p (noCx cx ni nj) no
      | _, _ => throw "ifeq: index outside the decidable fragment"
  | .cas acq rel w e v t ok fail => do
      let tw ← cx.peek w
      match wordOf tw with
      | none =>
          -- A plain `pub` cell: compare-and-swap one word.  No region, no token:
          -- the cell's type is invariant, so success and failure both leave it
          -- well typed, and the expected value is compared, not duplicated.
          let u ← casCellTy cx tw
          if u.rawWords != some 1 then throw "cas needs a one-word cell (§3.5)"
          if affine cx.ke u then throw "cas would duplicate an affine value"
          let te ← cx.peek e
          let (tv, cx) ← cx.use v
          if !sub cx te u then throw "cas: the expected value does not have the cell's type"
          if !sub cx tv u then throw "cas: the new value does not have the cell's type"
          if Ty.sensitiveIn cx.ke u && !(acq && rel) then
            throw "cas: a view-sensitive type needs acq and rel (§3.8)"
          check p (← cx.bind t .unit) ok
          check p cx fail
      | some (r, P) =>
      if P.epoch then
        -- An epoch counter: `cas e -> e + 1` enters epoch `e + 1` and yields
        -- its token, never the region (the counter has no held state).
        if !acq then throw "entering an epoch needs acq"
        let i ← intIdx cx e
        let j ← intIdx cx v
        let (c, k) ← classifyM cx P i
        let (c', k') ← classifyM cx P j
        if !pstep P c k c' k' then throw "not a transition of the protocol"
        check p (← cx.bind t (.tokE r (.word P) j)) ok
        check p cx fail
      else
        if P.ghost then throw "cas on a ghost word: it has no runtime value"
        let i ← intIdx cx e
        let j ← intIdx cx v
        let (c, k) ← classifyM cx P i
        let (c', k') ← classifyM cx P j
        let cl ← clauseM P c
        let cl' ← clauseM P c'
        if !cl.holds then throw "cas from a held state: the holder stores instead"
        if !pstep P c k c' k' then throw "not a transition of the protocol"
        if cl'.holds then
          check p (← lendCx cx acq rel r (shareMove P c k c' k') t) ok
        else
          if P.lends.contains c || P.lendsDown.contains c then
            throw "taking the region from a lending state: shares are out"
          if !acq then throw "taking the region needs acq"
          let cx' ← cx.bind t (.tok r (some (P, j)))
          let cx' := if monotone P then { cx' with unsealed := r :: cx'.unsealed } else cx'
          check p cx' ok
        check p cx fail
  | .casp acq rel w e0 e1 v0 v1 t ok fail => do
      let tw ← cx.peek w
      match word2Of tw with
      | none =>
        match epairOf tw with
        | none => throw "casp needs a reference to a protocol pair"
        | some (r, P) =>
          -- The epoch-fenced write: the new epoch must be the one a live epoch
          -- token names, and the write publishes (`rel`).  The compare is the
          -- fence: a re-stamp by a later epoch makes a stale writer's expected
          -- pair wrong, and a stale pair that lands still names its epoch.
          if !rel then throw "an epoch-fenced write needs rel"
          let _ ← intIdx cx e0
          let _ ← intIdx cx e1
          let j0 ← intIdx cx v0
          let _ ← intIdx cx v1
          if !cx.hasTokE r P j0 then throw "an epoch-fenced write needs the epoch token of its new epoch"
          check p (← cx.bind t .unit) ok
          check p cx fail
      | some (r, P) =>
      let i0 ← intIdx cx e0
      let i1 ← intIdx cx e1
      let j0 ← intIdx cx v0
      let j1 ← intIdx cx v1
      let (c, k0, k1) ← classify2M cx P i0 i1
      let (c', k0', k1') ← classify2M cx P j0 j1
      let cl ← clause2M P c
      let cl' ← clause2M P c'
      if !cl.holds then throw "casp from a held state: the holder stores instead"
      if !pstep2 P c k0 k1 c' k0' k1' then throw "not a transition of the pair protocol"
      if cl'.holds then
        if bump2 P k0 k0' then
          -- An epoch pair's move that bumps the epoch issues the new epoch's token.
          if !acq then throw "entering an epoch needs acq"
          check p (← cx.bind t (.tokE r (.pair P) j0)) ok
        else
          -- Between shared states nothing changes hands (a pair lends no shares).
          check p (← cx.bind t .unit) ok
      else
        if !acq then throw "taking the region needs acq"
        check p (← cx.bind t (.tok2 r P j0 j1)) ok
      check p cx fail
  | .ret a => do
      let (t, cx) ← cx.use a
      noLeak cx t
      noDrop cx
      if !sub cx t cx.ret then throw "ret: the value does not have the return type"
  | .tail f is a ts => tailCheck p cx f is a ts

/-- (T6) The pointee types a device decl's argument hands to the device: through pointers, nullable pointers and LOCATIVES
(`Loc (rgn r) Desc`, buffers), inside pairs, sums, arrays, refinements, binders and `mu`. (`cap`/`share`/`tok`/`word` values
name no cell by themselves; `code` captures nothing.) -/
def devCells : Ty → List Ty
  | .ptr _ t | .ptrOpt _ t | .loc _ t => [t]
  | .prod a b | .sum a b => devCells a ++ devCells b
  | .array _ t | .refine t _ | .iex t | .iall t | .tex _ t | .mu t => devCells t
  | _ => []
/-- A cell the device may hold: plain bits (`bitsIn`), or a protocol-governed word (the slot/ring words it moves only by
`cas`/token stores). Pointer-containing cells fail `bitsIn`, so nested pointees need no recursion. -/
def devCellOK : Ty → Bool
  | .refine t _ => devCellOK t
  | .word .. | .word2 .. | .epair .. => true
  | t => bitsIn t
/-- (T6) No device-only extern, and no use of a device decl (call, tail, spawn, `fnptr`), anywhere in `e`; `isDev f` =
`(p.find? (·.name = f)).map (·.kind = .device)`. Every `Expr` form, nested branches included. -/
def exprNoDevOnly (isDev : String → Bool) : Expr → Bool
  | .let_ _ (.ext n _) e => !n.deviceOnly && exprNoDevOnly isDev e
  | .let_ _ (.call f _ _ _) e | .let_ _ (.fnptr f) e | .let_ _ (.spawn f _ _ _) e => !isDev f && exprNoDevOnly isDev e
  | .let_ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e | .openPub _ _ _ _ e =>
      exprNoDevOnly isDev e
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂ =>
      exprNoDevOnly isDev e₁ && exprNoDevOnly isDev e₂
  | .cas _ _ _ _ _ _ ok fail | .casp _ _ _ _ _ _ _ _ ok fail => exprNoDevOnly isDev ok && exprNoDevOnly isDev fail
  | .ret _ => true
  | .tail f _ _ _ => !isDev f
/-- (T6) No `fnptr` of a device decl anywhere, in EVERY decl: a device decl could otherwise hand a code value of
itself to a CPU thread (`spawn`, a store), which would then `callc` device externs. -/
def exprNoDevFnptr (isDev : String → Bool) : Expr → Bool
  | .let_ _ (.fnptr f) e => !isDev f && exprNoDevFnptr isDev e
  | .let_ _ _ e | .split _ _ _ e | .unpack _ _ _ e | .unpackT _ _ _ e | .region _ _ _ _ e | .openPub _ _ _ _ e =>
      exprNoDevFnptr isDev e
  | .case _ _ e₁ _ e₂ | .ifnull _ e₁ _ e₂ | .parity _ _ e₁ e₂ | .ifeq _ _ e₁ e₂ =>
      exprNoDevFnptr isDev e₁ && exprNoDevFnptr isDev e₂
  | .cas _ _ _ _ _ _ ok fail | .casp _ _ _ _ _ _ _ _ ok fail => exprNoDevFnptr isDev ok && exprNoDevFnptr isDev fail
  | .ret _ | .tail .. => true

def checkDecl (p : Prog) (d : Decl) : M Unit := do
  let nt := d.tparams.length
  if !d.argTy.wf nt d.idx.length || !d.retTy.wf nt d.idx.length then
    throw s!"{d.name}: signature is not well formed"
  if !d.argTy.scTop || d.retTy.secondClass then
    throw s!"{d.name}: a second-class capability may be passed, not returned or stored"
  check p { inames := d.idx.reverse, vars := [(d.arg, d.argTy, true)], ret := d.retTy,
            ke := d.tparams.reverse.map some } d.body
  -- the kind rules; no rule mentions a decl by name (`isDev` is by KIND)
  let isDev : String → Bool := fun f => ((p.find? (·.name == f)).map (·.kind == .device)).getD false
  if d.kind == .device && !(devCells d.argTy).all devCellOK then
    throw s!"{d.name}: a device function may only be given cells of plain bits, protocol words or word pairs"
  if d.kind != .device && !exprNoDevOnly isDev d.body then
    throw s!"{d.name}: device externs and device functions may be used only inside a device function"
  if !exprNoDevFnptr isDev d.body then
    throw s!"{d.name}: a device function cannot be taken as a value"
  match d.kind with
  | .restricted _ _ =>
      throw s!"{d.name}: restricted functions are not supported yet (fuel and stack budgets are not checked)"
  | _ => pure ()

def checkProg (p : Prog) : M Unit := p.forM (checkDecl p)

def accepts (r : M Unit) : Bool :=
  match r with
  | .ok _ => true
  | .error _ => false

/-- Rejected, and for this reason. -/
def rejects (r : M Unit) (why : String) : Bool :=
  match r with
  | .ok _ => false
  | .error e => (e.splitOn why).length > 1

/-! ## §6. Synchronisation as library code

Nothing below is a primitive.  Each block is an ordinary code block over
`cas`, `load`, `store` and `fence`, and the checker accepts it.  Each hazard is
then written as a variant, and the checker rejects it **with the reason
given**, so a rule that stopped biting would fail the build. -/

def v (x : String) : At := .var x

/-- `Ptr pub (Word[r, P] × Ptr r τ)` with `r` the innermost index variable:
`guardedBy`'s body, what a caller has after unpacking. -/
def cell (P : Proto) (τ : Ty) : Ty :=
  .ptr .pub (.prod (.word (.var 0) P) (.ptr (.rgn (.var 0)) (τ.shiftI 0)))

/-! ### The mutex -/

def lockD : Decl where
  name := "lock"; idx := ["r"]; arg := "m"
  argTy := cell mutexP .int
  retTy := .tok (.var 0) (some (mutexP, .lit 1))
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 1) "t"
      (.ret (v "t"))
      (.tail "lock" ["r"] (v "m")))

def unlockD : Decl where
  name := "unlock"; idx := ["r"]; arg := "a"
  argTy := .prod (cell mutexP .int) (.tok (.var 0) (some (mutexP, .lit 1)))
  retTy := .unit
  body := .split (v "a") "m" "t"
    (lets [("w", .fld 0 (v "m")), ("u", .store true (v "w") (.lit 0) (some (v "t")))]
      (.ret .unit))

/-- A critical section: lock, read, add one, write, unlock. -/
def incrD : Decl where
  name := "incr"; idx := ["r"]; arg := "m"
  argTy := cell mutexP .int
  retTy := .unit
  body := lets [("t", .call "lock" ["r"] (v "m")),
                ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                ("x", .load false (v "d")), ("y", .add (v "x") (.lit 1)),
                ("u", .store false (v "d") (v "y") none),
                ("p", .pair (v "m") (v "t")), ("u2", .call "unlock" ["r"] (v "p"))]
    (.ret .unit)

/-- Allocate the payload, turn it into a region, give the region to a new word
in its free state, publish the pair, and hide the region behind `∃r`. -/
def mkMutexD : Decl where
  name := "mkMutex"; idx := []; arg := "x"
  argTy := .int
  retTy := mutex .int
  body := lets [("p", .new (v "x"))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wv", .mkWord "r" mutexP (.lit 0) (v "t0")),
             ("pr", .pair (v "wv") (v "d")), ("s", .new (v "pr")),
             ("s2", .publish (v "s")), ("mx", .pack (v "s2") "r" (mutex .int))]
        (.ret (v "mx"))))

/-- A client that only has the abstract type. -/
def useMutexD : Decl where
  name := "useMutex"; idx := []; arg := "m"
  argTy := mutex .int
  retTy := .unit
  body := .unpack (v "m") "r" "s" (lets [("u", .call "incr" ["r"] (v "s"))] (.ret .unit))

def mutexLib : Prog := [lockD, unlockD, incrD, mkMutexD, useMutexD]

#guard accepts (checkProg mutexLib)

/-! ### The seqlock (§4.4), for a two-word payload that would tear -/

def pay : Ty := .prod .int .int

/-- The reader, with each ingredient switchable so the hazards below are the
same program with one thing missing. -/
def readBody (acq fence1 fence2 compare : Bool) (tornInOdd : Bool := false) : Expr :=
  let retry := Expr.tail "read" ["r"] (v "m")
  let critical : Expr :=
    lets ([("d0", .fld 1 (v "m")), ("d", .load false (v "d0")), ("x", .load false (v "d"))] ++
          (if fence2 then [("f2", .fence .ld)] else []) ++
          [("c2", .load false (v "w"))])
      (if compare then
         .ifeq (v "c2") (v "c1") (lets [("y", .validate "x")] (.ret (v "y"))) retry
       else lets [("y", .validate "x")] (.ret (v "y")))
  lets ([("w", .fld 0 (v "m")), ("c1", .load acq (v "w"))] ++
        (if fence1 then [("f1", .fence .ld)] else []))
    (.parity (v "c1") "k"
      (if tornInOdd then retry else critical)
      (if tornInOdd then critical else retry))

def readD' (body : Expr) (P : Proto := seqP) : Decl where
  name := "read"; idx := ["r"]; arg := "m"
  argTy := cell P pay
  retTy := pay
  body := body

/-- The canonical reader: `ldar` the counter, read the payload torn, `dmb
ishld`, re-read, and accept on equality. -/
def readD : Decl := readD' (readBody true false true true)

def writeBody (fenceSt rel : Bool) (parity : Bool := true) : Expr :=
  let retry := lets [("p", .pair (v "m") (v "v"))] (.tail "write" ["r"] (v "p"))
  let critical : Expr :=
    lets [("c1", .add (v "c") (.lit 1))]
      (.cas true false (v "w") (v "c") (v "c1") "t"
        (lets ((if fenceSt then [("f", .fence .st)] else []) ++
               [("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                ("u", .store false (v "d") (v "v") none),
                ("c2", .add (v "c1") (.lit 1)),
                ("u2", .store rel (v "w") (v "c2") (some (v "t")))])
          (.ret .unit))
        retry)
  .split (v "a") "m" "v"
    (lets [("w", .fld 0 (v "m")), ("c", .load false (v "w"))]
      (if parity then .parity (v "c") "k" critical retry else critical))

def writeD' (body : Expr) : Decl where
  name := "write"; idx := ["r"]; arg := "a"
  argTy := .prod (cell seqP pay) pay
  retTy := .unit
  body := body

/-- The writer: `cas` the counter from even to odd (taking the region), `dmb
ishst` (sealing it), write the payload, release-store the next even value. -/
def writeD : Decl := writeD' (writeBody true true)

def mkSeqD : Decl where
  name := "mkSeq"; idx := []; arg := "x"
  argTy := pay
  retTy := seqLock pay
  body := lets [("p", .new (v "x"))]
    (.region (v "p") "r" "d" "t0"
      (lets [("wv", .mkWord "r" seqP (.lit 0) (v "t0")),
             ("pr", .pair (v "wv") (v "d")), ("s", .new (v "pr")),
             ("s2", .publish (v "s")), ("sq", .pack (v "s2") "r" (seqLock pay))]
        (.ret (v "sq"))))

def seqLib : Prog := [readD, writeD, mkSeqD]

#guard accepts (checkProg seqLib)
-- A plain first read followed by `dmb ishld` is as good as `ldar` (§4.4 rule 1).
#guard accepts (checkDecl seqLib (readD' (readBody false true true true)))

/-! ### What each rule is for: the same programs, one ingredient removed -/

-- Mutex.  No lock: the region has no token, and a mutex offers no observation.
#guard rejects (checkDecl mutexLib { incrD with
    body := lets [("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                  ("x", .load false (v "d"))] (.ret .unit) })
  "without its token, and no observation"
-- Writing after unlock: the token went back with the store.
#guard rejects (checkDecl mutexLib { incrD with
    body := lets [("t", .call "lock" ["r"] (v "m")),
                  ("d0", .fld 1 (v "m")), ("d", .load false (v "d0")),
                  ("p", .pair (v "m") (v "t")), ("u2", .call "unlock" ["r"] (v "p")),
                  ("u", .store false (v "d") (.lit 7) none)] (.ret .unit) })
  "store into a region without its token"
-- Unlocking twice: the token is affine.
#guard rejects (checkDecl mutexLib { incrD with
    body := lets [("t", .call "lock" ["r"] (v "m")),
                  ("p", .pair (v "m") (v "t")), ("u1", .call "unlock" ["r"] (v "p")),
                  ("q", .pair (v "m") (v "t"))] (.ret .unit) })
  "already used"
-- Never unlocking: a mutex token can be given back, so it is linear, and a
-- block may not end still holding it (`noDrop`).  In a pair just the same.
#guard rejects (checkDecl mutexLib { incrD with
    body := lets [("t", .call "lock" ["r"] (v "m"))] (.ret .unit) })
  "still holds a token"
#guard rejects (checkDecl mutexLib { incrD with
    body := lets [("t", .call "lock" ["r"] (v "m")), ("p", .pair (v "m") (v "t"))] (.ret .unit) })
  "still holds a token"
-- Taking without acquire, giving back without release.
#guard rejects (checkDecl mutexLib { lockD with
    body := lets [("w", .fld 0 (v "m"))]
      (.cas false false (v "w") (.lit 0) (.lit 1) "t" (.ret (v "t")) (.tail "lock" ["r"] (v "m"))) })
  "taking the region needs acq"
#guard rejects (checkDecl mutexLib { unlockD with
    body := .split (v "a") "m" "t"
      (lets [("w", .fld 0 (v "m")), ("u", .store false (v "w") (.lit 0) (some (v "t")))] (.ret .unit)) })
  "giving the region back needs rel"
-- A value the protocol does not have.
#guard rejects (checkDecl mutexLib { unlockD with
    body := .split (v "a") "m" "t"
      (lets [("w", .fld 0 (v "m")), ("u", .store true (v "w") (.lit 2) (some (v "t")))] (.ret .unit)) })
  "no single state of the protocol"
-- A lock born locked would hold a region nobody can take.
#guard rejects (checkDecl mutexLib { mkMutexD with
    body := lets [("p", .new (v "x"))]
      (.region (v "p") "r" "d" "t0"
        (lets [("wv", .mkWord "r" mutexP (.lit 1) (v "t0"))] (.ret .unit))) })
  "born in a state that holds its region"
-- Two words over one region: the second has no fresh token left.
#guard rejects (checkDecl mutexLib { mkMutexD with
    body := lets [("p", .new (v "x"))]
      (.region (v "p") "r" "d" "t0"
        (lets [("w1", .mkWord "r" mutexP (.lit 0) (v "t0")),
               ("w2", .mkWord "r" mutexP (.lit 0) (v "t0"))] (.ret .unit))) })
  "already used"
-- Row 17 still holds outside regions: an `own` reference cannot be published.
def leakD : Decl where
  name := "leak"; idx := []; arg := "x"
  argTy := .int
  retTy := .unit
  body := lets [("p", .new (v "x")), ("q", .new (v "p")), ("s", .publish (v "q"))] (.ret .unit)
#guard rejects (checkDecl [] leakD) "not shareable"
-- A mutex has no optimistic readers: `0 → 1 → 0` re-enters a state (ABA).
#guard rejects (checkDecl [readD' (readBody true false true true) mutexP]
    (readD' (readBody true false true true) mutexP))
  "no version measure"
-- ...and a seqlock whose writer steps back has no version measure.
#guard rejects (checkDecl [readD' (readBody true false true true) badSeqP]
    (readD' (readBody true false true true) badSeqP))
  "no version measure"

-- Seqlock reader.  The first read neither acquires nor is fenced.
#guard rejects (checkDecl seqLib (readD' (readBody false false true true)))
  "not ordered before it"
-- No `dmb ishld` between the payload and the re-check.
#guard rejects (checkDecl seqLib (readD' (readBody true false false true)))
  "no fence ld between the torn read and the re-check"
-- A fence, but no re-read after it: fencing twice is not re-checking.
#guard rejects (checkDecl seqLib (readD' (readBody true true false true)))
  "no fence ld between the torn read and the re-check"
-- Re-read, but never compared.
#guard rejects (checkDecl seqLib (readD' (readBody true false true false)))
  "not known to equal the observed state"
-- Reading while the counter is odd: that state does not hold the region.
#guard rejects (checkDecl seqLib (readD' (readBody true false true true (tornInOdd := true))))
  "does not hold the region"

-- Seqlock writer.  No `dmb ishst` after taking: payload writes could pass the
-- counter, and a reader would not see the transaction open (§11.3's writer fence).
#guard rejects (checkDecl seqLib (writeD' (writeBody false true)))
  "before fence st"
#guard rejects (checkDecl seqLib (writeD' (writeBody true false)))
  "giving the region back needs rel"
-- `cas` on a counter of unknown parity: which state is it leaving?
#guard rejects (checkDecl seqLib (writeD' (writeBody true true (parity := false))))
  "no single state of the protocol"

/-! ### A lockless queue (Michael–Scott)

No new primitive: `cas` on a one-word `pub` cell, `Ptr?` with `null` and
`ifnull`, and `μ` with `fold`.  The collector makes pointer `cas` ABA-free (a
node cannot be reused while anyone holds it), so there are no counted pointers,
and the dequeuer's `head = tail` check, which exists so that a node is not
freed while `tail` points at it, is not needed.  The checker establishes
memory and type safety; it does not establish linearisability. -/

/-- `μN. τ × Ptr? pub N`. -/
def node (τ : Ty) : Ty := .mu (.prod (τ.shiftT 0) (.ptrOpt .pub (.tvar 0)))

/-- `(head, tail)`.  `head` points at a dummy node whose successor is the front. -/
def queue (τ : Ty) : Ty := .ptr .pub (.prod (.ptr .pub (node τ)) (.ptr .pub (node τ)))

/-- A node for `x`, with no successor, published. -/
def mkNode (τ : Ty) (x n : String) : List (String × Op) :=
  [("nl", .null .pub (node τ)), ("n0", .pair (v x) (v "nl")), ("n1", .new (v "n0")),
   ("n2", .fold (v "n1") (.ptr .own (node τ))), (n, .publish (v "n2"))]

/-- The dummy's value is the argument: a queue needs no `τ` to be zeroable. -/
def mkQueueD (τ : Ty) : Decl where
  name := "mkQueue"; idx := []; arg := "x"
  argTy := τ
  retTy := queue τ
  body := lets (mkNode τ "x" "d" ++
                [("c", .pair (v "d") (v "d")), ("c1", .new (v "c")), ("q", .publish (v "c1"))])
    (.ret (v "q"))

/-- Link `n` after the last node, then swing `tail`; if `tail` lags, help it
along first. -/
def enqLoop (N : Ty) (ts : List Ty := []) : Expr :=
  let retry := lets [("a2", .pair (v "q") (v "n"))] (.tail "enq" [] (v "a2") ts)
  lets [("tc", .fld 1 (v "q")), ("t", .load false (v "tc")), ("tn", .fld 1 (v "t")),
        ("nx", .load false (v "tn")), ("nl", .null .pub N)]
    (.ifnull (v "nx")
      (.cas false false (v "tn") (v "nl") (v "n") "u"
        (.cas false false (v "tc") (v "t") (v "n") "u2" (.ret .unit) (.ret .unit))
        retry)
      "nxt"
      (.cas false false (v "tc") (v "t") (v "nxt") "u3" retry retry))

def enqD (τ : Ty) (ts : List Ty := []) : Decl where
  name := "enq"; idx := []; arg := "a"
  argTy := .prod (queue τ) (.ptr .pub (node τ))
  retTy := .unit
  body := .split (v "a") "q" "n" (enqLoop (node τ) ts)

def enqueueD (τ : Ty) (ts : List Ty := []) : Decl where
  name := "enqueue"; idx := []; arg := "a"
  argTy := .prod (queue τ) τ
  retTy := .unit
  body := .split (v "a") "q" "x"
    (lets (mkNode τ "x" "n" ++ [("b", .pair (v "q") (v "n"))]) (.tail "enq" [] (v "b") ts))

/-- Swing `head` from the dummy to its successor, which becomes the dummy; its
value is the result.  Empty is `inr ()`. -/
def deqBody (τ : Ty) (front : List (String × Op) := []) (ts : List Ty := []) : Expr :=
  lets ([("hc", .fld 0 (v "q")), ("h", .load false (v "hc")), ("hn", .fld 1 (v "h")),
         ("nx", .load false (v "hn"))] ++ front)
    (.ifnull (v "nx")
      (lets [("r", .inr τ .unit)] (.ret (v "r")))
      "p"
      (.cas false false (v "hc") (v "h") (v "p") "u"
        (lets [("pv", .fld 0 (v "p")), ("x", .load false (v "pv")), ("r", .inl .unit (v "x"))]
          (.ret (v "r")))
        (.tail "deq" [] (v "q") ts)))

def deqD (τ : Ty) (ts : List Ty := []) : Decl where
  name := "deq"; idx := []; arg := "q"
  argTy := queue τ
  retTy := .sum τ .unit
  body := deqBody τ [] ts

def queueLib (τ : Ty) : Prog := [mkQueueD τ, enqD τ, enqueueD τ, deqD τ]

#guard accepts (checkProg (queueLib .int))
-- A payload that would tear is fine: it is written before `publish` and never again.
#guard accepts (checkProg (queueLib pay))
-- So is a payload that is itself a shared reference.
#guard accepts (checkProg (queueLib (.ptr .pub .int)))

/-! What each rule is for. -/

-- Linking a node that was never published: an `own` reference is not a `pub` one.
#guard rejects (checkDecl (queueLib .int)
    { enqD .int with argTy := .prod (queue .int) (.ptr .own (node .int)) })
  "cas: the new value does not have the cell's type"
-- Following `next` without asking whether it is null.
#guard rejects (checkDecl (queueLib .int)
    { deqD .int with body := deqBody .int [("pv", .fld 0 (v "nx"))] })
  "fld needs a reference"
-- Asking of a reference that cannot be null.
#guard rejects (checkDecl (queueLib .int)
    { deqD .int with body := .ifnull (v "q") (.ret .unit) "z" (.ret .unit) })
  "ifnull needs a nullable reference"
-- A queue of `own` references: publishing the first node would leak one.
#guard rejects (checkDecl (queueLib (.ptr .own .int)) (mkQueueD (.ptr .own .int)))
  "not shareable"
-- `cas` on a two-word payload: no single-copy-atomic access covers it.
def casWide : Expr :=
  lets [("hc", .fld 0 (v "q")), ("h", .load false (v "hc")), ("pv", .fld 0 (v "h")),
        ("y", .load false (v "pv"))]
    (.cas false false (v "pv") (v "y") (v "y") "u" (.ret .unit) (.ret .unit))
#guard rejects (checkDecl (queueLib pay) { deqD pay with body := casWide })
  "cas needs a one-word cell"
-- Comparing a pointer cell against an integer.
def casIll : Expr :=
  lets [("hc", .fld 0 (v "q"))]
    (.cas false false (v "hc") (.lit 0) (.lit 0) "u" (.ret .unit) (.ret .unit))
#guard rejects (checkDecl (queueLib .int) { deqD .int with body := casIll })
  "cas: the expected value does not have the cell's type"
-- Folding something that is not an unrolling of the node type.
def foldBad : Expr :=
  lets [("p", .new (v "x")), ("p2", .fold (v "p") (.ptr .own (node .int)))] (.ret .unit)
#guard rejects (checkDecl (queueLib .int) { mkQueueD .int with body := foldBad })
  "not one unrolling"
-- A node's successor is `Ptr?`, so an empty queue's dummy cannot be built without `null`.
def foldNoNull : Expr :=
  lets [("d0", .pair (v "x") (v "x")), ("d1", .new (v "d0")),
        ("d2", .fold (v "d1") (.ptr .own (node .int)))] (.ret .unit)
#guard rejects (checkDecl (queueLib .int) { mkQueueD .int with body := foldNoNull })
  "not one unrolling"

/-! ### The same queue, polymorphic

One copy of the code, checked once, for every payload type `α` whose kind is

    copy    — `deq` loads the value out of a shared node, so it is duplicated
    share   — the node is the target of a `pub` reference (row 16)
    noOwn   — and reaches no `own` reference (row 17)
    insens  — plain loads suffice (§3.8); drop it and `deq` must load with acq

The code is `queueLib` at `α = tvar 0`, with `enq` and `deq` passing `α` to
their own tail calls.  Each use instantiates `α` (row 18: prenex, kinded,
monomorphised); the instance is not re-checked, which is sound by `CoreLang`
§8's lemma — sampled there, T3's to prove. -/

def qκ : Kind := { share := true, noOwn := true, copy := true, insens := true }
def α : Ty := .tvar 0

def polyQueueLib (κ : Kind := qκ) : Prog :=
  [{ mkQueueD α with tparams := [κ] }, { enqD α [α] with tparams := [κ] },
   { enqueueD α [α] with tparams := [κ] }, { deqD α [α] with tparams := [κ] }]

#guard accepts (checkProg (polyQueueLib))

/-- A client: make a queue of `σ`, push one element, pop one. -/
def clientD (σ : Ty) (x₀ x₁ : At) : Decl where
  name := "client"; idx := []; arg := "a"
  argTy := .prod σ σ
  retTy := .sum σ .unit
  body := .split (v "a") "x0" "x1"
    (lets [("q", .call "mkQueue" [] x₀ [σ]), ("p", .pair (v "q") x₁),
           ("u", .call "enqueue" [] (v "p") [σ]), ("r", .call "deq" [] (v "q") [σ])]
      (.ret (v "r")))

def client (σ : Ty) : Decl := clientD σ (v "x0") (v "x1")

#guard accepts (checkDecl (polyQueueLib) (client .int))
#guard accepts (checkDecl (polyQueueLib) (client pay))
#guard accepts (checkDecl (polyQueueLib) (client (.ptr .pub .int)))
-- A polymorphic client of the polymorphic queue: `α` passes its kind on.
#guard accepts (checkDecl (polyQueueLib) { client α with tparams := [qκ] })

/-! At the use: the kind is the whole interface. -/

-- An `own` payload: not `noOwn`.
#guard rejects (checkDecl (polyQueueLib) (client (.ptr .own .int)))
  "does not have its parameter's kind"
-- A protocol word reaches no `own` reference, but it is affine: `copy` refuses it.
def wordClientD : Decl where
  name := "client"; idx := ["r"]; arg := "w"
  argTy := .word (.var 0) mutexP
  retTy := .unit
  body := lets [("q", .call "mkQueue" [] (v "w") [.word (.var 0) mutexP])] (.ret .unit)
#guard rejects (checkDecl (polyQueueLib) wordClientD) "does not have its parameter's kind"
-- A polymorphic client whose own parameter promises less than the queue needs.
-- Each field separately: a caller's parameter that drops one is refused.
#guard [{ qκ with copy := false }, { qκ with noOwn := false }, { qκ with share := false },
        { qκ with insens := false }].all fun κ =>
  rejects (checkDecl (polyQueueLib) { client α with tparams := [κ] })
    "does not have its parameter's kind"
-- A caller's kind that asserts *more* is fine (subkinding is `Kind.le`).
#guard accepts (checkDecl (polyQueueLib) { client α with tparams := [{ qκ with zero := true }] })
-- Forgetting the type argument.
def noTyArg : Expr := lets [("q", .call "mkQueue" [] (v "x0"))] (.ret .unit)
#guard rejects (checkDecl (polyQueueLib) { client .int with body := noTyArg })
  "wrong number of type arguments"

/-! In the body: each field of the kind is used, and removing it breaks the
generic check at the operation that needed it. -/

#guard rejects (checkProg (polyQueueLib { qκ with copy := false }))
  "load would duplicate an affine value"
#guard rejects (checkProg (polyQueueLib { qκ with noOwn := false })) "not shareable"
#guard rejects (checkProg (polyQueueLib { qκ with share := false })) "not shareable"
#guard rejects (checkProg (polyQueueLib { qκ with insens := false }))
  "a view-sensitive type needs acq"

/-! ### Exactly-once delivery: a queue of claim cells

The queue above is safe but promises nothing about *how many* dequeuers get an
element: its payload is copyable, so a `deq` that forgot its `cas` would hand
the same value to everyone, and the checker cannot object.  Here each node's
payload sits in a region owned by a **claim word** with a one-shot protocol

    state 0 (value 0): holds the region        state 1 (value 1): taken
    transition 0 → 1, and nothing out of 1

Winning the `cas 0 → 1` is the only way to get the region's token, and no
transition ever gives it back, so at most one thread ever holds it.  The
payload may now be exclusive — an `own` buffer, opened as the node's region
by the enqueuer (`own := true`: `region x` on the buffer itself, so the cell
is the buffer and its type stays shareable, D1) — and `deq` returns it as
`∃r. Ptr r τ × Tok r 1`: a region reference and the permanent right to use it.
Exactly-once is a typing fact, not a linearisability argument.

Because the protocol is monotone, the claimed region is unsealed until
`fence st` (§4.4 rule 7: an optimistic reader that saw state 0 must not see
the new owner's writes before the claim), and the token may not leave `deq`
before the fence. -/

def claimP : Proto := ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩], [(0, 1, 0)], false, [], [], [], false, false, false, false, false, []⟩
#guard pwf claimP && monotone claimP

/-- A claimed payload: its region reference, and the token for state 1. -/
def claimed (τ : Ty) : Ty :=
  .iex (.prod (.ptr (.rgn (.var 0)) (τ.shiftI 0)) (.tok (.var 0) (some (claimP, .lit 1))))

def cnode (τ : Ty) : Ty := .mu (.prod ((guardedBy claimP τ).shiftT 0) (.ptrOpt .pub (.tvar 0)))
def cqueue (τ : Ty) : Ty := .ptr .pub (.prod (.ptr .pub (cnode τ)) (.ptr .pub (cnode τ)))

/-- Put `x` in a fresh region (`own`: `x` is already an own cell of `τ`, which
becomes the region), give it to a claim word in state 0, and wrap the claim
cell in a published node `n`; then continue with `k`. -/
def withCNode (τ : Ty) (x n : String) (k : Expr) (own : Bool := false) : Expr :=
  let inRgn :=
    .region (v (if own then x else "p")) "r" "dp" "t0"
      (lets [("wv", .mkWord "r" claimP (.lit 0) (v "t0")), ("pr", .pair (v "wv") (v "dp")),
             ("s", .new (v "pr")), ("s2", .publish (v "s")),
             ("cc", .pack (v "s2") "r" (guardedBy claimP τ)),
             ("nl", .null .pub (cnode τ)), ("n0", .pair (v "cc") (v "nl")), ("n1", .new (v "n0")),
             ("n2", .fold (v "n1") (.ptr .own (cnode τ))), (n, .publish (v "n2"))] k)
  if own then inRgn else lets [("p", .new (v x))] inRgn

def cmkQueueD (τ : Ty) (own : Bool := false) : Decl where
  name := "mkQueue"; idx := []; arg := "x"
  argTy := if own then .ptr .own τ else τ
  retTy := cqueue τ
  body := withCNode τ "x" "d" (own := own)
    (lets [("c", .pair (v "d") (v "d")), ("c1", .new (v "c")), ("q", .publish (v "c1"))]
      (.ret (v "q")))

def cenqD (τ : Ty) : Decl where
  name := "enq"; idx := []; arg := "a"
  argTy := .prod (cqueue τ) (.ptr .pub (cnode τ))
  retTy := .unit
  body := .split (v "a") "q" "n" (enqLoop (cnode τ))

def cenqueueD (τ : Ty) (own : Bool := false) : Decl where
  name := "enqueue"; idx := []; arg := "a"
  argTy := .prod (cqueue τ) (if own then .ptr .own τ else τ)
  retTy := .unit
  body := .split (v "a") "q" "x"
    (withCNode τ "x" "n" (lets [("b", .pair (v "q") (v "n"))] (.tail "enq" [] (v "b"))) (own := own))

/-- Swing `head`, then claim the new front's payload.  Each ingredient is
switchable so that the hazards below are this program with one thing changed. -/
def cdeqBody (τ : Ty) (swing : Bool := true) (claimAcq : Bool := true)
    (fenceSt : Bool := true) (expect : Nat := 0) (new : Nat := expect + 1) : Expr :=
  let retry := Expr.tail "deq" [] (v "q")
  let claim : Expr :=
    lets [("pv", .fld 0 (v "p")), ("c", .load false (v "pv"))]
      (.unpack (v "c") "r" "s"
        (lets [("w", .fld 0 (v "s"))]
          (.cas claimAcq false (v "w") (.lit expect) (.lit new) "t"
            (lets ((if fenceSt then [("f", .fence .st)] else []) ++
                   [("d0", .fld 1 (v "s")), ("d", .load false (v "d0")),
                    ("g", .pair (v "d") (v "t")), ("k", .pack (v "g") "r" (claimed τ)),
                    ("res", .inl .unit (v "k"))])
              (.ret (v "res")))
            retry)))
  lets [("hc", .fld 0 (v "q")), ("h", .load false (v "hc")), ("hn", .fld 1 (v "h")),
        ("nx", .load false (v "hn"))]
    (.ifnull (v "nx")
      (lets [("e", .inr (claimed τ) .unit)] (.ret (v "e")))
      "p"
      (if swing then .cas false false (v "hc") (v "h") (v "p") "u" claim retry else claim))

def cdeqD (τ : Ty) : Decl where
  name := "deq"; idx := []; arg := "q"
  argTy := cqueue τ
  retTy := .sum (claimed τ) .unit
  body := cdeqBody τ

/-- A buffer, owned by whoever dequeues it. -/
def buf : Ty := .ptr .own .int

/-- The winner uses what it claimed: the enqueuer's `own` buffer *is* the
region's cell, so it reads as `Ptr r Int`, and the token licenses reading and
writing it.  (Before D1 the buffer sat inside the region cell as an `own`
reference and was read out as `Ptr r Int` by `adapt`; D1 removes that reading.) -/
def useClaimedD : Decl where
  name := "useClaimed"; idx := []; arg := "k"
  argTy := claimed .int
  retTy := .unit
  body := .unpack (v "k") "r" "g"
    (.split (v "g") "b" "t"
      (lets [("x", .load false (v "b")), ("y", .add (v "x") (.lit 1)),
             ("u", .store false (v "b") (v "y") none)] (.ret .unit)))

/-- `own`: the queue of `own` cells of `τ` (each becomes its node's region). -/
def claimLib (τ : Ty) (own : Bool := false) : Prog :=
  [cmkQueueD τ own, cenqD τ, cenqueueD τ own, cdeqD τ]

#guard accepts (checkProg (claimLib .int true ++ [useClaimedD]))
-- `useClaimed` ends holding the claim's token.  It may: state 1 of `claimP` has
-- no move out, so the token is affine, not linear (`noDrop`); a mutex token is.
#guard rejects (checkDecl [useClaimedD] { useClaimedD with
    argTy := .iex (.prod (.ptr (.rgn (.var 0)) .int) (.tok (.var 0) (some (mutexP, .lit 1)))) })
  "still holds a token"
#guard accepts (checkProg (claimLib .int))
-- D1: an `own` reference may not sit *inside* a region cell; the pre-D1 queue
-- of `own` buffers (cell type `Ptr own Int`) is refused at its `region`.
#guard rejects (checkProg (claimLib buf)) "not shareable"
#guard rejects (checkProg (claimLib buf)) "intoRgn"
-- A queue of `own` buffers is exactly what the plain queue refuses.
#guard rejects (checkDecl (queueLib buf) (mkQueueD buf)) "not shareable"

/-! What each ingredient is for. -/

-- The broken `deq` of before, which never swings `head`, is still *accepted*:
-- every caller finds the same front node, one wins its claim, and the rest spin.
-- That is a liveness bug; nothing is delivered twice.
#guard accepts (checkDecl (claimLib .int true) { cdeqD .int with body := cdeqBody .int (swing := false) })

-- Skipping the claim: the payload is in a region whose token nobody here holds.
def noClaim : Expr :=
  lets [("hc", .fld 0 (v "q")), ("h", .load false (v "hc")), ("pv", .fld 0 (v "h")),
        ("c", .load false (v "pv"))]
    (.unpack (v "c") "r" "s"
      (lets [("d0", .fld 1 (v "s")), ("d", .load false (v "d0")), ("b", .load false (v "d"))]
        (.ret .unit)))
#guard rejects (checkDecl (claimLib buf) { cdeqD buf with body := noClaim })
  "without its token, and no observation"
-- Claiming from state 1: there is nothing to take, and no transition out.
#guard rejects (checkDecl (claimLib .int true) { cdeqD .int with body := cdeqBody .int (expect := 1) (new := 1) })
  "cas from a held state"
-- A claim without acq would read the payload before the enqueuer's writes.
#guard rejects (checkDecl (claimLib .int true) { cdeqD .int with body := cdeqBody .int (claimAcq := false) })
  "taking the region needs acq"
-- Handing the token out before `fence st`: the receiver would write unfenced.
#guard rejects (checkDecl (claimLib .int true) { cdeqD .int with body := cdeqBody .int (fenceSt := false) })
  "before fence st"
-- The same rule at `ret`: a block that claims and returns the bare token.
def claimTokD (fenceSt : Bool) : Decl where
  name := "claimTok"; idx := ["r"]; arg := "m"
  argTy := cell claimP .int
  retTy := .tok (.var 0) (some (claimP, .lit 1))
  body := lets [("w", .fld 0 (v "m"))]
    (.cas true false (v "w") (.lit 0) (.lit 1) "t"
      (lets (if fenceSt then [("f", .fence .st)] else []) (.ret (v "t")))
      (.tail "claimTok" ["r"] (v "m")))
#guard accepts (checkDecl [claimTokD true] (claimTokD true))
#guard rejects (checkDecl [claimTokD false] (claimTokD false)) "before fence st"
-- Using the claimed buffer twice over: the token is affine.
def useTwice : Expr :=
  .unpack (v "k") "r" "g"
    (.split (v "g") "d" "t"
      (lets [("g2", .pair (v "d") (v "t")), ("g3", .pair (v "d") (v "t"))] (.ret .unit)))
#guard rejects (checkDecl [useClaimedD] { useClaimedD with body := useTwice })
  "already used (affine)"

/-! ### Exactly-once delivery, polymorphic

The claim-cell queue again, written once for every payload type.  What is
striking is the kind it needs: **none**.  `α : {}` — not `copy`, not `share`,
not `noOwn`, not `insens` — where the plain polymorphic queue needed all four.
Each is discharged by the protocol instead:

    copy    — `deq` never loads an `α`; it hands over the region that holds it
    share   — behind `Ptr (rgn r)`, only the token holder writes (row 16)
    noOwn   — the caller opens the element's cell as a region (`region`, D1),
              and that is where the cell's type is checked shareable, at its
              concrete type; the queue only ever sees `Ptr r α` and `Tok r`
    insens  — the claim is an acquiring `cas` that reads the enqueuer's release

So the queue carries anything a thread can own: buffers (opened as regions),
pairs that would tear, even protocol words (a lock handed from thread to
thread).  What goes in is a *region package* `rpkg α = ∃r. Ptr r α × Tok r`:
the enqueuer's `region` on its own cell, packed.  The price is that generic
code cannot *look* at an `α` — only the monomorphic winner, who knows what `α`
is, can.  (This copies §6's claim queue rather than parameterising it, so each
version reads on its own.) -/

def pcκ : Kind := {}

/-- A cell of `τ` opened as a region, with the region's fresh token. -/
def rpkg (τ : Ty) : Ty := .iex (.prod (.ptr (.rgn (.var 0)) (τ.shiftI 0)) (.tok (.var 0) none))

/-- Open the package `x` (`r`, `dp : Ptr r α`, `t0 : Tok r`), give the region to
a claim word in state 0, and wrap the claim cell in a published node `n`. -/
def withPCNode (x n : String) (k : Expr) : Expr :=
  .unpack (v x) "r" "g" (.split (v "g") "dp" "t0"
    (lets [("wv", .mkWord "r" claimP (.lit 0) (v "t0")), ("pr", .pair (v "wv") (v "dp")),
           ("s", .new (v "pr")), ("s2", .publish (v "s")),
           ("cc", .pack (v "s2") "r" (guardedBy claimP α)),
           ("nl", .null .pub (cnode α)), ("n0", .pair (v "cc") (v "nl")), ("n1", .new (v "n0")),
           ("n2", .fold (v "n1") (.ptr .own (cnode α))), (n, .publish (v "n2"))] k))

def pcmkQueueD (κ : Kind := pcκ) : Decl where
  name := "mkQueue"; tparams := [κ]; idx := []; arg := "x"
  argTy := rpkg α
  retTy := cqueue α
  body := withPCNode "x" "d"
    (lets [("c", .pair (v "d") (v "d")), ("c1", .new (v "c")), ("q", .publish (v "c1"))]
      (.ret (v "q")))

def pcenqD (κ : Kind := pcκ) : Decl where
  name := "enq"; tparams := [κ]; idx := []; arg := "a"
  argTy := .prod (cqueue α) (.ptr .pub (cnode α))
  retTy := .unit
  body := .split (v "a") "q" "n" (enqLoop (cnode α) [α])

def pcenqueueD (κ : Kind := pcκ) : Decl where
  name := "enqueue"; tparams := [κ]; idx := []; arg := "a"
  argTy := .prod (cqueue α) (rpkg α)
  retTy := .unit
  body := .split (v "a") "q" "x"
    (withPCNode "x" "n" (lets [("b", .pair (v "q") (v "n"))] (.tail "enq" [] (v "b") [α])))

/-- `peek`: after claiming, also load the payload itself — which generic code
may not do, since `α` might be affine. -/
def pcdeqBody (fenceSt : Bool := true) (peek : Bool := false) : Expr :=
  let retry := Expr.tail "deq" [] (v "q") [α]
  let claim : Expr :=
    lets [("pv", .fld 0 (v "p")), ("c", .load false (v "pv"))]
      (.unpack (v "c") "r" "s"
        (lets [("w", .fld 0 (v "s"))]
          (.cas true false (v "w") (.lit 0) (.lit 1) "t"
            (lets ((if fenceSt then [("f", .fence .st)] else []) ++
                   [("d0", .fld 1 (v "s")), ("d", .load false (v "d0"))] ++
                   (if peek then [("y", .load false (v "d"))] else []) ++
                   [("g", .pair (v "d") (v "t")), ("k", .pack (v "g") "r" (claimed α)),
                    ("res", .inl .unit (v "k"))])
              (.ret (v "res")))
            retry)))
  lets [("hc", .fld 0 (v "q")), ("h", .load false (v "hc")), ("hn", .fld 1 (v "h")),
        ("nx", .load false (v "hn"))]
    (.ifnull (v "nx")
      (lets [("e", .inr (claimed α) .unit)] (.ret (v "e")))
      "p"
      (.cas false false (v "hc") (v "h") (v "p") "u" claim retry))

def pcdeqD (κ : Kind := pcκ) : Decl where
  name := "deq"; tparams := [κ]; idx := []; arg := "q"
  argTy := cqueue α
  retTy := .sum (claimed α) .unit
  body := pcdeqBody

def pcLib (κ : Kind := pcκ) : Prog := [pcmkQueueD κ, pcenqD κ, pcenqueueD κ, pcdeqD κ]

#guard accepts (checkProg (pcLib))

/-- `x` (a value of `σ`, or with `own` an own cell of `σ`) as a region package
`k`: allocate if needed, open the region, pack.  `σ` is relative to the scope
outside; `e` runs inside the region's binder (types there see `σ.shiftI 0`). -/
def mkPkg (σ : Ty) (x k : String) (own : Bool := false) : Expr → Expr :=
  fun e =>
    let rn := "r" ++ k
    let inRgn := .region (v (if own then x else "p" ++ k)) rn ("d" ++ k) ("t" ++ k)
      (lets [("g" ++ k, .pair (v ("d" ++ k)) (v ("t" ++ k))), (k, .pack (v ("g" ++ k)) rn (rpkg (σ.shiftI 0)))] e)
    if own then inRgn else lets [("p" ++ k, .new (v x))] inRgn

/-- Make a queue of `σ`, push one element, and claim one.  Each element is
used exactly once here, so `σ` may be affine.  With `own`, the elements come
in as own cells of `σ`, which become the regions. -/
def pcClientD (σ : Ty) (idx : List String := []) (own : Bool := false) : Decl where
  name := "client"; idx := idx; arg := "a"
  argTy := let τ := if own then .ptr .own σ else σ; .prod τ τ
  retTy := .sum (claimed σ) .unit
  body :=
    let σ1 := σ.shiftI 0
    let σ2 := σ1.shiftI 0
    .split (v "a") "x0" "x1"
      (mkPkg σ "x0" "k0" own (lets [("q", .call "mkQueue" [] (v "k0") [σ1])]
        (mkPkg σ1 "x1" "k1" own
          (lets [("p", .pair (v "q") (v "k1")), ("u", .call "enqueue" [] (v "p") [σ2]),
                 ("r", .call "deq" [] (v "q") [σ2])]
            (.ret (v "r"))))))

-- Everything the plain polymorphic queue refused, and what it accepted.  An
-- `own` buffer goes in as the region itself (`own := true`, element type `Int`);
-- inside a region cell it is refused, at the client's `region`.
#guard [.int, pay, .ptr .pub .int].all fun σ =>
  accepts (checkDecl (pcLib) (pcClientD σ))
#guard accepts (checkDecl (pcLib) (pcClientD .int (own := true)))
#guard rejects (checkDecl (pcLib) (pcClientD buf)) "must be moved in with intoRgn"
-- A protocol word: a lock (its word, and so its region) handed between threads.
#guard accepts (checkDecl (pcLib) (pcClientD (.word (.var 0) mutexP) ["r"]))
-- A polymorphic client: it opens the regions itself, so *its* `α` needs `noOwn`
-- (a region cell holds no `own` reference); the queue's `α` still needs nothing.
#guard accepts (checkDecl (pcLib) { pcClientD α with tparams := [{ noOwn := true }] })
#guard rejects (checkDecl (pcLib) { pcClientD α with tparams := [{}] }) "not shareable"

/-- The queue at `Int`, with its elements allocated here: for the machine runs. -/
def pcMkQueueID : Decl where
  name := "mkQueueI"; idx := []; arg := "x"; argTy := .int; retTy := cqueue .int
  body := mkPkg .int "x" "k" false (lets [("q", .call "mkQueue" [] (v "k") [.int])] (.ret (v "q")))
def pcEnqueueID : Decl where
  name := "enqueueI"; idx := []; arg := "a"; argTy := .prod (cqueue .int) .int; retTy := .unit
  body := .split (v "a") "q" "x"
    (mkPkg .int "x" "k" false (lets [("p", .pair (v "q") (v "k")), ("u", .call "enqueue" [] (v "p") [.int])]
      (.ret .unit)))
def pcIntLib : Prog := pcLib ++ [pcMkQueueID, pcEnqueueID]
#guard accepts (checkProg pcIntLib)
-- The contrast: the plain polymorphic queue refuses the `own` buffer and the word.
#guard rejects (checkDecl (polyQueueLib) (client buf)) "does not have its parameter's kind"

/-! What the protocol is still doing. -/

-- Generic code may not look at the payload: `α` might be affine.
#guard rejects (checkDecl (pcLib) { pcdeqD pcκ with body := pcdeqBody (peek := true) })
  "load would duplicate an affine value"
-- …though with `copy` it may, and nothing else changes.
#guard accepts (checkDecl (pcLib { copy := true })
    { pcdeqD { copy := true } with body := pcdeqBody (peek := true) })
-- The token may not leave before `fence st`, generic or not.
#guard rejects (checkDecl (pcLib) { pcdeqD pcκ with body := pcdeqBody (fenceSt := false) })
  "before fence st"
-- Skipping the claim is refused exactly as in the monomorphic version.
#guard rejects (checkDecl (pcLib) { pcdeqD pcκ with body := noClaim }) "without its token"

/-! ## Type existentials: a closure with a hidden environment

`pack a at [σ] : ∃(α:κ). b` and `let <[α], x> = unpack a`.  The package's
variable occurs only under a reference (`Ty.guardT`), and inside the unpack it
is *opaque*: nothing whose layout depends on it may be bound, allocated, or
passed as a type argument.  The witness is erased at runtime.  The closure
below is coupled (`E` in both words), so it is one two-word granule. -/

def cloK : Kind := { share := true, noOwn := true }

/-- `∃(E : {share, noOwn}). Code(Int × Ptr pub E, Int) × Ptr pub E`. -/
def cloT (κ : Kind := cloK) : Ty :=
  .tex κ (.prod (.code (.prod .int (.ptr .pub (.tvar 0))) .int .plain) (.ptr .pub (.tvar 0)))

#guard cloT.coupledOK && cloT.words == some 2

def addEnvD : Decl where
  name := "addEnv"; idx := []; arg := "a"
  argTy := .prod .int (.ptr .pub .int); retTy := .int
  body := .split (v "a") "n" "e"
    (lets [("k", .load false (v "e")), ("s", .add (v "n") (v "k"))] (.ret (v "s")))

/-- Close `addEnv` over an environment: the witness is `Int`. -/
def mkCloD (σ : Ty := .int) (target : Ty := cloT) : Decl where
  name := "mkClo"; idx := []; arg := "e"
  argTy := .ptr .pub σ; retTy := target
  body := lets [("f", .fnptr "addEnv"), ("p", .pair (v "f") (v "e")),
                ("c", .packT (v "p") σ target)] (.ret (v "c"))

def useCloBody (peek : Bool := false) : Expr :=
  .unpackT (v "c") "E" "q" (.split (v "q") "f" "e"
    (lets ((if peek then [("k", .load false (v "e"))] else []) ++
           [("a", .pair (.lit 5) (v "e")), ("r", .callc (v "f") (v "a"))]) (.ret (v "r"))))

/-- Call a closure without knowing its environment's type. -/
def useCloD : Decl where
  name := "useClo"; idx := []; arg := "c"
  argTy := cloT; retTy := .int
  body := useCloBody

def cloLib : Prog := [addEnvD, mkCloD, useCloD]

#guard accepts (checkProg cloLib)
-- The client may not look at the environment: its layout is the witness's.
-- (With `copy` and `insens`, so that the load is not refused for another reason first.)
def peekCloD : Decl :=
  { useCloD with argTy := cloT ({ cloK with copy := true, insens := true } : Kind),
                 body := useCloBody (peek := true) }
#guard rejects (checkDecl cloLib peekCloD) "unpacked type"
-- …nor let the environment escape: its type names the unpacked variable.
#guard rejects (checkDecl cloLib { useCloD with retTy := .ptr .pub .int, body := .unpackT (v "c") "E" "q" (.split (v "q") "f" "e" (.ret (v "e"))) })
  "does not have the return type"
-- …nor allocate at it.
#guard rejects (checkDecl cloLib { useCloD with
    body := .unpackT (v "c") "E" "q" (lets [("b", .newBuf (.lit 1) (.tvar 0))] (.ret (.lit 0))) })
  "unpacked type"
-- The witness must have the variable's kind: an `own` environment is refused.
#guard rejects (checkDecl cloLib (mkCloD (σ := .ptr .own .int))) "variable's kind"
-- Bare in a code type is not guarded here: the client could never supply an `E`.
#guard rejects (checkDecl cloLib { mkCloD with
    body := lets [("f", .fnptr "addEnv"), ("c", .packT (v "f") (.prod .int (.ptr .pub .int))
      (.tex {} (.code (.tvar 0) .int .plain)))] (.ret (.lit 0)) }) "only under a reference"
-- The variable must be guarded: `∃E. E × Int` would have a witness-dependent layout.
#guard rejects (checkDecl cloLib { mkCloD with
    body := lets [("p", .pair (.lit 1) (.lit 2)), ("c", .packT (v "p") .int (.tex {} (.prod (.tvar 0) .int)))]
      (.ret (.lit 0)) }) "only under a reference"

/-! ### `noWord`: a generic store cannot write a protocol word

A store to a word cell is a protocol step and needs the region's token.  A
generic `store`/`xchg` through `Ptr own α` used to be accepted at any kind, so
instantiating `α := Word[r, P]` wrote a word cell with no token.  The checker
now asks that the cell's type be word-free (`Ty.wordFreeIn`): a type variable
there needs kind `noWord` (or `copy`, which admits no word since words are
affine), and `noWord` refuses a word as the type argument. -/

def nwW : Ty := .word (.var 0) mutexP

def gstoreD (κ : Kind) : Decl where
  name := "gstore"; tparams := [κ]; idx := []; arg := "a"
  argTy := .prod (.ptr .own (.tvar 0)) (.tvar 0); retTy := .unit
  body := .split (v "a") "p" "w" (lets [("u", .store false (v "p") (v "w") none)] (.ret .unit))

def gxchgD (κ : Kind) : Decl where
  name := "gxchg"; tparams := [κ]; idx := []; arg := "a"
  argTy := .prod (.ptr .own (.tvar 0)) (.tvar 0); retTy := .tvar 0
  body := .split (v "a") "p" "w" (lets [("o", .xchg (v "p") (v "w"))] (.ret (v "o")))

def callStoreD (σ : Ty) : Decl where
  name := "main"; idx := ["r"]; arg := "a"
  argTy := .prod (.ptr .own σ) σ; retTy := .unit
  body := lets [("u", .call "gstore" [] (v "a") [σ])] (.ret .unit)

-- At the top kind the generic store and exchange are refused …
#guard rejects (checkDecl [] (gstoreD {})) "may hold a protocol word"
#guard rejects (checkDecl [] (gxchgD {})) "may hold a protocol word"
-- … at `noWord` they are accepted, and so is an instance at a token …
#guard accepts (checkDecl [] (gstoreD { noWord := true }))
#guard accepts (checkDecl [] (gxchgD { noWord := true }))
#guard accepts (checkDecl [gstoreD { noWord := true }] (callStoreD (.tok (.var 0) none)))
-- … but not at a protocol word, which a direct store refuses too.
#guard rejects (checkDecl [gstoreD { noWord := true }] (callStoreD nwW)) "parameter's kind"
#guard rejects (checkDecl [] { callStoreD nwW with
    body := .split (v "a") "p" "w" (lets [("u", .store false (v "p") (v "w") none)] (.ret .unit)) })
  "needs the region's token"
-- `copy` also suffices: a word is affine, so a `copy` kind admits none.
#guard accepts (checkDecl [] (gstoreD { copy := true }))
-- A refinement does not hide a word: `Ptr own {Word | tt}` takes no plain store.
#guard rejects (checkDecl [] { callStoreD (.refine nwW .tt) with
    body := .split (v "a") "p" "w" (lets [("u", .store false (v "p") (v "w") none)] (.ret .unit)) })
  "may hold a protocol word"

end CoreTerm
