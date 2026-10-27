import Scc.Lower.Spec

/-!
# The fragment `Accepted1`: several code blocks, calls, `if` and `-`

`Accepted0` (`Scc/Lower/Spec.lean`) is one code block `main` of straight-line
`let`s and checked `+`s. `Accepted1` widens it to several code blocks with
non-recursive calls between them, the integer `if` and the integer `-`:

* the program's code blocks have distinct names, and one of them is
  `main(u : Unit) : Int`; every other one takes one `Int` and returns an
  `Int`; none has type or index parameters;
* a body (`body1`) is a tree of `let`s ending in `ret` of an atom:
  - `let x = a`, `let x = a + b` (checked: it aborts on overflow, as in
    `Accepted0`), `let x = a - b` (saturating: scc emits `subs` and
    `csel hs`, the source's `TermRun.subW`, truncated `Nat` subtraction;
    the checker accepts it only where `b ≤ a` is provable, and it has no
    abort edge);
  - `let x = g(a)`, a call of a code block `g` declared **before** the
    caller (so the call graph is acyclic and scc's stack need is finite),
    not `main`, with no index or type arguments;
  - `if a = b then e₁ else e₂` on integer atoms (`ifeq`);
* atoms are variables bound before (or the code block's `Int` parameter),
  or integer literals below `2 ^ 63`;
* coherent immediates (`immsCoherent`): a let-bound literal is the same at
  every point with the same remaining term; programs that reuse a name with
  different literals are refused (`let x = 1  ret x` in one code block and
  `let x = 2  ret x` in another, or in the two arms of an `if`).

Not in the fragment: tail calls, externs (output, `park`), allocation,
memory operations, spawn, setup blocks, loops (a loop is a tail call). There
is no bound on the number of `let`s: the frames' sizes are a placement fact
of the output (`Scc.Cert.PlaceOK.A64.fnCode1Ok`), not a count here.

`accepted1_of_accepted0`: every `Accepted0` program is in `Accepted1`.
`Accepted1K` (`accepted1_of_K`): the same verdict with names compared as
numbers, the form for `decide +kernel` (a 100-`let` body: 4 s, 0.4 GB, against
13 s, 2 GB).
-/

open CoreLang CoreTerm

namespace Scc.Lower

/-- An atom of an `Accepted1` body: a variable in `scope` or an integer
literal below `2 ^ 63` (`atom0`). -/
abbrev atom1 (scope : List String) (a : At) : Bool := atom0 scope a

/-- A callee of an `Accepted1` body: a code block of `earlier` (the code
blocks declared before the caller), not `main`. -/
def callee1 (earlier : List String) (g : String) : Bool :=
  earlier.contains g && g != "main"

/-- An `Accepted1` body (see the module docstring): `scope` the variables
bound so far, `earlier` the code blocks it may call. -/
def body1 (earlier : List String) (scope : List String) : Expr → Bool
  | .let_ x (.atom a) e => atom1 scope a && body1 earlier (x :: scope) e
  | .let_ x (.add a b) e => atom1 scope a && atom1 scope b && body1 earlier (x :: scope) e
  | .let_ x (.sub a b) e => atom1 scope a && atom1 scope b && body1 earlier (x :: scope) e
  | .let_ x (.call g is a ts) e =>
      callee1 earlier g && is.isEmpty && ts.isEmpty && atom1 scope a && body1 earlier (x :: scope) e
  | .ifeq a b yes no => atom1 scope a && atom1 scope b && body1 earlier scope yes && body1 earlier scope no
  | .ret a => atom1 scope a
  | _ => false

/-- The variables in scope at an `Accepted1` code block's body: its
parameter for an `Int` code block, none for `main` (`Unit`). -/
def params1 (d : Decl) : List String :=
  if d.argTy == .int then [d.arg] else []

/-- An `Accepted1` code block, `earlier` the code blocks declared before
it: `main(u : Unit) : Int` or `f(x : Int) : Int`, no type or index
parameters, an `Accepted1` body. -/
def decl1 (earlier : List String) (d : Decl) : Bool :=
  d.tparams.isEmpty && d.idx.isEmpty && d.retTy == .int &&
    (if d.name == "main" then d.argTy == .unit else d.argTy == .int) &&
    body1 earlier (params1 d) d.body

/-- The code blocks of `p` in order, each with an `Accepted1` body that
calls only code blocks before it (`earlier`, the names so far). -/
def decls1 (earlier : List String) : Prog → Bool
  | [] => true
  | d :: ds => decl1 earlier d && decls1 (d.name :: earlier) ds

/-! ## Coherent immediates

The lowering keeps a variable bound to a literal (through `let`s of atoms)
as an immediate, and the runtime layout's immediate table is keyed by the
remaining term only. With several code blocks and `if`, one term can be
reached with a variable bound to different literals (`let x = 1  ret x` in
one code block, `let x = 2  ret x` in another); `Accepted1` rejects such
programs (`immsCoherent`), so that one table (`imms1Of`) serves them all. -/

/-- An atom's key: one token per atom. -/
def atKey : At → List (Nat × String × Nat)
  | .var x => [(0, x, 0)]
  | .lit n => [(1, "", n)]
  | .unit => [(2, "", 0)]

/-- A term's key: injective on the constructors of `body1` (anything else is
one token; `body1` rejects it). `Expr` has no decidable equality, so terms
are compared by key; the tag of `ifeq` carries its first branch's key length,
so the split is unambiguous. -/
def termKey : Expr → List (Nat × String × Nat)
  | .let_ x (.atom a) e => (3, x, 0) :: atKey a ++ termKey e
  | .let_ x (.add a b) e => (4, x, 0) :: atKey a ++ atKey b ++ termKey e
  | .let_ x (.sub a b) e => (5, x, 0) :: atKey a ++ atKey b ++ termKey e
  | .let_ x (.call g _ a _) e => (6, x, 0) :: (7, g, 0) :: atKey a ++ termKey e
  | .ifeq a b y n => (8, "", (termKey y).length) :: atKey a ++ atKey b ++ termKey y ++ termKey n
  | .ret a => (9, "", 0) :: atKey a
  | _ => [(10, "", 0)]

/-- An atom's literal, given the literal bindings `lits` (`some n` for a
variable bound to the literal `n`, `none` for any other binding). -/
def litOf (lits : List (String × Option Nat)) : At → Option Nat
  | .var x => (lits.lookup x).join
  | .lit n => some n
  | .unit => none

/-- The points of a body (each remaining term) with the literal bindings
visible there. -/
def litWalk (lits : List (String × Option Nat)) : Expr → List (Expr × List (String × Option Nat))
  | .let_ x op e =>
      (.let_ x op e, lits) ::
        litWalk ((x, match op with | .atom a => litOf lits a | _ => none) :: lits) e
  | .ifeq a b y n => (.ifeq a b y n, lits) :: (litWalk lits y ++ litWalk lits n)
  | t => [(t, lits)]

/-- The points of every code block of `p`, its parameter bound to no
literal. -/
def litWalks (p : Prog) : List (Expr × List (String × Option Nat)) :=
  p.flatMap fun d => litWalk ((params1 d).map (·, none)) d.body

/-- **The immediate table of an `Accepted1` program**: at term `t`, word 0 of
`x`, the literal of `x` at the first point with `t`'s key that binds `x` to
one. -/
def imms1Of (p : Prog) (t : Expr) (x : String) (k : Nat) : Option Nat :=
  if k = 0 then
    (litWalks p).findSome? fun q => if termKey q.1 == termKey t then (q.2.lookup x).join else none
  else none

/-- **Coherent immediates**: at every point, every variable bound to a
literal has that literal in `imms1Of p`. -/
def immsCoherent (p : Prog) : Bool :=
  (litWalks p).all fun q => q.2.all fun b =>
    match (q.2.lookup b.1).join with
    | some n => imms1Of p q.1 b.1 0 == some n
    | none => true

/-- **The fragment `Accepted1`** (see the module docstring): distinct code
block names, one of them `main`, every code block `decl1` in program
order, and coherent immediates (`immsCoherent`). -/
def Accepted1 (p : Prog) : Bool :=
  (p.map (·.name)).Nodup && p.any (·.name == "main") && decls1 [] p && immsCoherent p

/-! ## `Accepted0` is in `Accepted1` -/

/-- An `Accepted0` body is an `Accepted1` body (no calls, so any `earlier`). -/
theorem body1_of_body0 (earlier : List String) (scope : List String) (e : Expr)
    (h : body0 scope e = true) : body1 earlier scope e = true := by
  induction e generalizing scope with
  | let_ x op e ih =>
    cases op <;> simp only [body0, body1, atom1, Bool.and_eq_true, reduceCtorEq] at h ⊢
    · exact ⟨h.1, ih _ h.2⟩
    · exact ⟨h.1, ih _ h.2⟩
  | ret a => simpa [body0, body1, atom1] using h
  | _ => simp [body0] at h

/-- The points of an `Accepted0` body have keys no longer than its own. -/
theorem litWalk_key_le (e : Expr) : ∀ (scope : List String) (lits : List (String × Option Nat)),
    body0 scope e = true → ∀ r ∈ litWalk lits e, (termKey r.1).length ≤ (termKey e).length := by
  induction e with
  | let_ x op e ih =>
    intro scope lits h r hr
    cases op <;> simp only [body0, Bool.and_eq_true, reduceCtorEq] at h
    · simp only [litWalk, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Nat.le_refl _
      · have := ih _ _ h.2 r hr; simp only [termKey, List.length_cons, List.length_append]; omega
    · simp only [litWalk, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact Nat.le_refl _
      · have := ih _ _ h.2 r hr; simp only [termKey, List.length_cons, List.length_append]; omega
  | ret a => intro _ _ _ r hr; simp [litWalk] at hr; subst hr; exact Nat.le_refl _
  | _ => intro _ _ h; simp [body0] at h

/-- Along the walk of an `Accepted0` body, keys get strictly shorter. -/
theorem litWalk_pairwise (e : Expr) : ∀ (scope : List String) (lits : List (String × Option Nat)),
    body0 scope e = true →
      (litWalk lits e).Pairwise (fun q r => (termKey r.1).length < (termKey q.1).length) := by
  induction e with
  | let_ x op e ih =>
    intro scope lits h
    cases op <;> simp only [body0, Bool.and_eq_true, reduceCtorEq] at h
    · simp only [litWalk, List.pairwise_cons]
      refine ⟨fun r hr => ?_, ih _ _ h.2⟩
      have := litWalk_key_le e _ _ h.2 r hr
      simp only [termKey, List.length_cons, List.length_append]; omega
    · simp only [litWalk, List.pairwise_cons]
      refine ⟨fun r hr => ?_, ih _ _ h.2⟩
      have := litWalk_key_le e _ _ h.2 r hr
      simp only [termKey, List.length_cons, List.length_append]; omega
  | ret a => intro _ _ _; simp [litWalk]
  | _ => intro _ _ h; simp [body0] at h

/-- In a walk whose keys get strictly shorter, the first point with a
point's key is that point. -/
theorem findSome_key {β : Type} (g : Expr × List (String × Option Nat) → Option β) :
    ∀ (L : List (Expr × List (String × Option Nat))),
      L.Pairwise (fun q r => (termKey r.1).length < (termKey q.1).length) → ∀ q ∈ L,
        L.findSome? (fun r => if termKey r.1 == termKey q.1 then g r else none) = g q
  | [], _, q, hq => by simp at hq
  | a :: L, hp, q, hq => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hnone : L.findSome? (fun r => if termKey r.1 == termKey q.1 then g r else none) = none := by
        rw [List.findSome?_eq_none_iff]
        intro r hr
        have hlt := hp.1 r hr
        have hne : (termKey r.1 == termKey q.1) = false := by
          rw [beq_eq_false_iff_ne]; intro he; rw [he] at hlt; omega
        simp only [hne, Bool.false_eq_true, ite_false]
      simp only [List.findSome?_cons, beq_self_eq_true, ite_true]
      cases hg : g q
      · exact hnone
      · rfl
    · have hlt := hp.1 q hq'
      have hne : (termKey a.1 == termKey q.1) = false := by
        rw [beq_eq_false_iff_ne]; intro he; rw [he] at hlt; omega
      simp only [List.findSome?_cons, hne, Bool.false_eq_true, ite_false]
      exact findSome_key g L hp.2 q hq'

/-- An `Accepted0` program's immediates are coherent. -/
theorem immsCoherent_of_body0 (d : Decl) (h : body0 (params1 d) d.body = true) : immsCoherent [d] = true := by
  have hp := litWalk_pairwise d.body _ ((params1 d).map (·, none)) h
  simp only [immsCoherent, litWalks, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.all_eq_true]
  intro q hq b _
  split
  · rename_i n hn
    simp only [imms1Of, ite_true, litWalks, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [findSome_key (fun r => (r.2.lookup b.1).join) _ hp q hq, hn]
    simp
  · rfl

/-- **Every `Accepted0` program is in `Accepted1`**: its one code block is
`main(u : Unit) : Int`, with no parameter in scope and an `Accepted0`
body. -/
theorem accepted1_of_accepted0 {p : Prog} (h : Accepted0 p = true) : Accepted1 p = true := by
  match p, h with
  | [d], h =>
    simp only [Accepted0, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨hn, ht⟩, hi⟩, ha⟩, hr⟩, hb⟩, -⟩ := h
    have hp : params1 d = [] := by simp [params1, ha]
    have hc := immsCoherent_of_body0 d (by rw [hp]; exact hb)
    simp [Accepted1, decls1, decl1, hn, ht, hi, ha, hr, hp, body1_of_body0 [] [] d.body hb, hc]

/-! ## Keyed immediates

`immsCoherent` compares terms by `termKey`, lists of tokens carrying the
variables' names, and looks variables up by name: in the kernel each `String`
comparison encodes both strings in UTF-8, so `decide` on a 100-`let` body
takes seconds and gigabytes. The keyed twins below compute the walk once,
with each name encoded once into a number (`strKey`, injective), compare
numbers only, and filter a point's term once for all its variables;
`accepted1_of_K` turns their verdict into `Accepted1`'s. -/

/-- A byte string as a number: its bytes as digits base 257 (each byte plus
one, so no digit is zero). -/
def bytesKey : List UInt8 → Nat
  | [] => 0
  | b :: bs => bytesKey bs * 257 + (b.toNat + 1)

theorem bytesKey_inj : ∀ {bs cs : List UInt8}, bytesKey bs = bytesKey cs → bs = cs
  | [], [], _ => rfl
  | [], c :: cs, h => by simp only [bytesKey] at h; omega
  | b :: bs, [], h => by simp only [bytesKey] at h; omega
  | b :: bs, c :: cs, h => by
    have hb := b.toNat_lt
    have hc := c.toNat_lt
    simp only [bytesKey] at h
    have h1 : b.toNat = c.toNat := by omega
    have h2 : bytesKey bs = bytesKey cs := by omega
    rw [UInt8.toNat_inj.mp h1, bytesKey_inj h2]

/-- **A name as a number**: its UTF-8 bytes by `bytesKey`. -/
def strKey (s : String) : Nat := bytesKey s.toByteArray.data.toList

theorem strKey_inj {s t : String} (h : strKey s = strKey t) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.ext' (bytesKey_inj h)))

/-- A token of `termKey` as three numbers. -/
def tokK : Nat × String × Nat → List Nat
  | (a, s, n) => [a, strKey s, n]

/-- **A term's key as numbers**: `termKey`, each token by `tokK`. -/
def termKeyK (e : Expr) : List Nat := (termKey e).flatMap tokK

theorem flatMap_tokK_inj : ∀ {l m : List (Nat × String × Nat)}, l.flatMap tokK = m.flatMap tokK → l = m
  | [], [], _ => rfl
  | [], (_, _, _) :: _, h => by simp [tokK] at h
  | (_, _, _) :: _, [], h => by simp [tokK] at h
  | (a, s, n) :: l, (b, t, k) :: m, h => by
    simp only [List.flatMap_cons, tokK, List.cons_append, List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, hs, rfl, h⟩ := h
    rw [strKey_inj hs, flatMap_tokK_inj h]

theorem termKeyK_beq (e f : Expr) : (termKeyK e == termKeyK f) = (termKey e == termKey f) := by
  by_cases h : termKey e = termKey f
  · rw [termKeyK, termKeyK, h, beq_self_eq_true, beq_self_eq_true]
  · have h' : termKeyK e ≠ termKeyK f := fun he => h (flatMap_tokK_inj he)
    rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']

/-- Literal bindings with their names as numbers. -/
def keyLits (lits : List (String × Option Nat)) : List (Nat × Option Nat) :=
  lits.map fun b => (strKey b.1, b.2)

theorem lookup_keyLits (x : String) :
    ∀ lits : List (String × Option Nat), (keyLits lits).lookup (strKey x) = lits.lookup x
  | [] => rfl
  | (y, o) :: l => by
    simp only [keyLits, List.map_cons, List.lookup_cons]
    by_cases h : x = y
    · subst h; simp
    · have hk : (strKey x == strKey y) = false := by
        rw [beq_eq_false_iff_ne]; exact fun he => h (strKey_inj he)
      have hx : (x == y) = false := by rw [beq_eq_false_iff_ne]; exact h
      simp only [hk, hx]
      exact lookup_keyLits x l

/-- `litWalks` keyed: each point's term key and literal bindings as numbers. -/
def walkK (p : Prog) : List (List Nat × List (Nat × Option Nat)) :=
  (litWalks p).map fun q => (termKeyK q.1, keyLits q.2)

/-- The coherence of one keyed point `q` against the keyed walk `W`: the
points of `q`'s key are filtered out once (`imms1K` searches them for every
variable). -/
def cohK (W : List (List Nat × List (Nat × Option Nat))) (q : List Nat × List (Nat × Option Nat)) : Bool :=
  let Wt := W.filter fun r => r.1 == q.1
  q.2.all fun b =>
    match (q.2.lookup b.1).join with
    | some n => Wt.findSome? (fun r => (r.2.lookup b.1).join) == some n
    | none => true

/-- **`immsCoherent`, keyed**: the walk computed once, numbers compared. -/
def immsCoherentK (p : Prog) : Bool :=
  let W := walkK p
  W.all (cohK W)

theorem findSome_filter {α β : Type} (c : α → Bool) (g : α → Option β) :
    ∀ L : List α, L.findSome? (fun r => if c r then g r else none) = (L.filter c).findSome? g
  | [] => rfl
  | a :: L => by
    cases h : c a
    · simp only [List.findSome?_cons, h, Bool.false_eq_true, ite_false, List.filter_cons]
      exact findSome_filter c g L
    · simp only [List.findSome?_cons, h, ite_true, List.filter_cons]
      cases g a
      · exact findSome_filter c g L
      · rfl

theorem imms1K_eq (p : Prog) (t : Expr) (x : String) :
    ((walkK p).filter fun r => r.1 == termKeyK t).findSome? (fun r => (r.2.lookup (strKey x)).join) =
      imms1Of p t x 0 := by
  rw [← findSome_filter]
  simp only [walkK, imms1Of, ite_true, List.findSome?_map]
  congr 1
  funext r
  simp only [Function.comp, termKeyK_beq, lookup_keyLits]

theorem immsCoherentK_eq (p : Prog) : immsCoherentK p = immsCoherent p := by
  show (walkK p).all (cohK (walkK p)) = _
  rw [show (walkK p).all (cohK (walkK p)) =
      (litWalks p).all (cohK (walkK p) ∘ fun q => (termKeyK q.1, keyLits q.2)) from List.all_map]
  unfold immsCoherent
  congr 1
  funext q
  simp only [Function.comp, cohK]
  rw [keyLits, List.all_map, ← keyLits]
  congr 1
  funext b
  simp only [Function.comp]
  rw [lookup_keyLits]
  cases (q.2.lookup b.1).join with
  | some n => simp only [imms1K_eq]
  | none => rfl

/-- **`Accepted1`, keyed**: `immsCoherentK` for `immsCoherent`. -/
def Accepted1K (p : Prog) : Bool :=
  (p.map (·.name)).Nodup && p.any (·.name == "main") && decls1 [] p && immsCoherentK p

theorem Accepted1K_eq (p : Prog) : Accepted1K p = Accepted1 p := by
  simp only [Accepted1K, Accepted1, immsCoherentK_eq]

/-- `Accepted1` from its keyed form (the one to decide). -/
theorem accepted1_of_K {p : Prog} (h : Accepted1K p = true) : Accepted1 p = true :=
  Accepted1K_eq p ▸ h

end Scc.Lower
