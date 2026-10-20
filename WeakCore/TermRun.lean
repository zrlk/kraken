/-
# TermRun — the term layer run on the promise machine  (plan stage T2)

`CoreTerm` terms, executed by delegating every memory access to `Promises`'
own rules (`stepLoad`, `stepStore`, `stepRmw`, `stepFence`, the pair rules).
Nothing about ordering is decided here; this file only says which machine
access each term construct is.

Decisions, each with its reason:
  1. **Runtime types, for shape only.**  Syntax carries no widths or tiers, so
     each variable is bound to (type, words), the type computed as the checker
     would, type parameters substituted per frame, index terms ignored (they
     never change a shape).  Not a name→type table (sibling branches reuse
     names); not an elaborated IR (T3 would have to relate two languages).
  2. **`new` writes an `undef` message per cell first**, raises the thread's
     coherence past them, then runs the initialising stores.  `stepLoad` has no
     undef case; fresh memory holding "whatever was there" is this message.
  3. **Allocation labels are thread-local** (`freshLabel`): another thread's
     allocations cannot change the label a certifying run gets.  This is what
     makes a promise of a store of a *fresh* pointer possible at all.
  4. **Dependencies.**  The address word is always a dependency (obligation 7);
     a pointer data word goes in by register, so its view flows; every other
     data word, and every RMW operand, is a constant.  Moves keep words' views.
  5. **No control dependencies**: branch collapse is allowed (§1.2).
  6. **A multi-word access is one step**, its units in order; promises recover
     the reorderings.
  7. **Promises are unrestricted, certification is a `Prop`** (`Step`).  The
     explorer under-approximates both, so what it finds is real.
  8. **Boxed sums** are §3.5's born-frozen block: an injection allocates
     `[tag, payload…]`, fills it, `dmb ishst`, and yields the reference; a
     case chases it with address-dependent loads (`injM`/`projM`).
  9. **No step** for arrays, closures, unsubstituted type variables.

Build: LEAN_PATH=build lean TermRun.lean
-/
import WeakCore.Promises
import WeakCore.CoreTerm
import Std.Data.HashSet

namespace TermRun
open CoreLang CoreTerm
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A runtime word: a value together with its view and read timestamp. -/
abbrev Word := Promises.TVal

/-- A constant word (no view, no dependency). -/
def cst (v : Val) : Word := Promises.TVal.mk0 v

/-- A frame environment: variable, its (shape) type, and its words. -/
abbrev Env := List (String × Ty × List Word)

/-! ## §1 Layout -/

/-- One single-copy-atomic access: one word, or a 16-byte granule. -/
inductive Acc | one | two
  deriving DecidableEq, Repr

def Acc.size : Acc → Nat | .one => 1 | .two => 2

/-- The sequence of accesses that loads or stores a value of type `t`.
A coupled existential package (§3.8) is one access; a wide sum is one
granule.  `none`: no runtime layout (arrays, an unsubstituted variable). -/
def accs : Ty → Option (List Acc)
  | .unit | .void | .tok _ _ | .tok2 _ _ _ _ | .tokE _ _ _ | .share _ | .cap _ _ => some []
  | .int | .intS _ | .fix _ _ | .lanes _ _ => some [.one]
  | .prod a b => do pure ((← accs a) ++ (← accs b))
  | .refine t _ | .iall t | .mu t => accs t
  | .iex t =>
      if t.countI 0 ≥ 2 then
        match (Ty.iex t).rawWords with
        | some 0 => some [] | some 1 => some [.one] | some 2 => some [.two]
        | _ => accs t
      else accs t
  | .tex κ t =>
      if t.countT 0 ≥ 2 then
        match (Ty.tex κ t).rawWords with
        | some 0 => some [] | some 1 => some [.one] | some 2 => some [.two]
        | _ => accs t
      else accs t
  | s@(.sum _ _) => if s.tier = .wide then some [.two] else some [.one]
  | .array _ _ | .tvar _ => none
  | .word _ P => if P.ghost then some [] else some [.one]   -- a ghost word is erased
  | .word2 _ _ => some [.two]                                -- one granule (§3.5 tier 2)
  | .epair _ _ => some [.two]                                -- an epoch pair: the same granule
  | _ => some [.one]

/-- The flattened arms of a sum, as `CoreLang.info` sees them. -/
def armsOf : Ty → List Ty
  | .sum a b => armsOf a ++ armsOf b
  | .refine t _ | .iall t | .iex t | .mu t | .tex _ t => armsOf t
  | .void => []
  | t => [t]

/-- Is the head (under wrappers) a sum? -/
def sumHead : Ty → Bool
  | .sum _ _ => true
  | .refine t _ | .iall t | .iex t | .mu t | .tex _ t => sumHead t
  | _ => false

inductive ArmK | ptr | opt | nil | wide
  deriving DecidableEq, Repr

def armK (t : Ty) : ArmK :=
  let a := (info Ty.top t).arms
  if a = Arms.ptrArm then .ptr
  else if a = Arms.optArm then .opt
  else if a.wide = 0 ∧ a.ptrs = 0 then .nil
  else .wide

#eval accs (.prod .int (.ptr .pub .int))
#eval armsOf (.sum .unit (.sum .int .int))

def isPtrish (t : Ty) : Bool := armK t == .ptr || armK t == .opt

/-- Encode arm `j` (of the flattened arms `as`) with payload words `p`. -/
def encodeArm (tr : Tier) (as : List Ty) (j : Nat) (p : List Word) :
    Option (List Word) :=
  match tr with
  | .niche => do
      let arm ← as[j]?
      let slot := ((as.take j).filter isPtrish).length
      match armK arm, p with
      | .ptr, [w] | .opt, [w] =>
          match w.val with
          | .loc a _ => some [{ w with val := .loc a slot }]
          | .null => if armK arm == .opt then some [cst (.num j)] else none
          | _ => none
      | .nil, [] => some [cst (.num j)]
      | _, _ => none
  | .wide =>
      match p with
      | [] => some [cst (.num j), cst (.num 0)]
      | [w] => some [cst (.num j), w]
      | _ => none
  | .boxed => none

/-- Recover the arm index and payload words. -/
def decodeArm (tr : Tier) (as : List Ty) (ws : List Word) :
    Option (Nat × List Word) :=
  match tr, ws with
  | .niche, [w] =>
      match w.val with
      | .loc a g => do
          let (j, _) ← ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]?
          pure (j, [{ w with val := .loc a 0 }])
      | .num j => do
          let arm ← as[j]?
          match armK arm with
          | .nil => pure (j, [])
          | .opt => pure (j, [cst .null])
          | _ => none
      | _ => none
  | .wide, [t, w] =>
      match t.val with
      | .num j => do
          let arm ← as[j]?
          if arm.rawWords = some 0 then pure (j, []) else pure (j, [w])
      | _ => none
  | _, _ => none

/-- View a value of type `t` as (arm, payload); a non-sum is arm 0. -/
def asArm (t : Ty) (ws : List Word) : Option (Nat × List Word) :=
  if sumHead t then decodeArm t.tier (armsOf t) ws else some (0, ws)

/-- Build a value of type `t` from arm `j` and payload `p`. -/
def ofArm (t : Ty) (j : Nat) (p : List Word) : Option (List Word) :=
  if sumHead t then encodeArm t.tier (armsOf t) j p
  else if j == 0 then some p else none

section
private def tOpt : Ty := .sum (.ptr .pub .int) .unit
#eval (tOpt.tier, (ofArm tOpt 1 []).map (·.map (·.val)))
#eval ((ofArm tOpt 1 []).bind (asArm tOpt)).map (fun p => (p.1, p.2.map (·.val)))
private def tW : Ty := .sum .int .unit
#eval (tW.tier, (ofArm tW 0 [cst (.num 7)]).map (·.map (·.val)))
end

/-! ## §2 Memory accesses

Every access goes through the promise machine's own rules on a scratch
register file: register 0 is the address word (so the address is always a
dependency, obligation 7), registers 1 and 2 are data. -/

/-- The part of a thread the machine rules touch, plus bookkeeping. -/
structure St where
  mem      : Memory
  pairs    : List Ts
  vs       : VState
  promises : List Ts
  nalloc   : Nat
  /-- how many loads have returned `undef` -/
  undefs   : Nat
  deriving Inhabited

def regsOf (r0 r1 r2 : Word) : WeakMem.Reg → Word :=
  fun r => if r = 0 then r0 else if r = 1 then r1 else if r = 2 then r2 else cst (.num 0)

def mth (s : St) (r0 r1 r2 : Word) : Promises.Thread :=
  { prog := [], regs := regsOf r0 r1 r2, vs := s.vs, promises := s.promises }

def offs (a : Address) (k : Nat) : Address := { a with offset := a.offset + k }

def countUndef (ws : List Word) : Nat := (ws.filter (·.val == .undef)).length

/-- Load the units `us`, starting `k` words past `a`. -/
def loadUnits (arch : Arch) (pw : Word) (a : Address) (acq : Bool) :
    List Acc → Nat → St → List (St × List Word)
  | [], _, s => [(s, [])]
  | .one :: us, k, s =>
      (Promises.stepLoad arch s.mem s.pairs (mth s pw pw pw) 1 (offs a k) [0] acq).flatMap
        fun th =>
          let w := th.regs 1
          (loadUnits arch pw a acq us (k + 1)
              { s with vs := th.vs, undefs := s.undefs + countUndef [w] }).map
            fun (s', ws) => (s', w :: ws)
  | .two :: us, k, s =>
      (Promises.stepLoadPair arch s.mem s.pairs (mth s pw pw pw) 1 2 (offs a k) [0] acq).flatMap
        fun th =>
          let w0 := th.regs 1
          let w1 := th.regs 2
          (loadUnits arch pw a acq us (k + 2)
              { s with vs := th.vs, undefs := s.undefs + countUndef [w0, w1] }).map
            fun (s', ws) => (s', w0 :: w1 :: ws)

/-- A data word as a store operand: a pointer through its register (its view
and read timestamp flow into the store), anything else as a constant. -/
def dataE (r : WeakMem.Reg) (w : Word) : WeakMem.Expr :=
  match w.val with
  | .loc _ _ => .reg r
  | v => .const v

/-- The language's fetch-ops are the machine's. -/
def _root_.CoreTerm.FetchOp.kind : FetchOp → WeakMem.RmwKind
  | .add => .add | .or => .or | .and => .and | .xor => .xor

/-- What a fetch-op's result is tagged at runtime: the epoch package for an
epoch counter (the region is `0`, as every runtime word's is), else an `Int`. -/
def fetchRtTy (t : Ty) : Ty :=
  match wordOf t with
  | some (r, P) => if P.epoch then fetchEpochTy r P else .int
  | none => .int

/-- Store the words `ws` by units `us`, starting `k` words past `a`. -/
def storeUnits (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    List Acc → List Word → Nat → St → List St
  | [], _, _, s => [s]
  | .one :: us, w :: ws, i, s =>
      (Promises.stepStore k arch s.mem (mth s pw w w) (offs a i) (dataE 1 w) [0] rel).flatMap
        fun (mem', th) =>
          storeUnits k arch pw a rel us ws (i + 1)
            { s with mem := mem', vs := th.vs, promises := th.promises }
  | .two :: us, w0 :: w1 :: ws, i, s =>
      let (mem', pairs', th) :=
        Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
          (dataE 1 w0) (dataE 2 w1) [0] rel
      storeUnits k arch pw a rel us ws (i + 2)
        { s with mem := mem', pairs := pairs', vs := th.vs, promises := th.promises }
  | _, _, _, _ => []

def nWords (us : List Acc) : Nat := (us.map Acc.size).sum

/-- Thread-local allocation labels: thread `i` of `n` takes its `k`-th label
here, whatever the other threads do, so certification is stable under
interference. -/
def freshLabel (base n i k : Nat) : AllocLabel := base + i + n * k

theorem freshLabel_inj {base n i i' k k' : Nat} (hi : i < n) (hi' : i' < n)
    (h : freshLabel base n i k = freshLabel base n i' k') : i = i' ∧ k = k' := by
  have h0 : base + i + n * k = base + i' + n * k' := h
  have h1 : i + n * k = i' + n * k' := by omega
  have h2 : (i + n * k) % n = (i' + n * k') % n := by rw [h1]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hi'] at h2
  subst h2
  refine ⟨rfl, ?_⟩
  have hn : 0 < n := by omega
  have hm : n * k = n * k' := by omega
  exact Nat.eq_of_mul_eq_mul_left hn hm

/-- `new`: one `undef` message per cell first (fresh memory holds whatever was
there), coherence raised past them so the initialising stores come after, then
the initialising stores themselves, plain.  As in `allocBuf`, `vWr` is raised
to the last message in memory (`base + n - 1`, the pushed memory's size minus
one), even for a zero-word cell that pushes nothing: runtime obligation R11, the
allocator's header store orders the allocation after the thread's earlier
writes. -/
def alloc (k : Promises.Knobs) (arch : Arch) (lbl : AllocLabel) (us : List Acc)
    (ws : List Word) (s : St) : List (St × Word) :=
  let a : Address := ⟨lbl, 0⟩
  let n := nWords us
  let base := s.mem.size
  let mem := (List.range n).foldl (fun m j => m.push ⟨offs a j, .undef, 0⟩) s.mem
  let vs := s.vs
  let vs := { vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else vs.coh b
    vWr := max vs.vWr (base + n - 1) }
  let pw := cst (.loc a 0)
  (storeUnits k arch pw a false us ws 0
      { s with mem := mem, vs := vs, nalloc := s.nalloc + 1 }).map (·, pw)

/-- The flattened arm that is a sum's zero word (CoreLang's `zeroArmP`):
the first payload-free arm (niche), arm 0 (wide). -/
def zeroIdx : Tier → List Ty → Option Nat
  | .niche, as => as.findIdx? (·.payloadFree)
  | .wide, _ :: _ => some 0
  | _, _ => none

theorem armsOf_sizeOf : ∀ (t x : Ty), x ∈ armsOf t → sizeOf x ≤ sizeOf t
  | .sum a b, x, h => by
      simp only [armsOf, List.mem_append] at h
      rcases h with h | h
      · have := armsOf_sizeOf a x h; simp; omega
      · have := armsOf_sizeOf b x h; simp; omega
  | .refine t _, x, h => by have := armsOf_sizeOf t x (by simpa [armsOf] using h); simp; omega
  | .iall t, x, h => by have := armsOf_sizeOf t x (by simpa [armsOf] using h); simp; omega
  | .iex t, x, h => by have := armsOf_sizeOf t x (by simpa [armsOf] using h); simp; omega
  | .mu t, x, h => by have := armsOf_sizeOf t x (by simpa [armsOf] using h); simp; omega
  | .tex _ t, x, h => by have := armsOf_sizeOf t x (by simpa [armsOf] using h); simp; omega
  | .void, x, h => by simp [armsOf] at h
  | .prod _ _, x, h | .unit, x, h | .int, x, h | .intS _, x, h | .fix _ _, x, h | .lanes _ _, x, h | .code _ _, x, h
  | .array _ _, x, h | .ptr _ _, x, h | .ptrOpt _ _, x, h | .loc _ _, x, h | .word _ _, x, h
  | .tok _ _, x, h | .word2 _ _, x, h | .tok2 _ _ _ _, x, h | .share _, x, h | .cap _ _, x, h
  | .epair _ _, x, h | .tokE _ _ _, x, h
  | .tvar _, x, h => by
      simp [armsOf] at h; subst h; exact Nat.le_refl _

theorem armsOf_getElem_lt {a b arm : Ty} {j : Nat} (h : (armsOf (.sum a b))[j]? = some arm) :
    sizeOf arm < sizeOf (Ty.sum a b) := by
  have hm := List.mem_of_getElem? h
  simp only [armsOf, List.mem_append] at hm
  rcases hm with hm | hm
  · have := armsOf_sizeOf _ _ hm; simp; omega
  · have := armsOf_sizeOf _ _ hm; simp; omega

/-- The all-zero bits of a Zeroable type, word by word (§3.6: pre-zeroed pages),
as values (`zero`, `newBuf`).  A sum's is its zero arm (`zeroIdx`) with that
arm's zero payload.  `none` off `Zeroable`. -/
def zeroWords : Ty → Option (List Val)
  | .unit => some []
  | .int | .intS _ => some [.num 0]
  | .fix _ _ | .lanes _ _ => some [.num 0]
  | .ptrOpt _ _ => some [.null]
  | .loc _ (.array _ _) => some [.null]
  | .prod a b => do pure ((← zeroWords a) ++ (← zeroWords b))
  | .refine t _ | .iall t | .iex t | .mu t => zeroWords t
  | .sum a b =>
      match hz : zeroIdx (Ty.sum a b).tier (armsOf (.sum a b)) with
      | none => none
      | some j =>
          match ha : (armsOf (.sum a b))[j]? with
          | none => none
          | some arm => do
              let p ← zeroWords arm
              let ws ← encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j (p.map cst)
              pure (ws.map (·.val))
  | _ => none
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have h := armsOf_getElem_lt (by assumption); simp at h; omega)

/-- `newBuf`: `n` cells, each with one first message — the zero of its type if
`zero` gives one (a pre-zeroed page, below every view), else `undef` — and
coherence raised past them.  `vWr` is raised to the last message in memory
(`base + n - 1`, the pushed memory's size minus one), so a later `dmb st`
(e.g. `publish`'s) orders the pushed messages before anything that hands the
buffer out: zeroed pages are synchronised before hand-out.  With `n = 0`
nothing is pushed but `vWr` is still raised: runtime obligation R11, the
allocator's header store orders every allocation after the thread's earlier
writes, so a pointer to a cell cannot be promised before the cell exists.
No initialising stores: slots are written by `bufInit`. -/
def allocBuf (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) : St × Word :=
  let a : Address := ⟨lbl, 0⟩
  let base := s.mem.size
  let val (j : Nat) : Val :=
    match zero with
    | some (z :: zs) => (z :: zs).getD (j % (z :: zs).length) .undef
    | _ => .undef
  let mem := (List.range n).foldl (fun m j => m.push ⟨offs a j, val j, 0⟩) s.mem
  let vs := s.vs
  let vs := { vs with
    coh := fun b => if b.label = lbl ∧ b.offset < n then base + b.offset else vs.coh b
    vWr := max vs.vWr (base + n - 1) }
  ({ s with mem := mem, vs := vs, nalloc := s.nalloc + 1 }, cst (.loc a 0))

/-- The element type of a buffer's runtime type. -/
def bufElem : Ty → Option (Mode × Ty)
  | .refine (.loc μ (.array _ u)) _ => some (μ, u)
  | .loc μ (.array _ u) => some (μ, u)
  | _ => none

def numOf (ws : List Word) : Option Nat :=
  match ws with
  | [w] => match w.val with | .num n => some n | _ => none
  | _ => none

/-! ## §3 Threads -/

structure Frame where
  x    : String
  body : Expr
  env  : Env
  σs   : List Ty
  /-- The type the caller expects back: the callee's declared return type at
  the call's type arguments.  `ret` rebinds the value at it, as `enter` does
  for the argument, so the caller never sees the callee's runtime rendition
  (which `sub` may have weakened: `Ptr` for `Ptr?`, a dropped refinement). -/
  ty   : Ty

structure TTh where
  term     : Expr
  env      : Env
  σs       : List Ty := []
  stack    : List Frame := []
  vs       : VState := WeakMem.VState.init
  promises : List Ts := []
  nalloc   : Nat := 0
  undefs   : Nat := 0

/-- What a step needs to know about its surroundings. -/
structure G where
  p     : Prog
  k     : Promises.Knobs
  arch  : Arch
  n     : Nat
  i     : Nat
  lbase : Nat
  /-- the boxed injection's `dmb ishst`; off only to show it is needed -/
  boxFence : Bool := true
  /-- (iniop) **Proof-only ghost**: the labels at which a step's footprint keeps the counts
  (`TermStep.IniFixZ`, a conjunct of `TermStep.EFoot`).  Never read by the machine (`TermZf`);
  `gOf` sets it to `fun _ => False`. -/
  zf : AllocLabel → Prop := fun _ => False
  /-- (EFoot tags, PfrTag) **Proof-only ghost**: the labels at which a step may change the frontier
  of an existing cell (`TermStep.PfrG`, the last conjunct of `TermStep.EFoot`).  Never read by the
  machine (`TermPf`); `gOf` sets it to `fun _ => True`. -/
  pf : AllocLabel → Prop := fun _ => True

def ol {α : Type} (o : Option α) : List α := o.toList

def lookupE (env : Env) (x : String) : Option (Ty × List Word) :=
  (env.find? (·.1 == x)).map (·.2)

def evalAt (env : Env) : At → Option (Ty × List Word)
  | .var x => lookupE env x
  | .lit n => some (.intS (.lit n), [cst (.num n)])
  | .unit  => some (.unit, [])

def close (σs : List Ty) (τ : Ty) : Ty := substTs σs 0 0 τ

def addrOf (w : Word) : Option Address :=
  match w.val with
  | .loc a _ => some a
  | _ => none

def toWFence : Fence → WeakMem.Fence
  | .ld => .ld | .st => .st | .full => .sy

def fenceS (s : St) (f : WeakMem.Fence) : St :=
  let w := cst (.num 0)
  { s with vs := (Promises.stepFence (mth s w w w) f).vs }

def addW (a b : Word) : Word :=
  match a.val, b.val with
  | .num n, .num m => cst (.num (n + m))
  | _, _ => cst .undef

def subW (a b : Word) : Word :=
  match a.val, b.val with
  | .num n, .num m => cst (.num (n - m))
  | _, _ => cst .undef

/-! ### Fixed-width integers

A `fix sg w` value is its `w`-bit two's-complement pattern, a `Nat` below
`2^w`; signedness matters only to `fval`.  Every result goes through `fmask`, so
it is a pattern again.  Lanes are little-endian: lane `j` of `x` is bits
`[w·j, w·j + w)`. -/

def pw2 (w : Wd) : Nat := 2 ^ w.bits
def fmask (w : Wd) (x : Nat) : Nat := x % pw2 w
theorem pw2_pos (w : Wd) : 0 < pw2 w := Nat.two_pow_pos _
theorem fmask_lt (w : Wd) (x : Nat) : fmask w x < pw2 w := Nat.mod_lt _ (pw2_pos w)

/-- The value of the `w`-bit pattern `x`, signed or not. -/
def fval (sg : Bool) (w : Wd) (x : Nat) : Int :=
  let m := fmask w x
  if sg && 2 * m ≥ pw2 w then (m : Int) - pw2 w else m
/-- The `w`-bit pattern of `z`, wrapping. -/
def fenc (w : Wd) (z : Int) : Nat := fmask w (z % (pw2 w : Int)).toNat
/-- What `cvt` reads a source word as: a `fix` by its value, anything else as its bits. -/
def srcVal : Ty → Nat → Int
  | .fix sg w, x => fval sg w x
  | _, x => x
def cvtN (t : Ty) (w : Wd) (x : Nat) : Nat := fenc w (srcVal t x)

def fopRaw (sg : Bool) (w : Wd) : FOp → Nat → Nat → Nat
  | .add, x, y => x + y
  | .sub, x, y => fenc w ((x : Int) - y)
  | .mul, x, y => x * y
  | .div, x, y => fenc w (Int.tdiv (fval sg w x) (fval sg w y))
  | .rem, x, y => fenc w (Int.tmod (fval sg w x) (fval sg w y))
  | .and, x, y => x &&& y
  | .or,  x, y => x ||| y
  | .xor, x, y => x ^^^ y
  | .shl, x, y => x <<< (y % w.bits)
  | .shr, x, y => if sg then fenc w (fval sg w x >>> (y % w.bits)) else fmask w x >>> (y % w.bits)
def fopN (sg : Bool) (w : Wd) (o : FOp) (x y : Nat) : Nat := fmask w (fopRaw sg w o x y)

def fcmpN (sg : Bool) (w : Wd) (o : FCmp) (x y : Nat) : Nat :=
  let a := fval sg w x
  let b := fval sg w y
  let r : Bool := match o with
    | .eq => a == b | .ne => a != b | .lt => decide (a < b) | .le => decide (a ≤ b)
  if r then 1 else 0

def fop1N (sg : Bool) (w : Wd) : FOp1 → Nat → Nat
  | .not, x => fmask w (pw2 w - 1 - fmask w x)
  | .neg, x => fenc w (-(fval sg w x))

/-- Lane `j` of the word `x`. -/
def laneN (w : Wd) (x j : Nat) : Nat := fmask w (x / 2 ^ (w.bits * j))
/-- `x` with lane `j` replaced by `v`. -/
def setLaneN (w : Wd) (x j v : Nat) : Nat :=
  let sh := 2 ^ (w.bits * j)
  let x := x % 2 ^ 64
  x - laneN w x j * sh + fmask w v * sh

#guard fopN true .w8 .add 127 1 == 128                -- wraps to the pattern of -128
#guard fval true .w8 128 == -128
#guard fopN true .w8 .div (fenc .w8 (-7)) 2 == fenc .w8 (-3)
#guard fopN true .w8 .rem (fenc .w8 (-7)) 2 == fenc .w8 (-1)
#guard fopN false .w8 .div 7 0 == 0 && fopN false .w8 .rem 7 0 == 7
#guard fopN true .w8 .shr (fenc .w8 (-8)) 1 == fenc .w8 (-4)
#guard fopN false .w8 .shr 248 1 == 124
#guard fcmpN true .w8 .lt 255 0 == 1 && fcmpN false .w8 .lt 255 0 == 0
#guard cvtN (.fix true .w8) .w32 255 == 2 ^ 32 - 1     -- sign-extends
#guard cvtN (.fix false .w8) .w32 255 == 255           -- zero-extends
#guard cvtN .int .w8 300 == 44                         -- truncates
#guard fop1N true .w16 .neg 1 == 2 ^ 16 - 1 && fop1N false .w8 .not 0 == 255
#guard laneN .w8 0x0807060504030201 2 == 3
#guard setLaneN .w8 0x0807060504030201 2 0xff == 0x0807060504ff0201
#guard setLaneN .w16 0 3 0xabcd == 0xabcd000000000000

/-! ### 64-bit word primitives (swisstable) -/

def W64 : Nat := 2 ^ 64

/-- Byte `i` of `x`. -/
def byteAt (x i : Nat) : Nat := (x / 2 ^ (8 * i)) % 256

/-- Top bit of each of the 8 bytes of `x`, as an 8-bit mask. -/
def msb8 (x : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (byteAt x i / 128) * 2 ^ i) 0

/-- Bit `i` set iff byte `i` of `x` equals `b`. -/
def eq8 (x b : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => acc + (if byteAt x i == b % 256 then 2 ^ i else 0)) 0

def ctz64 (x : Nat) : Nat :=
  let x := x % W64
  ((List.range 64).find? fun i => (x >>> i) % 2 == 1).getD 64

def popcnt64 (x : Nat) : Nat :=
  let x := x % W64
  (List.range 64).foldl (fun acc i => acc + (x >>> i) % 2) 0

def bitN (o : BitOp) (a b : Nat) : Nat :=
  let a := a % W64
  let b := b % W64
  match o with
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => (a <<< (b % 64)) % W64
  | .shr => a >>> (b % 64)
  | .wadd => (a + b) % W64
  | .wsub => (a + W64 - b) % W64
  | .wmul => (a * b) % W64
  | .mulhi => a * b / W64
  | .msb16 => msb8 a + 256 * msb8 b

def bit1N (o : BitOp1) (a : Nat) : Nat :=
  let a := a % W64
  match o with
  | .not => W64 - 1 - a
  | .ctz => ctz64 a
  | .popcnt => popcnt64 a

/-- `pcmpeqb` + `pmovmskb` on the 16 bytes `lo:hi`. -/
def vmatchN (lo hi b : Nat) : Nat := eq8 (lo % W64) b + 256 * eq8 (hi % W64) b

/-- Type and word offset of the component at field path `p`. -/
def compOff : Ty → List Nat → Option (Ty × Nat)
  | t, [] => some (t, 0)
  | .prod a _, 0 :: p => compOff a p
  | .prod a b, 1 :: p => do
      let us ← accs a
      let (c, o) ← compOff b p
      pure (c, nWords us + o)
  | _, _ => none

def isBoxed (t : Ty) : Bool := sumHead t && t.tier == .boxed

/-- Build a value of type `t` from arm `j` and payload `p`.  Niche and wide
tiers are pure (`ofArm`).  The boxed tier is a born-frozen
block: allocate `[tag, payload…]`, fill it with plain stores, `dmb ishst`, and
the value is the one-word reference — §8's publication pattern, so a reader who
gets the reference by any route sees the filled block. -/
def injM (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) : List (St × List Word) :=
  if isBoxed t then
    match (armsOf t)[j]?.bind accs with
    | some us =>
        let lbl := freshLabel g.lbase g.n g.i s.nalloc
        (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p) s).map fun (s', pw) =>
          (if g.boxFence then fenceS s' .st else s', [pw])
    | none => []
  else ol ((ofArm t j p).map (s, ·))

/-- View a value of type `t` as (arm, payload).  For the boxed tier: load the
tag, then the arm's payload, both through the reference (address-dependent,
so no reader barrier — §3.5 property 3). -/
def projM (g : G) (s : St) (t : Ty) (ws : List Word) : List (St × Nat × List Word) :=
  if isBoxed t then
    match ws with
    | [pw] =>
        match addrOf pw with
        | some b =>
            (loadUnits g.arch pw b false [.one] 0 s).flatMap fun (s1, tw) =>
              match tw with
              | [tag] =>
                  match tag.val with
                  | .num j =>
                      match (armsOf t)[j]?.bind accs with
                      | some us => (loadUnits g.arch pw b false us 1 s1).map fun (s2, p) => (s2, j, p)
                      | none => []
                  | _ => []
              | _ => []
        | none => []
    | _ => []
  else ol ((asArm t ws).map fun (j, p) => (s, j, p))

/-- One operation: every outcome, as (state, runtime type, words).  `call` is
not here: it needs the frame stack. -/
def evalOp (g : G) (env : Env) (σs : List Ty) (s : St) : Op → List (St × Ty × List Word)
  | .atom a => ol ((evalAt env a).map fun (t, ws) => (s, t, ws))
  | .pair a b => ol do
      let (t, ws) ← evalAt env a
      let (u, us) ← evalAt env b
      pure (s, .prod t u, ws ++ us)
  | .inl τ a =>
      match evalAt env a with
      | some (t, ws) =>
          let S := Ty.sum t (close σs τ)
          (projM g s t ws).flatMap fun (s1, j, p) =>
            (injM g s1 S j p).map fun (s2, q) => (s2, S, q)
      | none => []
  | .inr τ a =>
      match evalAt env a with
      | some (t, ws) =>
          let τ' := close σs τ
          let S := Ty.sum τ' t
          (projM g s t ws).flatMap fun (s1, j, p) =>
            (injM g s1 S ((armsOf τ').length + j) p).map fun (s2, q) => (s2, S, q)
      | none => []
  | .add a b => ol do
      let (_, ws) ← evalAt env a
      let (_, us) ← evalAt env b
      match ws, us with
      | [x], [y] => pure (s, .int, [addW x y])
      | _, _ => none
  | .sub a b => ol do
      let (_, ws) ← evalAt env a
      let (_, us) ← evalAt env b
      match ws, us with
      | [x], [y] => pure (s, .int, [subW x y])
      | _, _ => none
  | .new a =>
      match evalAt env a with
      | none => []
      | some (t, ws) =>
          match accs t with
          | none => []
          | some us =>
              let lbl := freshLabel g.lbase g.n g.i s.nalloc
              (alloc g.k g.arch lbl us ws s).map fun (s', pw) => (s', .ptr .own t, [pw])
  | .null μ τ => [(s, .ptrOpt μ (close σs τ), [cst .null])]
  | .fold a τ => ol ((evalAt env a).map fun (_, ws) => (s, close σs τ, ws))
  | .publish a => ol do
      let (t, ws) ← evalAt env a
      match t with
      | .ptr _ u => pure (fenceS s .st, .ptr .pub u, ws)
      | .refine (.loc _ (.array n u)) ψ => pure (fenceS s .st, .refine (.loc .pub (.array n u)) ψ, ws)
      | _ => none
  -- `publish` with a region-mode result (D1): the same release fence.  Region
  -- ids are ghost at runtime (`lit 0`, as `region` binds them).
  | .intoRgn _ a => ol do
      let (t, ws) ← evalAt env a
      match t with
      | .ptr _ u => pure (fenceS s .st, .ptr (.rgn (.lit 0)) u, ws)
      | .refine (.loc _ (.array n u)) ψ => pure (fenceS s .st, .refine (.loc (.rgn (.lit 0)) (.array n u)) ψ, ws)
      | _ => none
  | .fld i a => ol do
      let (t, ws) ← evalAt env a
      let pw ← match ws with | [w] => some w | _ => none
      let (μ, u) ← cellOf t
      let (c1, c2) ← match unfold1 u with | .prod c1 c2 => some (c1, c2) | _ => none
      let off ← if i == 0 then some 0 else nWords <$> accs c1
      match pw.val with
      | .loc b g => pure (s, .loc μ (if i == 0 then c1 else c2),
                          [{ pw with val := .loc (offs b off) g }])
      | _ => none
  | .load acq a =>
      match evalAt env a with
      | some (t, [pw]) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              let rt := if (wordOf t).isSome then Ty.int else u
              match accs u with
              | some us => (loadUnits g.arch pw b acq us 0 s).map fun (s', ws) => (s', rt, ws)
              | none => []
          | _, _ => []
      | _ => []
  | .store rel a v _ =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, ws) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              match accs u with
              | some us => (storeUnits g.k g.arch pw b rel us ws 0 s).map (·, .unit, [])
              | none => []
          | _, _ => []
      | _, _ => []
  | .fence f => [(fenceS s (toWFence f), .unit, [])]
  | .mkWord _ P v _ =>
      if P.ghost then [(s, .prod (.word (.lit 0) P) (.tok (.lit 0) none), [])]  -- no runtime word
      else ol ((evalAt env v).map fun (_, ws) => (s, .word (.lit 0) P, ws))
  -- A pair: two words, moved as one granule (`Acc.two`: `stepLoadPair`,
  -- `stepStorePair`).  Reading one yields the plain `Int × Int`.
  | .mkWord2 _ P v0 v1 _ => ol do
      let (_, w0) ← evalAt env v0
      let (_, w1) ← evalAt env v1
      pure (s, .word2 (.lit 0) P, w0 ++ w1)
  | .ldp acq a _ _ =>
      match evalAt env a with
      | some (t, [pw]) =>
          if pairRef t then
            match addrOf pw with
            | some b =>
                (loadUnits g.arch pw b acq [.two] 0 s).map fun (s', ws) => (s', .prod .int .int, ws)
            | none => []
          else []
      | _ => []
  | .stp rel a v0 v1 _ =>
      match evalAt env a, evalAt env v0, evalAt env v1 with
      | some (t, [pw]), some (_, w0), some (_, w1) =>
          match word2Of t, addrOf pw with
          | some _, some b => (storeUnits g.k g.arch pw b rel [.two] (w0 ++ w1) 0 s).map (·, .unit, [])
          | _, _ => []
      | _, _, _ => []
  -- An epoch pair: laid out and moved exactly as a protocol pair is.
  | .mkEPair _ P v0 v1 => ol do
      let (_, w0) ← evalAt env v0
      let (_, w1) ← evalAt env v1
      pure (s, .epair (.lit 0) P, w0 ++ w1)
  -- A ticket lock: two words, dispenser then owner, both at `v`.
  | .mkTicket _ N P v _ =>
      ol ((evalAt env v).map fun (_, ws) => (s, .prod (.word (.lit 0) N) (.word (.lit 0) P), ws ++ ws))
  -- Acquisition by observation is a typing step: no instruction, a zero-width token.
  | .claim _ _ => [(s, .unit, [])]
  -- A fetch-op: one RMW (`Promises.stepRmw`) whose write is the value read
  -- combined with the operand, and whose result is the value read.  The
  -- operand goes in as `cas`'s new value does (`dataE`, register 1, which is
  -- also `dst`; the rule reads it before the load overwrites it).
  | .fetch o acq rel a v =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, [nw]) =>
          match addrOf pw with
          | some b =>
              (Promises.stepRmw g.k g.arch s.mem s.pairs (mth s pw nw nw) 1 b o.kind (dataE 1 nw)
                  [0] acq rel).map fun (mem', th') =>
                let rd := th'.regs 1
                ({ s with mem := mem', vs := th'.vs, promises := th'.promises,
                          undefs := s.undefs + countUndef [rd] }, fetchRtTy t, [rd])
          | none => []
      | _, _ => []
  | .pack a _ τ => ol ((evalAt env a).map fun (_, ws) => (s, close σs τ, ws))
  -- The witness is erased: the package is laid out as its guarded body is.
  | .packT a _ τ => ol ((evalAt env a).map fun (_, ws) => (s, close σs τ, ws))
  | .validate y => ol ((lookupE env y).map fun (t, ws) => (s, t, ws))
  | .call .. => []
  -- a spawn is a configuration step (`TermSpawnStep.StepX.spawn`), not a thread step.
  | .spawn .. => []
  -- Capabilities are zero-width: lending and taking back are no-ops at runtime.
  | .borrow c _ => [(s, .cap c (.lit 0), [])]
  | .freeze _ => [(s, .cap .frz (.lit 0), [])]
  -- Fixed-width integers: pure.
  | .cvt sg w a => ol do
      let (t, ws) ← evalAt env a
      let x ← numOf ws
      pure (s, .fix sg w, [cst (.num (cvtN t w x))])
  | .toInt a => ol do
      let x ← numOf (← evalAt env a).2
      pure (s, .int, [cst (.num x)])
  | .asLanes sg w a => ol do
      let x ← numOf (← evalAt env a).2
      pure (s, .lanes sg w, [cst (.num (x % W64))])
  | .fop o a b => ol do
      let (t, ws) ← evalAt env a
      let (sg, w) ← fixOf t
      let x ← numOf ws
      let y ← numOf (← evalAt env b).2
      pure (s, .fix sg w, [cst (.num (fopN sg w o x y))])
  | .fcmp o a b => ol do
      let (t, ws) ← evalAt env a
      let (sg, w) ← fixOf t
      let x ← numOf ws
      let y ← numOf (← evalAt env b).2
      pure (s, .int, [cst (.num (fcmpN sg w o x y))])
  | .fop1 o a => ol do
      let (t, ws) ← evalAt env a
      let (sg, w) ← fixOf t
      let x ← numOf ws
      pure (s, .fix sg w, [cst (.num (fop1N sg w o x))])
  | .lane a j => ol do
      let (t, ws) ← evalAt env a
      let (sg, w) ← lanesOf t
      let x ← numOf ws
      let jj ← numOf (← evalAt env j).2
      pure (s, .fix sg w, [cst (.num (laneN w x (jj % w.lanes)))])
  | .setLane a j v => ol do
      let (t, ws) ← evalAt env a
      let (sg, w) ← lanesOf t
      let x ← numOf ws
      let jj ← numOf (← evalAt env j).2
      let y ← numOf (← evalAt env v).2
      pure (s, .lanes sg w, [cst (.num (setLaneN w x (jj % w.lanes) y))])
  -- Lanes of an own buffer.  In the model a lane store is the owner's word
  -- read-modify-write; compiled, it is one sub-word store.  They agree because
  -- nobody else can see the word (T3c's obligation).
  | .ldl b i =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match lanesOf u with
              | some (sg, w) =>
                  (loadUnits g.arch pw (offs a (j / w.lanes)) false [.one] 0 s).filterMap fun (s1, old) =>
                    (numOf old).map fun x => (s1, .fix sg w, [cst (.num (laneN w x (j % w.lanes)))])
              | none => []
          | _, _, _ => []
      | _, _ => []
  | .ldlw b wi jl =>
      match evalAt env b, evalAt env wi, evalAt env jl with
      | some (t, [pw]), some (_, iws), some (_, jws) =>
          match bufElem t, numOf iws, numOf jws, addrOf pw with
          | some (_, u), some i, some j, some a =>
              match lanesOf u with
              | some (sg, w) =>
                  (loadUnits g.arch pw (offs a i) false [.one] 0 s).filterMap fun (s1, old) =>
                    (numOf old).map fun x => (s1, .fix sg w, [cst (.num (laneN w x (j % w.lanes)))])
              | none => []
          | _, _, _, _ => []
      | _, _, _ => []
  | .stlw b wi jl v =>
      match evalAt env b, evalAt env wi, evalAt env jl, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, jws), some (_, vs) =>
          match bufElem t, numOf iws, numOf jws, numOf vs, addrOf pw with
          | some (_, u), some i, some j, some y, some a =>
              match lanesOf u with
              | some (_, w) =>
                  (loadUnits g.arch pw (offs a i) false [.one] 0 s).flatMap fun (s1, old) =>
                    match numOf old with
                    | some x =>
                        (storeUnits g.k g.arch pw (offs a i) false [.one]
                            [cst (.num (setLaneN w x (j % w.lanes) y))] 0 s1).map fun s2 => (s2, .unit, [])
                    | none => []
              | none => []
          | _, _, _, _, _ => []
      | _, _, _, _ => []
  | .stl b i v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, vs) =>
          match bufElem t, numOf iws, numOf vs, addrOf pw with
          | some (_, u), some j, some y, some a =>
              match lanesOf u with
              | some (_, w) =>
                  let a' := offs a (j / w.lanes)
                  (loadUnits g.arch pw a' false [.one] 0 s).flatMap fun (s1, old) =>
                    match numOf old with
                    | some x =>
                        (storeUnits g.k g.arch pw a' false [.one]
                            [cst (.num (setLaneN w x (j % w.lanes) y))] 0 s1).map fun s2 => (s2, .unit, [])
                    | none => []
              | none => []
          | _, _, _, _ => []
      | _, _, _ => []
  | .endBorrow _ => [(s, .unit, [])]
  -- `xchg`: a plain load then a plain store.  The checker allows it only on a
  -- cell this thread holds exclusively, so nothing can come between them.
  | .xchg a v =>
      match evalAt env a, evalAt env v with
      | some (t, [pw]), some (_, ws) =>
          match cellOf t, addrOf pw with
          | some (_, u), some b =>
              match accs u with
              | some us =>
                  (loadUnits g.arch pw b false us 0 s).flatMap fun (s1, old) =>
                    (storeUnits g.k g.arch pw b false us ws 0 s1).map fun s2 => (s2, u, old)
              | none => []
          | _, _ => []
      | _, _ => []
  -- A code value is the block's position in the program.
  | .fnptr f =>
      match g.p.findIdx? (·.name == f), g.p.find? (·.name == f) with
      | some i, some d => [(s, .code d.argTy d.retTy, [cst (.num i)])]
      | _, _ => []
  | .callc .. => []
  | .rem a n => ol do
      let (_, ws) ← evalAt env a
      let (_, ns) ← evalAt env n
      let x ← numOf ws
      let m ← numOf ns
      if m == 0 then none else pure (s, .int, [cst (.num (x % m))])
  | .nameI a => ol ((evalAt env a).map fun (t, ws) => (s, t, ws))
  -- By-value slot access on an own buffer: the thread holds it exclusively, so
  -- `xchgAt` is a plain load then a plain store, like `xchg`.
  | .xchgAt b i v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u with
              | some us =>
                  let a' := offs a (j * nWords us)
                  (loadUnits g.arch pw a' false us 0 s).flatMap fun (s1, old) =>
                    (storeUnits g.k g.arch pw a' false us xs 0 s1).map fun s2 => (s2, u, old)
              | none => []
          | _, _, _ => []
      | _, _, _ => []
  | .loadAt b i =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u with
              | some us =>
                  (loadUnits g.arch pw (offs a (j * nWords us)) false us 0 s).map fun (s1, old) =>
                    (s1, u, old)
              | none => []
          | _, _, _ => []
      | _, _ => []
  -- Pure 64-bit word primitives.
  | .bits o a b => ol do
      let x ← numOf (← evalAt env a).2
      let y ← numOf (← evalAt env b).2
      pure (s, .int, [cst (.num (bitN o x y))])
  | .bit1 o a => ol do
      let x ← numOf (← evalAt env a).2
      pure (s, .int, [cst (.num (bit1N o x))])
  | .vmatch lo hi b => ol do
      let x ← numOf (← evalAt env lo).2
      let y ← numOf (← evalAt env hi).2
      let z ← numOf (← evalAt env b).2
      pure (s, .int, [cst (.num (vmatchN x y z))])
  | .band a m => ol do
      let x ← numOf (← evalAt env a).2
      let y ← numOf (← evalAt env m).2
      pure (s, .int, [cst (.num ((x % W64) &&& y))])
  | .zero τ => ol do
      let τ' := close σs τ
      let z ← zeroWords τ'
      pure (s, τ', z.map cst)
  -- Field-path slot access: as `loadAt`/`xchgAt`, on the component's words only.
  | .xchgAtF b i p v =>
      match evalAt env b, evalAt env i, evalAt env v with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, compOff u p with
              | some us, some (c, o) =>
                  match accs c with
                  | some cs =>
                      let a' := offs a (j * nWords us + o)
                      (loadUnits g.arch pw a' false cs 0 s).flatMap fun (s1, old) =>
                        (storeUnits g.k g.arch pw a' false cs xs 0 s1).map fun s2 => (s2, c, old)
                  | none => []
              | _, _ => []
          | _, _, _ => []
      | _, _, _ => []
  | .loadAtF b i p =>
      match evalAt env b, evalAt env i with
      | some (t, [pw]), some (_, iws) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, compOff u p with
              | some us, some (c, o) =>
                  match accs c with
                  | some cs =>
                      (loadUnits g.arch pw (offs a (j * nWords us + o)) false cs 0 s).map
                        fun (s1, old) => (s1, c, old)
                  | none => []
              | _, _ => []
          | _, _, _ => []
      | _, _ => []
  -- §3.7 buffers.  A Zeroable element type is born initialised (zero messages);
  -- anything else is born `undef`, and only `bufInit` writes it.
  | .newBuf n τ => ol do
      let (_, ws) ← evalAt env n
      let k ← numOf ws
      let τ' := close σs τ
      let us ← accs τ'
      let w := nWords us
      let z := if zeroableIn [] [] τ' then zeroWords τ' else none
      let lbl := freshLabel g.lbase g.n g.i s.nalloc
      let (s', pw) := allocBuf lbl (k * w) z s
      let ini := if z.isSome then k else 0
      pure (s', .refine (.loc .own (.array (.lit k) τ')) (.ini (.lit ini)), [pw])
  | .idx b i => ol do
      let (t, ws) ← evalAt env b
      let pw ← match ws with | [w] => some w | _ => none
      let (_, iws) ← evalAt env i
      let j ← numOf iws
      let (μ, u) ← bufElem t
      let w ← nWords <$> accs u
      match pw.val with
      | .loc a gg => pure (s, .loc μ u, [{ pw with val := .loc (offs a (j * w)) gg }])
      | _ => none
  | .bufInit b i x =>
      match evalAt env b, evalAt env i, evalAt env x with
      | some (t, [pw]), some (_, iws), some (_, xs) =>
          match bufElem t, numOf iws, addrOf pw with
          | some (_, u), some j, some a =>
              match accs u, t with
              | some us, .refine (.loc μ (.array n _)) _ =>
                  (storeUnits g.k g.arch pw (offs a (j * nWords us)) false us xs 0 s).map
                    fun s' => (s', .refine (.loc μ (.array n u)) (.ini (.lit (j + 1))), [pw])
              | _, _ => []
          | _, _, _ => []
      | _, _, _ => []

def stOf (mem : Memory) (pairs : List Ts) (th : TTh) : St :=
  ⟨mem, pairs, th.vs, th.promises, th.nalloc, th.undefs⟩

def withS (th : TTh) (s : St) : TTh :=
  { th with vs := s.vs, promises := s.promises, nalloc := s.nalloc, undefs := s.undefs }

/-- Enter code block `f` (a call pushes the continuation first). -/
def enter (g : G) (th : TTh) (f : String) (ts : List Ty) (a : At) : Option TTh := do
  let d ← g.p.find? (·.name == f)
  let (_, ws) ← evalAt th.env a
  let σs' := (ts.map (close th.σs)).reverse
  pure { th with term := d.body, env := [(d.arg, close σs' d.argTy, ws)], σs := σs' }

/-- The frame a call to `f` at `ts` pushes, returning into `x` and then `e`. -/
def callFrame (g : G) (th : TTh) (f : String) (ts : List Ty) (x : String) (e : Expr) :
    Option Frame := do
  let d ← g.p.find? (·.name == f)
  pure ⟨x, e, th.env, th.σs, close (ts.map (close th.σs)).reverse d.retTy⟩

/-- The return type a code value's own runtime signature promises: a closure
call returns into the caller at the caller's rendition of the signature, not
the block's (24e).  The block may return a type that mentions its
environment's concrete type, which the caller knows only as the package's
variable — as `enter` rebinds an argument at the callee's rendition (F2). -/
def retOf : Ty → Ty → Ty
  | .code _ r, _ => r
  | _, t => t

def isDone (th : TTh) : Bool :=
  match th.term, th.stack with
  | .ret _, [] => true
  | _, _ => false

/-- One step of one thread: every outcome. -/
def tstep (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    List (Memory × List Ts × TTh) :=
  let s := stOf mem pairs th
  let same (th' : TTh) : List (Memory × List Ts × TTh) := [(mem, pairs, th')]
  let bind (x : String) (t : Ty) (ws : List Word) (e : Expr) : TTh :=
    { th with term := e, env := (x, t, ws) :: th.env }
  match th.term with
  | .let_ x (.call f _ a ts) e =>
      ol (((callFrame g th f ts x e).bind fun fr =>
          enter g { th with stack := fr :: th.stack } f ts a).map
        fun th' => (mem, pairs, th'))
  | .let_ x (.callc f a) e =>
      match evalAt th.env f with
      | some (tf, [w]) =>
          match w.val with
          | .num i =>
              match g.p[i]? with
              | some d =>
                  ol (((callFrame g th d.name [] x e).bind fun fr =>
                      enter g { th with stack := { fr with ty := retOf tf fr.ty } :: th.stack } d.name [] a).map
                    fun th' => (mem, pairs, th'))
              | none => []
          | _ => []
      | _ => []
  | .let_ x op e =>
      (evalOp g th.env th.σs s op).map fun (s', t, ws) =>
        (s'.mem, s'.pairs, withS (bind x t ws e) s')
  | .split a x y e =>
      match evalAt th.env a with
      | some (.prod u w, ws) =>
          match accs u with
          | some us =>
              let n := nWords us
              same { th with term := e, env := (y, w, ws.drop n) :: (x, u, ws.take n) :: th.env }
          | none => []
      | _ => []
  | .unpack a _ x e =>
      match evalAt th.env a with
      | some (.iex b, ws) => same (bind x b ws e)
      | _ => []
  -- The witness was erased; the variable is opaque in `e`, so any placeholder
  -- lays out the same.  `unit` stands in, in the value's type and the frame's.
  | .unpackT a _ x e =>
      match evalAt th.env a with
      | some (.tex _ b, ws) =>
          same { th with term := e, env := (x, Ty.substT 0 .unit b, ws) :: th.env, σs := .unit :: th.σs }
      | _ => []
  -- D1: opening a region publishes its cell (the release fence of `publish`);
  -- the token then gates the writes.
  | .region a _ pn tn e =>
      let s' := fenceS s .st
      let fenced (th' : TTh) : List (Memory × List Ts × TTh) := [(s'.mem, s'.pairs, withS th' s')]
      match evalAt th.env a with
      | some (.ptr _ u, ws) =>
          fenced { th with term := e,
                           env := (tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: th.env }
      | some (.refine (.loc _ u) ψ, ws) =>
          fenced { th with term := e,
                           env := (tn, .tok (.lit 0) none, []) ::
                                  (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: th.env }
      | _ => []
  | .openPub a _ pn cn e =>
      match evalAt th.env a with
      | some (.ptr _ u, ws) =>
          same { th with term := e,
                         env := (cn, .cap .pub (.lit 0), []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: th.env }
      | _ => []
  | .case a x e₁ y e₂ =>
      match evalAt th.env a with
      | some (t@(.sum u w), ws) =>
          (projM g s t ws).flatMap fun (s1, j, p) =>
            let n := (armsOf u).length
            let (ty, j', x', e') := if j < n then (u, j, x, e₁) else (w, j - n, y, e₂)
            (injM g s1 ty j' p).map fun (s2, q) =>
              (s2.mem, s2.pairs, withS (bind x' ty q e') s2)
      | _ => []
  | .ifnull a e₁ y e₂ =>
      match evalAt th.env a with
      | some (.ptrOpt μ u, [w]) =>
          match w.val with
          | .null => same { th with term := e₁ }
          | .loc _ _ => same (bind y (.ptr μ u) [w] e₂)
          | _ => []
      | _ => []
  | .parity a _ ev od =>
      match evalAt th.env a with
      | some (_, [w]) =>
          match w.val with
          | .num n => same { th with term := if n % 2 == 0 then ev else od }
          | _ => []
      | _ => []
  | .ifeq a b yes no =>
      match evalAt th.env a, evalAt th.env b with
      | some (_, [x]), some (_, [y]) =>
          match x.val, y.val with
          | .num n, .num m => same { th with term := if n == m then yes else no }
          | _, _ => []
      | _, _ => []
  -- The new value goes in as a store's does (`dataE`, register 1): a pointer
  -- is a register operand, so its view is a data dependency of the write and
  -- is published with it, exactly as `storeUnits` publishes a stored pointer's.
  -- Register 1 is also `dst`; the RMW reads its new value before the load
  -- overwrites it (`Promises.stepRmw`).
  | .cas acq rel w e v t ok fail =>
      match evalAt th.env w, evalAt th.env e, evalAt th.env v with
      | some (_, [pw]), some (_, [ew]), some (_, [nw]) =>
          match addrOf pw with
          | some b =>
              (Promises.stepRmw g.k g.arch mem pairs (mth s pw nw nw) 1 b (.cas ew.val) (dataE 1 nw)
                  [0] acq rel).map fun (mem', th') =>
                let rd := th'.regs 1
                let s' := { s with mem := mem', vs := th'.vs, promises := th'.promises,
                                   undefs := s.undefs + countUndef [rd] }
                let next := if rd.val == ew.val then bind t .unit [] ok else { th with term := fail }
                (mem', pairs, withS next s')
          | none => []
      | _, _, _ => []
  -- `casp`: `Promises.stepRmwPair` (CASP / `cmpxchg16b`); both halves must
  -- compare equal, and a failure writes nothing.  The new pair goes in as
  -- `cas`'s new value does (`dataE`, registers 1 and 2, which are also the
  -- destinations; the rule reads them before the load overwrites them).
  | .casp acq rel w e0 e1 v0 v1 t ok fail =>
      match evalAt th.env w, evalAt th.env e0, evalAt th.env e1, evalAt th.env v0, evalAt th.env v1 with
      | some (_, [pw]), some (_, [x0]), some (_, [x1]), some (_, [n0]), some (_, [n1]) =>
          match addrOf pw with
          | some b =>
              (Promises.stepRmwPair g.arch mem pairs (mth s pw n0 n1) 1 2 b x0.val x1.val
                  (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
                let r0 := th'.regs 1
                let r1 := th'.regs 2
                let s' := { s with mem := mem', vs := th'.vs, promises := th'.promises,
                                   undefs := s.undefs + countUndef [r0, r1] }
                let next := if r0.val == x0.val && r1.val == x1.val then bind t .unit [] ok
                            else { th with term := fail }
                (mem', pairs', withS next s')
          | none => []
      | _, _, _, _, _ => []
  | .ret a =>
      match th.stack, evalAt th.env a with
      | f :: rest, some (_, ws) =>
          same { th with term := f.body, env := (f.x, f.ty, ws) :: f.env, σs := f.σs, stack := rest }
      | _, _ => []
  | .tail f _ a ts => ol ((enter g th f ts a).map fun th' => (mem, pairs, th'))

/-! ## §4 The machine

A configuration is shared memory plus threads.  A thread step is `tstep`.  A
promise step appends an arbitrary message `⟨a, v, w⟩` with `w` below its own
timestamp (Promises' `promiseViews`) and records it as outstanding.  After
every step the stepping thread must be *certified*: alone, it can reach a
state with no outstanding promises (Promises §2.4, thread-local because other
threads only raise views). -/

structure Cfg where
  mem   : Memory
  pairs : List Ts := []
  ths   : Array TTh
  /-- labels allocated before the run -/
  lbase : Nat := 0
  /-- see `G.boxFence` -/
  boxFence : Bool := true
  /-- (M0) thread capacity: labels are striped by `Cfg.n`; `0` (the default) is today's machine -/
  cap : Nat := 0

/-- (M0) The label stripe width `max cap ths.size`: constant along runs (no step changes `cap` or
`ths.size`); `ths.size` when `cap = 0`. -/
def Cfg.n (c : Cfg) : Nat := max c.cap c.ths.size

theorem Cfg.size_le_n (c : Cfg) : c.ths.size ≤ c.n := Nat.le_max_right _ _

theorem Cfg.lt_n {c : Cfg} {i : Nat} (h : i < c.ths.size) : i < c.n := Nat.lt_of_lt_of_le h c.size_le_n

theorem Cfg.n_of_cap0 {c : Cfg} (h : c.cap = 0) : c.n = c.ths.size := by
  simp [Cfg.n, h]

def gOf (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) : G :=
  ⟨p, k, arch, c.n, i, c.lbase, c.boxFence, fun _ => False, fun _ => True⟩

def threadSteps (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) : List Cfg :=
  match c.ths[i]? with
  | none => []
  | some th =>
      (tstep (gOf p k arch c i) c.mem c.pairs th).map fun (mem, pairs, th') =>
        { c with mem := mem, pairs := pairs, ths := c.ths.set! i th' }

def promise (c : Cfg) (i : Nat) (a : Address) (v : Val) (w : Ts) : Cfg :=
  match c.ths[i]? with
  | none => c
  | some th =>
      { c with mem := c.mem.push ⟨a, v, w⟩
               ths := c.ths.set! i { th with promises := th.promises ++ [c.mem.size] } }

/-- Steps of thread `i` alone, promises included. -/
inductive Solo (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) : Cfg → Cfg → Prop
  | refl (c) : Solo p k arch i c c
  | thread {c c' c''} : c' ∈ threadSteps p k arch c i → Solo p k arch i c' c'' →
      Solo p k arch i c c''
  | prom {c c''} (a v w) : w < c.mem.size → Solo p k arch i (promise c i a v w) c'' →
      Solo p k arch i c c''

def noPromises (c : Cfg) (i : Nat) : Bool := (c.ths[i]?.map (·.promises.isEmpty)).getD true

def Certified (p : Prog) (k : Promises.Knobs) (arch : Arch) (c : Cfg) (i : Nat) : Prop :=
  ∃ c', Solo p k arch i c c' ∧ noPromises c' i = true

/-- The machine step: a thread or promise step of thread `i`, after which `i`
is certified. -/
inductive Step (p : Prog) (k : Promises.Knobs) (arch : Arch) : Cfg → Cfg → Prop
  | thread {c c'} (i) : c' ∈ threadSteps p k arch c i → Certified p k arch c' i →
      Step p k arch c c'
  | prom {c} (i a v w) : i < c.ths.size → w < c.mem.size →
      Certified p k arch (promise c i a v w) i → Step p k arch c (promise c i a v w)

def Cfg.final (c : Cfg) : Bool := c.ths.all fun th => isDone th && th.promises.isEmpty

/-! ### A bounded explorer

Under-approximates `Step`: promises are drawn from what bounded solo runs of
the thread actually store, and certification is a bounded solo search without
further promises.  So everything it finds is a real behaviour; what it does not
find within the bounds is merely not found. -/

/-- Bounded certification: some solo run of at most `fuel` thread steps
discharges every promise of thread `i`. -/
def certB (p : Prog) (k : Promises.Knobs) (arch : Arch) : Nat → Cfg → Nat → Bool
  | 0, c, i => noPromises c i
  | f + 1, c, i => noPromises c i || (threadSteps p k arch c i).any fun c' => certB p k arch f c' i

/-- Messages (other than `undef` initialisation) that thread `i` can append
running alone for at most `fuel` steps: the promise candidates. -/
def soloWrites (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) : Nat → Cfg → List (Address × Val)
  | 0, _ => []
  | f + 1, c =>
      (threadSteps p k arch c i).flatMap fun c' =>
        let fresh := ((c'.mem.toList.drop c.mem.size).filter (·.val != .undef)).map fun m => (m.loc, m.val)
        fresh ++ soloWrites p k arch i f c'

structure Bounds where
  depth  : Nat := 40
  solo   : Nat := 30
  /-- promises per thread outstanding at once -/
  maxP   : Nat := 1

def successorsAll (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (c : Cfg) : List Cfg :=
  (List.range c.ths.size).flatMap fun i =>
    let ts := (threadSteps p k arch c i).filter fun c' => certB p k arch b.solo c' i
    let ps :=
      match c.ths[i]? with
      | some th =>
          -- `k.promises = false` means no promise steps, as in
          -- `Promises.promiseSteps`.  (Runs with that knob off
          -- never explore promises.)
          if k.promises && th.promises.length < b.maxP && !isDone th then
            ((soloWrites p k arch i b.solo c).eraseDups.flatMap fun (a, v) =>
              (List.range c.mem.size).map fun w => promise c i a v w).filter
                fun c' => certB p k arch b.solo c' i
          else []
      | none => []
    ts ++ ps

/-- Does the next step of this term touch memory or the thread's views?  The
others (moves, branches, calls, returns) are *silent*. -/
def touchesMem (th : TTh) : Bool :=
  let boxedAt (a : At) : Bool :=
    match evalAt th.env a with
    | some (t, _) => isBoxed t || (match t with | .sum u w => isBoxed u || isBoxed w | _ => false)
    | none => false
  match th.term with
  | .let_ _ op _ =>
      match op with
      | .load .. | .store .. | .xchg .. | .fetch .. | .xchgAt .. | .loadAt .. | .xchgAtF .. | .loadAtF .. | .ldl .. | .stl .. | .ldlw .. | .stlw .. | .new _ | .publish _ | .intoRgn .. | .fence _ | .newBuf .. | .bufInit .. | .ldp .. | .stp .. | .spawn .. => true
      -- an injection allocates when the source or the sum is boxed
      | .inl τ a | .inr τ a =>
          boxedAt a || isBoxed τ ||
          (match evalAt th.env a with
           | some (t, _) => isBoxed (.sum t (close th.σs τ)) || isBoxed (.sum (close th.σs τ) t)
           | none => false)
      | _ => false
  | .cas .. | .casp .. => true
  -- opening a region fences (D1)
  | .region .. => true
  -- a case on a boxed sum loads; re-injecting into a boxed arm allocates
  | .case a .. => boxedAt a
  | _ => false

/-- Partial-order reduction.  A silent step reads and writes only its own
thread's term and environment, so it commutes with every step of every other
thread and with every promise, and it leaves certification unchanged (the
thread's future is the same).  Taking the first one available as the *only*
successor therefore loses no final configuration. -/
def successors (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (c : Cfg) : List Cfg :=
  let silent := (List.range c.ths.size).find? fun i =>
    match c.ths[i]? with
    | some th => !isDone th && !touchesMem th && !(threadSteps p k arch c i).isEmpty
    | none => false
  match silent with
  | some i => threadSteps p k arch c i
  | none => successorsAll p k arch b c

/-- Final configurations reachable within `fuel` steps (with repetition). -/
def explore (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) : Nat → Cfg → List Cfg
  | 0, _ => []
  | f + 1, c => if c.final then [c] else (successors p k arch b c).flatMap (explore p k arch b f)

/-! ### Memoised exploration

A spin loop (a failed `cas`, then `tail` back) re-reads the same message and
comes back to the *same* configuration, so the tree search above is
exponential in the depth.  This one is breadth-first over configurations
identified by a canonical key: memory, and for each thread its term, frames,
environment, promises and views, with `coh` read only at addresses that occur
in memory (the only ones it can matter at). -/

deriving instance Hashable for WeakMem.Address, Val
deriving instance BEq, Hashable for Promises.TVal, Msg
deriving instance Hashable for Idx, Mode, Cap, Pred, Atom, Kind, Clause, Proto, Rel2, Clause2, Proto2, ECounter, Wd, Ty
deriving instance Hashable for At, Fence, FOp, FCmp, FOp1, BitOp, BitOp1, FetchOp
deriving instance BEq, Hashable for Op, Expr

/-- A thread's part of the key.  `coh` is read at the given addresses only. -/
structure ThKey where
  term     : Expr
  env      : Env
  σs       : List Ty
  stack    : List (String × Expr × Env × List Ty × Ty)
  coh      : List Ts
  views    : Ts × Ts × Ts × Ts × Ts
  promises : List Ts
  nalloc   : Nat
  undefs   : Nat
  deriving BEq, Hashable

structure CfgKey where
  mem   : List Msg
  pairs : List Ts
  ths   : List ThKey
  deriving BEq, Hashable

def thKey (addrs : List Address) (th : TTh) : ThKey :=
  { term := th.term, env := th.env, σs := th.σs
    stack := th.stack.map fun f => (f.x, f.body, f.env, f.σs, f.ty)
    coh := addrs.map th.vs.coh
    views := (th.vs.vRd, th.vs.vWr, th.vs.vCtrl, th.vs.vPreBase, th.vs.vRelSt)
    promises := th.promises, nalloc := th.nalloc, undefs := th.undefs }

/-- The key is the data itself (structural equality and hashing), not its
`repr`: pretty-printing a configuration's terms was the whole cost of a run. -/
def cfgKey (c : Cfg) : CfgKey :=
  let ms := c.mem.toList
  let addrs := (ms.map (·.loc)).eraseDups
  { mem := ms, pairs := c.pairs, ths := c.ths.toList.map (thKey addrs) }

structure Explored where
  finals : List Cfg
  /-- configurations visited -/
  seen : Nat
  /-- `true` if the depth bound cut the search off -/
  cut : Bool

def exploreM (p : Prog) (k : Promises.Knobs) (arch : Arch) (b : Bounds) (fuel : Nat) (c : Cfg) :
    Explored := Id.run do
  let mut seen : Std.HashSet CfgKey := Std.HashSet.emptyWithCapacity.insert (cfgKey c)
  let mut frontier : List Cfg := [c]
  let mut finals : List Cfg := []
  for _ in [0:fuel] do
    if frontier.isEmpty then break
    let mut next : List Cfg := []
    for d in frontier do
      if d.final then finals := d :: finals
      else
        for e in successors p k arch b d do
          let key := cfgKey e
          if !seen.contains key then
            seen := seen.insert key
            next := e :: next
    frontier := next
  return ⟨finals, seen.size, !frontier.isEmpty⟩

/-! ## §5 Message passing: the ill-typed version reads `undef`, the repair never does -/

namespace MP

def flagTy : Ty := .ptr .pub (.ptrOpt .pub .int)

/-- Allocate a cell holding `x` and store the *owned* pointer to the flag:
no `publish`, so no `fence st` between the initialising store and the flag. -/
def writerBad : Decl where
  name := "writer"; idx := []; arg := "a"
  argTy := .prod flagTy .int
  retTy := .unit
  body := .split (v "a") "f" "x"
    (lets [("c", .new (v "x")), ("u", .store false (v "f") (v "c") none)] (.ret .unit))

/-- The repair: `publish` first. -/
def writerGood : Decl where
  name := "writer"; idx := []; arg := "a"
  argTy := .prod flagTy .int
  retTy := .unit
  body := .split (v "a") "f" "x"
    (lets [("c", .new (v "x")), ("q", .publish (v "c")),
           ("u", .store false (v "f") (v "q") none)] (.ret .unit))

/-- Plain load of the flag; if set, plain load through it. -/
def reader : Decl where
  name := "reader"; idx := []; arg := "f"
  argTy := flagTy
  retTy := .int
  body := lets [("r", .load false (v "f"))]
    (.ifnull (v "r") (.ret (.lit 0)) "p"
      (lets [("y", .load false (v "p"))] (.ret (v "y"))))

def progBad : Prog := [writerBad, reader]
def progGood : Prog := [writerGood, reader]

#guard !accepts (checkProg progBad)
#guard accepts (checkProg progGood)
#eval match checkProg progBad with | .error e => e | .ok _ => "accepted"

/-- The flag is label 0, initially null; fresh labels start at 1. -/
def init : Cfg where
  mem := #[⟨⟨0, 0⟩, .null, 0⟩]
  lbase := 1
  ths := #[
    { term := .tail "writer" [] (v "a"),
      env := [("a", .prod flagTy .int, [cst (.loc ⟨0, 0⟩ 0), cst (.num 42)])] },
    { term := .tail "reader" [] (v "a"),
      env := [("a", flagTy, [cst (.loc ⟨0, 0⟩ 0)])] }]

def resultOf (th : TTh) : Option Val :=
  match th.term with
  | .ret a => (evalAt th.env a).bind fun (_, ws) => ws.head?.map (·.val)
  | _ => none

/-- Distinct outcomes: the reader's result and whether any load saw `undef`. -/
def outcomes (p : Prog) (arch : Arch) (b : Bounds := {}) : List (Option Val × Bool) :=
  ((explore p Promises.Knobs.all arch b b.depth init).map fun c =>
    ((c.ths[1]?).bind resultOf, c.ths.any (·.undefs > 0))).eraseDups

def sawUndef (p : Prog) (arch : Arch) : Bool := (outcomes p arch).any (·.2)

-- ARM: without `publish` the flag store may be promised ahead of the
-- initialising store, and the reader then sees the cell's `undef`.
#guard sawUndef progBad .arm
#guard (outcomes progBad .arm).contains (some .undef, true)
-- The repair never does, on either architecture; TSO orders the stores anyway.
#guard !sawUndef progGood .arm
#guard !sawUndef progBad .tso
#guard !sawUndef progGood .tso
-- ... and it still has both real outcomes (the explorer is not vacuous).
#guard (outcomes progGood .arm).contains (some (.num 42), false)
#guard (outcomes progGood .arm).contains (some (.num 0), false)

/-- The witness: memory, in timestamp order, of a run where the reader saw
`undef`.  Expect the promised flag store *before* the `undef` initialisation
and the store of 42. -/
def witness : List (Nat × Nat × String × Nat) :=
  match (explore progBad Promises.Knobs.all .arm {} 40 init).find? (·.ths.any (·.undefs > 0)) with
  | some c => c.mem.toList.map fun m => (m.loc.label, m.loc.offset, toString (repr m.val), m.view)
  | none => []

#eval witness

/-- Does any reachable configuration (within `fuel` explorer steps) hold an
outstanding promise? -/
def anyProm (k : Promises.Knobs) (p : Prog) (arch : Arch) : Nat → Cfg → Bool
  | 0, _ => false
  | f + 1, c => c.ths.any (!·.promises.isEmpty) ||
      (successorsAll p k arch {} c).any (anyProm k p arch f)

-- The `promises` knob is honoured by the explorer: off, no promise is ever
-- made; on, the run above that needs one makes it.
#guard !anyProm { promises := false } progBad .arm 8 init
#guard anyProm Promises.Knobs.all progBad .arm 8 init

end MP

#print axioms freshLabel_inj

end TermRun

namespace TermSpawn
open CoreLang CoreTerm TermRun
open WeakMem (Ts)

/-- (barrier spawn) An argument word carries the setup's release view. -/
def bumpW (V : Ts) (w : Word) : Word := { w with view := max w.view V, rts := max w.rts V }

end TermSpawn

#print axioms TermRun.Cfg.size_le_n
#print axioms TermRun.Cfg.lt_n
#print axioms TermRun.Cfg.n_of_cap0
