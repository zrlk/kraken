/-
**The lowering of an `Accepted2` code block: closed form** (ISA-neutral),
the `Accepted2` twin of `Scc/Lower/InvC1.lean`'s `lowerC` with the
per-constructor inversions of `Spike/Lib/LowerShapeC1.lean`.

`Accepted2` (`Scc/Lower/Spec2.lean`) adds to `Accepted1`'s bodies the setup
block's buffer and lane stores, the output extern's call, and the
constructs that move words without code (`nameI`, pairs, `pack`, `asLanes`,
`let (x, y) = a`, `unpack`). `lowerC2` is what the term lowering
(`Scc.Lower.lowerExpr`, without the depth counter, as the program lowering
`lowerWithMarks` runs it) produces on them (`Res2`: `Res1` with the
registers marked as trace words):

* a `let` of an atom, `nameI`, a pair, `pack` or `asLanes` (`pureOp`) binds
  its operands' words and emits nothing; its registers are marked by the
  value's trace mask (`markR`, as `markWords`);
* `let (x, y) = a` and `unpack` rebind `a`'s words and emit nothing;
* `let x = newBuf[τ] n`, `n` an immediate: one `call [x%k] scc_rt_alloc
  [imm h, n, u]` (`newBufCall`), its return point marked with the `let`;
* `let x = xchg b[i] v`, `b`'s words a register base and an immediate
  offset, `i` an immediate, one-word elements and `v` one word: one load of
  the slot into `x%k` and one store of `v` to it (`xchgLoad`, `xchgStore`);
* `let x = print{i}(a)` (the extern), `a`'s words `[b, o, m, n]` with `o`
  a register: `callBlock`'s `.print` block (`printInsts`: `ext`, `add`,
  `mul`, `select`, `call scc_rt_print`), its call's return point marked with
  the `let`;
* `let`s of `+`, `-` and a call of a code block, `if` and `ret` (of any
  number of words) as `lowerC` without the depth counter.

Each construct's instructions are one contiguous run in the open block: no
construct but `if` closes a block.

* `lowerExpr_lowerC2`: `lowerExpr` is `lowerC2` (no depth counter);
* `lowerDeclMarks_lowerC2`: the lowering of a code block whose body has the
  closed form is `func2` with the trace `marks2` (as `lowerWithMarks` calls
  `lowerDeclMarks`);
* `lowerC2_atom_inv` … `lowerC2_ret_inv`: one inversion lemma per
  constructor.
-/
import Scc.Lower.InvC1

namespace Spike.Lib.LowerShape

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower
open Scc.Lower.Inv

set_option linter.unusedSimpArgs false

/-! ## Marking a value's words -/

/-- The registers among a value's words split by its trace mask `bs` as
`markWords` marks them: (scalar, trace), each in order. -/
def markSplit : List Bool → List Operand → List Reg × List Reg
  | b :: bs, .reg r :: ws =>
      let q := markSplit bs ws
      if b then (q.1, r :: q.2) else (r :: q.1, q.2)
  | _ :: bs, .imm _ :: ws => markSplit bs ws
  | _, _ => ([], [])

/-- **`markWords` as a function**: the registers among the words `ws` of a
value of type `t` that it marks scalar and trace, `none` where it fails. -/
def markR (t : Ty) (ws : List Operand) : Option (List Reg × List Reg) := do
  let bs ← Scc.Obj.traceMask t
  if bs.length = ws.length then some (markSplit bs ws) else none

/-! ## The constructs without code -/

/-- **The value of a `let` without code**: an atom and `nameI` their
operand's, `pack` its operand's words at the package's type, a pair its
parts' words, `asLanes` its one word as a lanes word. -/
def pureOp (env : Env) : Op → Option (Ty × List Operand)
  | .atom a | .nameI a => atomV env a
  | .pack a _ τ => (atomV env a).map fun v => (τ, v.2)
  | .pair a b => do
      let (t, ws) ← atomV env a
      let (u, us) ← atomV env b
      pure (.prod t u, ws ++ us)
  | .asLanes sg w a => do
      let (_, ws) ← atomV env a
      match ws with
      | [p] => some (.lanes sg w, [p])
      | _ => none
  | _ => none

/-- A reference value's `(base, offset word)` (`refOf`). -/
def refO : List Operand → Option (Operand × Operand)
  | [p] => some (p, imm 0)
  | [b, o] => some (b, o)
  | _ => none

/-! ## The constructs with code -/

/-- `countsOf` as a function. -/
def countsO (o : Scc.ObjLayout) (t : Ty) : Option (Nat × Nat) := do
  let r ← Scc.Obj.regOf t
  let c ← Scc.Obj.counts o t
  if c = r then some c else none

/-- The source units of a buffer of `k` elements of `ew` words (`newBuf`'s
`u`, `k` an immediate). -/
def unitsOf (ew : Nat) (k : UInt64) : Operand :=
  if ew = 0 then imm 1 else imm (k.toNat * ew + 1)

/-- **`newBuf`'s call** into `p` for `k` elements, header `h` and `u`
units. -/
def newBufCall (p : Reg) (h : Nat) (k : UInt64) (u : Operand) : Inst :=
  .call [p] Names.alloc [imm h, .imm k, u]

/-- The type of a new buffer of `τ` (`newBuf`'s result). -/
def newBufTy (τ : Ty) : Ty := .refine (.loc .own (.array (.lit 0) τ)) (.ini (.lit 0))

/-- The address of a word with layout slot `(tr, i)` in the cell at base
register `b` and immediate offset word `w` (`cellAddrs`' immediate case). -/
def slotAddr (o : Scc.ObjLayout) (b : Reg) (w : UInt64) : Bool × Nat → Addr := fun (tr, i) =>
  let bias := Scc.Obj.traceBias o
  let sb : Int := w.toNat % 2 ^ Scc.Obj.halfBits
  let tb : Int := w.toNat / 2 ^ Scc.Obj.halfBits
  if tr then ⟨b, -(bias + tb + 8 * i)⟩ else ⟨b, sb + 8 * i⟩

/-- **`xchg b[i] v`'s load** of the old element into `d`. -/
def xchgLoad (d : Reg) (a : Addr) : Inst := .load .plain .w64 d a

/-- **`xchg b[i] v`'s store** of `v`. -/
def xchgStore (a : Addr) (w : Operand) : Inst := .store .plain .w64 a w

/-- **The output extern's block** from counter `n` (`callBlock`'s `.print`
case, the slice's offset word a register `o`): `lo%n := ext32 o`,
`s%(n+1) := b + lo%n`, `cap%(n+2) := m · 8`, `k%(n+3) := min(c, cap%(n+2))`
(`select .ult`), `call scc_rt_print [s%(n+1), k%(n+3)]`. -/
def printInsts (n : Nat) (b o m c : Operand) : List Inst :=
  [.ext false .w32 (regName "lo" n) o,
   .bin .add (regName "s" (n + 1)) b (.reg (regName "lo" n)),
   .bin .mul (regName "cap" (n + 2)) m (imm 8),
   .select .ult (regName "k" (n + 3)) c (.reg (regName "cap" (n + 2))) c (.reg (regName "cap" (n + 2))),
   .call [] Names.print [.reg (regName "s" (n + 1)), .reg (regName "k" (n + 3))]]

/-! ## The closed form -/

/-- **What lowering an `Accepted2` body produces** (`lowerC2`): `Res1`'s
fields and the registers marked as trace words. -/
structure Res2 extends Res1 where
  /-- The registers marked as trace words (`markHeap`), in order. -/
  heaped : List Reg

/-- **The closed form of `lowerExpr` on an `Accepted2` body** without the
depth counter, in environment `env` from counter `n`, with the open block
`l` holding `k` instructions (see the module docstring). `none` off the
shapes it covers. -/
def lowerC2 (cx : Scc.Lower.Ctx) (env : Env) (n : Nat) (l : Label) (k : Nat) : Expr → Option Res2
  | .let_ x op e =>
    match op with
    | .add a b => do
        let (_, ws) ← atomV env a
        let p ← match ws with | [p] => some p | _ => none
        let (_, us) ← atomV env b
        let q ← match us with | [q] => some q | _ => none
        let d := regName x n
        let r ← lowerC2 cx ((x, .int, [.reg d]) :: env) (n + 1) l (k + 1) e
        pure { r with insts := .addChk d p q :: r.insts, marked := d :: r.marked }
    | .sub a b => do
        let (_, ws) ← atomV env a
        let p ← match ws with | [p] => some p | _ => none
        let (_, us) ← atomV env b
        let q ← match us with | [q] => some q | _ => none
        let d := regName x n
        let r ← lowerC2 cx ((x, .int, [.reg d]) :: env) (n + 1) l (k + 1) e
        pure { r with insts := .subSat d p q :: r.insts, marked := d :: r.marked }
    | .call g is a ts =>
        let pt : Point := (env, .let_ x (.call g is a ts) e)
        match cx.externs.find? (·.1 == g) with
        | none => do
            let dg ← cx.prog.find? (·.name == g)
            if dg.retTy = .int then do
              let (_, ws) ← atomV env a
              let w ← match ws with | [w] => some w | _ => none
              let rr := regName "r" n
              let env' := (x, Ty.int, [Operand.reg rr]) :: env
              let r ← lowerC2 cx env' (n + 1) l (k + 1) e
              pure { r with insts := .call [rr] (Names.user g) [w] :: r.insts, marked := rr :: r.marked,
                            marks := [(.ret l k, pt), (.ret l k, (env', e))] ++ r.marks }
            else none
        | some _ => do
            let dg ← cx.prog.find? (·.name == g)
            if dg.retTy = .unit then do
              let (_, ws) ← atomV env a
              match ws with
              | [b, .reg o, m, c] =>
                  let r ← lowerC2 cx ((x, .unit, []) :: env) (n + 4) l (k + 5) e
                  pure { r with insts := printInsts n b (.reg o) m c ++ r.insts,
                                marks := (.ret l (k + 4), pt) :: r.marks }
              | _ => none
            else none
    | .newBuf c τ => do
        let (_, ks) ← atomV env c
        let kv ← match ks with | [.imm kv] => some kv | _ => none
        let (en, em) ← countsO cx.obj τ
        let h ← Scc.Obj.header0 cx.obj .array en em
        let ew := (Scc.Frontend.words τ).getD (en + em)
        if en + em ≤ 2 * ew then do
          let p := regName x n
          let (sc, hp) ← markR (newBufTy τ) [.reg p, imm 0]
          let r ← lowerC2 cx ((x, newBufTy τ, [.reg p, imm 0]) :: env) (n + 1) l (k + 1) e
          pure { r with insts := newBufCall p h kv (unitsOf ew kv) :: r.insts,
                        marked := sc ++ r.marked, heaped := hp ++ r.heaped,
                        marks := (.ret l k, (env, .let_ x (.newBuf c τ) e)) :: r.marks }
        else none
    | .xchgAt b i v => do
        let (t, bw) ← atomV env b
        let (base, off) ← refO bw
        let rb ← match base with | .reg rb => some rb | _ => none
        let o ← match off with | .imm o => some o | _ => none
        let (_, js) ← atomV env i
        let iv ← match js with | [.imm iv] => some iv | _ => none
        let (_, u) ← bufElem t
        let (nu, mu) ← Scc.Obj.regOf u
        let (_, vs) ← atomV env v
        let w ← match vs with | [w] => some w | _ => none
        let sl ← Scc.Obj.slots u 0 0
        let s1 ← match sl with | [s1] => some s1 | _ => none
        let a := slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1
        let d := regName x n
        let (sc, hp) ← markR u [.reg d]
        let r ← lowerC2 cx ((x, u, [.reg d]) :: env) (n + 1) l (k + 2) e
        pure { r with insts := xchgLoad d a :: xchgStore a w :: r.insts,
                      marked := sc ++ r.marked, heaped := hp ++ r.heaped }
    | op => do
        let (t, ws) ← pureOp env op
        let (sc, hp) ← markR t ws
        let r ← lowerC2 cx ((x, t, ws) :: env) n l k e
        pure { r with marked := sc ++ r.marked, heaped := hp ++ r.heaped }
  | .split a x y e => do
      let (t, ws) ← atomV env a
      let (u, w) ← prodOf t
      let nu ← Scc.Obj.valWords u
      lowerC2 cx ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env) n l k e
  | .unpack a _ x e => do
      let (t, ws) ← atomV env a
      match t with
      | .iex b => lowerC2 cx ((x, b, ws) :: env) n l k e
      | _ => none
  | .ifeq a b yes no => do
      let (_, ws) ← atomV env a
      let p ← match ws with | [p] => some p | _ => none
      let (_, us) ← atomV env b
      let q ← match us with | [q] => some q | _ => none
      let ly := labName "then" n
      let ln := labName "else" (n + 1)
      let ry ← lowerC2 cx env (n + 2) ly 0 yes
      let rn ← lowerC2 cx env ry.next ln 0 no
      pure { insts := [], term := .br .eq p q ly ln,
             blocks := ⟨ly, ry.insts, ry.term⟩ :: ry.blocks ++ ⟨ln, rn.insts, rn.term⟩ :: rn.blocks,
             next := rn.next, marked := ry.marked ++ rn.marked, heaped := ry.heaped ++ rn.heaped,
             marks := [(.block ly, (env, .ifeq a b yes no)), (.block ly, (env, yes))] ++ ry.marks ++
               [(.block ln, ry.here), (.block ln, (env, no))] ++ rn.marks,
             here := rn.here }
  | .ret a => do
      let (_, ws) ← atomV env a
      pure { insts := [], term := .ret ws, blocks := [], next := n, marked := [], heaped := [], marks := [],
             here := (env, .ret a) }
  | _ => none

/-! ## Builder steps -/

theorem markHeap_eq (r : Reg) (s : BState) :
    markHeap r s = .ok ((), { s with heapRegs := pushNew s.heapRegs r }) := by
  unfold markHeap
  rw [modify_eq]
  by_cases h : r ∈ s.heapRegs <;> simp [hasReg_eq, pushNew, h]

/-- `markWords`' loop over a value's words with their trace mask. -/
theorem markLoop : ∀ (bs : List Bool) (ws : List Operand) (s : BState),
    (forIn (bs.zip ws) PUnit.unit (fun x (_ : PUnit) => match x.snd with
      | .reg r => if x.fst = true then do markHeap r; pure (ForInStep.yield PUnit.unit)
                  else do markScalar r; pure (ForInStep.yield PUnit.unit)
      | .imm _ => pure (ForInStep.yield PUnit.unit)) : B PUnit) s =
      .ok (⟨⟩, { s with
        scalarRegs := (markSplit bs ws).1.foldl pushNew s.scalarRegs,
        heapRegs := (markSplit bs ws).2.foldl pushNew s.heapRegs }) := by
  intro bs
  induction bs with
  | nil => intro ws s; rfl
  | cons b bs ih =>
    intro ws s
    cases ws with
    | nil => rfl
    | cons w ws =>
      rw [List.zip_cons_cons, List.forIn_cons]
      cases w with
      | imm v =>
        simp only [markSplit]
        exact ih ws s
      | reg r =>
        cases b with
        | true =>
          simp only [ite_true, markSplit]
          rw [bind_ok (bind_ok (markHeap_eq r s))]
          exact (ih ws _).trans (by simp)
        | false =>
          simp only [Bool.false_eq_true, ite_false, markSplit]
          rw [bind_ok (bind_ok (markScalar_eq r s))]
          exact (ih ws _).trans (by simp)

/-- **`markWords` is `markR`.** -/
theorem markWords_eq {t : Ty} {ws : List Operand} {sc hp : List Reg} (h : markR t ws = some (sc, hp))
    (s : BState) :
    markWords t ws s = .ok ((), { s with
      scalarRegs := sc.foldl pushNew s.scalarRegs,
      heapRegs := hp.foldl pushNew s.heapRegs }) := by
  unfold markWords
  simp only [markR] at h
  cases hm : Scc.Obj.traceMask t with
  | none => simp [hm] at h
  | some bs =>
    simp only [hm, Option.bind_eq_bind, Option.bind_some] at h
    split at h
    · rename_i hl
      simp only [Option.some.injEq] at h
      simp only [needSome, hl, bne_self_eq_false, Bool.false_eq_true, ite_false, pure_bind]
      refine (bind_ok (markLoop bs ws s)).trans ?_
      rw [h]
      rfl
    · cases h

/-! ## Inversion -/

/-- The `let`s without code (`pureOp`). -/
def isPure : Op → Bool
  | .atom _ | .nameI _ | .pack .. | .pair .. | .asLanes .. => true
  | _ => false

theorem lowerC2_let_pure {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {op : Op} {e : Expr} (hp : isPure op = true) :
    lowerC2 cx env n l k (.let_ x op e) = (do
      let (t, ws) ← pureOp env op
      let (sc, hp) ← markR t ws
      let r ← lowerC2 cx ((x, t, ws) :: env) n l k e
      pure { r with marked := sc ++ r.marked, heaped := hp ++ r.heaped }) := by
  cases op <;> first | rfl | simp [isPure] at hp

/-- **A `let` without code** (`pureOp`): its value's words bound, its
registers marked (`markR`). -/
theorem lowerC2_pure_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {op : Op} {e : Expr} {r : Res2} (hp : isPure op = true)
    (hr : lowerC2 cx env n l k (.let_ x op e) = some r) :
    ∃ t ws sc hq r', pureOp env op = some (t, ws) ∧ markR t ws = some (sc, hq) ∧
      lowerC2 cx ((x, t, ws) :: env) n l k e = some r' ∧
      r = { r' with marked := sc ++ r'.marked, heaped := hq ++ r'.heaped } := by
  rw [lowerC2_let_pure hp] at hr
  cases ho : pureOp env op with
  | none => simp [ho] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    cases hm : markR t ws with
    | none => simp [ho, hm] at hr
    | some q =>
      obtain ⟨sc, hq⟩ := q
      cases hr' : lowerC2 cx ((x, t, ws) :: env) n l k e with
      | none => simp [ho, hm, hr'] at hr
      | some r' =>
        simp [ho, hm, hr'] at hr
        exact ⟨t, ws, sc, hq, r', rfl, hm, hr', hr.symm⟩

theorem lowerC2_add_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {a b : At} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ x (.add a b) e) = some r) :
    ∃ ta p tb q r', atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with insts := .addChk (regName x n) p q :: r'.insts, marked := regName x n :: r'.marked } := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    rw [ha] at hr
    match ws, hr with
    | [p], hr =>
    cases hb : atomV env b with
    | none => simp [hb] at hr
    | some u =>
      obtain ⟨t', us⟩ := u
      rw [hb] at hr
      match us, hr with
      | [q], hr =>
      cases hr' : lowerC2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e with
      | none => simp [hr'] at hr
      | some r' =>
        simp [hr'] at hr
        exact ⟨t, p, t', q, r', rfl, rfl, rfl, hr.symm⟩

theorem lowerC2_sub_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {a b : At} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ x (.sub a b) e) = some r) :
    ∃ ta p tb q r', atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with insts := .subSat (regName x n) p q :: r'.insts, marked := regName x n :: r'.marked } := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    rw [ha] at hr
    match ws, hr with
    | [p], hr =>
    cases hb : atomV env b with
    | none => simp [hb] at hr
    | some u =>
      obtain ⟨t', us⟩ := u
      rw [hb] at hr
      match us, hr with
      | [q], hr =>
      cases hr' : lowerC2 cx ((x, .int, [.reg (regName x n)]) :: env) (n + 1) l (k + 1) e with
      | none => simp [hr'] at hr
      | some r' =>
        simp [hr'] at hr
        exact ⟨t, p, t', q, r', rfl, rfl, rfl, hr.symm⟩

/-- **A call's closed form**: of a code block of the program returning an
`Int`, not an extern, one `call` in the open block; of the extern
(returning `Unit`, its slice's offset word a register), `printInsts`. -/
theorem lowerC2_call_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x g : String}
    {is : List String} {a : At} {ts : List Ty} {e : Expr} {r : Res2}
    (hr : lowerC2 cx env n l k (.let_ x (.call g is a ts) e) = some r) :
    (∃ dg t w r', cx.externs.find? (·.1 == g) = none ∧ cx.prog.find? (·.name == g) = some dg ∧
      dg.retTy = .int ∧ atomV env a = some (t, [w]) ∧
      lowerC2 cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with insts := .call [regName "r" n] (Names.user g) [w] :: r'.insts,
                    marked := regName "r" n :: r'.marked,
                    marks := [(.ret l k, (env, .let_ x (.call g is a ts) e)),
                      (.ret l k, ((x, .int, [.reg (regName "r" n)]) :: env, e))] ++ r'.marks }) ∨
    (∃ xe dg t b o m c r', cx.externs.find? (·.1 == g) = some xe ∧ cx.prog.find? (·.name == g) = some dg ∧
      dg.retTy = .unit ∧ atomV env a = some (t, [b, .reg o, m, c]) ∧
      lowerC2 cx ((x, .unit, []) :: env) (n + 4) l (k + 5) e = some r' ∧
      r = { r' with insts := printInsts n b (.reg o) m c ++ r'.insts,
                    marks := (.ret l (k + 4), (env, .let_ x (.call g is a ts) e)) :: r'.marks }) := by
  simp only [lowerC2] at hr
  cases hx : cx.externs.find? (·.1 == g) with
  | none =>
    refine .inl ?_
    rw [hx] at hr
    cases hd : cx.prog.find? (·.name == g) with
    | none => simp [hd] at hr
    | some dg =>
    by_cases hrt : dg.retTy = .int
    · cases ha : atomV env a with
      | none => simp [hd, hrt, ha] at hr
      | some v =>
      obtain ⟨t, ws⟩ := v
      simp only [hd, hrt, ha, ite_true, Option.bind_eq_bind, Option.bind_some] at hr
      match ws, hr with
      | [w], hr =>
      cases hr' : lowerC2 cx ((x, .int, [.reg (regName "r" n)]) :: env) (n + 1) l (k + 1) e with
      | none => simp [hr'] at hr
      | some r' =>
        simp [hr'] at hr
        exact ⟨dg, t, w, r', rfl, rfl, hrt, rfl, rfl, hr.symm⟩
    · simp [hd, hrt] at hr
  | some xe =>
    refine .inr ?_
    rw [hx] at hr
    cases hd : cx.prog.find? (·.name == g) with
    | none => simp [hd] at hr
    | some dg =>
    by_cases hrt : dg.retTy = .unit
    · cases ha : atomV env a with
      | none => simp [hd, hrt, ha] at hr
      | some v =>
      obtain ⟨t, ws⟩ := v
      simp only [hd, hrt, ha, ite_true, Option.bind_eq_bind, Option.bind_some] at hr
      match ws, hr with
      | [b, .reg o, m, c], hr =>
      cases hr' : lowerC2 cx ((x, .unit, []) :: env) (n + 4) l (k + 5) e with
      | none => simp [hr'] at hr
      | some r' =>
        simp [hr'] at hr
        exact ⟨xe, dg, t, b, o, m, c, r', rfl, rfl, hrt, rfl, rfl, hr.symm⟩
    · simp [hd, hrt] at hr

/-- **`newBuf`'s closed form**: its count an immediate, one `call` of the
allocator into `x%n` (`newBufCall`), its return point marked with the
`let`; the buffer's words `[x%n, 0]` (`newBufTy`). -/
theorem lowerC2_newBuf_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {c : At} {τ : Ty} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ x (.newBuf c τ) e) = some r) :
    ∃ tk kv en em h sc hq r', atomV env c = some (tk, [.imm kv]) ∧ countsO cx.obj τ = some (en, em) ∧
      Scc.Obj.header0 cx.obj .array en em = some h ∧
      en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em) ∧
      markR (newBufTy τ) [.reg (regName x n), imm 0] = some (sc, hq) ∧
      lowerC2 cx ((x, newBufTy τ, [.reg (regName x n), imm 0]) :: env) (n + 1) l (k + 1) e = some r' ∧
      r = { r' with
        insts := newBufCall (regName x n) h kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv) :: r'.insts,
        marked := sc ++ r'.marked, heaped := hq ++ r'.heaped,
        marks := (.ret l k, (env, .let_ x (.newBuf c τ) e)) :: r'.marks } := by
  simp only [lowerC2] at hr
  cases ha : atomV env c with
  | none => simp [ha] at hr
  | some v =>
  obtain ⟨tk, ks⟩ := v
  rw [ha] at hr
  match ks, hr with
  | [.imm kv], hr =>
  cases hc : countsO cx.obj τ with
  | none => simp [hc] at hr
  | some q =>
  obtain ⟨en, em⟩ := q
  cases hh : Scc.Obj.header0 cx.obj .array en em with
  | none => simp [hc, hh] at hr
  | some h =>
  by_cases hw : en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em)
  · cases hm : markR (newBufTy τ) [.reg (regName x n), imm 0] with
    | none => simp [hc, hh, hw, hm] at hr
    | some q =>
    obtain ⟨sc, hq⟩ := q
    cases hr' : lowerC2 cx ((x, newBufTy τ, [.reg (regName x n), imm 0]) :: env) (n + 1) l (k + 1) e with
    | none => simp [hc, hh, hw, hm, hr'] at hr
    | some r' =>
      simp [hc, hh, hw, hm, hr'] at hr
      refine ⟨tk, kv, en, em, h, sc, hq, r', ?_, ?_, ?_, hw, ?_, ?_, hr.symm⟩ <;> first | rfl | assumption
  · simp [hc, hh, hw] at hr

/-- **A lane store's closed form** (`xchg b[i] v`): `b`'s words a register
base and an immediate offset, `i` an immediate, a one-word element and `v`
one word: the load of the slot into `x%n` and the store of `v` to it, at
the slot's address `slotAddr` (the offset advanced by `i` strides). -/
theorem lowerC2_xchg_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {x : String}
    {b i v : At} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ x (.xchgAt b i v) e) = some r) :
    ∃ t bw rb o tj iv μ u nu mu tv w s1 sc hq r', atomV env b = some (t, bw) ∧
      refO bw = some (.reg rb, .imm o) ∧ atomV env i = some (tj, [.imm iv]) ∧ bufElem t = some (μ, u) ∧
      Scc.Obj.regOf u = some (nu, mu) ∧ atomV env v = some (tv, [w]) ∧ Scc.Obj.slots u 0 0 = some [s1] ∧
      markR u [.reg (regName x n)] = some (sc, hq) ∧
      lowerC2 cx ((x, u, [.reg (regName x n)]) :: env) (n + 1) l (k + 2) e = some r' ∧
      r = { r' with
        insts := xchgLoad (regName x n) (slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1) ::
          xchgStore (slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1) w :: r'.insts,
        marked := sc ++ r'.marked, heaped := hq ++ r'.heaped } := by
  simp only [lowerC2] at hr
  cases hb : atomV env b with
  | none => simp [hb] at hr
  | some q =>
  obtain ⟨t, bw⟩ := q
  rw [hb] at hr
  cases hrf : refO bw with
  | none => simp [hrf] at hr
  | some q =>
  obtain ⟨base, off⟩ := q
  cases base with
  | imm _ => simp [hrf] at hr
  | reg rb =>
  cases off with
  | reg _ => simp [hrf] at hr
  | imm o =>
  cases hi : atomV env i with
  | none => simp [hrf, hi] at hr
  | some q =>
  obtain ⟨tj, js⟩ := q
  rcases js with _ | ⟨_ | iv, _ | ⟨_, _⟩⟩ <;> try simp [hrf, hi] at hr
  cases he : bufElem t with
  | none => simp [hrf, hi, he] at hr
  | some q =>
  obtain ⟨μ, u⟩ := q
  cases hg : Scc.Obj.regOf u with
  | none => simp [hrf, hi, he, hg] at hr
  | some q =>
  obtain ⟨nu, mu⟩ := q
  cases hv : atomV env v with
  | none => simp [hrf, hi, he, hg, hv] at hr
  | some q =>
  obtain ⟨tv, vs⟩ := q
  rcases vs with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> try simp [hrf, hi, he, hg, hv] at hr
  cases hs : Scc.Obj.slots u 0 0 with
  | none => simp [hrf, hi, he, hg, hv, hs] at hr
  | some sl =>
  rcases sl with _ | ⟨s1, _ | ⟨_, _⟩⟩ <;> try simp [hrf, hi, he, hg, hv, hs] at hr
  cases hm : markR u [.reg (regName x n)] with
  | none => simp [hrf, hi, he, hg, hv, hs, hm] at hr
  | some q =>
  obtain ⟨sc, hq⟩ := q
  cases hr' : lowerC2 cx ((x, u, [.reg (regName x n)]) :: env) (n + 1) l (k + 2) e with
  | none => simp [hrf, hi, he, hg, hv, hs, hm, hr'] at hr
  | some r' =>
    simp [hrf, hi, he, hg, hv, hs, hm, hr'] at hr
    refine ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hr.symm⟩ <;> first | rfl | assumption

theorem lowerC2_split_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a : At}
    {x y : String} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.split a x y e) = some r) :
    ∃ t ws u w nu, atomV env a = some (t, ws) ∧ prodOf t = some (u, w) ∧ Scc.Obj.valWords u = some nu ∧
      lowerC2 cx ((y, w, ws.drop nu) :: (x, u, ws.take nu) :: env) n l k e = some r := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some q =>
  obtain ⟨t, ws⟩ := q
  cases hp : prodOf t with
  | none => simp [ha, hp] at hr
  | some q =>
  obtain ⟨u, w⟩ := q
  cases hv : Scc.Obj.valWords u with
  | none => simp [ha, hp, hv] at hr
  | some nu =>
    simp [ha, hp, hv] at hr
    refine ⟨t, ws, u, w, nu, ?_, ?_, ?_, hr⟩ <;> first | rfl | assumption

theorem lowerC2_unpack_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a : At}
    {i x : String} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.unpack a i x e) = some r) :
    ∃ b ws, atomV env a = some (.iex b, ws) ∧ lowerC2 cx ((x, b, ws) :: env) n l k e = some r := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some q =>
  obtain ⟨t, ws⟩ := q
  cases t with
  | iex b => simp [ha] at hr; exact ⟨b, ws, rfl, hr⟩
  | _ => simp [ha] at hr

theorem lowerC2_ifeq_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a b : At}
    {yes no : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.ifeq a b yes no) = some r) :
    ∃ ta p tb q ry rn, atomV env a = some (ta, [p]) ∧ atomV env b = some (tb, [q]) ∧
      lowerC2 cx env (n + 2) (labName "then" n) 0 yes = some ry ∧
      lowerC2 cx env ry.next (labName "else" (n + 1)) 0 no = some rn ∧
      r = { insts := [], term := .br .eq p q (labName "then" n) (labName "else" (n + 1)),
            blocks := ⟨labName "then" n, ry.insts, ry.term⟩ :: ry.blocks ++
              ⟨labName "else" (n + 1), rn.insts, rn.term⟩ :: rn.blocks,
            next := rn.next, marked := ry.marked ++ rn.marked, heaped := ry.heaped ++ rn.heaped,
            marks := [(.block (labName "then" n), (env, .ifeq a b yes no)), (.block (labName "then" n), (env, yes))] ++
              ry.marks ++ [(.block (labName "else" (n + 1)), ry.here), (.block (labName "else" (n + 1)), (env, no))] ++
              rn.marks,
            here := rn.here } := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    rw [ha] at hr
    match ws, hr with
    | [p], hr =>
    cases hb : atomV env b with
    | none => simp [hb] at hr
    | some u =>
      obtain ⟨t', us⟩ := u
      rw [hb] at hr
      match us, hr with
      | [q], hr =>
      cases hy : lowerC2 cx env (n + 2) (labName "then" n) 0 yes with
      | none => simp [hy] at hr
      | some ry =>
        cases hn : lowerC2 cx env ry.next (labName "else" (n + 1)) 0 no with
        | none => simp [hy, hn] at hr
        | some rn =>
          simp [hy, hn] at hr
          exact ⟨t, p, t', q, ry, rn, rfl, rfl, by first | exact hy | rfl, by first | exact hn | rfl,
            by rw [← hr]; simp⟩

/-- **A `ret`'s closed form**: it returns all of its atom's words. -/
theorem lowerC2_ret_inv {cx : Scc.Lower.Ctx} {env : Env} {n : Nat} {l : Label} {k : Nat} {a : At} {r : Res2}
    (hr : lowerC2 cx env n l k (.ret a) = some r) :
    ∃ t ws, atomV env a = some (t, ws) ∧
      r = { insts := [], term := .ret ws, blocks := [], next := n, marked := [], heaped := [], marks := [],
            here := (env, .ret a) } := by
  simp only [lowerC2] at hr
  cases ha : atomV env a with
  | none => simp [ha] at hr
  | some v =>
    obtain ⟨t, ws⟩ := v
    simp [ha] at hr
    exact ⟨t, ws, rfl, hr.symm⟩

/-! ## The lowering's steps on the new constructs -/

theorem lowerOp_pure (cx : Scc.Lower.Ctx) (env : Env) (x : String) {op : Op} {v : Ty × List Operand}
    (hp : isPure op = true) (h : pureOp env op = some v) (s : BState) : lowerOp cx env x op s = .ok (v, s) := by
  cases op with
  | atom a => exact evalAt_eq h s
  | nameI a => exact evalAt_eq h s
  | pack a i τ =>
    simp only [pureOp, Option.map_eq_some_iff] at h
    obtain ⟨⟨t, ws⟩, ha, rfl⟩ := h
    simp only [lowerOp]
    rw [bind_ok (evalAt_eq ha s)]
    rfl
  | pair a b =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some q =>
    obtain ⟨t, ws⟩ := q
    cases hb : atomV env b with
    | none => simp [ha, hb] at h
    | some q =>
    obtain ⟨u, us⟩ := q
    simp [ha, hb] at h
    subst h
    simp only [lowerOp]
    rw [bind_ok (evalAt_eq ha s), bind_ok (evalAt_eq hb s)]
    rfl
  | asLanes sg w a =>
    simp only [pureOp] at h
    cases ha : atomV env a with
    | none => simp [ha] at h
    | some q =>
    obtain ⟨t, ws⟩ := q
    rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> simp [ha] at h
    subst h
    simp only [lowerOp]
    rw [bind_ok (evalOne_eq ha _ s)]
    rfl
  | _ => simp [isPure] at hp

theorem countsOf_eq {o : Scc.ObjLayout} {t : Ty} {c : Nat × Nat} (h : countsO o t = some c) (s : BState) :
    countsOf o t s = .ok (c, s) := by
  simp only [countsO] at h
  unfold countsOf regOf
  cases hr : Scc.Obj.regOf t with
  | none => simp [hr] at h
  | some r =>
  cases hc : Scc.Obj.counts o t with
  | none => simp [hr, hc] at h
  | some c' =>
  by_cases he : c' = r
  · simp [hr, hc, he] at h
    subst h he
    simp [bind, StateT.bind, pure, StateT.pure, Except.pure, Except.bind]
  · simp [hr, hc, he] at h

theorem header_eq {o : Scc.ObjLayout} {k : Scc.Obj.HeaderKind} {n m h : Nat} (hh : Scc.Obj.header0 o k n m = some h)
    (s : BState) : header o k n m s = .ok (h, s) := by
  unfold header; rw [hh]; rfl

/-- **`newBuf`'s lowering** (an immediate count): one `call` of the
allocator into the fresh `x%n`, its return point marked with the source
point being lowered. -/
theorem lowerOp_newBuf (cx : Scc.Lower.Ctx) (env : Env) (x : String) {c : At} {τ : Ty} {tk : Ty} {kv : UInt64}
    {en em h : Nat} (ha : atomV env c = some (tk, [.imm kv])) (hc : countsO cx.obj τ = some (en, em))
    (hh : Scc.Obj.header0 cx.obj .array en em = some h)
    (hw : en + em ≤ 2 * (Scc.Frontend.words τ).getD (en + em)) {s : BState} {l : Label} {is : Array Inst}
    {p : Point} (hcur : s.cur = some (l, is)) (hhere : s.here = some p) :
    lowerOp cx env x (.newBuf c τ) s = .ok ((newBufTy τ, [.reg (regName x s.next), imm 0]), { s with
      next := s.next + 1,
      cur := some (l, is.push (newBufCall (regName x s.next) h kv
        (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv))),
      marks := markOp s.marks (.ret l is.size, p) }) := by
  simp only [lowerOp]
  rw [bind_ok (evalOne_eq ha _ _), bind_ok (countsOf_eq hc _), bind_ok (header_eq hh _), bind_ok (fresh_eq _ _)]
  simp only [hw, ite_true]
  generalize (Scc.Frontend.words τ).getD (en + em) = ew
  cases ew with
  | zero =>
    simp only [pure_bind]
    rw [bind_ok (emit_call _ _ _ (s := { s with next := s.next + 1 }) hcur hhere)]
    rfl
  | succ ew =>
    simp only [pure_bind]
    rw [bind_ok (emit_call _ _ _ (s := { s with next := s.next + 1 }) hcur hhere)]
    simp [unitsOf, newBufCall, newBufTy, imm]
    rfl

theorem refOf_eq {bw : List Operand} {q : Operand × Operand} (h : refO bw = some q) (what : String) (s : BState) :
    refOf bw what s = .ok (q, s) := by
  unfold refOf
  rcases bw with _ | ⟨p, _ | ⟨o, _ | ⟨_, _⟩⟩⟩ <;> simp [refO] at h <;> subst h <;> rfl

theorem needSome_eq {α : Type} {o : Option α} {a : α} (h : o = some a) (msg : String) (s : BState) :
    needSome o msg s = .ok (a, s) := by
  subst h; rfl

/-- **A lane store's lowering** (`xchg b[i] v` at an immediate slot of a
buffer with a register base): the load of the slot into the fresh `x%n`,
then the store of `v`. -/
theorem lowerOp_xchg (cx : Scc.Lower.Ctx) (env : Env) (x : String) {b i v : At} {t : Ty} {bw : List Operand}
    {rb : Reg} {o : UInt64} {tj : Ty} {iv : UInt64} {μ : Mode} {u : Ty} {nu mu : Nat} {tv : Ty} {w : Operand}
    {s1 : Bool × Nat} (hb : atomV env b = some (t, bw)) (hrf : refO bw = some (.reg rb, .imm o))
    (hi : atomV env i = some (tj, [.imm iv])) (he : bufElem t = some (μ, u))
    (hg : Scc.Obj.regOf u = some (nu, mu)) (hv : atomV env v = some (tv, [w]))
    (hs : Scc.Obj.slots u 0 0 = some [s1]) {s : BState} {l : Label} {is : Array Inst}
    (hcur : s.cur = some (l, is)) :
    lowerOp cx env x (.xchgAt b i v) s = .ok ((u, [.reg (regName x s.next)]), { s with
      next := s.next + 1,
      cur := some (l, (is.push (xchgLoad (regName x s.next)
        (slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1))).push
        (xchgStore (slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1) w)) }) := by
  simp only [lowerOp]
  rw [bind_ok (evalAt_eq hb _), bind_ok (refOf_eq hrf _ _), bind_ok (evalOne_eq hi _ _),
    bind_ok (needSome_eq he _ _)]
  have hsl : slotLoc (.reg rb) (.imm o) (.imm iv) u s =
      .ok ((.reg rb, .imm (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu))), s) := by
    unfold slotLoc regOf
    rw [hg]
    rfl
  rw [bind_ok hsl, bind_ok (evalAt_eq hv _)]
  have hca : cellAddrs cx.obj (.reg rb) (.imm (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu))) u s =
      .ok ([slotAddr cx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1], s) := by
    unfold cellAddrs
    rw [bind_ok (needSome_eq hs _ _)]
    rfl
  rw [bind_ok hca]
  cases s
  simp only at hcur
  subst hcur
  rfl

/-- **The output extern's call** (`callBlock`'s `.print` case, the slice's
offset word a register): `printInsts` appended to the open block, the
`call`'s return point (instruction `k + 4`) marked with the source point
being lowered. -/
theorem callBlock_print {cx : Scc.Lower.Ctx} {g : String} {xe : String × Scc.Frontend.Extern}
    (hx : cx.externs.find? (·.1 == g) = some xe) (b m c : Operand) (o : Reg) {s : BState} {l : Label}
    {is : Array Inst} {p : Point} (hcur : s.cur = some (l, is)) (hhere : s.here = some p) :
    callBlock cx g [b, .reg o, m, c] 0 s = .ok ([], { s with
      next := s.next + 4,
      cur := some (l, is ++ (printInsts s.next b (.reg o) m c).toArray),
      marks := markOp s.marks (.ret l (is.size + 4), p) }) := by
  obtain ⟨nm, ex⟩ := xe
  cases ex
  unfold callBlock
  rw [hx]
  simp only [bind_assoc]
  rw [bind_ok (fresh_eq _ _), bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c1),
    bind_ok (binR_eq _ _ _ _ ?c2), bind_ok (binR_eq _ _ _ _ ?c3), bind_ok (fresh_eq _ _),
    bind_ok (emit_plain (by intros; exact Inst.noConfusion) ?c4), bind_ok (emit_call _ _ _ ?c5 ?h1)]
  all_goals try first | exact hcur | exact hhere | rfl
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq, BState.mk.injEq, true_and,
    Array.size_push, and_true]
  congr 2

/-- The output extern's `lowerOp` (`callBlock_print`): no result word. -/
theorem lowerOp_print (cx : Scc.Lower.Ctx) (env : Env) (x g : String) (is' : List String) {a : At}
    (ts : List Ty) {xe : String × Scc.Frontend.Extern} {dg : Decl} {t : Ty} {b m c : Operand} {o : Reg}
    (hx : cx.externs.find? (·.1 == g) = some xe) (hd : cx.prog.find? (·.name == g) = some dg)
    (hrt : dg.retTy = .unit) (ha : atomV env a = some (t, [b, .reg o, m, c])) {s : BState} {l : Label}
    {is : Array Inst} {p : Point} (hcur : s.cur = some (l, is)) (hhere : s.here = some p) :
    lowerOp cx env x (.call g is' a ts) s = .ok ((.unit, []), { s with
      next := s.next + 4,
      cur := some (l, is ++ (printInsts s.next b (.reg o) m c).toArray),
      marks := markOp s.marks (.ret l (is.size + 4), p) }) := by
  simp only [lowerOp]
  have hw : words dg.retTy s = .ok (0, s) := by rw [hrt]; rfl
  rw [bind_ok (needSome_eq hd _ _), bind_ok (evalAt_eq ha _), bind_ok hw,
    bind_ok (callBlock_print hx b m c o hcur hhere), hrt]
  rfl

theorem words_eq {t : Ty} {n : Nat} (h : Scc.Obj.valWords t = some n) (s : BState) : words t s = .ok (n, s) := by
  unfold words; rw [h]; rfl

/-! ## `lowerExpr` is the closed form -/

/-- **`lowerExpr` on an `Accepted2` body is `lowerC2`** (without the depth
counter, as the program lowering runs it), from an open block `(l, is)`
(`lowerC2` from `l` and `is.size`): it closes `l` with `is` and the closed
form's instructions and terminator, pushes its blocks, and records its
marks and marked registers. -/
theorem lowerExpr_lowerC2 (cx : Scc.Lower.Ctx) (hf : cx.frames = none) :
    ∀ (e : Expr) (env : Env) (s : BState) (l : Label) (is : Array Inst) (r : Res2),
      s.cur = some (l, is) → lowerC2 cx env s.next l is.size e = some r →
      lowerExpr cx env e s = .ok ((), { s with
        blocks := (s.blocks.push ⟨l, is.toList ++ r.insts, r.term⟩) ++ r.blocks.toArray, cur := none,
        next := r.next, heapRegs := r.heaped.foldl pushNew s.heapRegs,
        scalarRegs := r.marked.foldl pushNew s.scalarRegs, here := some r.here,
        marks := r.marks.foldl markOp s.marks }) := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env s l is r hc hr
    cases op with
    | add a b =>
      obtain ⟨ta, p, tb, q, r', ha, hb, hr', rfl⟩ := lowerC2_add_inv hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_add cx env x ha hb (by simpa using hc))]
      rw [bind_ok (markWords_scalar1 rfl _)]
      refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
      simp [regsOf]
    | sub a b =>
      obtain ⟨ta, p, tb, q, r', ha, hb, hr', rfl⟩ := lowerC2_sub_inv hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_sub cx env x ha hb (by simpa using hc))]
      rw [bind_ok (markWords_scalar1 rfl _)]
      refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
      simp [regsOf]
    | call g is' a ts =>
      rcases lowerC2_call_inv hr with ⟨dg, t, w, r', hx, hd, hrt, ha, hr', rfl⟩ |
        ⟨xe, dg, t, b, o, m, c, r', hx, hd, hrt, ha, hr', rfl⟩
      · rw [lowerExpr]
        simp only [setHere]
        rw [bind_ok (modify_eq _ _)]
        rw [bind_ok (lowerOp_call env x g hd hrt ha (callBlock_none g w hf hx (by simpa using hc) rfl))]
        simp only [hx, Option.isNone_none, ite_true]
        rw [get_bind]
        simp only [markOp_back]
        rw [bind_ok (markAt_eq _ _ _), bind_ok (markWords_scalar1 rfl _)]
        refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
        simp [regsOf, markOp]
      · rw [lowerExpr]
        simp only [setHere]
        rw [bind_ok (modify_eq _ _)]
        rw [bind_ok (lowerOp_print cx env x g is' ts hx hd hrt ha (by simpa using hc) rfl)]
        simp only [hx, Option.isNone_some, Bool.false_eq_true, ite_false]
        have hmw : ∀ s : BState, markWords .unit [] s = .ok ((), s) := fun _ => rfl
        rw [bind_ok (hmw _)]
        refine (ih _ _ l _ r' rfl (by simpa [printInsts, Nat.add_assoc] using hr')).trans ?_
        simp
    | newBuf c τ =>
      obtain ⟨tk, kv, en, em, h, sc, hq, r', ha, hcn, hh, hw, hm, hr', rfl⟩ := lowerC2_newBuf_inv hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_newBuf cx env x ha hcn hh hw (by simpa using hc) rfl)]
      rw [bind_ok (markWords_eq hm _)]
      refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
      simp [List.foldl_append]
    | xchgAt b i v =>
      obtain ⟨t, bw, rb, o, tj, iv, μ, u, nu, mu, tv, w, s1, sc, hq, r', hb, hrf, hi, he, hg, hv, hs, hm, hr',
        rfl⟩ := lowerC2_xchg_inv hr
      rw [lowerExpr]
      simp only [setHere]
      rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_xchg cx env x hb hrf hi he hg hv hs (by simpa using hc))]
      rw [bind_ok (markWords_eq hm _)]
      refine (ih _ _ l _ r' rfl (by simpa using hr')).trans ?_
      simp [List.foldl_append]
    | _ =>
      first
      | (obtain ⟨t, ws, sc, hq, r', hpo, hm, hr', rfl⟩ := lowerC2_pure_inv rfl hr
         rw [lowerExpr]
         simp only [setHere]
         rw [bind_ok (modify_eq _ _), bind_ok (lowerOp_pure cx env x rfl hpo _)]
         rw [bind_ok (markWords_eq hm _)]
         refine (ih _ _ l is r' (by simpa using hc) (by simpa using hr')).trans ?_
         simp [List.foldl_append])
      | simp [lowerC2, pureOp] at hr
  | split a x y e ih =>
    intro env s l is r hc hr
    obtain ⟨t, ws, u, w, nu, ha, hp, hv, hr'⟩ := lowerC2_split_inv hr
    rw [lowerExpr]
    simp only [setHere]
    rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _), bind_ok (needSome_eq hp _ _), bind_ok (words_eq hv _)]
    refine (ih _ _ l is r (by simpa using hc) (by simpa using hr')).trans ?_
    simp
  | unpack a i x e ih =>
    intro env s l is r hc hr
    obtain ⟨b, ws, ha, hr'⟩ := lowerC2_unpack_inv hr
    rw [lowerExpr]
    simp only [setHere]
    rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _)]
    refine (ih _ _ l is r (by simpa using hc) (by simpa using hr')).trans ?_
    simp
  | ifeq a b yes no ihy ihn =>
    intro env s l is r hc hr
    obtain ⟨ta, p, tb, q, ry, rn, ha, hb, hy, hn, rfl⟩ := lowerC2_ifeq_inv hr
    rw [lowerExpr]
    simp only [setHere]
    rw [bind_ok (modify_eq _ _), bind_ok (evalOne_eq ha _ _), bind_ok (evalOne_eq hb _ _),
      bind_ok (freshLabel_eq _ _), bind_ok (freshLabel_eq _ _),
      bind_ok (terminate_eq _ (by simpa using hc)),
      bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)]
    rw [bind_ok (ihy env _ _ _ ry rfl (by simpa [Nat.add_assoc] using hy))]
    rw [bind_ok (startBlock_eq _ rfl rfl), bind_ok (markAt_eq _ _ _)]
    refine (ihn env _ _ _ rn rfl (by simpa using hn)).trans ?_
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.nil_append, List.append_nil,
      Except.ok.injEq, Prod.mk.injEq, true_and, BState.mk.injEq, and_true]
    apply Array.toList_inj.mp
    simp
  | ret a =>
    intro env s l is r hc hr
    obtain ⟨t, ws, ha, rfl⟩ := lowerC2_ret_inv hr
    rw [lowerExpr]
    simp only [setHere]
    rw [bind_ok (modify_eq _ _), bind_ok (evalAt_eq ha _), terminate_eq _ (by simpa using hc)]
    simp
  | _ => intro env s l is r _ hr; simp [lowerC2] at hr

/-! ## The lowering of a code block -/

/-- The parameter registers of a code block with `na` argument words
(`lowerDeclMarks`): `x.0`, …, `x.(na-1)` for parameter `x`. -/
def paramsR (d : Decl) (na : Nat) : List Reg := (List.range na).map fun k => s!"{d.arg}.{k}"

/-- The environment a code block's body is lowered in: its parameter bound
to the parameter registers. -/
def env2 (d : Decl) (na : Nat) : Env := [(d.arg, d.argTy, (paramsR d na).map .reg)]

/-- **The IR function of a code block** named `name` with parameter
registers `params`, marked `(sc, hp)` (`markR` of the parameter), whose
body's closed form is `r`: block `entry` holding `r`'s instructions and
terminator, then `r`'s blocks; stack-checked; the marked registers in
order. -/
def func2 (name : Sym) (params : List Reg) (sc hp : List Reg) (r : Res2) : Func :=
  { name, params, blocks := ⟨"entry", r.insts, r.term⟩ :: r.blocks, checkStack := true,
    heapRegs := ((hp ++ r.heaped).foldl pushNew #[]).toList,
    scalarRegs := ((sc ++ r.marked).foldl pushNew #[]).toList }

/-- **The placement trace of a code block** `d` with `na` argument words
whose body's closed form is `r`: the start of block `entry` with the
parameter and the whole body, then `r`'s marks. -/
def marks2 (d : Decl) (na : Nat) (r : Res2) : Array (Node × Point) :=
  r.marks.foldl markOp #[(.block "entry", (env2 d na, d.body))]

/-- **The lowering of a code block** (`lowerDeclMarks` as the program
lowering `lowerWithMarks` calls it: no depth counter) whose parameter and
result have runtime layouts within the argument and result registers and
whose body has the closed form `r` from the parameter's environment, counter
0 and the empty block `entry`, is `func2` with the trace `marks2`. -/
theorem lowerDeclMarks_lowerC2 (prog : Prog) (externs : List (String × Scc.Frontend.Extern))
    (obj : Scc.ObjLayout) {d : Decl} {na nr : Nat} {sc hp : List Reg} {r : Res2}
    (hna : Scc.Obj.valWords d.argTy = some na) (ha : na ≤ maxArgs)
    (hnr : Scc.Obj.valWords d.retTy = some nr) (hr : nr ≤ maxRets)
    (hm : markR d.argTy ((paramsR d na).map .reg) = some (sc, hp))
    (hl : lowerC2 { prog, externs, fn := d.name, obj } (env2 d na) 0 "entry" 0 d.body = some r) :
    lowerDeclMarks prog externs d obj = .ok (func2 (Names.user d.name) (paramsR d na) sc hp r, marks2 d na r) := by
  have ha' : ¬ (na > maxArgs) := by omega
  have hr' : ¬ (nr > maxRets) := by omega
  have hma : ∀ (p : Point) (s : BState), markAt (.block "entry") p s =
      .ok ((), { s with marks := markOp s.marks (.block "entry", p) }) := fun _ _ => rfl
  have hle := lowerExpr_lowerC2 { prog, externs, fn := d.name, obj } rfl d.body (env2 d na)
    { scalarRegs := sc.foldl pushNew #[], heapRegs := hp.foldl pushNew #[],
      marks := markOp #[] (.block "entry", (env2 d na, d.body)) } "entry" #[] r rfl hl
  simp only [lowerDeclMarks, hna, hnr, ha', hr', ite_false, pure_bind, buildFuncMarks, StateT.run]
  simp only [paramsR] at hm
  rw [bind_ok (markWords_eq hm _), bind_ok (hma _ _)]
  simp only [env2, paramsR] at hle
  erw [hle]
  simp [func2, marks2, env2, paramsR, List.foldl_append]
  rfl

end Spike.Lib.LowerShape
