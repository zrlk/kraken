import WeakCore.Syntax

/-!
# The output extern's model, and textual equality of declarations

The WeakCore model of the output extern on an owned slice: `printExtD`
(`print{m}`, the extern's declaration) and `printLoopD` (`printL{i, d}`, its
`emit` loop). scc does not compile either: the runtime's `scc_rt_print`
stands for them (`Frontend.externOf`). A program that writes them must write
them **textually** (`declIs`), so that the source the proofs run is the
program as written.

`declIs d d'` compares two declarations field by field, the bodies by
`exprEqT` (on the constructors of the model; `false` off them). `Expr` has no
decidable equality; `declIs_eq` makes `declIs` one.
-/

open CoreLang CoreTerm

namespace Scc.Frontend

/-! ## Textual equality of the extern's declarations -/

/-- Equality of the `let` operations of the extern's model (`atom`, `add`,
`sub`, `nameI`, `pair`, `loadAt`, `lane`, `ext`); `false` off them. -/
def opEqT : Op → Op → Bool
  | .atom a, o => match o with | .atom a' => a == a' | _ => false
  | .add a b, o => match o with | .add a' b' => a == a' && b == b' | _ => false
  | .sub a b, o => match o with | .sub a' b' => a == a' && b == b' | _ => false
  | .nameI a, o => match o with | .nameI a' => a == a' | _ => false
  | .pair a b, o => match o with | .pair a' b' => a == a' && b == b' | _ => false
  | .loadAt a b, o => match o with | .loadAt a' b' => a == a' && b == b' | _ => false
  | .lane a b, o => match o with | .lane a' b' => a == a' && b == b' | _ => false
  | .ext n a, o => match o with | .ext n' a' => n == n' && a == a' | _ => false
  | _, _ => false

theorem opEqT_eq {o o' : Op} (h : opEqT o o' = true) : o = o' := by
  cases o <;> simp only [opEqT, reduceCtorEq] at h
  all_goals split at h <;> simp_all

/-- **Equality of terms of the extern's model**: `let`s of `opEqT`
operations, `split`, `ifeq`, `ret`, `tail` without type arguments; `false`
off them. `Expr` has no decidable equality; `exprEqT_eq` makes this one. -/
def exprEqT : Expr → Expr → Bool
  | .let_ x op e, t => match t with
    | .let_ x' op' e' => x == x' && opEqT op op' && exprEqT e e'
    | _ => false
  | .split a x y e, t => match t with
    | .split a' x' y' e' => a == a' && x == x' && y == y' && exprEqT e e'
    | _ => false
  | .ifeq a b y n, t => match t with
    | .ifeq a' b' y' n' => a == a' && b == b' && exprEqT y y' && exprEqT n n'
    | _ => false
  | .ret a, t => match t with
    | .ret a' => a == a'
    | _ => false
  | .tail f is a ts, t => match t with
    | .tail f' is' a' ts' => f == f' && is == is' && a == a' && ts.isEmpty && ts'.isEmpty
    | _ => false
  | _, _ => false

theorem exprEqT_eq {e e' : Expr} (h : exprEqT e e' = true) : e = e' := by
  induction e generalizing e' with
  | let_ x op e ih =>
    simp only [exprEqT] at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1, opEqT_eq h.1.2, ih h.2]
    · simp at h
  | split a x y e ih =>
    simp only [exprEqT] at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1.1, h.1.1.2, h.1.2, ih h.2]
    · simp at h
  | ifeq a b y n ihy ihn =>
    simp only [exprEqT] at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1.1.1, h.1.1.2, ihy h.1.2, ihn h.2]
    · simp at h
  | ret a =>
    simp only [exprEqT] at h; split at h
    · simp only [beq_iff_eq] at h; rw [h]
    · simp at h
  | tail f is a ts =>
    simp only [exprEqT] at h; split at h
    · simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h; rfl
    · simp at h
  | _ => simp [exprEqT] at h

/-- **`d` is textually `d'`**: the same name, index and argument names,
types, no type parameters, the same body (`exprEqT`) and the same kind; then `d = d'`
(`declIs_eq`). -/
def declIs (d d' : Decl) : Bool :=
  d.name == d'.name && d.tparams.isEmpty && d'.tparams.isEmpty && d.idx == d'.idx && d.arg == d'.arg &&
    d.argTy == d'.argTy && d.retTy == d'.retTy && exprEqT d.body d'.body && d.kind == d'.kind

theorem declIs_eq {d d' : Decl} (h : declIs d d' = true) : d = d' := by
  cases d; cases d'
  simp only [declIs, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hb⟩, rfl⟩ := h
  rw [exprEqT_eq hb]

/-! ## The extern's model -/

/-- The owned slice `({Loc own Array[m] LanesU8 | ini >= m} * Int[m]) * Int`
(`Frontend.printOwnSig`'s type, `Scc.Lower.printOwnSig_eq`). -/
def ownSliceTy : Ty :=
  .prod (.prod (.refine (.loc .own (.array (.var 0) (.lanes false .w8))) (.ini (.var 0))) (.intS (.var 0))) .int

/-- The loop's buffer: an owned, initialised byte-lane array of
`(i + 1) + d` words. -/
def printLBufTy : Ty :=
  .refine (.loc .own (.array (.add (.add (.var 1) (.lit 1)) (.var 0)) (.lanes false .w8)))
    (.ini (.add (.add (.var 1) (.lit 1)) (.var 0)))

/-- The loop's argument: `(((buffer, i), d), ((c, n), j))`. -/
def printLTy : Ty :=
  .prod (.prod (.prod printLBufTy (.intS (.var 1))) (.intS (.var 0))) (.prod (.prod .int .int) .int)

/-- The loop's word advance (`j = 8`, `d ≠ 0`): the next word, `j = 0`. -/
def printAdv : Expr :=
  .let_ "d1" (.sub (.var "dv") (.lit 1)) <| .let_ "un" (.nameI (.var "d1")) <|
  .let_ "i1" (.add (.var "iv") (.lit 1)) <| .let_ "jn" (.nameI (.var "i1")) <|
  .let_ "bi1" (.pair (.var "b") (.var "jn")) <| .let_ "w1" (.pair (.var "bi1") (.var "un")) <|
  .let_ "z" (.atom (.lit 0)) <| .let_ "q1" (.pair (.var "cn") (.var "z")) <|
  .let_ "a1" (.pair (.var "w1") (.var "q1")) <| .tail "printL" ["jn", "un"] (.var "a1") []

/-- The loop's byte advance: bump `c` and `j`, loop. -/
def printNext : Expr :=
  .let_ "c1" (.add (.var "c") (.lit 1)) <| .let_ "j1" (.add (.var "j") (.lit 1)) <|
  .let_ "cn1" (.pair (.var "c1") (.var "n")) <| .let_ "q1" (.pair (.var "cn1") (.var "j1")) <|
  .let_ "bi2" (.pair (.var "b") (.var "iv")) <| .let_ "w2" (.pair (.var "bi2") (.var "dv")) <|
  .let_ "a1" (.pair (.var "w2") (.var "q1")) <| .tail "printL" ["i", "d"] (.var "a1") []

/-- The loop's body: stop at `c = n`; at `j = 8` stop on the last word or
advance a word; otherwise load the word and emit lane `j`. -/
def printLBody : Expr :=
  .split (.var "a") "w" "q" <| .split (.var "w") "bi" "dv" <| .split (.var "bi") "b" "iv" <|
  .split (.var "q") "cn" "j" <| .split (.var "cn") "c" "n" <|
  .ifeq (.var "c") (.var "n") (.ret .unit) <|
  .ifeq (.var "j") (.lit 8) (.ifeq (.var "dv") (.lit 0) (.ret .unit) printAdv) <|
  .let_ "wd" (.loadAt (.var "b") (.var "iv")) <| .let_ "x" (.lane (.var "wd") (.var "j")) <|
  .let_ "r" (.ext .emit (.var "x")) printNext

/-- **The extern's loop** `printL{i, d}`. -/
def printLoopD : Decl :=
  { name := "printL", idx := ["i", "d"], arg := "a", argTy := printLTy, retTy := .unit, body := printLBody }

/-- The extern's body: stop on an empty slice, otherwise the loop at word 0,
byte 0. -/
def printBody : Expr :=
  .split (.var "a") "bm" "n" <| .split (.var "bm") "b" "mv" <|
  .ifeq (.var "mv") (.lit 0) (.ret .unit) <|
  .let_ "m1" (.sub (.var "mv") (.lit 1)) <| .let_ "mn" (.nameI (.var "m1")) <|
  .let_ "z" (.nameI (.lit 0)) <| .let_ "bi" (.pair (.var "b") (.var "z")) <|
  .let_ "w" (.pair (.var "bi") (.var "mn")) <| .let_ "c0" (.atom (.lit 0)) <|
  .let_ "j0" (.atom (.lit 0)) <| .let_ "cn" (.pair (.var "c0") (.var "n")) <|
  .let_ "q" (.pair (.var "cn") (.var "j0")) <| .let_ "a1" (.pair (.var "w") (.var "q")) <|
  .tail "printL" ["z", "mn"] (.var "a1") []

/-- **The output extern** `print{m}(a : printOwnSig) : Unit` with its model. -/
def printExtD : Decl :=
  { name := "print", idx := ["m"], arg := "a", argTy := ownSliceTy, retTy := .unit, body := printBody }

end Scc.Frontend
