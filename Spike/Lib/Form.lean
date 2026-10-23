/-
**Per-IR-form source steps and the environment relation** (ISA-generic).

scc's lowering (`Scc/Lower/Term.lean`) keeps, for every source variable, its
words as IR operands (a register or an immediate): a number or a pointer is
one operand, a locative two, `(base, offset)`. The forms that only rename or
regroup words emit **no code**: `let x = a` (a variable or a literal), a
pair, `pack`/`packT`, `nameI`, `asLanes`, `let (x, y) = a`, `unpack`. Each
IR register lives in a frame slot (the emitters keep every IR register in
its slot between instructions), so at a node of a function's graph the
source environment is related to the abstract slot file through the
lowering's placement of each variable:

* `WordPl`: where a source word lives in the lowering, `one o` or
  `loc b off` (a locative, scalar layout: the base and a byte offset);
* `opdVal rs sl`: an operand's value, an immediate itself, a register the
  slot `rs r` of the slot file `sl`;
* `WordsRep`, `EnvRep`: every placed variable (`ρ x = some pls`) is bound
  in the environment to words its placement represents (`ValRep` for one
  operand, `LocRep` for a locative).

For each code-free form, `localStep_*` is the source's local step (one
successor, memory untouched). On top of them:

* `SEnv`, `SRep`: the lowering's environment (variable, type, a placement
  per word) representing the source's; `SEnv.ofFn` builds it from the
  generator's per-node data (type and IR operands per variable, regrouped
  per word by `group`, after `Scc.Obj.slots`);
* `sstep`, `srun`: the code-free forms run on the symbolic side, by
  evaluation; `sstep_sound`, `srun_sound`: a symbolic run is a local run of
  the source with the relation kept;
* `NodeJ`: a node's invariant (the term, and `SRep` with operands valued in
  the slot file through the register-slot map); `NodeJ.run` is an edge
  through code-free forms, `NodeJ.step` one that binds a variable a block
  computed.

`LocRep` is the scalar-only reading of a locative (`(base, 8 · offset)`,
offset in source words, no tag), the layout of buffers of scalars (the
`LanesU8` buffers of `hello1.w`); a cell with trace words has the
bipartite layout (`Scc.Obj`), where a source word offset is not
`8 · offset`.
-/
import Spike.Lib.Seg
import Scc.IR.Core
import Scc.Lower.Obj

namespace Spike.Lib.Form

open CoreLang CoreTerm
open Scc.Sem (ValRep)
open Scc.IR (Operand)

/-! ## Placements -/

/-- **Where a source word lives in the lowering**: one operand, or a
locative's base and byte offset. -/
inductive WordPl where
  | one (o : Operand)
  | loc (b off : Operand)

/-- The operands of a word's placement. -/
def WordPl.opds : WordPl → List Operand
  | .one o => [o]
  | .loc b off => [b, off]

/-- **An operand's value**: an immediate, or the slot of a register in the
slot file `sl` (`rs`: IR register ↦ its slot). -/
def opdVal (rs : Scc.IR.Reg → Option Int) (sl : Int → BitVec 64) : Operand → Option Nat
  | .imm v => some v.toNat
  | .reg r => (rs r).map fun k => (sl k).toNat

/-- **A locative's representation** (scalar layout): the base of its
label's object and the byte offset of its word; `undef` is any pair. -/
def LocRep (lbl : WeakMem.AllocLabel → Option Nat) : WeakMem.Val → Nat → Nat → Prop
  | .loc a tag, b, off => tag = 0 ∧ lbl a.label = some b ∧ off = 8 * a.offset
  | .undef, _, _ => True
  | _, _, _ => False

/-- **A source word at its placement**, operands valued by `val`. -/
def WordRep (lbl : WeakMem.AllocLabel → Option Nat) (val : Operand → Option Nat) (w : TermRun.Word) :
    WordPl → Prop
  | .one o => ∃ v, val o = some v ∧ ValRep lbl w.val v
  | .loc b off => ∃ vb vo, val b = some vb ∧ val off = some vo ∧ LocRep lbl w.val vb vo

/-- **Words at their placements**, one by one. -/
def WordsRep (lbl : WeakMem.AllocLabel → Option Nat) (val : Operand → Option Nat) :
    List TermRun.Word → List WordPl → Prop
  | [], [] => True
  | w :: ws, pl :: pls => WordRep lbl val w pl ∧ WordsRep lbl val ws pls
  | _, _ => False

/-- **The environment relation**: every placed variable is bound to words
its placement represents. -/
def EnvRep (lbl : WeakMem.AllocLabel → Option Nat) (val : Operand → Option Nat)
    (ρ : String → Option (List WordPl)) (env : TermRun.Env) : Prop :=
  ∀ x pls, ρ x = some pls → ∃ ty ws, TermRun.lookupE env x = some (ty, ws) ∧ WordsRep lbl val ws pls

/-- The placement after binding `x`. -/
def place (ρ : String → Option (List WordPl)) (x : String) (pls : Option (List WordPl)) :
    String → Option (List WordPl) :=
  fun y => if y = x then pls else ρ y

/-- **An atom's placement** under `ρ`: a variable's, a literal's immediate
(below `2^64`), `unit` none. -/
def AtPl (ρ : String → Option (List WordPl)) : At → List WordPl → Prop
  | .var x, pls => ρ x = some pls
  | .lit n, pls => n < 2 ^ 64 ∧ pls = [.one (.imm (UInt64.ofNat n))]
  | .unit, pls => pls = []

variable {lbl : WeakMem.AllocLabel → Option Nat} {val : Operand → Option Nat}

/-! ## Words -/

namespace WordsRep

theorem length {ws : List TermRun.Word} {pls : List WordPl} (h : WordsRep lbl val ws pls) :
    ws.length = pls.length := by
  induction ws generalizing pls with
  | nil => cases pls <;> simp_all [WordsRep]
  | cons w ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl pls => simp [ih h.2]

theorem append {ws ws' : List TermRun.Word} {pls pls' : List WordPl} (h : WordsRep lbl val ws pls)
    (h' : WordsRep lbl val ws' pls') : WordsRep lbl val (ws ++ ws') (pls ++ pls') := by
  induction ws generalizing pls with
  | nil => cases pls <;> simp_all [WordsRep]
  | cons w ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl pls => exact ⟨h.1, ih h.2⟩

theorem take {ws : List TermRun.Word} {pls : List WordPl} (h : WordsRep lbl val ws pls) (n : Nat) :
    WordsRep lbl val (ws.take n) (pls.take n) := by
  induction ws generalizing pls n with
  | nil => cases pls <;> simp_all [WordsRep]
  | cons w ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl pls =>
      cases n with
      | zero => simp [WordsRep]
      | succ n => exact ⟨h.1, ih h.2 n⟩

theorem drop {ws : List TermRun.Word} {pls : List WordPl} (h : WordsRep lbl val ws pls) (n : Nat) :
    WordsRep lbl val (ws.drop n) (pls.drop n) := by
  induction ws generalizing pls n with
  | nil => cases pls <;> simp_all [WordsRep]
  | cons w ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl pls =>
      cases n with
      | zero => exact h
      | succ n => exact ih h.2 n

/-- **Changing the operand values** off the placement's operands. -/
theorem congr {val' : Operand → Option Nat} {ws : List TermRun.Word} {pls : List WordPl}
    (h : WordsRep lbl val ws pls) (hv : ∀ pl ∈ pls, ∀ o ∈ pl.opds, val' o = val o) :
    WordsRep lbl val' ws pls := by
  induction ws generalizing pls with
  | nil => cases pls <;> simp_all [WordsRep]
  | cons w ws ih =>
    cases pls with
    | nil => simp [WordsRep] at h
    | cons pl pls =>
      refine ⟨?_, ih h.2 fun pl' hp => hv pl' (List.mem_cons_of_mem _ hp)⟩
      have hpl := hv pl List.mem_cons_self
      cases pl with
      | one o =>
        obtain ⟨v, hv1, hv2⟩ := h.1
        exact ⟨v, by rw [hpl o (by simp [WordPl.opds])]; exact hv1, hv2⟩
      | loc b off =>
        obtain ⟨vb, vo, hb, ho, hr⟩ := h.1
        exact ⟨vb, vo, by rw [hpl b (by simp [WordPl.opds])]; exact hb,
          by rw [hpl off (by simp [WordPl.opds])]; exact ho, hr⟩

/-- Words whose values are the same: a word changing only its view. -/
theorem val_congr {ws ws' : List TermRun.Word} {pls : List WordPl} (h : WordsRep lbl val ws pls)
    (hw : ws.map (·.val) = ws'.map (·.val)) : WordsRep lbl val ws' pls := by
  induction ws generalizing ws' pls with
  | nil => cases ws' <;> simp_all
  | cons w ws ih =>
    cases ws' with
    | nil => simp at hw
    | cons w' ws' =>
      cases pls with
      | nil => simp [WordsRep] at h
      | cons pl pls =>
        simp only [List.map_cons, List.cons.injEq] at hw
        refine ⟨?_, ih h.2 hw.2⟩
        cases pl <;> simpa [WordRep, hw.1] using h.1

end WordsRep

/-! ## The environment -/

namespace EnvRep

variable {ρ : String → Option (List WordPl)} {env : TermRun.Env}

/-- **An atom's words at its placement.** -/
theorem at_ (h : EnvRep lbl val ρ env) {a : At} {pls : List WordPl} (hp : AtPl ρ a pls) {t : Ty}
    {ws : List TermRun.Word} (ha : TermRun.evalAt env a = some (t, ws))
    (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) :
    WordsRep lbl val ws pls := by
  cases a with
  | var x =>
    obtain ⟨ty, ws', hl, hr⟩ := h x pls hp
    simp only [TermRun.evalAt, hl, Option.some.injEq, Prod.mk.injEq] at ha
    exact ha.2 ▸ hr
  | lit n =>
    obtain ⟨hn, rfl⟩ := hp
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at ha
    rw [← ha.2]
    refine ⟨⟨n, ?_, hn, rfl⟩, trivial⟩
    rw [hval]; simp [Nat.mod_eq_of_lt hn]
  | unit =>
    simp only [AtPl] at hp
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at ha
    rw [← ha.2, hp]; trivial

/-- **Binding `x`** at a placement of its words. -/
theorem bind (h : EnvRep lbl val ρ env) (x : String) (ty : Ty) {ws : List TermRun.Word} {pls : List WordPl}
    (hw : WordsRep lbl val ws pls) : EnvRep lbl val (place ρ x (some pls)) ((x, ty, ws) :: env) := by
  intro y pls' hy
  by_cases hyx : y = x
  · subst hyx
    simp only [place, ↓reduceIte, Option.some.injEq] at hy
    subst hy
    exact ⟨ty, ws, by simp [TermRun.lookupE], hw⟩
  · simp only [place, hyx, ↓reduceIte] at hy
    obtain ⟨ty', ws', hl, hr⟩ := h y pls' hy
    have hne : (x == y) = false := by simp [Ne.symm hyx]
    exact ⟨ty', ws', by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, hr⟩

/-- **Binding `x` unplaced** (a dead variable, or one with no words). -/
theorem bind_none (h : EnvRep lbl val ρ env) (x : String) (ty : Ty) (ws : List TermRun.Word) :
    EnvRep lbl val (place ρ x none) ((x, ty, ws) :: env) := by
  intro y pls' hy
  by_cases hyx : y = x
  · subst hyx; simp [place] at hy
  · simp only [place, hyx, ↓reduceIte] at hy
    obtain ⟨ty', ws', hl, hr⟩ := h y pls' hy
    have hne : (x == y) = false := by simp [Ne.symm hyx]
    exact ⟨ty', ws', by simp [TermRun.lookupE, List.find?, hne] at hl ⊢; exact hl, hr⟩

/-- **Forgetting placements** (variables no longer read). -/
theorem weaken (h : EnvRep lbl val ρ env) {ρ' : String → Option (List WordPl)}
    (hρ : ∀ x pls, ρ' x = some pls → ρ x = some pls) : EnvRep lbl val ρ' env :=
  fun x pls hx => h x pls (hρ x pls hx)

/-- **Changing the operand values** off every placed operand (a block that
writes only free slots, or registers no placement reads). -/
theorem congr (h : EnvRep lbl val ρ env) {val' : Operand → Option Nat}
    (hv : ∀ x pls, ρ x = some pls → ∀ pl ∈ pls, ∀ o ∈ pl.opds, val' o = val o) : EnvRep lbl val' ρ env := by
  intro x pls hx
  obtain ⟨ty, ws, hl, hr⟩ := h x pls hx
  exact ⟨ty, ws, hl, hr.congr (hv x pls hx)⟩

end EnvRep

theorem opdVal_imm (rs : Scc.IR.Reg → Option Int) (sl : Int → BitVec 64) (n : UInt64) :
    opdVal rs sl (.imm n) = some n.toNat := rfl

/-- A slot write off every placed register's slot keeps the operand values
of the placement. -/
theorem opdVal_upd {rs : Scc.IR.Reg → Option Int} {sl sl' : Int → BitVec 64} {o : Operand}
    (h : ∀ r k, o = .reg r → rs r = some k → sl' k = sl k) : opdVal rs sl' o = opdVal rs sl o := by
  cases o with
  | imm n => rfl
  | reg r =>
    simp only [opdVal]
    cases hr : rs r with
    | none => rfl
    | some k => simp [h r k rfl hr]

/-! ## The code-free forms: local steps -/

section Steps

variable {p : Prog} {c : Ctl} {x : String} {e : Expr} {t : Ty} {ws : List TermRun.Word}

/-- **`let x = a`** binds `a`'s words. -/
theorem localStep_atom {a : At} (ht : c.term = .let_ x (.atom a) e) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStep p c ⟨e, (x, t, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = (a, b)`** binds the concatenation. -/
theorem localStep_pair {a b : At} {u : Ty} {us : List TermRun.Word} (ht : c.term = .let_ x (.pair a b) e)
    (ha : TermRun.evalAt c.env a = some (t, ws)) (hb : TermRun.evalAt c.env b = some (u, us)) :
    LocalStep p c ⟨e, (x, .prod t u, ws ++ us) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hb, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = pack a at w : τ`** binds `a`'s words (the witness erased). -/
theorem localStep_pack {a : At} {w : String} {τ : Ty} (ht : c.term = .let_ x (.pack a w τ) e)
    (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStep p c ⟨e, (x, TermRun.close [] τ, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he hσ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hσ, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = packT a σ τ`** binds `a`'s words (the witness erased). -/
theorem localStep_packT {a : At} {σ τ : Ty} (ht : c.term = .let_ x (.packT a σ τ) e)
    (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStep p c ⟨e, (x, TermRun.close [] τ, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he hσ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hσ, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = nameI a`** binds `a`'s words. -/
theorem localStep_nameI {a : At} (ht : c.term = .let_ x (.nameI a) e) (ha : TermRun.evalAt c.env a = some (t, ws)) :
    LocalStep p c ⟨e, (x, t, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let x = asLanes sg w a`** of a number `n` binds `n mod 2^64`. -/
theorem localStep_asLanes {a : At} {sg : Bool} {w : Wd} {n : Nat} (ht : c.term = .let_ x (.asLanes sg w a) e)
    (ha : TermRun.evalAt c.env a = some (t, ws)) (hn : TermRun.numOf ws = some n) :
    LocalStep p c ⟨e, (x, .lanes sg w, [TermRun.cst (.num (n % TermRun.W64))]) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, TermRun.evalOp, he, ha, hn, TermRun.ol, TermRun.withS, TermRun.stOf]

/-- **`let (x, y) = a`** for `a` of type `u × v`: the first `nWords (accs u)`
words to `x`, the rest to `y`. -/
theorem localStep_split {a : At} {y : String} {u v : Ty} {us : List TermRun.Acc}
    (ht : c.term = .split a x y e) (ha : TermRun.evalAt c.env a = some (.prod u v, ws))
    (hu : TermRun.accs u = some us) :
    LocalStep p c ⟨e, (y, v, ws.drop (TermRun.nWords us)) :: (x, u, ws.take (TermRun.nWords us)) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, he, ha, hu]

/-- **`let <i, x> = unpack a`** of an index package binds its words. -/
theorem localStep_unpack {a : At} {i : String} {b : Ty} (ht : c.term = .unpack a i x e)
    (ha : TermRun.evalAt c.env a = some (.iex b, ws)) :
    LocalStep p c ⟨e, (x, b, ws) :: c.env, none⟩ := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht' he _ _
  simp [TermRun.tstep, ht', ht, he, ha]

end Steps

/-! ## Symbolic environments

The lowering's environment mirrors the source's: each variable with its
type and, per source word, its placement. `SRep` relates the two pointwise
(same names, same types, each word at its placement); `sstep` runs the
code-free forms on the symbolic side, and `sstep_sound` turns a symbolic
step into the source's local step with the relation kept. A block's edge
obligation through code-free forms is then `srun k s t = some (t', s')`,
decided by evaluation. -/

/-- **A symbolic environment**: variable, type, a placement per word. -/
abbrev SEnv := List (String × Ty × List WordPl)

/-- A variable's type and placements (the first binding). -/
def lookupS (s : SEnv) (x : String) : Option (Ty × List WordPl) :=
  (s.find? (·.1 == x)).map (·.2)

/-- **The symbolic environment represents the source's**: each variable it
binds is bound in the source at the same type, each word at its placement.
The source may bind more (variables the lowering dropped). -/
def SRep (lbl : WeakMem.AllocLabel → Option Nat) (val : Operand → Option Nat) (s : SEnv) (env : TermRun.Env) :
    Prop :=
  ∀ x t pls, lookupS s x = some (t, pls) → ∃ ws, TermRun.lookupE env x = some (t, ws) ∧ WordsRep lbl val ws pls

/-- **An atom's type and placements**: a literal below `2^64` is its
immediate (as the lowering's `evalAt`). -/
def sevalAt (s : SEnv) : At → Option (Ty × List WordPl)
  | .var x => lookupS s x
  | .lit n => if n < 2 ^ 64 then some (.intS (.lit n), [.one (.imm (UInt64.ofNat n))]) else none
  | .unit => some (.unit, [])

/-- **One code-free form, symbolically**: the continuation and the
symbolic environment after it; `none` off the code-free forms (and for
`asLanes` of anything but a literal, whose word the relation does not know
to be a number). -/
def sstep (s : SEnv) : Expr → Option (Expr × SEnv)
  | .let_ x (.atom a) e => (sevalAt s a).map fun (t, pls) => (e, (x, t, pls) :: s)
  | .let_ x (.nameI a) e => (sevalAt s a).map fun (t, pls) => (e, (x, t, pls) :: s)
  | .let_ x (.pair a b) e => do
      let (t, p) ← sevalAt s a
      let (u, q) ← sevalAt s b
      pure (e, (x, .prod t u, p ++ q) :: s)
  | .let_ x (.pack a _ τ) e => (sevalAt s a).map fun (_, pls) => (e, (x, TermRun.close [] τ, pls) :: s)
  | .let_ x (.packT a _ τ) e => (sevalAt s a).map fun (_, pls) => (e, (x, TermRun.close [] τ, pls) :: s)
  | .let_ x (.asLanes sg w (.lit n)) e =>
      if n < 2 ^ 64 then some (e, (x, .lanes sg w, [.one (.imm (UInt64.ofNat n))]) :: s) else none
  | .split a x y e =>
      match sevalAt s a with
      | some (.prod u v, pls) =>
          (TermRun.accs u).map fun us =>
            (e, (y, v, pls.drop (TermRun.nWords us)) :: (x, u, pls.take (TermRun.nWords us)) :: s)
      | _ => none
  | .unpack a _ x e =>
      match sevalAt s a with
      | some (.iex b, pls) => some (e, (x, b, pls) :: s)
      | _ => none
  | _ => none

/-- **`k` code-free forms, symbolically.** -/
def srun : Nat → SEnv → Expr → Option (Expr × SEnv)
  | 0, s, t => some (t, s)
  | k + 1, s, t => (sstep s t).bind fun (t', s') => srun k s' t'

namespace SRep

theorem lookup {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) {x : String} {t : Ty}
    {pls : List WordPl} (hx : lookupS s x = some (t, pls)) :
    ∃ ws, TermRun.lookupE env x = some (t, ws) ∧ WordsRep lbl val ws pls :=
  h x t pls hx

/-- **Binding `x`** on both sides. -/
theorem bind {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) (x : String) (t : Ty) {ws : List TermRun.Word}
    {pls : List WordPl} (hw : WordsRep lbl val ws pls) : SRep lbl val ((x, t, pls) :: s) ((x, t, ws) :: env) := by
  intro y u q hy
  by_cases hyx : x = y
  · subst hyx
    simp only [lookupS, List.find?_cons, beq_self_eq_true, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨ws, by simp [TermRun.lookupE], hw⟩
  · have hne : (x == y) = false := by simp [hyx]
    simp only [lookupS, List.find?_cons, hne] at hy
    obtain ⟨ws', hl, hr⟩ := h y u q hy
    exact ⟨ws', by simpa [TermRun.lookupE, List.find?_cons, hne] using hl, hr⟩

/-- **Forgetting variables**: every binding of `s'` is one of `s`
(decided on concrete environments). -/
theorem sub {s s' : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) (hs : ∀ b ∈ s', lookupS s b.1 = some b.2) :
    SRep lbl val s' env := by
  intro x t pls hx
  simp only [lookupS, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  have hbx : b.1 = x := by simpa using List.find?_some hb
  have := hs b (List.mem_of_find?_eq_some hb)
  rw [hbx, hbe] at this
  exact h x _ _ this

theorem evalAt {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env)
    (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) {a : At} {t : Ty} {pls : List WordPl}
    (ha : sevalAt s a = some (t, pls)) :
    ∃ ws, TermRun.evalAt env a = some (t, ws) ∧ WordsRep lbl val ws pls := by
  cases a with
  | var x => exact h.lookup ha
  | lit n =>
    simp only [sevalAt] at ha
    split at ha
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      refine ⟨_, rfl, ⟨n, ?_, hn, rfl⟩, trivial⟩
      rw [hval]; simp [Nat.mod_eq_of_lt hn]
    · cases ha
  | unit =>
    simp only [sevalAt, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨[], rfl, trivial⟩

/-- **Changing the operand values** off every placed operand. -/
theorem congr {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) {val' : Operand → Option Nat}
    (hv : ∀ b ∈ s, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, val' o = val o) : SRep lbl val' s env := by
  intro x t pls hx
  obtain ⟨ws, hl, hr⟩ := h x t pls hx
  simp only [lookupS, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, hbe⟩ := hx
  exact ⟨ws, hl, hr.congr fun pl hp => hv b (List.mem_of_find?_eq_some hb) pl (by rw [hbe]; exact hp)⟩

/-- The relation gives the placement-function view `EnvRep`. -/
theorem envRep {s : SEnv} {env : TermRun.Env} (h : SRep lbl val s env) :
    EnvRep lbl val (fun x => (lookupS s x).map (·.2)) env := by
  intro x pls hx
  cases hl : lookupS s x with
  | none => simp [hl] at hx
  | some tp =>
    obtain ⟨t, q⟩ := tp
    simp only [hl, Option.map_some, Option.some.injEq] at hx
    subst hx
    obtain ⟨ws, hw, hr⟩ := h.lookup hl
    exact ⟨t, ws, hw, hr⟩

end SRep

/-- **A symbolic step is the source's local step**, the relation kept. -/
theorem sstep_sound {p : Prog} {c : Ctl} {s s' : SEnv} {t' : Expr} (h : SRep lbl val s c.env)
    (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) (hs : sstep s c.term = some (t', s')) :
    ∃ env', LocalStep p c ⟨t', env', none⟩ ∧ SRep lbl val s' env' := by
  obtain ⟨term, env⟩ := c
  simp only at h hs ⊢
  unfold sstep at hs
  split at hs
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_atom rfl hw, h.bind _ _ hr⟩
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_nameI rfl hw, h.bind _ _ hr⟩
  · rename_i x a b e
    cases ha : sevalAt s a with
    | none => simp [ha] at hs
    | some tp =>
    cases hb : sevalAt s b with
    | none => simp [ha, hb] at hs
    | some uq =>
    obtain ⟨t, pa⟩ := tp
    obtain ⟨u, pb⟩ := uq
    simp only [ha, hb] at hs
    cases hs
    obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
    obtain ⟨us, hu, hr'⟩ := h.evalAt hval hb
    exact ⟨_, localStep_pair rfl hw hu, h.bind _ _ (hr.append hr')⟩
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_pack rfl hw, h.bind _ _ hr⟩
  · obtain ⟨⟨t, pls⟩, ha, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
    exact ⟨_, localStep_packT rfl hw, h.bind _ _ hr⟩
  · rename_i x sg w n e
    split at hs
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨_, localStep_asLanes (n := n) rfl rfl (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0]),
        h.bind _ _ ⟨⟨n, ?_, ?_⟩, trivial⟩⟩
      · rw [hval]; simp [Nat.mod_eq_of_lt hn]
      · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
    · cases hs
  · split at hs
    · rename_i u v pls ha
      obtain ⟨us, hu, he⟩ := Option.map_eq_some_iff.mp hs
      cases he
      obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
      exact ⟨_, localStep_split rfl hw hu, (h.bind _ _ (hr.take _)).bind _ _ (hr.drop _)⟩
    · cases hs
  · split at hs
    · rename_i b pls ha
      cases hs
      obtain ⟨ws, hw, hr⟩ := h.evalAt hval ha
      exact ⟨_, localStep_unpack rfl hw, h.bind _ _ hr⟩
    · cases hs
  · cases hs

/-- **A symbolic run is a local run of the source**, the relation kept. -/
theorem srun_sound {p : Prog} (hval : ∀ n : UInt64, val (.imm n) = some n.toNat) :
    ∀ (k : Nat) {c : Ctl} {s s' : SEnv} {t' : Expr}, c.hold = none → SRep lbl val s c.env →
      srun k s c.term = some (t', s') → ∃ env', LocalRun p c ⟨t', env', none⟩ ∧ SRep lbl val s' env'
  | 0, c, s, s', t', hc, h, hs => by
    simp only [srun, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨t, env, hold⟩ := c
    cases hc
    exact ⟨env, .refl _, h⟩
  | k + 1, c, s, s', t', hc, h, hs => by
    simp only [srun, Option.bind_eq_some_iff] at hs
    obtain ⟨⟨t₁, s₁⟩, h1, h2⟩ := hs
    obtain ⟨env₁, hl, hr⟩ := sstep_sound (p := p) h hval h1
    obtain ⟨env', hl', hr'⟩ := srun_sound hval k (c := ⟨t₁, env₁, none⟩) rfl hr h2
    exact ⟨env', .step hl hl', hr'⟩

/-! ## From the lowering's environment

The lowering keeps, per variable, its type and one IR operand per runtime
word (`Scc.Obj.slots`: a locative is two, trace base then offset word).
`group` regroups them per source word; `SEnv.ofFn` builds the symbolic
environment of a node from the generator's per-node data (a variable's type
and operands) over the variables listed. -/

/-- **The placements of a value of type `t` from its runtime operands**
(the prefix it takes, and the rest); `none` off the layout fragment. -/
def grp : Ty → List Operand → Option (List WordPl × List Operand)
  | .unit, os | .void, os => some ([], os)
  | .int, o :: os | .intS _, o :: os | .fix _ _, o :: os | .lanes _ _, o :: os | .ptr _ _, o :: os =>
      some ([.one o], os)
  | .loc _ _, b :: off :: os => some ([.loc b off], os)
  | .prod a b, os => do
      let (p, os) ← grp a os
      let (q, os) ← grp b os
      pure (p ++ q, os)
  | .refine t _, os | .iall t, os | .mu t, os => grp t os
  | t@(.iex b), os | t@(.tex _ b), os => if Scc.Obj.coupledPair t then none else grp b os
  | _, _ => none

/-- The placements of a value of type `t` with operands exactly `os`. -/
def group (t : Ty) (os : List Operand) : Option (List WordPl) :=
  match grp t os with
  | some (pls, []) => some pls
  | _ => none

/-- **The symbolic environment of a node** from the generator's data `ρ`
over the variables `xs`. -/
def SEnv.ofFn (ρ : String → Option (Ty × List Operand)) : List String → Option SEnv
  | [] => some []
  | x :: xs => do
      let (t, os) ← ρ x
      let pls ← group t os
      let s ← SEnv.ofFn ρ xs
      pure ((x, t, pls) :: s)

/-! ## Node invariants and edges -/

/-- **The invariant at a node**: the source is at term `t` with no hold
(`Ctl.hold`), and the symbolic environment `s` represents its environment,
with operands valued in the slot file `sl` through the register-slot map
`rs`. -/
def NodeJ (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (t : Expr) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  c.term = t ∧ c.hold = none ∧ SRep lbl (opdVal rs sl) s c.env

/-- **An edge through code-free forms**: `k` symbolic steps from the node's
term reach `t'`; the target node's environment `s₂` keeps bindings of the
reached one, and the block leaves the operands of `s₂` unchanged. Then the
source takes a local run to the target node's invariant. -/
theorem NodeJ.run {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {p : Prog}
    {t t' : Expr} {s s₁ s₂ : SEnv} {sl sl' : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl rs t s sl c) (k : Nat)
    (hr : srun k s t = some (t', s₁)) (hsub : ∀ b ∈ s₂, lookupS s₁ b.1 = some b.2)
    (hsl : ∀ b ∈ s₂, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    ∃ c', LocalRun p c c' ∧ NodeJ lbl rs t' s₂ sl' c' := by
  obtain ⟨ht, hc, hs⟩ := h
  rw [← ht] at hr
  obtain ⟨env', hl, hr'⟩ := srun_sound (p := p) (opdVal_imm rs sl) k hc hs hr
  exact ⟨_, hl, rfl, rfl, (hr'.sub hsub).congr hsl⟩

/-- **A node's invariant after one local step that binds `x`** (a form that
emits code: its words at the placements `pls`, valued in the new slot file
`sl'`), the other bindings' operands unchanged. -/
theorem NodeJ.step {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int} {p : Prog}
    {t e : Expr} {s : SEnv} {sl sl' : Int → BitVec 64} {c : Ctl} {x : String} {ty : Ty}
    {ws : List TermRun.Word} {pls : List WordPl} (h : NodeJ lbl rs t s sl c)
    (hst : LocalStep p c ⟨e, (x, ty, ws) :: c.env, none⟩) (hw : WordsRep lbl (opdVal rs sl') ws pls)
    (hsl : ∀ b ∈ s, ∀ pl ∈ b.2.2, ∀ o ∈ pl.opds, opdVal rs sl' o = opdVal rs sl o) :
    LocalRun p c ⟨e, (x, ty, ws) :: c.env, none⟩ ∧
      NodeJ lbl rs e ((x, ty, pls) :: s) sl' ⟨e, (x, ty, ws) :: c.env, none⟩ :=
  ⟨.single hst, rfl, rfl, (h.2.2.congr hsl).bind x ty hw⟩

/-! ## Tests: the code-free edges of `hello1.w` -/

/-- `rodata`, from its entry to the allocator call of `newBuf`: two
code-free forms bind `two` and `m` to the immediate `2`. -/
example (T : Expr) :
    srun 2 [("u", .unit, [])] (.let_ "two" (.atom (.lit 2)) (.let_ "m" (.nameI (.var "two")) T)) =
      some (T, [("m", .intS (.lit 2), [.one (.imm 2)]), ("two", .intS (.lit 2), [.one (.imm 2)]),
        ("u", .unit, [])]) := rfl

/-- `main`'s argument type: the slice package and the thread id. -/
def mainArgTy : Ty :=
  .prod (.iex (.prod (.prod (.refine (.loc .own (.array (.var 0) (.lanes false .w8))) (.ini (.var 0)))
    (.intS (.var 0))) .int)) (.ptr .pub .void)

/-- `main`'s argument at its operands `a.0 … a.4`: the locative, the
length, the count, the thread id. -/
example : group mainArgTy (["a.0", "a.1", "a.2", "a.3", "a.4"].map .reg) =
    some [.loc (.reg "a.0") (.reg "a.1"), .one (.reg "a.2"), .one (.reg "a.3"), .one (.reg "a.4")] := rfl

/-- `main`, from its entry to the call of `print`: `split` and `unpack`
regroup the argument's placements (the locative is one source word). -/
example (T : Expr) :
    (srun 2 [("a", mainArgTy, [.loc (.reg "a.0") (.reg "a.1"), .one (.reg "a.2"), .one (.reg "a.3"),
        .one (.reg "a.4")])] (.split (.var "a") "sl0" "me" (.unpack (.var "sl0") "q" "sl" T))).map (·.2.map (·.2.2)) =
      some [[.loc (.reg "a.0") (.reg "a.1"), .one (.reg "a.2"), .one (.reg "a.3")], [.one (.reg "a.4")],
        [.loc (.reg "a.0") (.reg "a.1"), .one (.reg "a.2"), .one (.reg "a.3")],
        [.loc (.reg "a.0") (.reg "a.1"), .one (.reg "a.2"), .one (.reg "a.3"), .one (.reg "a.4")]] := rfl

end Spike.Lib.Form
