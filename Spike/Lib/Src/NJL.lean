import Spike.Lib.Src.NJ3

/-!
**The node invariant indexed by the walk** (ISA-neutral). `EnvNum''` reads
a binding's number facts off its type (`numMask`), so a `pack` needs its
target's mask to be its operand's, and an `if` needs its operands' types to
be numeric. `EnvLit` reads them off the walk's layout (`litWalk2`'s `LitV`):
every word of a binding at a `.leaf` of its layout is a number below `2^64`
(`NumL`), and the binding's type has that layout (`Compat`). The walk gives a
`pack` its operand's layout, so the `pack` keeps it with no premise on
masks; an `if` whose operands are one word each (which the lowering's
`evalOne` asks) reads numbers.

- `litMask`, `litMask_length`, `compat_plLen`; `NumL` (`.pair`, `.split`,
  `.one`); `EnvLit` (`.cons`, `.evalAt`);
- `NJL`, per construct as `litWalk2` binds: code-free `NJL.atom`, `.nameI`,
  `.pair`, `.pack`, `.asLanes`, `.split`, `.unpack`; checked arithmetic and
  `if`: `NJL.ops`, `.add_ok`, `.sub_ok`, `.ifeq`, `.add_ovf` into `AbSrcL`.

Not here: calls and returns (`callsOk2`), `xchg`'s old element (a fact on
the buffer's cells), the start (`meW`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)
open Scc.Lower (LitV litAt)

/-! ## Layout leaves -/

/-- **Which source words of a layout are one-word scalars**: a `.leaf`'s
`true`, a locative's `false`, one flag per source word (`LitV.words`). -/
def litMask : LitV → List Bool
  | .nil => []
  | .leaf _ => [true]
  | .loc => [false]
  | .node l r => litMask l ++ litMask r

theorem litMask_length : ∀ L : LitV, (litMask L).length = L.words.length
  | .nil | .leaf _ | .loc => rfl
  | .node l r => by simp [litMask, LitV.words, litMask_length l, litMask_length r]

/-- **A type of layout `L` has `L`'s placements.** -/
theorem compat_plLen : ∀ (t : Ty) (L : LitV), Compat t L = true → plLen t = some L.words.length := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L h
    cases L <;> simp only [Compat, Bool.and_eq_true, Bool.false_eq_true] at h
    simp [plLen, iha _ h.1, ihb _ h.2, LitV.words]
  | refine t _ ih => intro L h; exact ih L h
  | iall t ih => intro L h; exact ih L h
  | mu t ih => intro L h; exact ih L h
  | iex b ih =>
    intro L h
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [plLen, h.1, ih L h.2]
  | tex k b ih =>
    intro L h
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [plLen, h.1, ih L h.2]
  | _ => intro L h; cases L <;> simp_all [Compat, plLen, LitV.words]

/-- **The words at a layout's leaves are numbers.** -/
def NumL (L : LitV) (ws : List TermRun.Word) : Prop :=
  ∀ (i : Nat) w, ws[i]? = some w → (litMask L)[i]? = some true → IsNum w

namespace NumL

theorem pair {la lb : LitV} {wa wb : List TermRun.Word} (ha : NumL la wa) (hb : NumL lb wb)
    (hl : wa.length = la.words.length) : NumL (.node la lb) (wa ++ wb) := by
  intro i w hw hi
  have hlen : (litMask la).length = wa.length := by rw [litMask_length, hl]
  simp only [litMask] at hi
  by_cases hi' : i < wa.length
  · rw [List.getElem?_append_left hi'] at hw
    rw [List.getElem?_append_left (by omega)] at hi
    exact ha i w hw hi
  · rw [List.getElem?_append_right (by omega)] at hw
    rw [List.getElem?_append_right (by omega), hlen] at hi
    exact hb _ w hw hi

/-- **A pair's parts**: the first `l.words.length` words at `l`, the rest at `r`. -/
theorem split {l r : LitV} {ws : List TermRun.Word} (h : NumL (.node l r) ws) :
    NumL l (ws.take l.words.length) ∧ NumL r (ws.drop l.words.length) := by
  have hlen := litMask_length l
  constructor
  · intro i w hw hi
    have hik : i < l.words.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
    rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hik h)] at hw
    exact h i w hw (by simp only [litMask]; rw [List.getElem?_append_left (by omega)]; exact hi)
  · intro i w hw hi
    rw [List.getElem?_drop] at hw
    exact h _ w hw (by simp only [litMask]; rw [List.getElem?_append_right (by omega), hlen]; simpa using hi)

/-- A one-word value at a leaf is a number. -/
theorem one {L : LitV} {w : TermRun.Word} (h : NumL L [w]) (hm : litMask L = [true]) : IsNum w :=
  h 0 w rfl (by rw [hm]; rfl)

theorem of_all {L : LitV} {ws : List TermRun.Word} (h : ∀ w ∈ ws, IsNum w) : NumL L ws :=
  fun _ w hw _ => h w (List.mem_of_getElem? hw)

end NumL

/-- **A one-word layout of the lowering is a leaf**: one runtime word, so no
locative (two) and one scalar. -/
theorem litMask_of_flatL : ∀ {L : LitV} {f : Option (Option Nat)}, flatL L = [f] → litMask L = [true]
  | .leaf _, _, _ => rfl
  | .nil, _, h => by simp [flatL] at h
  | .loc, _, h => by simp [flatL] at h
  | .node l r, f, h => by
    simp only [flatL] at h
    cases hl : flatL l with
    | nil =>
      rw [hl, List.nil_append] at h
      have hl0 : litMask l = [] := litMask_nil_of_flatL hl
      simp [litMask, hl0, litMask_of_flatL h]
    | cons a as =>
      rw [hl] at h
      cases as with
      | cons _ _ => simp at h
      | nil =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
        have hr0 : litMask r = [] := litMask_nil_of_flatL h.2
        simp [litMask, hr0, litMask_of_flatL hl]
where
  litMask_nil_of_flatL : ∀ {L : LitV}, flatL L = [] → litMask L = []
    | .nil, _ => rfl
    | .leaf _, h => by simp [flatL] at h
    | .loc, h => by simp [flatL] at h
    | .node l r, h => by
      simp only [flatL, List.append_eq_nil_iff] at h
      simp [litMask, litMask_nil_of_flatL h.1, litMask_nil_of_flatL h.2]

/-! ## Environments -/

/-- **Every binding of the walk has its layout and its leaves' numbers** in
the source's environment. -/
def EnvLit (lits : List (String × LitV)) (env : TermRun.Env) : Prop :=
  ∀ x L, lits.lookup x = some L →
    ∃ t ws, TermRun.lookupE env x = some (t, ws) ∧ Compat t L = true ∧ NumL L ws

theorem lookupE_cons (x y : String) (t : Ty) (ws : List TermRun.Word) (env : TermRun.Env) :
    TermRun.lookupE ((x, t, ws) :: env) y = if y = x then some (t, ws) else TermRun.lookupE env y := by
  by_cases h : y = x
  · subst h; simp [TermRun.lookupE, List.find?]
  · simp [TermRun.lookupE, List.find?, beq_false_of_ne (Ne.symm h), h]

theorem EnvLit.cons {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvLit lits env) {x : String}
    {L : LitV} {t : Ty} {ws : List TermRun.Word} (hc : Compat t L = true) (hn : NumL L ws) :
    EnvLit ((x, L) :: lits) ((x, t, ws) :: env) := by
  intro y M hy
  rw [lookup_cons_name] at hy
  rw [lookupE_cons]
  split at hy
  · cases hy; rename_i hyx; exact ⟨t, ws, by simp [hyx], hc, hn⟩
  · rename_i hyx; simp only [hyx, ite_false]; exact h y M hy

/-- **An atom of the walk's scope** (its variable bound in `lits`). -/
def InLits (lits : List (String × LitV)) (a : At) : Prop := ∀ x, a = .var x → (lits.lookup x).isSome = true

/-- **An atom's words keep their layout's facts**, a literal below `2^64` as
`sevalAt` places it. -/
theorem EnvLit.evalAt {lits : List (String × LitV)} {env : TermRun.Env} (h : EnvLit lits env) {s : SEnv}
    {a : At} {t t' : Ty} {pls : List WordPl} {ws : List TermRun.Word} (hsc : InLits lits a)
    (hs : sevalAt s a = some (t', pls)) (he : TermRun.evalAt env a = some (t, ws)) :
    Compat t (litAt lits a) = true ∧ NumL (litAt lits a) ws := by
  cases a with
  | var x =>
    obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 (hsc x rfl)
    obtain ⟨t0, ws0, he0, hc, hn⟩ := h x L hL
    simp only [TermRun.evalAt, he0, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [litAt, hL, Option.getD_some]
    exact ⟨hc, hn⟩
  | lit n =>
    simp only [sevalAt] at hs
    split at hs
    · rename_i hn
      simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨rfl, NumL.of_all fun w hw => ?_⟩
      simp only [List.mem_singleton] at hw; subst hw; exact ⟨n, rfl, hn⟩
    · cases hs
  | unit =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨rfl, NumL.of_all (by simp)⟩

/-! ## The node invariant -/

section NJL

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **The node invariant indexed by the walk**: the source runs locally to
`NodeJ` with `EnvLit` for the walk's bindings `lits` at that node. -/
def NJL (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int)
    (lits : List (String × LitV)) (t : Expr) (s : SEnv) (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ c', LocalRun p c c' ∧ NodeJ lbl rs t s sl c' ∧ EnvLit lits c'.env

theorem NJL.of_nodeJ {lits : List (String × LitV)} {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl}
    (h : NodeJ lbl rs t s sl c) (hn : EnvLit lits c.env) : NJL p lbl rs lits t s sl c :=
  ⟨c, .refl c, h, hn⟩

theorem NJL.pre {lits : List (String × LitV)} {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c c0 : Ctl}
    (h0 : LocalRun p c0 c) (h : NJL p lbl rs lits t s sl c) : NJL p lbl rs lits t s sl c0 :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', h0.trans hr, hj, hn⟩

variable {lits : List (String × LitV)}

/-! ### Code-free forms -/

theorem NJL.atom {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJL p lbl rs lits (.let_ x (.atom a) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hsc : InLits lits a) : NJL p lbl rs ((x, litAt lits a) :: lits) e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_atom hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hc, hl⟩ := hn.evalAt hsc ha he
  exact ⟨_, hr.trans hr2, hj2, hn.cons hc hl⟩

theorem NJL.nameI {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJL p lbl rs lits (.let_ x (.nameI a) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hsc : InLits lits a) : NJL p lbl rs ((x, litAt lits a) :: lits) e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_nameI hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hc, hl⟩ := hn.evalAt hsc ha he
  exact ⟨_, hr.trans hr2, hj2, hn.cons hc hl⟩

/-- A pair, the first atom's placements one per placement of its type. -/
theorem NJL.pair {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t u : Ty}
    {pa pb : List WordPl} (h : NJL p lbl rs lits (.let_ x (.pair a b) e) s sl c) (ha : sevalAt s a = some (t, pa))
    (hb : sevalAt s b = some (u, pb)) (hla : plLen t = some pa.length) (hsa : InLits lits a)
    (hsb : InLits lits b) :
    NJL p lbl rs ((x, .node (litAt lits a) (litAt lits b)) :: lits) e ((x, .prod t u, pa ++ pb) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨us, he', hw'⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  obtain ⟨hr2, hj2⟩ :=
    hj.step (Spike.Lib.Form.localStep_pair hj.1 he he') (hw.append hw') (fun _ _ _ _ _ _ => rfl)
  obtain ⟨hca, hla'⟩ := hn.evalAt hsa ha he
  obtain ⟨hcb, hlb⟩ := hn.evalAt hsb hb he'
  have hlen : ws.length = (litAt lits a).words.length := by
    have := compat_plLen _ _ hca
    rw [hla] at this
    rw [hw.length]; exact Option.some.inj this
  exact ⟨_, hr.trans hr2, hj2, hn.cons (by simp [Compat, hca, hcb]) (hla'.pair hlb hlen)⟩

/-- **A `pack`**: the package at its operand's layout (`layoutOk2` gives
the package's type that layout), no premise on masks. -/
theorem NJL.pack {x w : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t τ : Ty}
    {pls : List WordPl} (h : NJL p lbl rs lits (.let_ x (.pack a w τ) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hsc : InLits lits a) (hτ : Compat τ (litAt lits a) = true) :
    NJL p lbl rs ((x, litAt lits a) :: lits) e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_pack (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons hτ (hn.evalAt hsc ha he).2⟩

theorem NJL.asLanes {x : String} {sg : Bool} {w : Wd} {n : Nat} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c : Ctl} (h : NJL p lbl rs lits (.let_ x (.asLanes sg w (.lit n)) e) s sl c) (hn : n < 2 ^ 64) :
    NJL p lbl rs ((x, .leaf (litAt lits (.lit n)).one) :: lits) e
      ((x, .lanes sg w, [.one (.imm (UInt64.ofNat n))]) :: s) sl c := by
  obtain ⟨c1, hr, hj, hnum⟩ := h
  have hst := Spike.Lib.Form.localStep_asLanes (p := p) (n := n) hj.1 rfl
    (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0])
  have hw : WordsRep lbl (opdVal rs sl) [TermRun.cst (.num (n % TermRun.W64))] [.one (.imm (UInt64.ofNat n))] := by
    refine ⟨⟨n, ?_, ?_⟩, trivial⟩
    · rw [Spike.Lib.Form.opdVal_imm]; simp [Nat.mod_eq_of_lt hn]
    · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  refine ⟨_, hr.trans hr2, hj2, hnum.cons rfl (NumL.of_all fun w' hw' => ?_)⟩
  simp only [List.mem_singleton] at hw'
  subst hw'
  exact ⟨n % TermRun.W64, by simp [TermRun.cst, Promises.TVal.mk0], Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn⟩

/-- **`let (x, y) = a` emits nothing**, the walk taking the pair's parts
(`hl`: the lowering's `splitStep` gives the operand a pair's layout). -/
theorem NJL.split {a : At} {x y : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {u v : Ty}
    {pls : List WordPl} {us : List TermRun.Acc} {l r : LitV} (h : NJL p lbl rs lits (.split a x y e) s sl c)
    (ha : sevalAt s a = some (.prod u v, pls)) (hu : TermRun.accs u = some us)
    (hk : plLen u = some (TermRun.nWords us)) (hsc : InLits lits a) (hl : litAt lits a = .node l r) :
    NJL p lbl rs ((y, r) :: (x, l) :: lits) e
      ((y, v, pls.drop (TermRun.nWords us)) :: (x, u, pls.take (TermRun.nWords us)) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_split (p := p) (y := y) hj.1 he hu
  obtain ⟨hc, hnl⟩ := hn.evalAt hsc ha he
  rw [hl] at hc hnl
  simp only [Compat, Bool.and_eq_true] at hc
  have hkl : TermRun.nWords us = l.words.length := by
    have := compat_plLen _ _ hc.1
    rw [hk] at this; exact Option.some.inj this
  obtain ⟨h1, h2⟩ := hnl.split
  rw [← hkl] at h1 h2
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, (hj.2.2.bind _ _ (hw.take _)).bind _ _ (hw.drop _)⟩,
    (hn.cons hc.1 h1).cons hc.2 h2⟩

/-- **An index unpack emits nothing**: `x` at the package's layout. -/
theorem NJL.unpack {a : At} {i x : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {b : Ty}
    {pls : List WordPl} (h : NJL p lbl rs lits (.unpack a i x e) s sl c) (ha : sevalAt s a = some (.iex b, pls))
    (hsc : InLits lits a) : NJL p lbl rs ((x, litAt lits a) :: lits) e ((x, b, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_unpack (p := p) (i := i) hj.1 he
  obtain ⟨hc, hnl⟩ := hn.evalAt hsc ha he
  simp only [Compat, Bool.and_eq_true] at hc
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2.bind _ _ hw⟩, hn.cons hc.2 hnl⟩

/-! ### Checked arithmetic and the `if` -/

theorem NJL.ops {t : Expr} {a b : At} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJL p lbl rs lits t s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb, LocalRun p c c1 ∧ NodeJ lbl rs t s sl c1 ∧ EnvLit lits c1.env ∧
      TermRun.evalAt c1.env a = some (ta, [wa]) ∧ TermRun.evalAt c1.env b = some (tb, [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb ∧
      va < 2 ^ 64 ∧ vb < 2 ^ 64 := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨wsa, hea, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨wsb, heb, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := (hn.evalAt hsa ha hea).2
  have hnb := (hn.evalAt hsb hb heb).2
  match wsa, wsb, hwa, hwb, hna, hnb with
  | [wa], [wb], ⟨⟨v, hv, hra⟩, _⟩, ⟨⟨u, hu, hrb⟩, _⟩, hna, hnb =>
    rw [hva] at hv; rw [hvb] at hu
    cases hv; cases hu
    obtain ⟨n, hn1, hn2⟩ := hna.one hma
    obtain ⟨m, hm1, hm2⟩ := hnb.one hmb
    have e1 := hra; rw [hn1] at e1
    have e2 := hrb; rw [hm1] at e2
    rw [valRep_num e1] at hra ⊢; rw [valRep_num e2] at hrb ⊢
    exact ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hn1, hm1, hn2, hm2⟩

theorem NJL.add_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJL p lbl rs lits (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hlt : va + vb < 2 ^ 64)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va + vb) :
    NJL p lbl rs ((x, .leaf none) :: lits) e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, -, -⟩ := h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_add (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons rfl (NumL.of_all fun w hw => ?_)⟩
  · refine ⟨⟨va + vb, ?_, Scc.Sem.valRep_addW hra hrb hlt⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va + vb, by simp [TermRun.addW, hna, hnb, TermRun.cst]; rfl, hlt⟩

theorem NJL.sub_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJL p lbl rs lits (.let_ x (.sub a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va - vb) :
    NJL p lbl rs ((x, .leaf none) :: lits) e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, hlta, -⟩ :=
    h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_sub (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons rfl (NumL.of_all fun w hw => ?_)⟩
  · refine ⟨⟨va - vb, ?_, Scc.Sem.valRep_subW hra hrb⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va - vb, by simp [TermRun.subW, hna, hnb, TermRun.cst]; rfl, by omega⟩

/-- **The `if`**, its operands one word each at a leaf of the walk: no
premise on their types. -/
theorem NJL.ifeq {a b : At} {yes no : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJL p lbl rs lits (.ifeq a b yes no) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    NJL p lbl rs lits (if va = vb then yes else no) s sl c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hsa hsb hma hmb hva hvb
  have hst := localStep_ifeq (p := p) hj.1 hea heb hna hnb
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2⟩, hn⟩

/-- **The source at the overflow abort, indexed by the walk**: `AbSrc''`
with `EnvLit`. -/
def AbSrcL (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (lits : List (String × LitV))
    (s : SEnv) (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  OvfReady c ∧ EnvLit lits c.env ∧ SRep lbl (opdVal rs sl) s c.env ∧
    ∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome

theorem NJL.add_ovf {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJL p lbl rs lits (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hsa : InLits lits a) (hsb : InLits lits b)
    (hma : litMask (litAt lits a) = [true]) (hmb : litMask (litAt lits b) = [true])
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrcL lbl rs lits s sl c1 := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hsa hsb hma hmb hva hvb
  refine ⟨c1, hr, ⟨x, a, b, e, ta, tb, wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2, ?_⟩
  rw [hj.1]; exact htot

end NJL

/-- Literals do not change which words are scalars. -/
theorem litMask_erase : ∀ L : LitV, litMask L.erase = litMask L
  | .nil | .leaf _ | .loc => rfl
  | .node l r => by simp [litMask, LitV.erase, litMask_erase l, litMask_erase r]

/-- **Across a call or a return that passes `callsOk2`**: an operand at
layout `L` whose erasure is the declared layout `M` (`argShape`, `shapeOf`
of the result) has `M`'s number facts. -/
theorem NumL.of_erase {L M : LitV} {ws : List TermRun.Word} (h : NumL L ws) (he : L.erase = M) : NumL M ws := by
  intro i w hw hi
  rw [← he, litMask_erase] at hi
  exact h i w hw hi

/-- **A block's entry**: its parameter at its declared layout. -/
theorem EnvLit.entry {d : Decl} {ws : List TermRun.Word} (hc : Compat d.argTy (Scc.Lower.shapeOf d.argTy) = true)
    (hn : NumL (Scc.Lower.shapeOf d.argTy) ws) {env : TermRun.Env} :
    EnvLit ((Scc.Lower.params2 d).map (·, Scc.Lower.shapeOf d.argTy)) ((d.arg, d.argTy, ws) :: env) := by
  intro y M hy
  unfold Scc.Lower.params2 at hy
  split at hy
  · cases hy
  · simp only [List.map_cons, List.map_nil, lookup_cons_name, List.lookup_nil] at hy
    split at hy
    · cases hy; rename_i hyx; exact ⟨d.argTy, ws, by rw [lookupE_cons]; simp [hyx], hc, hn⟩
    · cases hy

/-! ## No refined products (`refOk2`) -/

/-- **Under `noRefProd`, the lowering's split is the source's**: a type
`prodOf` reads as a pair is a literal product. -/
theorem eq_prod_of_noRefProd {t u w : Ty} (hn : Scc.Lower.noRefProd t = true)
    (h : Scc.Lower.prodOf t = some (u, w)) : t = .prod u w := by
  cases t with
  | prod a b => simp only [Scc.Lower.prodOf, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1, h.2]
  | refine t _ =>
    simp only [Scc.Lower.noRefProd, Bool.and_eq_true, Option.isNone_iff_eq_none] at hn
    simp only [Scc.Lower.prodOf] at h
    rw [hn.1] at h; cases h
  | _ => simp [Scc.Lower.prodOf] at h

/-- `noRefProd` passes to a pair's parts and a package's body. -/
theorem noRefProd_prod {a b : Ty} (h : Scc.Lower.noRefProd (.prod a b) = true) :
    Scc.Lower.noRefProd a = true ∧ Scc.Lower.noRefProd b = true := by
  simpa [Scc.Lower.noRefProd] using h

theorem noRefProd_iex {b : Ty} (h : Scc.Lower.noRefProd (.iex b) = true) : Scc.Lower.noRefProd b = true := by
  simpa [Scc.Lower.noRefProd] using h

/-! ## From the walk's checks -/

/-- **A `pack` point that passes `layoutOk2`** (`layQ`): the package's type
has its operand's layout. -/
theorem compat_pack_of_layQ {lits : List (String × LitV)} {x w : String} {a : At} {τ : Ty} {e : Expr}
    (hL : layQ (.let_ x (.pack a w τ) e, lits) = true) : Compat τ (litAt lits a) = true := by
  simp only [layQ, Bool.and_eq_true, beq_iff_eq] at hL
  rw [← compat_erase, hL.1.1]
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hL.2
  exact compat_shapeOf τ 0 0 hL.1.2 (slots_of_valWords hk)

/-- **An operand the lowering reads as one word** (`evalOne`, `AgreeW` against
its layout) is at a leaf of the walk. -/
theorem litMask_of_agreeW {L : LitV} {w : Scc.IR.Operand} (h : AgreeW [w] (flatL L)) : litMask L = [true] := by
  cases hf : flatL L with
  | nil => rw [hf] at h; exact h.elim
  | cons f fs =>
    cases fs with
    | nil => exact litMask_of_flatL hf
    | cons _ _ => rw [hf] at h; exact h.2.elim

/-! ## Tests -/

-- `main`'s argument in `hello1L.w`'s walk: the locative, the count, the length, `me`.
#guard litMask (Scc.Lower.shapeOf Spike.Lib.Form.mainArgTy) == [false, true, true, true]
#guard Compat Spike.Lib.Form.mainArgTy (Scc.Lower.shapeOf Spike.Lib.Form.mainArgTy)

end Spike.Lib.LowerNode
