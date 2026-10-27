import Spike.Lib.Src.GroupShape

/-!
**The node invariant with numeric layout leaves** (ISA-neutral). `EnvNum'`
asks a number only of the words of a binding whose whole type is numeric
(`numTy`). A numeric component of a pair or of an index package therefore
loses its number fact once `split` or `unpack` binds it. `EnvNum''` asks it
per layout leaf: every word at a numeric leaf of its binding's type (`numMask`,
one flag per source word, in `plLen`'s shape) is a number below `2^64`. So
`split` and `unpack` keep it.

- `numMask`, `numMask_plLen` (its length is `plLen`), `plLen_numMask`,
  `numMask_numTy`; `NumOK t ws`, `EnvNum''`;
- the lifts: `EnvNum.toEnvNum''`, and `EnvNum'.toEnvNum''` on a flat
  environment (`Flat`: no numeric leaf under a non-numeric binding);
- `NJ''`, with `NJ.toNJ''`, `NJ'.toNJ''` (flat), and per construct:
  - code-free: `NJ''.atom`, `.nameI`, `.pair`, `.pack`, `.packT`,
    `.asLanes`, `.split`, `.unpack`;
  - checked arithmetic and `if`: `NJ''.ops`, `.add_ok`, `.sub_ok`, `.ifeq`,
    `.add_ovf` into `AbSrc''`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)

/-! ## Numeric layout leaves -/

/-- **Which source words of a value of type `t` are at a numeric leaf**, in
`plLen`'s shape: an integer, fixed-width number or lanes word `true`, a
pointer or locative `false`. -/
def numMask : Ty → Option (List Bool)
  | .unit | .void => some []
  | .int | .intS _ | .fix _ _ | .lanes _ _ => some [true]
  | .ptr _ _ | .tid | .loc _ _ => some [false]
  | .prod a b => do pure ((← numMask a) ++ (← numMask b))
  | .refine t _ | .iall t | .mu t => numMask t
  | t@(.iex b) | t@(.tex _ b) => if Scc.Obj.coupledPair t then none else numMask b
  | _ => none

/-- **The mask has one flag per placement.** -/
theorem numMask_plLen : ∀ (t : Ty), (numMask t).map List.length = plLen t := by
  intro t
  induction t with
  | prod a b iha ihb =>
    simp only [numMask, plLen]
    rw [← iha, ← ihb]
    cases numMask a <;> cases numMask b <;> simp
  | refine t _ ih => exact ih
  | iall t ih => exact ih
  | mu t ih => exact ih
  | iex b ih =>
    simp only [numMask, plLen]
    split <;> simp_all
  | tex k b ih =>
    simp only [numMask, plLen]
    split <;> simp_all
  | _ => rfl

theorem plLen_numMask {t : Ty} {m : List Bool} (h : numMask t = some m) : plLen t = some m.length := by
  rw [← numMask_plLen, h]; rfl

theorem numMask_numTy : ∀ (t : Ty), numTy t = true → numMask t = some [true] := by
  intro t
  induction t with
  | refine t _ ih => intro h; exact ih h
  | _ => intro h; first | rfl | simp [numTy] at h

/-- **A number below `2^64`.** -/
def IsNum (w : TermRun.Word) : Prop := ∃ n, w.val = .num n ∧ n < 2 ^ 64

/-- **The words at numeric leaves are numbers.** -/
def NumOK (t : Ty) (ws : List TermRun.Word) : Prop :=
  ∀ m, numMask t = some m → ∀ (i : Nat) w, ws[i]? = some w → m[i]? = some true → IsNum w

/-- **Every word at a numeric leaf of its binding is a number.** -/
def EnvNum'' (env : TermRun.Env) : Prop := ∀ b ∈ env, NumOK b.2.1 b.2.2

namespace NumOK

theorem of_all {t : Ty} {ws : List TermRun.Word} (h : ∀ w ∈ ws, IsNum w) : NumOK t ws :=
  fun _ _ _ w hw _ => h w (List.mem_of_getElem? hw)

theorem of_noTrue {t : Ty} {ws : List TermRun.Word} (h : ∀ m, numMask t = some m → true ∉ m) : NumOK t ws :=
  fun m hm _ _ _ hi => absurd (List.mem_of_getElem? hi) (h m hm)

/-- A numeric one-word value is a number. -/
theorem one {t : Ty} {w : TermRun.Word} (ht : numTy t = true) (h : NumOK t [w]) : IsNum w :=
  h _ (numMask_numTy t ht) 0 w rfl rfl

theorem pair {t u : Ty} {ws us : List TermRun.Word} (ha : NumOK t ws) (hb : NumOK u us)
    (hl : plLen t = some ws.length) : NumOK (.prod t u) (ws ++ us) := by
  intro m hm i w hw hi
  simp only [numMask, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm
  obtain ⟨ma, hma, mb, hmb, rfl⟩ := hm
  have hlen : ma.length = ws.length := by
    have := plLen_numMask hma; rw [hl] at this; exact (Option.some.inj this).symm
  by_cases hi' : i < ws.length
  · rw [List.getElem?_append_left hi'] at hw
    rw [List.getElem?_append_left (by omega)] at hi
    exact ha ma hma i w hw hi
  · rw [List.getElem?_append_right (by omega)] at hw
    rw [List.getElem?_append_right (by omega), hlen] at hi
    exact hb mb hmb _ w hw hi

/-- **A pair's parts**: the first `plLen u` words at `u`, the rest at `v`. -/
theorem split {u v : Ty} {ws : List TermRun.Word} {k : Nat} (h : NumOK (.prod u v) ws)
    (hpl : (plLen (.prod u v)).isSome = true) (hk : plLen u = some k) :
    NumOK u (ws.take k) ∧ NumOK v (ws.drop k) := by
  have hpl' : (numMask (.prod u v)).isSome = true := by
    rw [← numMask_plLen] at hpl; simpa using hpl
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hpl'
  have hm' := hm
  simp only [numMask, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hm'
  obtain ⟨mu, hmu, mv, hmv, rfl⟩ := hm'
  have hlen : mu.length = k := by
    have := plLen_numMask hmu; rw [hk] at this; exact (Option.some.inj this).symm
  constructor
  · intro m' hm'' i w hw hi
    rw [hmu] at hm''; cases hm''
    have hik : i < k := by
      cases Nat.lt_or_ge i k with
      | inl hlt => exact hlt
      | inr hge =>
        rw [List.getElem?_take] at hw
        simp [show ¬ i < k by omega] at hw
    rw [List.getElem?_take] at hw
    simp only [hik, ite_true] at hw
    exact h _ hm i w hw (by rw [List.getElem?_append_left (by omega)]; exact hi)
  · intro m' hm'' i w hw hi
    rw [hmv] at hm''; cases hm''
    rw [List.getElem?_drop] at hw
    exact h _ hm (k + i) w hw (by rw [List.getElem?_append_right (by omega), ← hlen]; simpa using hi)

/-- **An index package's body** has its words. -/
theorem unpack {b : Ty} {ws : List TermRun.Word} (h : NumOK (.iex b) ws)
    (hc : Scc.Obj.coupledPair (.iex b) = false) : NumOK b ws := by
  intro m hm
  exact h m (by simp [numMask, hc, hm])

/-- A type with the same mask. -/
theorem congr {t t' : Ty} {ws : List TermRun.Word} (h : NumOK t ws) (he : numMask t' = numMask t) :
    NumOK t' ws := by
  intro m hm; rw [he] at hm; exact h m hm

end NumOK

/-! ## Environments -/

theorem EnvNum''.cons {env : TermRun.Env} (h : EnvNum'' env) {x : String} {t : Ty} {ws : List TermRun.Word}
    (hw : NumOK t ws) : EnvNum'' ((x, t, ws) :: env) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hw
  · exact h b hb

/-- **An atom's words keep their leaves' number facts**, a literal's below
`2^64` as `sevalAt` places it. -/
theorem EnvNum''.evalAt {env : TermRun.Env} (h : EnvNum'' env) {s : SEnv} {a : At} {t t' : Ty}
    {pls : List WordPl} {ws : List TermRun.Word} (hs : sevalAt s a = some (t', pls))
    (he : TermRun.evalAt env a = some (t, ws)) : NumOK t ws := by
  cases a with
  | var x =>
    simp only [TermRun.evalAt, TermRun.lookupE, Option.map_eq_some_iff] at he
    obtain ⟨⟨y, u, vs⟩, hb, he⟩ := he
    cases he
    exact h _ (List.mem_of_find?_eq_some hb)
  | lit n =>
    simp only [sevalAt] at hs
    split at hs
    · rename_i hn
      simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      exact NumOK.of_all fun w hw => by
        simp only [List.mem_singleton] at hw; subst hw; exact ⟨n, rfl, hn⟩
    · cases hs
  | unit =>
    simp only [TermRun.evalAt, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    exact NumOK.of_all (by simp)

theorem EnvNum.toEnvNum'' {env : TermRun.Env} (h : EnvNum env) : EnvNum'' env :=
  fun b hb => NumOK.of_all (h b hb)

/-- **A flat environment**: a binding of a type that is not numeric has no
numeric leaf (no number hides in a pair or a package). -/
def Flat (env : TermRun.Env) : Prop :=
  ∀ b ∈ env, numTy b.2.1 = false → ∀ m, numMask b.2.1 = some m → true ∉ m

/-- **On a flat environment `EnvNum'` is `EnvNum''`.** -/
theorem EnvNum'.toEnvNum'' {env : TermRun.Env} (h : EnvNum' env) (hf : Flat env) : EnvNum'' env := by
  intro b hb
  cases ht : numTy b.2.1
  · exact NumOK.of_noTrue (hf b hb ht)
  · exact NumOK.of_all (h b hb ht)

/-! ## The node invariant -/

section NJ''

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}

/-- **The node invariant with numeric layout leaves**: `NJ'` with
`EnvNum''`. -/
def NJ'' (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (t : Expr)
    (s : SEnv) (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  ∃ c', LocalRun p c c' ∧ NodeJ lbl rs t s sl c' ∧ EnvNum'' c'.env

theorem NJ.toNJ'' {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NJ p lbl rs t s sl c) :
    NJ'' p lbl rs t s sl c :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', hr, hj, hn.toEnvNum''⟩

/-- `NJ'` is `NJ''` where the source environment reached is flat. -/
theorem NJ'.toNJ'' {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NJ' p lbl rs t s sl c)
    (hf : ∀ c', LocalRun p c c' → Flat c'.env) : NJ'' p lbl rs t s sl c :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', hr, hj, hn.toEnvNum'' (hf c' hr)⟩

theorem NJ''.of_nodeJ {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl rs t s sl c)
    (hn : EnvNum'' c.env) : NJ'' p lbl rs t s sl c :=
  ⟨c, .refl c, h, hn⟩

theorem NJ''.pre {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c c0 : Ctl} (h0 : LocalRun p c0 c)
    (h : NJ'' p lbl rs t s sl c) : NJ'' p lbl rs t s sl c0 :=
  let ⟨c', hr, hj, hn⟩ := h
  ⟨c', h0.trans hr, hj, hn⟩

/-! ### Code-free forms -/

theorem NJ''.atom {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJ'' p lbl rs (.let_ x (.atom a) e) s sl c) (ha : sevalAt s a = some (t, pls)) :
    NJ'' p lbl rs e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_atom hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons (hn.evalAt ha he)⟩

theorem NJ''.nameI {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t : Ty}
    {pls : List WordPl} (h : NJ'' p lbl rs (.let_ x (.nameI a) e) s sl c) (ha : sevalAt s a = some (t, pls)) :
    NJ'' p lbl rs e ((x, t, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨hr2, hj2⟩ := hj.step (Spike.Lib.Form.localStep_nameI hj.1 he) hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons (hn.evalAt ha he)⟩

/-- A pair, the first atom's placements one per placement of its type. -/
theorem NJ''.pair {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t u : Ty}
    {pa pb : List WordPl} (h : NJ'' p lbl rs (.let_ x (.pair a b) e) s sl c) (ha : sevalAt s a = some (t, pa))
    (hb : sevalAt s b = some (u, pb)) (hla : plLen t = some pa.length) :
    NJ'' p lbl rs e ((x, .prod t u, pa ++ pb) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨us, he', hw'⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  obtain ⟨hr2, hj2⟩ :=
    hj.step (Spike.Lib.Form.localStep_pair hj.1 he he') (hw.append hw') (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons ((hn.evalAt ha he).pair (hn.evalAt hb he') (by rw [hw.length]; exact hla))⟩

/-- A `pack`, the packed type with the atom's type's mask. -/
theorem NJ''.pack {x w : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t τ : Ty}
    {pls : List WordPl} (h : NJ'' p lbl rs (.let_ x (.pack a w τ) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hτ : numMask τ = numMask t) : NJ'' p lbl rs e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_pack (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons ((hn.evalAt ha he).congr hτ)⟩

theorem NJ''.packT {x : String} {a : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {t σ τ : Ty}
    {pls : List WordPl} (h : NJ'' p lbl rs (.let_ x (.packT a σ τ) e) s sl c) (ha : sevalAt s a = some (t, pls))
    (hτ : numMask τ = numMask t) : NJ'' p lbl rs e ((x, τ, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_packT (p := p) hj.1 he
  rw [close_nil] at hst
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  exact ⟨_, hr.trans hr2, hj2, hn.cons ((hn.evalAt ha he).congr hτ)⟩

theorem NJ''.asLanes {x : String} {sg : Bool} {w : Wd} {n : Nat} {e : Expr} {s : SEnv} {sl : Int → BitVec 64}
    {c : Ctl} (h : NJ'' p lbl rs (.let_ x (.asLanes sg w (.lit n)) e) s sl c) (hn : n < 2 ^ 64) :
    NJ'' p lbl rs e ((x, .lanes sg w, [.one (.imm (UInt64.ofNat n))]) :: s) sl c := by
  obtain ⟨c1, hr, hj, hnum⟩ := h
  have hst := Spike.Lib.Form.localStep_asLanes (p := p) (n := n) hj.1 rfl
    (by simp [TermRun.numOf, TermRun.cst, Promises.TVal.mk0])
  have hw : WordsRep lbl (opdVal rs sl) [TermRun.cst (.num (n % TermRun.W64))] [.one (.imm (UInt64.ofNat n))] := by
    refine ⟨⟨n, ?_, ?_⟩, trivial⟩
    · rw [Spike.Lib.Form.opdVal_imm]; simp [Nat.mod_eq_of_lt hn]
    · simp [TermRun.cst, Promises.TVal.mk0, ValRep, TermRun.W64, Nat.mod_eq_of_lt hn, hn]
  obtain ⟨hr2, hj2⟩ := hj.step hst hw (fun _ _ _ _ _ _ => rfl)
  refine ⟨_, hr.trans hr2, hj2, hnum.cons (NumOK.of_all fun w' hw' => ?_)⟩
  simp only [List.mem_singleton] at hw'
  subst hw'
  exact ⟨n % TermRun.W64, by simp [TermRun.cst, Promises.TVal.mk0], Nat.lt_of_le_of_lt (Nat.mod_le _ _) hn⟩

/-- **`let (x, y) = a` emits nothing**: the first `nWords (accs u)`
placements to `x`, the rest to `y`, where that count is `u`'s placements'
and the pair has placements. -/
theorem NJ''.split {a : At} {x y : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {u v : Ty}
    {pls : List WordPl} {us : List TermRun.Acc} (h : NJ'' p lbl rs (.split a x y e) s sl c)
    (ha : sevalAt s a = some (.prod u v, pls)) (hu : TermRun.accs u = some us)
    (hk : plLen u = some (TermRun.nWords us)) (hpl : (plLen (.prod u v)).isSome = true) :
    NJ'' p lbl rs e ((y, v, pls.drop (TermRun.nWords us)) :: (x, u, pls.take (TermRun.nWords us)) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_split (p := p) (y := y) hj.1 he hu
  obtain ⟨h1, h2⟩ := (hn.evalAt ha he).split hpl hk
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, (hj.2.2.bind _ _ (hw.take _)).bind _ _ (hw.drop _)⟩,
    (hn.cons h1).cons h2⟩

/-- **An index unpack emits nothing**: `x` bound to the package's
placements at its body. -/
theorem NJ''.unpack {a : At} {i x : String} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {b : Ty}
    {pls : List WordPl} (h : NJ'' p lbl rs (.unpack a i x e) s sl c) (ha : sevalAt s a = some (.iex b, pls))
    (hc : Scc.Obj.coupledPair (.iex b) = false) : NJ'' p lbl rs e ((x, b, pls) :: s) sl c := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  have hst := Spike.Lib.Form.localStep_unpack (p := p) (i := i) hj.1 he
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2.bind _ _ hw⟩, hn.cons ((hn.evalAt ha he).unpack hc)⟩

/-! ### Checked arithmetic and the `if` -/

theorem NJ''.ops {t : Expr} {a b : At} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ'' p lbl rs t s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    ∃ c1 wa wb, LocalRun p c c1 ∧ NodeJ lbl rs t s sl c1 ∧ EnvNum'' c1.env ∧
      TermRun.evalAt c1.env a = some (ta, [wa]) ∧ TermRun.evalAt c1.env b = some (tb, [wb]) ∧
      ValRep lbl wa.val va ∧ ValRep lbl wb.val vb ∧ wa.val = .num va ∧ wb.val = .num vb ∧
      va < 2 ^ 64 ∧ vb < 2 ^ 64 := by
  obtain ⟨c1, hr, hj, hn⟩ := h
  obtain ⟨wsa, hea, hwa⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) ha
  obtain ⟨wsb, heb, hwb⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm rs sl) hb
  have hna := hn.evalAt ha hea
  have hnb := hn.evalAt hb heb
  match wsa, wsb, hwa, hwb, hna, hnb with
  | [wa], [wb], ⟨⟨v, hv, hra⟩, _⟩, ⟨⟨u, hu, hrb⟩, _⟩, hna, hnb =>
    rw [hva] at hv; rw [hvb] at hu
    cases hv; cases hu
    obtain ⟨n, hn1, hn2⟩ := hna.one hta
    obtain ⟨m, hm1, hm2⟩ := hnb.one htb
    have e1 := hra; rw [hn1] at e1
    have e2 := hrb; rw [hm1] at e2
    rw [valRep_num e1] at hra ⊢; rw [valRep_num e2] at hrb ⊢
    exact ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hn1, hm1, hn2, hm2⟩

theorem NJ''.add_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ'' p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hlt : va + vb < 2 ^ 64)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va + vb) :
    NJ'' p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_add (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons (NumOK.of_all fun w hw => ?_)⟩
  · refine ⟨⟨va + vb, ?_, Scc.Sem.valRep_addW hra hrb hlt⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va + vb, by simp [TermRun.addW, hna, hnb, TermRun.cst]; rfl, hlt⟩

theorem NJ''.sub_ok {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ'' p lbl rs (.let_ x (.sub a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb)
    {d : Scc.IR.Reg} {k : Int} (hd : rs d = some k)
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r k', o = .reg r → rs r = some k' → k' ≠ k)
    {v : BitVec 64} (hv : v.toNat = va - vb) :
    NJ'' p lbl rs e ((x, .int, [.one (.reg d)]) :: s) (upd sl k v) c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, hra, hrb, hna, hnb, hlta, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_sub (p := p) hj.1 hea heb
  refine ⟨_, hr.trans (.single hst), (hj.step hst ?_ ?_).2, hn.cons (NumOK.of_all fun w hw => ?_)⟩
  · refine ⟨⟨va - vb, ?_, Scc.Sem.valRep_subW hra hrb⟩, trivial⟩
    simp [opdVal, hd, upd_apply, hv]
  · intro q hq pl hpl o ho
    exact Spike.Lib.Form.opdVal_upd fun r k' hor hr' => by
      simp [upd_apply, hfr q hq pl hpl o ho r k' hor hr']
  · simp only [List.mem_singleton] at hw
    subst hw
    exact ⟨va - vb, by simp [TermRun.subW, hna, hnb, TermRun.cst]; rfl, by omega⟩

theorem NJ''.ifeq {a b : At} {yes no : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ'' p lbl rs (.ifeq a b yes no) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) :
    NJ'' p lbl rs (if va = vb then yes else no) s sl c := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  have hst := localStep_ifeq (p := p) hj.1 hea heb hna hnb
  exact ⟨_, hr.trans (.single hst), ⟨rfl, rfl, hj.2.2⟩, hn⟩

/-- **The source at the overflow abort, with numeric leaves**: `AbSrc'`
with `EnvNum''`. -/
def AbSrc'' (lbl : WeakMem.AllocLabel → Option Nat) (rs : Scc.IR.Reg → Option Int) (s : SEnv)
    (sl : Int → BitVec 64) (c : Ctl) : Prop :=
  OvfReady c ∧ EnvNum'' c.env ∧ SRep lbl (opdVal rs sl) s c.env ∧
    ∀ y ∈ Scc.Sem.exprFv c.term, (lookupS s y).isSome

theorem AbSrc.toAbSrc'' {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : AbSrc lbl rs s sl c) :
    AbSrc'' lbl rs s sl c :=
  ⟨h.1, h.2.1.toEnvNum'', h.2.2⟩

theorem NJ''.add_ovf {x : String} {a b : At} {e : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} {ta tb : Ty}
    {pa pb : Scc.IR.Operand} {va vb : Nat} (h : NJ'' p lbl rs (.let_ x (.add a b) e) s sl c)
    (ha : sevalAt s a = some (ta, [.one pa])) (hb : sevalAt s b = some (tb, [.one pb]))
    (hta : numTy ta = true) (htb : numTy tb = true)
    (hva : opdVal rs sl pa = some va) (hvb : opdVal rs sl pb = some vb) (hge : 2 ^ 64 ≤ va + vb)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome) :
    ∃ c1, LocalRun p c c1 ∧ AbSrc'' lbl rs s sl c1 := by
  obtain ⟨c1, wa, wb, hr, hj, hn, hea, heb, -, -, hna, hnb, -, -⟩ := h.ops ha hb hta htb hva hvb
  refine ⟨c1, hr, ⟨x, a, b, e, ta, tb, wa, wb, va, vb, hj.1, hea, heb, hna, hnb, hge⟩, hn, hj.2.2, ?_⟩
  rw [hj.1]; exact htot

end NJ''

/-! ## Tests: `main`'s argument -/

-- The locative, the length (numeric), the count (numeric), the thread id: after `split` and
-- `unpack` the length and the count keep their number facts.
#guard numMask Spike.Lib.Form.mainArgTy == some [false, true, true, false]
#guard (numMask Spike.Lib.Form.mainArgTy).map List.length == plLen Spike.Lib.Form.mainArgTy

end Spike.Lib.LowerNode
