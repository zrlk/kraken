import WeakCore.TermC1Lem
import WeakCore.TermPtrRtsDefs

/-! # TermC1Cnt: counted words with region references counted (`mPub1`)

`mPub1`/`sNo1`/`pubWords1`/`pubArm1`/`cntIdx1` are `TermPtrRts`'s `mPub`/`sNo`/`pubWords`/`pubArm`/`cntIdx`
with a region reference counted like a `pub` one.  Off region references they agree with the
originals (`sNo1_eq`, `pub1_eq`); a shallow-pub type counts every word (`pubWords1_of_sNo1`,
`cntIdx1_of_sNo1`), in particular a region reference (`sNo1_rgn`).
-/

namespace TermC1
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermPtrRts

/-- (c1, f1) `TermPtrRts.mPub` with a region reference counted as `pub`: under `ModeOK1` it carries a view. -/
def mPub1 : Mode → Bool
  | .pub => true
  | .rgn _ => true -- c1
  | _ => false

/-- (c1) `TermPtrRts.sNo` over `mPub1`.  **Shallow pub-ness**: every reference at a value position is `pub` and every package kind
there is `noOwn` (positions under a reference, and type variables, are not looked at).  Array
elements are looked at. -/
def sNo1 : Ty → Bool
  | .ptr μ _ => mPub1 μ
  | .ptrOpt μ _ => mPub1 μ
  | .loc μ _ => mPub1 μ
  | .prod a b => sNo1 a && sNo1 b
  | .sum a b => sNo1 a && sNo1 b
  | .refine t _ => sNo1 t
  | .iall t => sNo1 t
  | .iex t => sNo1 t
  | .mu t => sNo1 t
  | .tex κ t => κ.noOwn && sNo1 t
  | .array _ t => sNo1 t
  | _ => true

mutual
/-- (c1) `TermPtrRts.pubWords` over `sNo1`/`pubArm1`.  The words of a value of runtime type `rt` that are counted (`cnt`): all of them under a
shallow-pub (`sNo1`) type; otherwise structurally — a `pub` reference's words, the two halves of a
pair, a non-boxed sum's decoded arm payload (decoded at the `lnorm` arms, so skeleton- and
token-erasure-invariant), a boxed sum's box reference, the body under a binder or refinement (an
array is never a value: only under `sNo1`); nothing at an `own` reference or a type variable. -/
def pubWords1 : Ty → List Word → List Word
  | .prod a b, ws =>
      if sNo1 (.prod a b) then ws else
      match wc a with
      | some n => pubWords1 a (ws.take n) ++ pubWords1 b (ws.drop n)
      | none => []
  | .sum a b, ws =>
      if sNo1 (.sum a b) then ws else
      if (Ty.sum a b).tier = .boxed then ws
      else
        match decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
        | some (j, p) => if j < (armsOf a).length then pubArm1 a j p else pubArm1 b (j - (armsOf a).length) p
        | none => []
  | .refine t ψ, ws => if sNo1 (.refine t ψ) then ws else pubWords1 t ws
  | .iall t, ws => if sNo1 (.iall t) then ws else pubWords1 t ws
  | .iex t, ws => if sNo1 (.iex t) then ws else pubWords1 t ws
  | .mu t, ws => if sNo1 (.mu t) then ws else pubWords1 t ws
  | .tex κ t, ws => if sNo1 (.tex κ t) then ws else pubWords1 t ws
  -- `array` falls here: an array is never a value (`accs` is `none`), so cnt on
  -- arrFree types is unchanged by dropping the per-element case.
  | t, ws => if sNo1 t then ws else []

/-- (c1) `TermPtrRts.pubArm` over `pubWords1`.  `pubWords1` of the payload `p` of arm `j` of a (possibly nested) sum. -/
def pubArm1 : Ty → Nat → List Word → List Word
  | .sum a b, j, p => if j < (armsOf a).length then pubArm1 a j p else pubArm1 b (j - (armsOf a).length) p
  | .refine t _, j, p => pubArm1 t j p
  | .iall t, j, p => pubArm1 t j p
  | .iex t, j, p => pubArm1 t j p
  | .mu t, j, p => pubArm1 t j p
  | .tex _ t, j, p => pubArm1 t j p
  | t, _, p => pubWords1 t p
end

/-- (c1) `TermPtrRts.cntIdx` (TermPtrRtsDefs L483) over `pubWords1`.  The counted positions of a value `ws` of runtime type `S`: `pubWords1` by position (each word's
`rts` replaced by its index plus one; `pubWords1` reads only `val`).  The words `pubWords1` synthesises
(a niche `Ptr?` arm's `cst .null`, `rts = 0`) are dropped. -/
def cntIdx1 (S : Ty) (ws : List Word) : List Nat :=
  (pubWords1 S (ws.mapIdx fun i w => { w with rts := i + 1 })).filterMap fun w =>
    if w.rts = 0 then none else some (w.rts - 1)

theorem mPub1_of_mPub {μ : Mode} (h : mPub μ = true) : mPub1 μ = true := by
  cases μ <;> simp_all [mPub, mPub1]

/-- Every reference `sNo` admits, `sNo1` admits. -/
theorem sNo1_of_sNo : ∀ t : Ty, sNo t = true → sNo1 t = true := by
  intro t
  induction t with
  | ptr μ _ _ | ptrOpt μ _ _ | loc μ _ _ => intro h; exact mPub1_of_mPub h
  | prod a b iha ihb | sum a b iha ihb =>
      intro h; simp only [sNo, sNo1, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1, ihb h.2⟩
  | tex κ t ih => intro h; simp only [sNo, sNo1, Bool.and_eq_true] at h ⊢; exact ⟨h.1, ih h.2⟩
  | refine t _ ih | iall t ih | iex t ih | mu t ih | array _ t ih =>
      intro h; simp only [sNo, sNo1] at h ⊢; exact ih h
  | _ => intro _; rfl

/-- Off region references, `sNo1` is `sNo`. -/
theorem sNo1_eq : ∀ t : Ty, rgnFree t = true → sNo1 t = sNo t := by
  intro t
  induction t with
  | ptr μ _ _ | ptrOpt μ _ _ | loc μ _ _ => intro h; cases μ <;> simp_all [rgnFree, sNo, sNo1, mPub, mPub1]
  | prod a b iha ihb | sum a b iha ihb =>
      intro h; simp only [rgnFree, Bool.and_eq_true] at h; simp only [sNo, sNo1, iha h.1, ihb h.2]
  | tex κ t ih => intro h; simp only [rgnFree] at h; simp only [sNo, sNo1, ih h]
  | refine t _ ih | iall t ih | iex t ih | mu t ih | array _ t ih =>
      intro h; simp only [rgnFree] at h; simp only [sNo, sNo1, ih h]
  | _ => intro _; rfl

/-- Off region references, `pubWords1`/`pubArm1` are `pubWords`/`pubArm`. -/
theorem pub1_eq : ∀ t : Ty, rgnFree t = true →
    (∀ ws, pubWords1 t ws = pubWords t ws) ∧ (∀ j p, pubArm1 t j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      intro h
      have hs := sNo1_eq (.prod a b) h
      simp only [rgnFree, Bool.and_eq_true] at h
      have h1 : ∀ ws, pubWords1 (.prod a b) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords1, pubWords, (iha h.1).1, (ihb h.2).1]; rw [hs]; exact rfl
      exact ⟨h1, fun j p => by simp only [pubArm1, pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      intro h
      have hs := sNo1_eq (.sum a b) h
      simp only [rgnFree, Bool.and_eq_true] at h
      exact ⟨fun ws => by simp only [pubWords1, pubWords, (iha h.1).2, (ihb h.2).2]; rw [hs]; exact rfl,
        fun j p => by simp only [pubArm1, pubArm, (iha h.1).2, (ihb h.2).2]⟩
  | refine t _ ih | iall t ih | iex t ih | mu t ih | tex _ t ih =>
      intro h; have hs := sNo1_eq _ h; simp only [rgnFree] at h
      exact ⟨fun ws => by simp only [pubWords1, pubWords, hs, (ih h).1], fun j p => by simp only [pubArm1, pubArm, (ih h).2]⟩
  | _ =>
      intro h
      have hs := sNo1_eq _ h
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords1.eq_def, pubWords.eq_def]; simp only [hs]
      · simp only [pubArm1, pubArm]; rw [pubWords1.eq_def, pubWords.eq_def]; simp only [hs]

/-- Under a shallow-pub (`sNo1`) type every word counts (`pubWords_of_sNo`). -/
theorem pubWords1_of_sNo1 {t : Ty} (h : sNo1 t = true) (ws : List Word) : pubWords1 t ws = ws := by
  cases t
  all_goals first
    | (simp only [pubWords1, h, ite_true]; done)
    | (rw [pubWords1.eq_def]; simp only [h, ite_true])

/-- A region reference is shallow-pub. -/
theorem sNo1_rgn (r : Idx) (u : Ty) :
    sNo1 (.ptr (.rgn r) u) = true ∧ sNo1 (.ptrOpt (.rgn r) u) = true ∧ sNo1 (.loc (.rgn r) u) = true :=
  ⟨rfl, rfl, rfl⟩

theorem filterMap_tagIdx : ∀ (ws : List Word) (k : Nat),
    (ws.mapIdx fun i w => { w with rts := i + k + 1 }).filterMap
      (fun w => if w.rts = 0 then none else some (w.rts - 1)) = List.range' k ws.length := by
  intro ws
  induction ws with
  | nil => intro k; rfl
  | cons w ws ih =>
      intro k
      have e : (fun (i : Nat) (w : Word) => { w with rts := (i + 1) + k + 1 }) =
          (fun (i : Nat) (w : Word) => { w with rts := i + (k + 1) + 1 }) := by
        funext i w; rw [show i + 1 + k + 1 = i + (k + 1) + 1 by omega]
      simp only [List.mapIdx_cons, List.filterMap_cons, Nat.zero_add, List.length_cons, List.range'_succ]
      rw [e, ih (k + 1)]
      simp

/-- Under a shallow-pub type every position is counted. -/
theorem cntIdx1_of_sNo1 {S : Ty} (h : sNo1 S = true) (ws : List Word) :
    cntIdx1 S ws = List.range ws.length := by
  unfold cntIdx1
  rw [pubWords1_of_sNo1 h, List.range_eq_range']
  have := filterMap_tagIdx ws 0
  simp only [Nat.add_zero] at this ⊢
  exact this

/-- Off region references, `cntIdx1` is `cntIdx`. -/
theorem cntIdx1_eq {S : Ty} (h : rgnFree S = true) (ws : List Word) : cntIdx1 S ws = cntIdx S ws := by
  unfold cntIdx1 cntIdx
  rw [(pub1_eq S h).1]

/-- On a `noOwnIn` cell type (every region payload, `rgnCellOK`), `adapt` leaves the counted words. -/
theorem pubWords1_adapt {ke : KEnv} {u : Ty} (r : Idx) (h : Ty.noOwnIn ke u = true) (ws : List Word) :
    pubWords1 (adapt r u) ws = pubWords1 u ws := by
  rw [adapt_noOwn u h]

end TermC1

#print axioms TermC1.mPub1_of_mPub
#print axioms TermC1.sNo1_of_sNo
#print axioms TermC1.sNo1_eq
#print axioms TermC1.pub1_eq
#print axioms TermC1.pubWords1_of_sNo1
#print axioms TermC1.sNo1_rgn
#print axioms TermC1.filterMap_tagIdx
#print axioms TermC1.cntIdx1_of_sNo1
#print axioms TermC1.cntIdx1_eq
#print axioms TermC1.pubWords1_adapt
