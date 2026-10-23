/-
T3c-5c: the tear lemma ("M2b design: placeholder hiding").

A non-atomic load of a shared cell reads each access unit (`accs`) from a
possibly different store.  For a type that passes `coupledOK`, splicing two
values at a unit boundary gives a value (`VR_tear`); `Valid` tears for any type
(`Valid_tear`).  Every coupled package and every sum is one unit, so the words
that must agree (a witness and the words that mention it) are read together.
-/
import WeakCore.TermSound
open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound

set_option linter.unusedSimpArgs false
namespace TermTear

/-! ## Splicing and boundaries -/

def splice (k : Nat) (ws1 ws2 : List Word) : List Word := ws1.take k ++ ws2.drop k
def Bnd (us : List Acc) (k : Nat) : Prop := ∃ i, k = nWords (us.take i)

theorem nWords_append (x y : List Acc) : nWords (x ++ y) = nWords x + nWords y := by
  simp [nWords]

theorem nWords_take_le (us : List Acc) (i : Nat) : nWords (us.take i) ≤ nWords us := by
  induction us generalizing i with
  | nil => simp [nWords]
  | cons a us ih =>
      cases i with
      | zero => simp [nWords]
      | succ i => have := ih i; simp [nWords] at this ⊢; omega

theorem Bnd_left {ua ub : List Acc} {k : Nat} (hb : Bnd (ua ++ ub) k) (hk : k ≤ nWords ua) :
    Bnd ua k := by
  obtain ⟨i, rfl⟩ := hb
  rw [List.take_append, nWords_append] at hk ⊢
  by_cases hi : i ≤ ua.length
  · refine ⟨i, ?_⟩
    have : i - ua.length = 0 := by omega
    simp [this, nWords]
  · rw [List.take_of_length_le (by omega)] at hk ⊢
    refine ⟨ua.length, ?_⟩
    simp only [List.take_length]
    omega

theorem Bnd_right {ua ub : List Acc} {k : Nat} (hb : Bnd (ua ++ ub) k) (hk : nWords ua < k) :
    Bnd ub (k - nWords ua) := by
  obtain ⟨i, rfl⟩ := hb
  rw [List.take_append, nWords_append] at hk ⊢
  by_cases hi : i ≤ ua.length
  · have : i - ua.length = 0 := by omega
    have h2 := nWords_take_le ua i
    simp only [this, List.take_zero] at hk
    have h0 : nWords ([] : List Acc) = 0 := rfl
    omega
  · rw [List.take_of_length_le (by omega)] at hk ⊢
    exact ⟨i - ua.length, by omega⟩

theorem Bnd_small {us : List Acc} {k : Nat} (hl : us.length ≤ 1) (hb : Bnd us k) :
    k = 0 ∨ nWords us ≤ k := by
  obtain ⟨i, rfl⟩ := hb
  match us, hl with
  | [], _ => simp [nWords]
  | [a], _ =>
      cases i with
      | zero => simp [nWords]
      | succ i => right; simp

theorem length_splice {k n : Nat} {ws1 ws2 : List Word} (l1 : ws1.length = n) (l2 : ws2.length = n) :
    (splice k ws1 ws2).length = n := by
  simp [splice, l1, l2]; omega

theorem splice_zero (ws1 ws2 : List Word) : splice 0 ws1 ws2 = ws2 := by simp [splice]

theorem splice_full {k : Nat} {ws1 ws2 : List Word} (l1 : ws1.length ≤ k) (l2 : ws2.length ≤ k) :
    splice k ws1 ws2 = ws1 := by
  simp [splice, List.take_of_length_le l1, List.drop_of_length_le l2]

theorem take_splice_le {k na : Nat} {ws1 ws2 : List Word} (hk : k ≤ na) (l1 : na ≤ ws1.length) :
    (splice k ws1 ws2).take na = splice k (ws1.take na) (ws2.take na) := by
  simp only [splice, List.take_append, List.take_take, List.length_take, List.drop_take]
  have e1 : min k na = k := by omega
  have e1' : min na k = k := by omega
  have e2 : min k ws1.length = k := by omega
  simp only [e1, e1', e2]

theorem drop_splice_le {k na : Nat} {ws1 ws2 : List Word} (hk : k ≤ na) (l1 : na ≤ ws1.length) :
    (splice k ws1 ws2).drop na = ws2.drop na := by
  simp only [splice, List.drop_append, List.length_take, List.drop_drop]
  have e2 : min k ws1.length = k := by omega
  rw [e2, List.drop_eq_nil_of_le (by simp; omega)]
  simp only [List.nil_append]
  congr 1; omega

theorem take_splice_ge {k na : Nat} {ws1 ws2 : List Word} (hk : na ≤ k) (l1 : na ≤ ws1.length) :
    (splice k ws1 ws2).take na = ws1.take na := by
  simp only [splice, List.take_append, List.take_take, List.length_take]
  have e1 : min na k = na := by omega
  have e2 : na - min k ws1.length = 0 := by omega
  rw [e1, e2]; simp

theorem drop_splice_ge {k na : Nat} {ws1 ws2 : List Word} (hk : na ≤ k) (l1 : na ≤ ws1.length) :
    (splice k ws1 ws2).drop na = splice (k - na) (ws1.drop na) (ws2.drop na) := by
  simp only [splice, List.drop_append, List.length_take, List.drop_drop, List.drop_take]
  have e2 : na - min k ws1.length = 0 := by omega
  rw [e2]
  have e3 : na + (k - na) = k := by omega
  simp [e3]

/-! ## Congruence: closing, evaluating and `VR` read only mentioned variables -/

theorem ev_congr {ρ ρ' : Nat → Nat} : ∀ (i : Idx), (∀ j, i.mentions j = true → ρ j = ρ' j) →
    ev ρ i = ev ρ' i
  | .lit _, _ => rfl
  | .var k, h => by simp only [ev]; exact h k (by simp [Idx.mentions])
  | .add a b, h => by
      simp only [ev]
      rw [ev_congr a (fun j hj => h j (by simp [Idx.mentions, hj])),
        ev_congr b (fun j hj => h j (by simp [Idx.mentions, hj]))]
  | .sub a b, h => by
      simp only [ev]
      rw [ev_congr a (fun j hj => h j (by simp [Idx.mentions, hj])),
        ev_congr b (fun j hj => h j (by simp [Idx.mentions, hj]))]
  | .smul n a, h => by
      simp only [ev]
      rw [ev_congr a (fun j hj => h j (by simp [Idx.mentions, hj]))]

theorem clI_congr {ρ ρ' : Nat → Nat} : ∀ (i : Idx) (d : Nat),
    (∀ j, i.mentions (j + d) = true → ρ j = ρ' j) → clI ρ d i = clI ρ' d i
  | .lit _, _, _ => rfl
  | .var k, d, h => by
      simp only [clI]
      split
      · rfl
      · rw [h (k - d) (by simp [Idx.mentions]; omega)]
  | .add a b, d, h => by
      simp only [clI]
      rw [clI_congr a d (fun j hj => h j (by simp [Idx.mentions, hj])),
        clI_congr b d (fun j hj => h j (by simp [Idx.mentions, hj]))]
  | .sub a b, d, h => by
      simp only [clI]
      rw [clI_congr a d (fun j hj => h j (by simp [Idx.mentions, hj])),
        clI_congr b d (fun j hj => h j (by simp [Idx.mentions, hj]))]
  | .smul n a, d, h => by
      simp only [clI]
      rw [clI_congr a d (fun j hj => h j (by simp [Idx.mentions, hj]))]

theorem clM_congr {ρ ρ' : Nat → Nat} (μ : Mode) (d : Nat)
    (h : ∀ j, μ.mentions (j + d) = true → ρ j = ρ' j) : clM ρ d μ = clM ρ' d μ := by
  cases μ with
  | rgn r => simp only [clM]; rw [clI_congr r d (fun j hj => h j (by simp [Mode.mentions, hj]))]
  | _ => rfl

theorem clP_congr {ρ ρ' : Nat → Nat} : ∀ (ψ : Pred) (d : Nat),
    (∀ j, ψ.mentions (j + d) = true → ρ j = ρ' j) → clP ρ d ψ = clP ρ' d ψ
  | .tt, _, _ => rfl
  | .le a b, d, h => by
      simp only [clP]
      rw [clI_congr a d (fun j hj => h j (by simp [Pred.mentions, hj])),
        clI_congr b d (fun j hj => h j (by simp [Pred.mentions, hj]))]
  | .eq a b, d, h => by
      simp only [clP]
      rw [clI_congr a d (fun j hj => h j (by simp [Pred.mentions, hj])),
        clI_congr b d (fun j hj => h j (by simp [Pred.mentions, hj]))]
  | .and p q, d, h => by
      simp only [clP]
      rw [clP_congr p d (fun j hj => h j (by simp [Pred.mentions, hj])),
        clP_congr q d (fun j hj => h j (by simp [Pred.mentions, hj]))]
  | .ini a, d, h => by
      simp only [clP]
      rw [clI_congr a d (fun j hj => h j (by simp [Pred.mentions, hj]))]

theorem cl_congr : ∀ (u : Ty) (c d : Nat) (ρ ρ' : Nat → Nat) (W W' : Nat → Ty),
    (∀ j, u.idxMentions (j + d) = true → ρ j = ρ' j) → (∀ j, u.tyMentions (j + c) = true → W j = W' j) →
    cl ρ W c d u = cl ρ' W' c d u := by
  intro u
  induction u with
  | unit | void | int | tid | fix | lanes => intros; rfl
  | intS i =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr i d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | prod a b iha ihb =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [iha c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj])),
        ihb c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | sum a b iha ihb =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [iha c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj])),
        ihb c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | code a b iha ihb =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [iha c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj])),
        ihb c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | array i t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clI_congr i d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        ih c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | ptr μ t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clM_congr μ d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        ih c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | ptrOpt μ t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clM_congr μ d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        ih c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | loc μ t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clM_congr μ d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        ih c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | share r =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | cap s r =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | word r P =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | word2 r P =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | tok2 r P i j =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        clI_congr i d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        clI_congr j d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | epair r P =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]; rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | tokE r P i =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        clI_congr i d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | tok r st =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [clI_congr r d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
      cases st with
      | none => rfl
      | some p =>
          obtain ⟨P, i⟩ := p
          simp only [Option.map_some]
          rw [clI_congr i d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]
  | tvar k =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      split
      · rfl
      · exact hT (k - c) (by simp [Ty.tyMentions]; omega)
  | mu t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [ih (c + 1) d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (fun j hj => hT j (by simp only [Ty.tyMentions]; rw [show j + c + 1 = j + (c + 1) by omega]; exact hj))]
  | tex κ t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [ih (c + 1) d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (fun j hj => hT j (by simp only [Ty.tyMentions]; rw [show j + c + 1 = j + (c + 1) by omega]; exact hj))]
  | iall t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [ih c (d + 1) ρ ρ' W W'
        (fun j hj => hI j (by simp only [Ty.idxMentions]; rw [show j + d + 1 = j + (d + 1) by omega]; exact hj))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | iex t ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [ih c (d + 1) ρ ρ' W W'
        (fun j hj => hI j (by simp only [Ty.idxMentions]; rw [show j + d + 1 = j + (d + 1) by omega]; exact hj))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj]))]
  | refine t ψ ih =>
      intro c d ρ ρ' W W' hI hT
      simp only [cl]
      rw [ih c d ρ ρ' W W' (fun j hj => hI j (by simp [Ty.idxMentions, hj])) (fun j hj => hT j (by simp [Ty.tyMentions, hj])),
        clP_congr ψ d (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]

theorem IniR_congr {ρ ρ' : Nat → Nat} {ini ini' : WeakMem.AllocLabel → Nat} (hi : ini = ini') {ws : List Word} :
    ∀ (ψ : Pred), (∀ j, ψ.mentions j = true → ρ j = ρ' j) → IniR ρ ini ψ ws → IniR ρ' ini' ψ ws := by
  intro ψ
  induction ψ with
  | ini k =>
      intro h hv; simp only [IniR] at hv ⊢; intro a ha
      rw [← ev_congr k (fun j hj => h j (by simp [Pred.mentions, hj])), ← hi]; exact hv a ha
  | and p q ihp ihq =>
      intro h hv; simp only [IniR] at hv ⊢
      exact ⟨ihp (fun j hj => h j (by simp [Pred.mentions, hj])) hv.1,
        ihq (fun j hj => h j (by simp [Pred.mentions, hj])) hv.2⟩
  | _ => intros; simp [IniR]

/-- `IniR` constrains only one-word lists. -/
theorem IniR_short {ρ : Nat → Nat} {ini : WeakMem.AllocLabel → Nat} {ws : List Word} (hl : ws.length ≠ 1) :
    ∀ ψ : Pred, IniR ρ ini ψ ws := by
  intro ψ
  induction ψ with
  | ini k =>
      simp only [IniR]; intro a ha
      have := congrArg List.length ha; simp at this; exact absurd this hl
  | and p q ihp ihq => exact ⟨ihp, ihq⟩
  | _ => simp [IniR]

theorem push0_agree {η η' : TEnv} {s s' : Ty} {P : Nat → Prop} (h0 : P 0 → s = s')
    (h : ∀ j, P (j + 1) → η.wit j = η'.wit j ∧ η.rels j = η'.rels j ∧ η.urels j = η'.urels j) :
    ∀ j, P j → (η.push0 s).wit j = (η'.push0 s').wit j ∧ (η.push0 s).rels j = (η'.push0 s').rels j ∧
      (η.push0 s).urels j = (η'.push0 s').urels j
  | 0, hj => by rw [h0 hj]; simp [TEnv.push0, TEnv.ins, TEnv.insR]
  | j + 1, hj => by have := h j hj; simp [TEnv.push0, TEnv.ins, TEnv.insR, this.1, this.2.1, this.2.2]

theorem vcons_agree {ρ ρ' : Nat → Nat} {w w' : Nat} {P : Nat → Prop} (h0 : P 0 → w = w')
    (h : ∀ j, P (j + 1) → ρ j = ρ' j) : ∀ j, P j → vcons w ρ j = vcons w' ρ' j
  | 0, hj => by simp [vins, h0 hj]
  | j + 1, hj => by simp [vins, h j hj]

theorem CE_push0 (η : TEnv) (s : Ty) : CE (η.push0 s) = CE η := rfl

section
variable {η η' : TEnv} (h : CE η = CE η')
include h
theorem CEsto : η.sto = η'.sto := by have := congrArg TEnv.sto h; exact this
theorem CEprog : η.prog = η'.prog := by have := congrArg TEnv.prog h; exact this
theorem CEtid : η.tid = η'.tid := by have := congrArg TEnv.tid h; exact this
theorem CEini : η.ini = η'.ini := by have := congrArg TEnv.ini h; exact this
theorem CEpfr : η.pfr = η'.pfr := by have := congrArg TEnv.pfr h; exact this
theorem CEseen : η.seen = η'.seen := by have := congrArg TEnv.seen h; exact this
theorem CErini : η.rini = η'.rini := by have := congrArg TEnv.rini h; exact this
end

/-- (F2′ (a′)) The count an `ini` refinement reads agrees on views with the same
contents and the same witnesses for the mentioned type variables. -/
theorem selIni_CE {η η' : TEnv} (t : Ty) (hw : ∀ j, t.tyMentions j = true → η.wit j = η'.wit j)
    (hE : CE η = CE η') : η.selIni t = η'.selIni t := by
  have hi := CEini hE
  have hr : η.rini = η'.rini := by have := congrArg TEnv.rini hE; exact this
  have ho : η.ownTop t = η'.ownTop t := by
    cases t with
    | tvar k => exact congrArg Ty.ownHead (hw k (by simp [Ty.tyMentions]))
    | _ => rfl
  unfold TEnv.selIni; rw [ho, hi, hr]

theorem VR_congr : ∀ (t : Ty) (ρ ρ' : Nat → Nat) (η η' : TEnv) (rt : Shp) (ws : List Word),
    (∀ j, t.idxMentions j = true → ρ j = ρ' j) →
    (∀ j, t.tyMentions j = true → η.wit j = η'.wit j ∧ η.rels j = η'.rels j ∧ η.urels j = η'.urels j) →
    CE η = CE η' → VR ρ η t rt ws → VR ρ' η' t rt ws := by
  intro t
  induction t with
  | unit | void | int | fix | lanes | share | cap | word | tok | word2 | tok2 | epair | tokE | array =>
      intro ρ ρ' η η' rt ws hI hT hE h; exact h
  | tid =>
      intro ρ ρ' η η' rt ws hI hT hE h
      have e1 : η.sto = η'.sto := by have hh := congrArg TEnv.sto hE; exact hh
      have e2 : η.tid = η'.tid := by have hh := congrArg TEnv.tid hE; exact hh
      have e3 : η.seen = η'.seen := by have hh := congrArg TEnv.seen hE; exact hh
      have e4 : η.pfr = η'.pfr := by have hh := congrArg TEnv.pfr hE; exact hh
      simp only [VR, e1, e2, e3, e4] at h ⊢; exact h
  | iall b ih =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      exact fun n => ih (vcons n ρ) (vcons n ρ') η η' rt ws
        (vcons_agree (P := fun j => b.idxMentions j = true) (fun _ => rfl)
          (fun j hj => hI j (by simp [Ty.idxMentions, hj])))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE (h n)
  | intS i =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      rw [← ev_congr i (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | refine t ψ ih =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      exact ⟨ih ρ ρ' η η' rt ws (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h.1,
        IniR_congr (selIni_CE t (fun j hj => (hT j (by simp [Ty.tyMentions, hj])).1) hE) ψ (fun j hj => hI j (by simp [Ty.idxMentions, hj])) h.2⟩
  | iex b ih =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := h
      exact ⟨n, rb, w, hr, ih _ _ η η' rb ws
        (vcons_agree (P := fun j => b.idxMentions j = true) (fun _ => rfl)
          (fun j hj => hI j (by simp [Ty.idxMentions, hj])))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE hv⟩
  | prod a b iha ihb =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      obtain ⟨ra, rb, hr, hv⟩ := h
      refine ⟨ra, rb, hr, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hv n hn
      exact ⟨h1, iha ρ ρ' η η' _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h2,
        ihb ρ ρ' η η' _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h3⟩
  | sum a b iha ihb =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      obtain ⟨n, Ra, Rb, hr, hv⟩ := h
      refine ⟨n, Ra, Rb, hr, ?_⟩
      rcases hv with ⟨htr, x, s, B, hw, ho, hbx, hn, hs, hm, hA, hB⟩ | ⟨j, p, hd, h1, h2⟩
      · have ebox : η.box = η'.box := by have := congrArg TEnv.box hE; exact this
        have hEu : CE η.unsee = CE η'.unsee := by rw [← CE_unsee, ← CE_unsee, hE]
        have hIa := fun j (hj : a.idxMentions j = true) => hI j (by simp [Ty.idxMentions, hj])
        have hIb := fun j (hj : b.idxMentions j = true) => hI j (by simp [Ty.idxMentions, hj])
        have hTa := fun j (hj : a.tyMentions j = true) => hT j (by simp [Ty.tyMentions, hj])
        have hTb := fun j (hj : b.tyMentions j = true) => hT j (by simp [Ty.tyMentions, hj])
        refine Or.inl ⟨htr, x, s, B, hw, ho, by rw [← ebox]; exact hbx, hn, hs, by rw [← CEseen hE, ← CEpfr hE]; exact hm,
          fun hj => ⟨fun hb => iha ρ ρ' η η' _ _ hIa hTa hE ((hA hj).1 hb), fun hb => ?_⟩,
          fun hj => ⟨fun hb => ihb ρ ρ' η η' _ _ hIb hTb hE ((hB hj).1 hb), fun hb => ?_⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 hb
          exact ⟨q, hq, hs1, hw1, hv1, iha ρ ρ' η.unsee η'.unsee _ _ hIa
            (fun j hj => have h := hTa j hj; ⟨h.1, h.2.2, h.2.2⟩) hEu hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hB hj).2 hb
          exact ⟨q, hq, hs1, hw1, hv1, ihb ρ ρ' η.unsee η'.unsee _ _ hIb
            (fun j hj => have h := hTb j hj; ⟨h.1, h.2.2, h.2.2⟩) hEu hv⟩
      refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, hq, hv⟩ := h1 hj
        exact ⟨q, hq, iha ρ ρ' η η' _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE hv⟩
      · obtain ⟨q, hq, hv⟩ := h2 hj
        exact ⟨q, hq, ihb ρ ρ' η η' _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE hv⟩
  | tvar k =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR, TEnv.get] at h ⊢
      rw [← (hT k (by simp [Ty.tyMentions])).2.1]; exact h
  | code σ τ _ _ =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      have hp : η.prog = η'.prog := CEprog hE
      rw [cl_congr σ 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        cl_congr τ 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1), hp] at h
      exact h
  | ptr μ u _ =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE] at h
      exact h
  | ptrOpt μ u _ =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE] at h
      exact h
  | loc μ u _ =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE,
        CEini hE, CErini hE] at h
      exact h
  | tex κ b ih =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := h
      exact ⟨n, rb, s, hr, hs, haf, ih ρ ρ' _ _ rb ws (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (push0_agree (P := fun j => b.tyMentions j = true) (fun _ => rfl)
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])))
        (by rw [CE_push0, CE_push0]; exact hE) hv⟩
  | mu b ih =>
      intro ρ ρ' η η' rt ws hI hT hE h
      simp only [VR] at h ⊢
      have hc : cl ρ η.wit 0 0 (.mu b) = cl ρ' η'.wit 0 0 (.mu b) :=
        cl_congr _ 0 0 ρ ρ' _ _ (fun j hj => hI j (by simpa using hj))
          (fun j hj => (hT j (by simpa using hj)).1)
      rw [← hc]
      exact ih ρ ρ' _ _ rt ws (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (push0_agree (P := fun j => b.tyMentions j = true) (fun _ => rfl)
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])))
        (by rw [CE_push0, CE_push0]; exact hE) h

/-! ## Which variables each side of a split reads

`SI L k t j` (`L = true`: the words before `k`; `false`: from `k` on) — does the
part of `t` on that side read index variable `j`?  `ST` likewise for type
variables.  At `k = 0` everything is right; at or past the end, everything is
left.  Inside, a pair splits; `∀` reads nothing (`VR` is `True` there); and a
`μ`'s own variable, read on a side, reads everything the `μ` mentions. -/

def wn (t : Ty) : Nat := (wc t).getD 0

def edge (L : Bool) (k n : Nat) (m inner : Bool) : Bool :=
  if k = 0 then (!L && m) else if n ≤ k then (L && m) else inner

def ST (L : Bool) : Nat → Ty → Nat → Bool
  | k, .prod a b, j => edge L k (wn (.prod a b)) ((Ty.prod a b).tyMentions j)
      (if k ≤ wn a then ST L k a j || (!L && b.tyMentions j)
       else (L && a.tyMentions j) || ST L (k - wn a) b j)
  | k, .refine t ψ, j => edge L k (wn (.refine t ψ)) ((Ty.refine t ψ).tyMentions j) (ST L k t j)
  | k, .iex b, j => edge L k (wn (.iex b)) ((Ty.iex b).tyMentions j) (ST L k b j)
  | k, .tex κ b, j => edge L k (wn (.tex κ b)) ((Ty.tex κ b).tyMentions j) (ST L k b (j + 1))
  | k, .mu b, j => edge L k (wn (.mu b)) ((Ty.mu b).tyMentions j)
      (ST L k b (j + 1) || (b.tyMentions (j + 1) && ST L k b 0))
  | k, .iall b, j => edge L k (wn (.iall b)) ((Ty.iall b).tyMentions j) (ST L k b j)
  | k, t, j => edge L k (wn t) (t.tyMentions j) (L && t.tyMentions j)

def SI (L : Bool) : Nat → Ty → Nat → Bool
  | k, .prod a b, j => edge L k (wn (.prod a b)) ((Ty.prod a b).idxMentions j)
      (if k ≤ wn a then SI L k a j || (!L && b.idxMentions j)
       else (L && a.idxMentions j) || SI L (k - wn a) b j)
  | k, .refine t ψ, j => edge L k (wn (.refine t ψ)) ((Ty.refine t ψ).idxMentions j) (SI L k t j)
  | k, .iex b, j => edge L k (wn (.iex b)) ((Ty.iex b).idxMentions j) (SI L k b (j + 1))
  | k, .tex κ b, j => edge L k (wn (.tex κ b)) ((Ty.tex κ b).idxMentions j) (SI L k b j)
  | k, .mu b, j => edge L k (wn (.mu b)) ((Ty.mu b).idxMentions j)
      (SI L k b j || (b.idxMentions j && ST L k b 0))
  | k, .iall b, j => edge L k (wn (.iall b)) ((Ty.iall b).idxMentions j) (SI L k b (j + 1))
  | k, t, j => edge L k (wn t) (t.idxMentions j) (L && t.idxMentions j)

theorem ST_zero (L : Bool) (t : Ty) (j : Nat) : ST L 0 t j = (!L && t.tyMentions j) := by
  cases t <;> simp [ST, edge]
theorem SI_zero (L : Bool) (t : Ty) (j : Nat) : SI L 0 t j = (!L && t.idxMentions j) := by
  cases t <;> simp [SI, edge]
theorem ST_full {L : Bool} {t : Ty} {k : Nat} (j : Nat) (h0 : k ≠ 0) (hw : wn t ≤ k) :
    ST L k t j = (L && t.tyMentions j) := by
  cases t <;> simp [ST, edge, h0, hw]
theorem SI_full {L : Bool} {t : Ty} {k : Nat} (j : Nat) (h0 : k ≠ 0) (hw : wn t ≤ k) :
    SI L k t j = (L && t.idxMentions j) := by
  cases t <;> simp [SI, edge, h0, hw]

theorem countT_pos : ∀ (t : Ty) (j : Nat), t.tyMentions j = true → 1 ≤ t.countT j := by
  intro t
  induction t <;> intro j h
  case prod a b iha ihb =>
    simp only [Ty.tyMentions, Bool.or_eq_true] at h; simp only [Ty.countT]
    rcases h with h | h
    · have := iha j h; omega
    · have := ihb j h; omega
  case refine t ψ ih => exact ih j h
  case iall t ih => exact ih j h
  case iex t ih => exact ih j h
  case tex κ t ih => exact ih (j + 1) h
  case mu t ih => have := ih (j + 1) h; simp only [Ty.countT]; omega
  all_goals simp_all [Ty.countT]

theorem countI_pos : ∀ (t : Ty) (j : Nat), t.idxMentions j = true → 1 ≤ t.countI j := by
  intro t
  induction t <;> intro j h
  case prod a b iha ihb =>
    simp only [Ty.idxMentions, Bool.or_eq_true] at h; simp only [Ty.countI]
    rcases h with h | h
    · have := iha j h; omega
    · have := ihb j h; omega
  case refine t ψ ih =>
    simp only [Ty.idxMentions, Bool.or_eq_true] at h; simp only [Ty.countI]
    rcases h with h | h
    · have := ih j h; omega
    · simp [h]
  case iall t ih => exact ih (j + 1) h
  case iex t ih => exact ih (j + 1) h
  case tex κ t ih => exact ih j h
  case mu t ih => have := ih j h; simp only [Ty.countI]; omega
  all_goals simp_all [Ty.countI]

theorem edge_any {L : Bool} {k n : Nat} {m inner : Bool} (h : edge L k n m inner = true) :
    m = true ∨ (k ≠ 0 ∧ ¬ n ≤ k ∧ inner = true) := by
  unfold edge at h
  by_cases h0 : k = 0 <;> by_cases hw : n ≤ k <;> simp_all

theorem edge_TF {k n : Nat} {m m' i1 i2 : Bool} (h1 : edge true k n m i1 = true)
    (h2 : edge false k n m' i2 = true) : k ≠ 0 ∧ ¬ n ≤ k ∧ i1 = true ∧ i2 = true := by
  unfold edge at h1 h2
  by_cases h0 : k = 0 <;> by_cases hw : n ≤ k <;> simp_all

theorem ST_ment : ∀ (t : Ty) (L : Bool) (k j : Nat), ST L k t j = true → t.tyMentions j = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp only [Ty.tyMentions, Bool.or_eq_true]
    by_cases hk : k ≤ wn a <;> simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at h
    · rcases h with h | h
      · exact Or.inl (iha _ _ _ h)
      · exact Or.inr h.2
    · rcases h with h | h
      · exact Or.inl h.2
      · exact Or.inr (ihb _ _ _ h)
  | refine t ψ ih =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h
  | iex b ih =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h
  | tex κ b ih =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h
  | mu b ih =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h; simp only [Ty.tyMentions]
    rcases h with h | h
    · exact ih _ _ _ h
    · exact h.1
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp_all
  | iall b ih =>
    intro L k j h; simp only [ST] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h

theorem SI_ment : ∀ (t : Ty) (L : Bool) (k j : Nat), SI L k t j = true → t.idxMentions j = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp only [Ty.idxMentions, Bool.or_eq_true]
    by_cases hk : k ≤ wn a <;> simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true] at h
    · rcases h with h | h
      · exact Or.inl (iha _ _ _ h)
      · exact Or.inr h.2
    · rcases h with h | h
      · exact Or.inl h.2
      · exact Or.inr (ihb _ _ _ h)
  | refine t ψ ih =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp only [Ty.idxMentions, Bool.or_eq_true]; exact Or.inl (ih _ _ _ h)
  | iex b ih =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h
  | tex κ b ih =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h
  | mu b ih =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h; simp only [Ty.idxMentions]
    rcases h with h | h
    · exact ih _ _ _ h
    · exact h.1
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    simp_all
  | iall b ih =>
    intro L k j h; simp only [SI] at h; rcases edge_any h with hm | ⟨h0, hw, h⟩; · exact hm
    exact ih _ _ _ h

/-- **Both sides read a type variable only if two words mention it.** -/
theorem ST_two : ∀ (t : Ty) (k j : Nat), ST true k t j = true → ST false k t j = true →
    2 ≤ t.countT j := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp only [Ty.countT]
    by_cases hk : k ≤ wn a <;> simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or,
      and_true, true_and, false_and, or_false, false_or] at h1 h2
    · rcases h2 with h2 | h2
      · have := iha k j h1 h2; omega
      · have := countT_pos a j (ST_ment _ _ _ _ h1); have := countT_pos b j h2; omega
    · rcases h1 with h1 | h1
      · have := countT_pos a j h1; have := countT_pos b j (ST_ment _ _ _ _ h2); omega
      · have := ihb _ j h1 h2; omega
  | refine t ψ ih =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k j h1 h2
  | iex b ih =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k j h1 h2
  | tex κ b ih =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k (j + 1) h1 h2
  | mu b ih =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 h2
    simp only [Ty.countT]
    rcases h1 with h1 | ⟨m1, h1⟩ <;> rcases h2 with h2 | ⟨m2, h2⟩
    · have := ih k (j + 1) h1 h2; omega
    · have := countT_pos b (j + 1) (ST_ment _ _ _ _ h1); have := countT_pos b 0 (ST_ment _ _ _ _ h2)
      simp only [m2, ↓reduceIte]; omega
    · have := countT_pos b (j + 1) (ST_ment _ _ _ _ h2); have := countT_pos b 0 (ST_ment _ _ _ _ h1)
      simp only [m1, ↓reduceIte]; omega
    · have := ih k 0 h1 h2; simp only [m1, ↓reduceIte]; omega
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp_all
  | iall b ih =>
    intro k j h1 h2; simp only [ST] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k j h1 h2

theorem SI_two : ∀ (t : Ty) (k j : Nat), SI true k t j = true → SI false k t j = true →
    2 ≤ t.countI j := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp only [Ty.countI]
    by_cases hk : k ≤ wn a <;> simp only [hk, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_true, Bool.not_false, Bool.true_and, Bool.false_and, Bool.or_false, Bool.false_or,
      and_true, true_and, false_and, or_false, false_or] at h1 h2
    · rcases h2 with h2 | h2
      · have := iha k j h1 h2; omega
      · have := countI_pos a j (SI_ment _ _ _ _ h1); have := countI_pos b j h2; omega
    · rcases h1 with h1 | h1
      · have := countI_pos a j h1; have := countI_pos b j (SI_ment _ _ _ _ h2); omega
      · have := ihb _ j h1 h2; omega
  | refine t ψ ih =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    have := ih k j h1 h2; simp only [Ty.countI]; omega
  | iex b ih =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k (j + 1) h1 h2
  | tex κ b ih =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k j h1 h2
  | mu b ih =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 h2
    simp only [Ty.countI]
    rcases h1 with h1 | ⟨m1, h1⟩ <;> rcases h2 with h2 | ⟨m2, h2⟩
    · have := ih k j h1 h2; omega
    · have := countI_pos b j (SI_ment _ _ _ _ h1); have := countT_pos b 0 (ST_ment _ _ _ _ h2)
      simp only [m2, ↓reduceIte]; omega
    · have := countI_pos b j (SI_ment _ _ _ _ h2); have := countT_pos b 0 (ST_ment _ _ _ _ h1)
      simp only [m1, ↓reduceIte]; omega
    · have := ST_two b k 0 h1 h2; simp only [m1, ↓reduceIte]; omega
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    simp_all
  | iall b ih =>
    intro k j h1 h2; simp only [SI] at h1 h2; obtain ⟨h0, hw, h1, h2⟩ := edge_TF h1 h2
    exact ih k (j + 1) h1 h2

/-! ## The tear -/

theorem wn_of_accs {t : Ty} {us : List Acc} (hu : accs t = some us) : wn t = nWords us := by
  simp [wn, wc, hu]

theorem small_absurd {t : Ty} {us : List Acc} {k : Nat} (hu : accs t = some us) (hl : us.length ≤ 1)
    (hb : Bnd us k) (h0 : k ≠ 0) (hw : ¬ wn t ≤ k) : False := by
  rcases Bnd_small hl hb with h | h
  · exact h0 h
  · exact hw (by rw [wn_of_accs hu]; exact h)

/-- At an interior boundary an index package is not one access: it is
uncoupled, and laid out as its body. -/
theorem iex_int {ke : KEnv} {b : Ty} {us : List Acc} {k : Nat} (hok : Ty.coupledOKIn ke (.iex b) = true)
    (hu : accs (.iex b) = some us) (hb : Bnd us k) (h0 : k ≠ 0) (hk : ¬ wn (.iex b) ≤ k) :
    b.countI 0 < 2 ∧ accs b = some us := by
  by_cases hc : 2 ≤ b.countI 0
  · exfalso
    simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have hf : (Ty.iex b).fitsGranule = true := hok.2.resolve_left (by omega)
    have hf' : ((Ty.iex b).rawWords).any (· ≤ 2) = true := hf
    have hu' := hu
    simp only [accs] at hu'
    rw [if_pos (by omega)] at hu'
    cases hr : (Ty.iex b).rawWords with
    | none => rw [hr] at hf'; simp at hf'
    | some m =>
      rw [hr] at hf' hu'; simp at hf'
      have hl : us.length ≤ 1 := by
        rcases m with _ | _ | _ | m
        all_goals simp at hu'
        all_goals (try omega)
        all_goals (subst hu'; simp)
      exact small_absurd hu hl hb h0 hk
  · refine ⟨by omega, ?_⟩
    simp only [accs] at hu
    rwa [if_neg (by omega)] at hu

theorem tex_int {ke : KEnv} {κ : Kind} {b : Ty} {us : List Acc} {k : Nat}
    (hok : Ty.coupledOKIn ke (.tex κ b) = true)
    (hu : accs (.tex κ b) = some us) (hb : Bnd us k) (h0 : k ≠ 0) (hk : ¬ wn (.tex κ b) ≤ k) :
    b.countT 0 < 2 ∧ accs b = some us := by
  by_cases hc : 2 ≤ b.countT 0
  · exfalso
    simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have hf : (Ty.tex κ b).fitsGranule = true := hok.2.resolve_left (by omega)
    have hf' : ((Ty.tex κ b).rawWords).any (· ≤ 2) = true := hf
    have hu' := hu
    simp only [accs] at hu'
    rw [if_pos (by omega)] at hu'
    cases hr : (Ty.tex κ b).rawWords with
    | none => rw [hr] at hf'; simp at hf'
    | some m =>
      rw [hr] at hf' hu'; simp at hf'
      have hl : us.length ≤ 1 := by
        rcases m with _ | _ | _ | m
        all_goals simp at hu'
        all_goals (try omega)
        all_goals (subst hu'; simp)
      exact small_absurd hu hl hb h0 hk
  · refine ⟨by omega, ?_⟩
    simp only [accs] at hu
    rwa [if_neg (by omega)] at hu

/-- The boundary cases: everything is one side's value. -/
theorem tear_wrap {t : Ty} {k : Nat} {us : List Acc} {ρ1 ρ2 ρ : Nat → Nat} {η1 η2 η : TEnv}
    {ws1 ws2 : List Word} (hu : accs t = some us)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us)
    (hI1 : ∀ j, SI true k t j = true → ρ j = ρ1 j) (hI2 : ∀ j, SI false k t j = true → ρ j = ρ2 j)
    (hT1 : ∀ j, ST true k t j = true → η.wit j = η1.wit j ∧ η.rels j = η1.rels j ∧ η.urels j = η1.urels j)
    (hT2 : ∀ j, ST false k t j = true → η.wit j = η2.wit j ∧ η.rels j = η2.rels j ∧ η.urels j = η2.urels j)
    (hE1 : CE η = CE η1) (hE2 : CE η = CE η2)
    (h1 : VR ρ1 η1 t (shp t) ws1) (h2 : VR ρ2 η2 t (shp t) ws2)
    (hint : k ≠ 0 → ¬ wn t ≤ k → VR ρ η t (shp t) (splice k ws1 ws2)) :
    VR ρ η t (shp t) (splice k ws1 ws2) := by
  by_cases h0 : k = 0
  · subst h0
    rw [splice_zero]
    exact VR_congr t ρ2 ρ η2 η _ _ (fun j hj => (hI2 j (by rw [SI_zero]; simp [hj])).symm)
      (fun j hj => have h := hT2 j (by rw [ST_zero]; simp [hj]); ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩) hE2.symm h2
  by_cases hw : wn t ≤ k
  · rw [wn_of_accs hu] at hw
    rw [splice_full (by omega) (by omega)]
    exact VR_congr t ρ1 ρ η1 η _ _
      (fun j hj => (hI1 j (by rw [SI_full j h0 (by rw [wn_of_accs hu]; exact hw)]; simp [hj])).symm)
      (fun j hj => have h := hT1 j (by rw [ST_full j h0 (by rw [wn_of_accs hu]; exact hw)]; simp [hj])
        ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩) hE1.symm h1
  exact hint h0 hw

theorem SI_false_of_two {b : Ty} {k j : Nat} (hc : b.countI j < 2) (h : SI false k b j = true) :
    SI true k b j = false := by
  cases e : SI true k b j
  · rfl
  · have := SI_two b k j e h; omega

theorem ST_false_of_two {b : Ty} {k j : Nat} (hc : b.countT j < 2) (h : ST false k b j = true) :
    ST true k b j = false := by
  cases e : ST true k b j
  · rfl
  · have := ST_two b k j e h; omega

theorem tear_gen : ∀ (t : Ty) (ke : KEnv) (k : Nat) (us : List Acc) (ρ1 ρ2 ρ : Nat → Nat)
    (η1 η2 η : TEnv) (ws1 ws2 : List Word),
    Ty.coupledOKIn ke t = true → accs t = some us → Bnd us k →
    ws1.length = nWords us → ws2.length = nWords us →
    (∀ j, SI true k t j = true → ρ j = ρ1 j) → (∀ j, SI false k t j = true → ρ j = ρ2 j) →
    (∀ j, ST true k t j = true → η.wit j = η1.wit j ∧ η.rels j = η1.rels j ∧ η.urels j = η1.urels j) →
    (∀ j, ST false k t j = true → η.wit j = η2.wit j ∧ η.rels j = η2.rels j ∧ η.urels j = η2.urels j) →
    CE η = CE η1 → CE η = CE η2 →
    VR ρ1 η1 t (shp t) ws1 → VR ρ2 η2 t (shp t) ws2 → VR ρ η t (shp t) (splice k ws1 ws2) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    have hSI : ∀ L j, SI L k (.prod a b) j = (if k ≤ wn a then SI L k a j || (!L && b.idxMentions j)
        else (L && a.idxMentions j) || SI L (k - wn a) b j) := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.prod a b) j = (if k ≤ wn a then ST L k a j || (!L && b.tyMentions j)
        else (L && a.tyMentions j) || ST L (k - wn a) b j) := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok
    cases ha : accs a with
    | none => simp [accs, ha] at hu
    | some ua =>
    cases hb' : accs b with
    | none => simp [accs, ha, hb'] at hu
    | some ub =>
    have hus : us = ua ++ ub := by simp [accs, ha, hb'] at hu; exact hu.symm
    subst hus
    have hna : wn a = nWords ua := wn_of_accs ha
    have hlen1 := l1
    have hlen2 := l2
    rw [nWords_append] at hlen1 hlen2
    simp only [shp, VR] at h1 h2 ⊢
    obtain ⟨ra1, rb1, e1, h1⟩ := h1
    obtain ⟨ra2, rb2, e2, h2⟩ := h2
    cases e1; cases e2
    have hwa : (shp a).wc = some (nWords ua) := by rw [shp_wc]; simp [wc, ha]
    obtain ⟨_, h1a, h1b⟩ := h1 _ hwa
    obtain ⟨_, h2a, h2b⟩ := h2 _ hwa
    refine ⟨shp a, shp b, rfl, fun n hn => ?_⟩
    rw [hwa] at hn; cases hn
    have hlen := length_splice (k := k) l1 l2
    refine ⟨by omega, ?_⟩
    by_cases hk : k ≤ nWords ua
    · rw [take_splice_le hk (by omega), drop_splice_le hk (by omega)]
      refine ⟨?_, ?_⟩
      · exact iha ke k ua ρ1 ρ2 ρ η1 η2 η _ _ hok.1 ha (Bnd_left hb hk) (by simp; omega) (by simp; omega)
          (fun j hj => hI1 j (by rw [hSI]; simp [hna, hk, hj]))
          (fun j hj => hI2 j (by rw [hSI]; simp [hna, hk, hj]))
          (fun j hj => hT1 j (by rw [hST]; simp [hna, hk, hj]))
          (fun j hj => hT2 j (by rw [hST]; simp [hna, hk, hj])) hE1 hE2 h1a h2a
      · exact VR_congr b ρ2 ρ η2 η _ _ (fun j hj => (hI2 j (by rw [hSI]; simp [hna, hk, hj])).symm)
          (fun j hj => have h := hT2 j (by rw [hST]; simp [hna, hk, hj]); ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
          hE2.symm h2b
    · have hk' : nWords ua ≤ k := by omega
      rw [take_splice_ge hk' (by omega), drop_splice_ge hk' (by omega)]
      refine ⟨?_, ?_⟩
      · exact VR_congr a ρ1 ρ η1 η _ _ (fun j hj => (hI1 j (by rw [hSI]; simp [hna, hk, hj])).symm)
          (fun j hj => have h := hT1 j (by rw [hST]; simp [hna, hk, hj]); ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
          hE1.symm h1a
      · exact ihb ke (k - nWords ua) ub ρ1 ρ2 ρ η1 η2 η _ _ hok.2 hb' (Bnd_right hb (by omega))
          (by simp; omega) (by simp; omega)
          (fun j hj => hI1 j (by rw [hSI]; simp [hna, hk, hj]))
          (fun j hj => hI2 j (by rw [hSI]; simp [hna, hk, hj]))
          (fun j hj => hT1 j (by rw [hST]; simp [hna, hk, hj]))
          (fun j hj => hT2 j (by rw [hST]; simp [hna, hk, hj])) hE1 hE2 h1b h2b
  | iex b ih =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    obtain ⟨hcI, hub⟩ := iex_int hok hu hb h0 hw
    have hokb : Ty.coupledOKIn ke b = true := by
      simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok; exact hok.1
    have hSI : ∀ L j, SI L k (.iex b) j = SI L k b (j + 1) := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.iex b) j = ST L k b j := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    simp only [shp, VR] at h1 h2 ⊢
    obtain ⟨n1, rb1, w1, e1, h1⟩ := h1
    obtain ⟨n2, rb2, w2, e2, h2⟩ := h2
    cases e1; cases e2
    refine ⟨_, _, if SI true k b 0 then w1 else w2, rfl, ?_⟩
    exact ih ke k us _ _ _ η1 η2 η ws1 ws2 hokb hub hb l1 l2
      (vcons_agree (P := fun j => SI true k b j = true) (fun h => by simp [h])
        (fun j hj => hI1 j (by rw [hSI]; exact hj)))
      (vcons_agree (P := fun j => SI false k b j = true)
        (fun h => by simp [SI_false_of_two hcI h])
        (fun j hj => hI2 j (by rw [hSI]; exact hj)))
      (fun j hj => hT1 j (by rw [hST]; exact hj)) (fun j hj => hT2 j (by rw [hST]; exact hj))
      hE1 hE2 h1 h2
  | tex κ b ih =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    obtain ⟨hcT, hub⟩ := tex_int hok hu hb h0 hw
    have hokb : Ty.coupledOKIn (some κ :: ke) b = true := by
      simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok; exact hok.1
    have hSI : ∀ L j, SI L k (.tex κ b) j = SI L k b j := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.tex κ b) j = ST L k b (j + 1) := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    simp only [shp, VR] at h1 h2 ⊢
    obtain ⟨n1, rb1, s1, e1, hs1, ha1, h1⟩ := h1
    obtain ⟨n2, rb2, s2, e2, hs2, ha2, h2⟩ := h2
    cases e1; cases e2
    refine ⟨_, _, if ST true k b 0 then s1 else s2, rfl, by split <;> assumption,
      by split <;> assumption, ?_⟩
    exact ih (some κ :: ke) k us ρ1 ρ2 ρ _ _ _ ws1 ws2 hokb hub hb l1 l2
      (fun j hj => hI1 j (by rw [hSI]; exact hj)) (fun j hj => hI2 j (by rw [hSI]; exact hj))
      (push0_agree (P := fun j => ST true k b j = true) (fun h => by simp [h])
        (fun j hj => hT1 j (by rw [hST]; exact hj)))
      (push0_agree (P := fun j => ST false k b j = true)
        (fun h => by simp [ST_false_of_two hcT h])
        (fun j hj => hT2 j (by rw [hST]; exact hj)))
      (by rw [CE_push0, CE_push0]; exact hE1) (by rw [CE_push0, CE_push0]; exact hE2) h1 h2
  | mu b ih =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    have hub : accs b = some us := by simpa [accs] using hu
    have hokb : Ty.coupledOKIn (none :: ke) b = true := by simpa [Ty.coupledOKIn] using hok
    have hSI : ∀ L j, SI L k (.mu b) j = (SI L k b j || (b.idxMentions j && ST L k b 0)) := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.mu b) j =
        (ST L k b (j + 1) || (b.tyMentions (j + 1) && ST L k b 0)) := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    simp only [shp, VR] at h1 h2 ⊢
    exact ih (none :: ke) k us ρ1 ρ2 ρ _ _ _ ws1 ws2 hokb hub hb l1 l2
      (fun j hj => hI1 j (by rw [hSI]; simp [hj])) (fun j hj => hI2 j (by rw [hSI]; simp [hj]))
      (push0_agree (P := fun j => ST true k b j = true)
        (fun h0' => cl_congr _ 0 0 _ _ _ _
          (fun j hj => hI1 j (by
            simp only [Ty.idxMentions, Nat.add_zero] at hj; rw [hSI]; simp [hj, h0']))
          (fun j hj => (hT1 j (by
            simp only [Ty.tyMentions, Nat.add_zero] at hj; rw [hST]; simp [hj, h0'])).1))
        (fun j hj => hT1 j (by rw [hST]; simp [hj])))
      (push0_agree (P := fun j => ST false k b j = true)
        (fun h0' => cl_congr _ 0 0 _ _ _ _
          (fun j hj => hI2 j (by
            simp only [Ty.idxMentions, Nat.add_zero] at hj; rw [hSI]; simp [hj, h0']))
          (fun j hj => (hT2 j (by
            simp only [Ty.tyMentions, Nat.add_zero] at hj; rw [hST]; simp [hj, h0'])).1))
        (fun j hj => hT2 j (by rw [hST]; simp [hj])))
      (by rw [CE_push0, CE_push0]; exact hE1) (by rw [CE_push0, CE_push0]; exact hE2) h1 h2
  | refine t ψ ih =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    have hub : accs t = some us := by simpa [accs] using hu
    have hokt : Ty.coupledOKIn ke t = true := by simpa [Ty.coupledOKIn] using hok
    have hSI : ∀ L j, SI L k (.refine t ψ) j = SI L k t j := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.refine t ψ) j = ST L k t j := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    have hwn := wn_of_accs hu
    simp only [shp, VR] at h1 h2 ⊢
    refine ⟨ih ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hokt hub hb l1 l2
      (fun j hj => hI1 j (by rw [hSI]; exact hj)) (fun j hj => hI2 j (by rw [hSI]; exact hj))
      (fun j hj => hT1 j (by rw [hST]; exact hj)) (fun j hj => hT2 j (by rw [hST]; exact hj))
      hE1 hE2 h1.1 h2.1, IniR_short ?_ ψ⟩
    rw [length_splice l1 l2]; omega
  | iall b ih =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    have hub : accs b = some us := by simpa [accs] using hu
    have hokb : Ty.coupledOKIn ke b = true := by simpa [Ty.coupledOKIn] using hok
    have hSI : ∀ L j, SI L k (.iall b) j = SI L k b (j + 1) := by
      intro L j; simp only [SI, edge, h0, hw, if_false]
    have hST : ∀ L j, ST L k (.iall b) j = ST L k b j := by
      intro L j; simp only [ST, edge, h0, hw, if_false]
    simp only [shp, VR] at h1 h2 ⊢
    intro n
    exact ih ke k us _ _ _ η1 η2 η ws1 ws2 hokb hub hb l1 l2
      (vcons_agree (P := fun j => SI true k b j = true) (fun _ => rfl)
        (fun j hj => hI1 j (by rw [hSI]; exact hj)))
      (vcons_agree (P := fun j => SI false k b j = true) (fun _ => rfl)
        (fun j hj => hI2 j (by rw [hSI]; exact hj)))
      (fun j hj => hT1 j (by rw [hST]; exact hj)) (fun j hj => hT2 j (by rw [hST]; exact hj))
      hE1 hE2 (h1 n) (h2 n)
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro ke k us ρ1 ρ2 ρ η1 η2 η ws1 ws2 hok hu hb l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2
    refine tear_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun h0 hw => ?_)
    exfalso
    refine small_absurd hu ?_ hb h0 hw
    simp only [accs] at hu
    (try split at hu) <;> (first | (cases hu; simp) | simp at hu)

/-- **The tear lemma.**  Splicing two values of a `coupledOK` type at a unit
boundary of its layout gives a value. -/
theorem VR_tear {ρ : Nat → Nat} {η : TEnv} {T : Ty} {us : List Acc} {k : Nat} {ws1 ws2 : List Word}
    (hc : Ty.coupledOKIn [] T = true) (hu : accs T = some us) (hb : Bnd us k)
    (h1 : VR ρ η T (shp T) ws1) (h2 : VR ρ η T (shp T) ws2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    VR ρ η T (shp T) (splice k ws1 ws2) :=
  tear_gen T [] k us ρ ρ ρ η η η ws1 ws2 hc hu hb l1 l2 (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) rfl rfl h1 h2

/-- The tear lemma at any kind environment (`coupledOKIn ke`). -/
theorem VR_tearIn {ke : KEnv} {ρ : Nat → Nat} {η : TEnv} {T : Ty} {us : List Acc} {k : Nat}
    {ws1 ws2 : List Word}
    (hc : Ty.coupledOKIn ke T = true) (hu : accs T = some us) (hb : Bnd us k)
    (h1 : VR ρ η T (shp T) ws1) (h2 : VR ρ η T (shp T) ws2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    VR ρ η T (shp T) (splice k ws1 ws2) :=
  tear_gen T ke k us ρ ρ ρ η η η ws1 ws2 hc hu hb l1 l2 (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) rfl rfl h1 h2

/-! ## `Valid` tears too (it reads no witnesses; no `coupledOK` needed) -/

theorem iex_accs {b : Ty} {us : List Acc} (hu : accs (.iex b) = some us) :
    us.length ≤ 1 ∨ accs b = some us := by
  simp only [accs] at hu
  split at hu
  · split at hu
    · cases hu; simp
    · cases hu; simp
    · cases hu; simp
    · exact Or.inr hu
  · exact Or.inr hu

theorem tex_accs {κ : Kind} {b : Ty} {us : List Acc} (hu : accs (.tex κ b) = some us) :
    us.length ≤ 1 ∨ accs b = some us := by
  simp only [accs] at hu
  split at hu
  · split at hu
    · cases hu; simp
    · cases hu; simp
    · cases hu; simp
    · exact Or.inr hu
  · exact Or.inr hu

theorem Valid_wrap {t : Ty} {k : Nat} {us : List Acc} {ws1 ws2 : List Word}
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us)
    (h1 : Valid t ws1) (h2 : Valid t ws2)
    (hint : k ≠ 0 → ¬ nWords us ≤ k → Valid t (splice k ws1 ws2)) : Valid t (splice k ws1 ws2) := by
  by_cases h0 : k = 0
  · subst h0; rw [splice_zero]; exact h2
  by_cases hw : nWords us ≤ k
  · rw [splice_full (by omega) (by omega)]; exact h1
  exact hint h0 hw

theorem Valid_gen : ∀ (t : Ty) (k : Nat) (us : List Acc) (ws1 ws2 : List Word),
    accs t = some us → Bnd us k → ws1.length = nWords us → ws2.length = nWords us →
    Valid t ws1 → Valid t ws2 → Valid t (splice k ws1 ws2) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    refine Valid_wrap l1 l2 h1 h2 (fun h0 hw => ?_)
    cases ha : accs a with
    | none => simp [accs, ha] at hu
    | some ua =>
    cases hb' : accs b with
    | none => simp [accs, ha, hb'] at hu
    | some ub =>
    have hus : us = ua ++ ub := by simp [accs, ha, hb'] at hu; exact hu.symm
    subst hus
    have hlen1 := l1
    have hlen2 := l2
    rw [nWords_append] at hlen1 hlen2
    have hwa : wc a = some (nWords ua) := by simp [wc, ha]
    simp only [Valid] at h1 h2 ⊢
    obtain ⟨h1a, h1b⟩ := h1 _ hwa
    obtain ⟨h2a, h2b⟩ := h2 _ hwa
    intro n hn
    rw [hwa] at hn; cases hn
    by_cases hk : k ≤ nWords ua
    · rw [take_splice_le hk (by omega), drop_splice_le hk (by omega)]
      exact ⟨iha k ua _ _ ha (Bnd_left hb hk) (by simp; omega) (by simp; omega) h1a h2a, h2b⟩
    · have hk' : nWords ua ≤ k := by omega
      rw [take_splice_ge hk' (by omega), drop_splice_ge hk' (by omega)]
      exact ⟨h1a, ihb (k - nWords ua) ub _ _ hb' (Bnd_right hb (by omega))
        (by simp; omega) (by simp; omega) h1b h2b⟩
  | iex b ih =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    refine Valid_wrap l1 l2 h1 h2 (fun h0 hw => ?_)
    rcases iex_accs hu with hl | hub
    · rcases Bnd_small hl hb with h | h <;> omega
    · exact ih k us ws1 ws2 hub hb l1 l2 h1 h2
  | tex κ b ih =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    refine Valid_wrap l1 l2 h1 h2 (fun h0 hw => ?_)
    rcases tex_accs hu with hl | hub
    · rcases Bnd_small hl hb with h | h <;> omega
    · exact ih k us ws1 ws2 hub hb l1 l2 h1 h2
  | mu b ih =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    exact ih k us ws1 ws2 (by simpa [accs] using hu) hb l1 l2 h1 h2
  | iall b ih =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    exact ih k us ws1 ws2 (by simpa [accs] using hu) hb l1 l2 h1 h2
  | refine b ψ ih =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    exact ih k us ws1 ws2 (by simpa [accs] using hu) hb l1 l2 h1 h2
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro k us ws1 ws2 hu hb l1 l2 h1 h2
    refine Valid_wrap l1 l2 h1 h2 (fun h0 hw => ?_)
    exfalso
    have hl : us.length ≤ 1 := by
      simp only [accs] at hu
      (try split at hu) <;> (first | (cases hu; simp) | simp at hu)
    rcases Bnd_small hl hb with h | h <;> omega

theorem Valid_tear {T : Ty} {us : List Acc} {k : Nat} {ws1 ws2 : List Word}
    (hu : accs T = some us) (hb : Bnd us k) (h1 : Valid T ws1) (h2 : Valid T ws2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    Valid T (splice k ws1 ws2) :=
  Valid_gen T k us ws1 ws2 hu hb l1 l2 h1 h2

/-! ## Assembling a torn read from per-unit values -/

theorem splice_length {k : Nat} {ws1 ws2 : List Word} (h : ws1.length = ws2.length) :
    (splice k ws1 ws2).length = ws2.length := by
  simp only [splice, List.length_append, List.length_take, List.length_drop]
  omega

theorem splice_get_lt {k j : Nat} {ws1 ws2 : List Word} (hj : j < k) (hl : k ≤ ws1.length) :
    (splice k ws1 ws2)[j]? = ws1[j]? := by
  simp only [splice]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hj]

theorem splice_get_ge {k j : Nat} {ws1 ws2 : List Word} (hj : k ≤ j) (hl : k ≤ ws1.length) :
    (splice k ws1 ws2)[j]? = ws2[j]? := by
  simp only [splice]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_drop]
  congr 1; omega

/-- Words related pointwise below a bound. -/
def WLeB (n : Nat) (v r : List Word) : Prop :=
  ∀ j x y, j < n → v[j]? = some x → r[j]? = some y → WLe1 x y

theorem WLe_of_WLeB : ∀ {v r : List Word}, v.length = r.length → WLeB v.length v r → WLe v r
  | [], [], _, _ => trivial
  | x :: v, y :: r, hl, h => by
      refine ⟨h 0 x y (by simp) rfl rfl, WLe_of_WLeB (by simpa using hl) fun j x' y' hj h1 h2 => ?_⟩
      exact h (j + 1) x' y' (by simp; omega) (by simpa using h1) (by simpa using h2)
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- **Assembling a torn read.**  If `P` (a set of values, all `nWords us`
long) is closed under splicing at unit boundaries, and each unit of `r` is
dominated by the same unit of some value, then `r` dominates a value. -/
theorem assemble {P : List Word → Prop} {us : List Acc}
    (htear : ∀ k ws1 ws2, Bnd us k → P ws1 → P ws2 → P (splice k ws1 ws2))
    (hlen : ∀ ws, P ws → ws.length = nWords us)
    (r : List Word) (hr : r.length = nWords us)
    (hunit : ∀ i, i < us.length → ∃ ws, P ws ∧ ∀ j x y, nWords (us.take i) ≤ j → j < nWords (us.take (i + 1)) →
      ws[j]? = some x → r[j]? = some y → WLe1 x y)
    (h0 : ∃ ws, P ws) : ∃ vals, P vals ∧ WLe vals r := by
  have claim : ∀ i, i ≤ us.length → ∃ v, P v ∧ WLeB (nWords (us.take i)) v r := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨v, hv⟩ := h0
      exact ⟨v, hv, fun j _ _ hj => by simp [nWords] at hj⟩
    | succ i ih =>
      intro hi
      obtain ⟨v, hv, hb⟩ := ih (by omega)
      obtain ⟨ws, hws, hu⟩ := hunit i (by omega)
      have hlv := hlen v hv
      have hp : nWords (us.take i) ≤ v.length := by rw [hlv]; exact nWords_take_le us i
      refine ⟨splice (nWords (us.take i)) v ws, htear _ v ws ⟨i, rfl⟩ hv hws, fun j x y hj h1 h2 => ?_⟩
      by_cases hji : j < nWords (us.take i)
      · rw [splice_get_lt hji hp] at h1
        exact hb j x y hji h1 h2
      · rw [splice_get_ge (by omega) hp] at h1
        exact hu j x y (by omega) hj h1 h2
  obtain ⟨v, hv, hb⟩ := claim us.length (Nat.le_refl _)
  refine ⟨v, hv, WLe_of_WLeB (by rw [hlen v hv, hr]) ?_⟩
  rw [hlen v hv]
  simpa using hb

/-! ## `VRR` reads only mentioned variables -/

theorem push0_agreeR {η η' : TEnv} {s s' : Ty} {P : Nat → Prop} (h0 : P 0 → s = s')
    (h : ∀ j, P (j + 1) → η.wit j = η'.wit j ∧ η.rrs j = η'.rrs j ∧ η.urrs j = η'.urrs j) :
    ∀ j, P j → (η.push0 s).wit j = (η'.push0 s').wit j ∧ (η.push0 s).rrs j = (η'.push0 s').rrs j ∧
      (η.push0 s).urrs j = (η'.push0 s').urrs j
  | 0, hj => by rw [h0 hj]; simp [TEnv.push0, TEnv.ins, TEnv.insR]
  | j + 1, hj => by have := h j hj; simp [TEnv.push0, TEnv.ins, TEnv.insR, this.1, this.2.1, this.2.2]

theorem VRR_congr : ∀ (t : Ty) (ρ ρ' : Nat → Nat) (η η' : TEnv) (rt : Shp) (ws : List Word) (R : Res),
    (∀ j, t.idxMentions j = true → ρ j = ρ' j) →
    (∀ j, t.tyMentions j = true → η.wit j = η'.wit j ∧ η.rrs j = η'.rrs j ∧ η.urrs j = η'.urrs j) →
    CE η = CE η' → VRR ρ η t rt ws R → VRR ρ' η' t rt ws R := by
  intro t
  induction t with
  | unit | void | int | fix | lanes | cap | epair | array =>
      intro ρ ρ' η η' rt ws R hI hT hE h; exact h
  | tid =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      have e1 : η.sto = η'.sto := by have hh := congrArg TEnv.sto hE; exact hh
      have e2 : η.tid = η'.tid := by have hh := congrArg TEnv.tid hE; exact hh
      have e3 : η.seen = η'.seen := by have hh := congrArg TEnv.seen hE; exact hh
      have e4 : η.pfr = η'.pfr := by have hh := congrArg TEnv.pfr hE; exact hh
      simp only [VRR, VR, e1, e2, e3, e4] at h ⊢; exact h
  | word r P =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | word2 r P =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | tok r st =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | tok2 r P i k =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | share r =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | tokE r P e =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr r (fun j hj => hI j (by simp [Ty.idxMentions, hj])),
        ← ev_congr e (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | iall b ih =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      exact fun n => ih (vcons n ρ) (vcons n ρ') η η' rt ws R
        (vcons_agree (P := fun j => b.idxMentions j = true) (fun _ => rfl)
          (fun j hj => hI j (by simp [Ty.idxMentions, hj])))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE (h n)
  | intS i =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← ev_congr i (fun j hj => hI j (by simp [Ty.idxMentions, hj]))]; exact h
  | refine t ψ ih =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      exact ⟨ih ρ ρ' η η' rt ws R (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h.1,
        IniR_congr (selIni_CE t (fun j hj => (hT j (by simp [Ty.tyMentions, hj])).1) hE) ψ (fun j hj => hI j (by simp [Ty.idxMentions, hj])) h.2⟩
  | iex b ih =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      obtain ⟨n, rb, w, hr, hv⟩ := h
      exact ⟨n, rb, w, hr, ih _ _ η η' rb ws R
        (vcons_agree (P := fun j => b.idxMentions j = true) (fun _ => rfl)
          (fun j hj => hI j (by simp [Ty.idxMentions, hj])))
        (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE hv⟩
  | prod a b iha ihb =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      obtain ⟨ra, rb, hr, Ra, Rb, hR, hz, hv⟩ := h
      refine ⟨ra, rb, hr, Ra, Rb, hR, hz, fun n hn => ?_⟩
      obtain ⟨h1, h2, h3⟩ := hv n hn
      exact ⟨h1, iha ρ ρ' η η' _ _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h2,
        ihb ρ ρ' η η' _ _ _ (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])) hE h3⟩
  | sum a b iha ihb =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      obtain ⟨n, Ra, Rb, hr, hv⟩ := h
      refine ⟨n, Ra, Rb, hr, ?_⟩
      have hIa := fun j (hj : a.idxMentions j = true) => hI j (by simp [Ty.idxMentions, hj])
      have hIb := fun j (hj : b.idxMentions j = true) => hI j (by simp [Ty.idxMentions, hj])
      have hTa := fun j (hj : a.tyMentions j = true) => hT j (by simp [Ty.tyMentions, hj])
      have hTb := fun j (hj : b.tyMentions j = true) => hT j (by simp [Ty.tyMentions, hj])
      rcases hv with ⟨htr, x, s, B, hw, ho, hbx, hn, hs, hm, hA, hB⟩ | ⟨j, p, hd, h1, h2⟩
      · have ebox : η.box = η'.box := by have := congrArg TEnv.box hE; exact this
        have hEu : CE η.unsee = CE η'.unsee := by rw [← CE_unsee, ← CE_unsee, hE]
        refine Or.inl ⟨htr, x, s, B, hw, ho, by rw [← ebox]; exact hbx, hn, hs,
          by rw [← CEseen hE, ← CEpfr hE]; exact hm,
          fun hj => ⟨fun hb => iha ρ ρ' η η' _ _ _ hIa hTa hE ((hA hj).1 hb), fun hb => ?_⟩,
          fun hj => ⟨fun hb => ihb ρ ρ' η η' _ _ _ hIb hTb hE ((hB hj).1 hb), fun hb => ?_⟩⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 hb
          exact ⟨q, hq, hs1, hw1, hv1, iha ρ ρ' η.unsee η'.unsee _ _ _ hIa
            (fun j hj => have h := hTa j hj; ⟨h.1, h.2.2, h.2.2⟩) hEu hv⟩
        · obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hB hj).2 hb
          exact ⟨q, hq, hs1, hw1, hv1, ihb ρ ρ' η.unsee η'.unsee _ _ _ hIb
            (fun j hj => have h := hTb j hj; ⟨h.1, h.2.2, h.2.2⟩) hEu hv⟩
      refine Or.inr ⟨j, p, hd, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, hq, hv⟩ := h1 hj
        exact ⟨q, hq, iha ρ ρ' η η' _ _ _ hIa hTa hE hv⟩
      · obtain ⟨q, hq, hv⟩ := h2 hj
        exact ⟨q, hq, ihb ρ ρ' η η' _ _ _ hIb hTb hE hv⟩
  | tvar k =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [← (hT k (by simp [Ty.tyMentions])).2.1]; exact h
  | code σ τ _ _ =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      have hp : η.prog = η'.prog := CEprog hE
      rw [cl_congr σ 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        cl_congr τ 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1), hp] at h
      exact h
  | ptr μ u _ =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE] at h
      exact h
  | ptrOpt μ u _ =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE] at h
      exact h
  | loc μ u _ =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      rw [cl_congr u 0 0 ρ ρ' η.wit η'.wit (fun j hj => hI j (by simp at hj; simp [Ty.idxMentions, hj]))
          (fun j hj => (hT j (by simp at hj; simp [Ty.tyMentions, hj])).1),
        CEsto hE, CEtid hE, CEpfr hE, CEseen hE, CEini hE, CErini hE] at h
      exact h
  | tex κ b ih =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      obtain ⟨n, rb, s, hr, hs, haf, hv⟩ := h
      exact ⟨n, rb, s, hr, hs, haf, ih ρ ρ' _ _ rb ws R (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (push0_agreeR (P := fun j => b.tyMentions j = true) (fun _ => rfl)
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])))
        (by rw [CE_push0, CE_push0]; exact hE) hv⟩
  | mu b ih =>
      intro ρ ρ' η η' rt ws R hI hT hE h
      simp only [VRR] at h ⊢
      have hc : cl ρ η.wit 0 0 (.mu b) = cl ρ' η'.wit 0 0 (.mu b) :=
        cl_congr _ 0 0 ρ ρ' _ _ (fun j hj => hI j (by simpa using hj))
          (fun j hj => (hT j (by simpa using hj)).1)
      rw [← hc]
      exact ih ρ ρ' _ _ rt ws R (fun j hj => hI j (by simp [Ty.idxMentions, hj]))
        (push0_agreeR (P := fun j => b.tyMentions j = true) (fun _ => rfl)
          (fun j hj => hT j (by simp [Ty.tyMentions, hj])))
        (by rw [CE_push0, CE_push0]; exact hE) h

/-! ## Unit-selection mixes -/

/-- Take each access unit of `us` from `ws1` (where `sel` says `true`) or `ws2`. -/
def mixU : List Acc → (Nat → Bool) → List Word → List Word → List Word
  | [], _, _, _ => []
  | u :: us, sel, ws1, ws2 => (if sel 0 then ws1.take u.size else ws2.take u.size) ++
      mixU us (fun i => sel (i + 1)) (ws1.drop u.size) (ws2.drop u.size)

theorem nWords_nil : nWords [] = 0 := rfl
theorem nWords_cons (u : Acc) (us : List Acc) : nWords (u :: us) = u.size + nWords us := by
  simp [nWords]

theorem Acc_size_pos (u : Acc) : 1 ≤ u.size := by cases u <;> simp [Acc.size]

theorem length_le_nWords : ∀ us : List Acc, us.length ≤ nWords us
  | [] => by simp [nWords]
  | u :: us => by rw [nWords_cons]; have := Acc_size_pos u; have := length_le_nWords us; simp; omega

theorem length_mixU : ∀ (us : List Acc) (sel : Nat → Bool) (ws1 ws2 : List Word),
    ws1.length = nWords us → ws2.length = nWords us → (mixU us sel ws1 ws2).length = nWords us
  | [], _, _, _, _, _ => rfl
  | u :: us, sel, ws1, ws2, l1, l2 => by
      rw [nWords_cons] at l1 l2
      simp only [mixU, List.length_append]
      rw [length_mixU us _ _ _ (by simp; omega) (by simp; omega), nWords_cons]
      split <;> simp <;> omega

theorem mixU_append : ∀ (ua ub : List Acc) (sel : Nat → Bool) (ws1 ws2 : List Word),
    nWords ua ≤ ws1.length → nWords ua ≤ ws2.length →
    mixU (ua ++ ub) sel ws1 ws2 = mixU ua sel (ws1.take (nWords ua)) (ws2.take (nWords ua)) ++
      mixU ub (fun i => sel (i + ua.length)) (ws1.drop (nWords ua)) (ws2.drop (nWords ua))
  | [], ub, sel, ws1, ws2, _, _ => by simp [mixU, nWords]
  | u :: ua, ub, sel, ws1, ws2, l1, l2 => by
      rw [nWords_cons] at l1 l2
      simp only [List.cons_append, mixU]
      rw [mixU_append ua ub _ _ _ (by simp; omega) (by simp; omega)]
      rw [nWords_cons]
      have e1 : ∀ ws : List Word, (ws.take (u.size + nWords ua)).take u.size = ws.take u.size := by
        intro ws; rw [List.take_take]; congr 1; omega
      have e2 : ∀ ws : List Word, (ws.take (u.size + nWords ua)).drop u.size =
          (ws.drop u.size).take (nWords ua) := by
        intro ws; rw [List.drop_take]; congr 1; omega
      have e3 : ∀ ws : List Word, (ws.drop u.size).drop (nWords ua) = ws.drop (u.size + nWords ua) := by
        intro ws; rw [List.drop_drop]
      have e4 : (fun i => sel (i + ua.length + 1)) = (fun i => sel (i + (u :: ua).length)) := by
        funext i; simp only [List.length_cons]; congr 1
      simp only [e1, e2, e3, List.append_assoc]
      rw [← e4]

theorem mixU_small {us : List Acc} {sel : Nat → Bool} {ws1 ws2 : List Word} (hl : us.length ≤ 1)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    mixU us sel ws1 ws2 = if sel 0 then ws1 else ws2 := by
  match us, hl with
  | [], _ =>
      rw [List.eq_nil_of_length_eq_zero l1, List.eq_nil_of_length_eq_zero l2]; simp [mixU]
  | [u], _ =>
      rw [nWords_cons, nWords_nil] at l1 l2
      simp only [mixU, List.append_nil]
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

theorem mixU_const : ∀ (us : List Acc) (c : Bool) (ws1 ws2 : List Word),
    ws1.length = nWords us → ws2.length = nWords us →
    mixU us (fun _ => c) ws1 ws2 = if c then ws1 else ws2
  | [], c, ws1, ws2, l1, l2 => by
      rw [List.eq_nil_of_length_eq_zero l1, List.eq_nil_of_length_eq_zero l2]; simp [mixU]
  | u :: us, c, ws1, ws2, l1, l2 => by
      rw [nWords_cons] at l1 l2
      simp only [mixU]
      rw [mixU_const us c _ _ (by simp; omega) (by simp; omega)]
      cases c <;> simp

/-! ## Which variables each side of a selection reads

`MT L sel t j`: does a part of `t` lying in a unit that `sel` assigns to side
`L` read type variable `j`?  `MI` likewise for index variables.  A type of at
most one unit is read wholesale from side `sel 0`; otherwise the predicates
follow `accs`: a pair splits its units (the right part's selection shifted by
the left part's unit count), wrappers pass through, and a `μ`'s own variable,
read on a side, reads everything the `μ` mentions. -/

/-- The number of access units of `t`. -/
def nU (t : Ty) : Nat := ((accs t).getD []).length

def edgeU (L : Bool) (sel : Nat → Bool) (n : Nat) (m inner : Bool) : Bool :=
  if n ≤ 1 then (sel 0 == L) && m else inner

def MT (L : Bool) : (Nat → Bool) → Ty → Nat → Bool
  | sel, .prod a b, j => edgeU L sel (nU (.prod a b)) ((Ty.prod a b).tyMentions j)
      (MT L sel a j || MT L (fun i => sel (i + nU a)) b j)
  | sel, .refine t ψ, j => edgeU L sel (nU (.refine t ψ)) ((Ty.refine t ψ).tyMentions j) (MT L sel t j)
  | sel, .iex b, j => edgeU L sel (nU (.iex b)) ((Ty.iex b).tyMentions j) (MT L sel b j)
  | sel, .tex κ b, j => edgeU L sel (nU (.tex κ b)) ((Ty.tex κ b).tyMentions j) (MT L sel b (j + 1))
  | sel, .mu b, j => edgeU L sel (nU (.mu b)) ((Ty.mu b).tyMentions j)
      (MT L sel b (j + 1) || (b.tyMentions (j + 1) && MT L sel b 0))
  | sel, .iall b, j => edgeU L sel (nU (.iall b)) ((Ty.iall b).tyMentions j) (MT L sel b j)
  | sel, t, j => edgeU L sel (nU t) (t.tyMentions j) ((sel 0 == L) && t.tyMentions j)

def MI (L : Bool) : (Nat → Bool) → Ty → Nat → Bool
  | sel, .prod a b, j => edgeU L sel (nU (.prod a b)) ((Ty.prod a b).idxMentions j)
      (MI L sel a j || MI L (fun i => sel (i + nU a)) b j)
  | sel, .refine t ψ, j => edgeU L sel (nU (.refine t ψ)) ((Ty.refine t ψ).idxMentions j)
      (MI L sel t j || ((sel 0 == L) && ψ.mentions j))
  | sel, .iex b, j => edgeU L sel (nU (.iex b)) ((Ty.iex b).idxMentions j) (MI L sel b (j + 1))
  | sel, .tex κ b, j => edgeU L sel (nU (.tex κ b)) ((Ty.tex κ b).idxMentions j) (MI L sel b j)
  | sel, .mu b, j => edgeU L sel (nU (.mu b)) ((Ty.mu b).idxMentions j)
      (MI L sel b j || (b.idxMentions j && MT L sel b 0))
  | sel, .iall b, j => edgeU L sel (nU (.iall b)) ((Ty.iall b).idxMentions j) (MI L sel b (j + 1))
  | sel, t, j => edgeU L sel (nU t) (t.idxMentions j) ((sel 0 == L) && t.idxMentions j)

theorem MT_small {L : Bool} {sel : Nat → Bool} {t : Ty} (j : Nat) (h : nU t ≤ 1) :
    MT L sel t j = ((sel 0 == L) && t.tyMentions j) := by
  cases t <;> simp [MT, edgeU, h]
theorem MI_small {L : Bool} {sel : Nat → Bool} {t : Ty} (j : Nat) (h : nU t ≤ 1) :
    MI L sel t j = ((sel 0 == L) && t.idxMentions j) := by
  cases t <;> simp [MI, edgeU, h]

theorem edgeU_any {L : Bool} {sel : Nat → Bool} {n : Nat} {m inner : Bool}
    (h : edgeU L sel n m inner = true) : m = true ∨ (¬ n ≤ 1 ∧ inner = true) := by
  unfold edgeU at h
  by_cases hn : n ≤ 1 <;> simp_all

theorem edgeU_TF {sel : Nat → Bool} {n : Nat} {m m' i1 i2 : Bool} (h1 : edgeU true sel n m i1 = true)
    (h2 : edgeU false sel n m' i2 = true) : ¬ n ≤ 1 ∧ i1 = true ∧ i2 = true := by
  unfold edgeU at h1 h2
  by_cases hn : n ≤ 1 <;> simp_all

theorem MT_ment : ∀ (t : Ty) (L : Bool) (sel : Nat → Bool) (j : Nat), MT L sel t j = true →
    t.tyMentions j = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp only [Ty.tyMentions, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (iha _ _ _ h)
    · exact Or.inr (ihb _ _ _ h)
  | refine t ψ ih =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | iex b ih =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | tex κ b ih =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | mu b ih =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h; simp only [Ty.tyMentions]
    rcases h with h | h
    · exact ih _ _ _ h
    · exact h.1
  | iall b ih =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L sel j h; simp only [MT] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp_all

theorem MI_ment : ∀ (t : Ty) (L : Bool) (sel : Nat → Bool) (j : Nat), MI L sel t j = true →
    t.idxMentions j = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp only [Ty.idxMentions, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (iha _ _ _ h)
    · exact Or.inr (ihb _ _ _ h)
  | refine t ψ ih =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp only [Ty.idxMentions, Bool.or_eq_true, Bool.and_eq_true] at h ⊢
    rcases h with h | h
    · exact Or.inl (ih _ _ _ h)
    · exact Or.inr h.2
  | iex b ih =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | tex κ b ih =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | mu b ih =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h; simp only [Ty.idxMentions]
    rcases h with h | h
    · exact ih _ _ _ h
    · exact h.1
  | iall b ih =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    exact ih _ _ _ h
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L sel j h; simp only [MI] at h; rcases edgeU_any h with hm | ⟨_, h⟩; · exact hm
    simp_all

/-- **Both sides read a type variable only if two words mention it.** -/
theorem MT_two : ∀ (t : Ty) (sel : Nat → Bool) (j : Nat), MT true sel t j = true →
    MT false sel t j = true → 2 ≤ t.countT j := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp only [Ty.countT]
    simp only [Bool.or_eq_true] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have := iha _ j h1 h2; omega
    · have := countT_pos a j (MT_ment _ _ _ _ h1); have := countT_pos b j (MT_ment _ _ _ _ h2); omega
    · have := countT_pos b j (MT_ment _ _ _ _ h1); have := countT_pos a j (MT_ment _ _ _ _ h2); omega
    · have := ihb _ j h1 h2; omega
  | refine t ψ ih =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ j h1 h2
  | iex b ih =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ j h1 h2
  | tex κ b ih =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ (j + 1) h1 h2
  | mu b ih =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 h2
    simp only [Ty.countT]
    rcases h1 with h1 | ⟨m1, h1⟩ <;> rcases h2 with h2 | ⟨m2, h2⟩
    · have := ih _ (j + 1) h1 h2; omega
    · have := countT_pos b (j + 1) (MT_ment _ _ _ _ h1); have := countT_pos b 0 (MT_ment _ _ _ _ h2)
      simp only [m2, ↓reduceIte]; omega
    · have := countT_pos b (j + 1) (MT_ment _ _ _ _ h2); have := countT_pos b 0 (MT_ment _ _ _ _ h1)
      simp only [m1, ↓reduceIte]; omega
    · have := ih _ 0 h1 h2; simp only [m1, ↓reduceIte]; omega
  | iall b ih =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ j h1 h2
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro sel j h1 h2; simp only [MT] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp_all

theorem MI_two : ∀ (t : Ty) (sel : Nat → Bool) (j : Nat), MI true sel t j = true →
    MI false sel t j = true → 2 ≤ t.countI j := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp only [Ty.countI]
    simp only [Bool.or_eq_true] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have := iha _ j h1 h2; omega
    · have := countI_pos a j (MI_ment _ _ _ _ h1); have := countI_pos b j (MI_ment _ _ _ _ h2); omega
    · have := countI_pos b j (MI_ment _ _ _ _ h1); have := countI_pos a j (MI_ment _ _ _ _ h2); omega
    · have := ihb _ j h1 h2; omega
  | refine t ψ ih =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 h2
    simp only [Ty.countI]
    rcases h1 with h1 | ⟨s1, m1⟩ <;> rcases h2 with h2 | ⟨s2, m2⟩
    · have := ih _ j h1 h2; omega
    · have := countI_pos t j (MI_ment _ _ _ _ h1); simp only [m2, ↓reduceIte]; omega
    · have := countI_pos t j (MI_ment _ _ _ _ h2); simp only [m1, ↓reduceIte]; omega
    · simp_all
  | iex b ih =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ (j + 1) h1 h2
  | tex κ b ih =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ j h1 h2
  | mu b ih =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp only [Bool.or_eq_true, Bool.and_eq_true] at h1 h2
    simp only [Ty.countI]
    rcases h1 with h1 | ⟨m1, h1⟩ <;> rcases h2 with h2 | ⟨m2, h2⟩
    · have := ih _ j h1 h2; omega
    · have := countI_pos b j (MI_ment _ _ _ _ h1); have := countT_pos b 0 (MT_ment _ _ _ _ h2)
      simp only [m2, ↓reduceIte]; omega
    · have := countI_pos b j (MI_ment _ _ _ _ h2); have := countT_pos b 0 (MT_ment _ _ _ _ h1)
      simp only [m1, ↓reduceIte]; omega
    · have := MT_two b _ 0 h1 h2; simp only [m1, ↓reduceIte]; omega
  | iall b ih =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    exact ih _ (j + 1) h1 h2
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro sel j h1 h2; simp only [MI] at h1 h2; obtain ⟨_, h1, h2⟩ := edgeU_TF h1 h2
    simp_all

theorem MI_false_of_two {b : Ty} {sel : Nat → Bool} {j : Nat} (hc : b.countI j < 2)
    (h : MI false sel b j = true) : MI true sel b j = false := by
  cases e : MI true sel b j
  · rfl
  · have := MI_two b sel j e h; omega

theorem MT_false_of_two {b : Ty} {sel : Nat → Bool} {j : Nat} (hc : b.countT j < 2)
    (h : MT false sel b j = true) : MT true sel b j = false := by
  cases e : MT true sel b j
  · rfl
  · have := MT_two b sel j e h; omega

/-- A constant selection reads everything from its side. -/
theorem MT_const : ∀ (t : Ty) (L c : Bool) (j : Nat),
    MT L (fun _ => c) t j = ((c == L) && t.tyMentions j) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L c j; simp only [MT, edgeU, iha, ihb, Ty.tyMentions]; split <;> cases c <;> cases L <;> simp
  | refine t ψ ih => intro L c j; simp only [MT, edgeU, ih, Ty.tyMentions]; split <;> rfl
  | iex b ih => intro L c j; simp only [MT, edgeU, ih, Ty.tyMentions]; split <;> rfl
  | tex κ b ih => intro L c j; simp only [MT, edgeU, ih, Ty.tyMentions]; split <;> rfl
  | iall b ih => intro L c j; simp only [MT, edgeU, ih, Ty.tyMentions]; split <;> rfl
  | mu b ih =>
    intro L c j; simp only [MT, edgeU, ih, Ty.tyMentions]
    split <;> cases c <;> cases L <;> cases b.tyMentions (j + 1) <;> simp
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L c j; simp only [MT, edgeU]; split <;> rfl

theorem MI_const : ∀ (t : Ty) (L c : Bool) (j : Nat),
    MI L (fun _ => c) t j = ((c == L) && t.idxMentions j) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L c j; simp only [MI, edgeU, iha, ihb, Ty.idxMentions]; split <;> cases c <;> cases L <;> simp
  | refine t ψ ih =>
    intro L c j; simp only [MI, edgeU, ih, Ty.idxMentions]
    split <;> cases c <;> cases L <;> simp
  | iex b ih => intro L c j; simp only [MI, edgeU, ih, Ty.idxMentions]; split <;> rfl
  | tex κ b ih => intro L c j; simp only [MI, edgeU, ih, Ty.idxMentions]; split <;> rfl
  | iall b ih => intro L c j; simp only [MI, edgeU, ih, Ty.idxMentions]; split <;> rfl
  | mu b ih =>
    intro L c j; simp only [MI, edgeU, ih, MT_const, Ty.idxMentions]
    split <;> cases c <;> cases L <;> cases b.idxMentions j <;> simp
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro L c j; simp only [MI, edgeU]; split <;> rfl

/-! ## Resources, copy-kinded variables, `∀` bodies -/

theorem Res_le_zero {R : Res} (h : R ≤ Res.zero) : R = Res.zero :=
  Res.ext fun k => by have := h k; simp at this; simp [this]

theorem Res_le_add_left (a b : Res) : b ≤ a + b := fun k => by simp

theorem Res_add4 {Ra Rb Ra1 Ra2 Rb1 Rb2 : Res} (ha : Ra ≤ Ra1 + Ra2) (hb : Rb ≤ Rb1 + Rb2) :
    Ra + Rb ≤ (Ra1 + Rb1) + (Ra2 + Rb2) := fun k => by
  have h1 := ha k; have h2 := hb k; simp only [Res.add_apply] at h1 h2 ⊢; omega

/-- Every copy-kinded variable of `ke` denotes resource-free values in `η`
(`VRR_copy_zero`'s hypotheses). -/
def CZ (ke : KEnv) (η : TEnv) : Prop :=
  (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.rrs k S vs Y → Y = .zero) ∧
  (∀ k, ke.ask k true (·.copy) = true → ∀ S vs Y, η.urrs k S vs Y → Y = .zero)

theorem CZ_push0 {ke : KEnv} {η : TEnv} (o : Option Kind) (s : Ty) (h : CZ ke η) :
    CZ (o :: ke) (η.push0 s) := by
  refine ⟨fun k hk S vs Y hy => ?_, fun k hk S vs Y hy => ?_⟩
  · cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hy
    | succ k =>
        simp [TEnv.push0, TEnv.ins, TEnv.insR] at hy
        exact h.1 k (by simpa [KEnv.ask] using hk) S vs Y hy
  · cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hy
    | succ k =>
        simp [TEnv.push0, TEnv.ins, TEnv.insR] at hy
        exact h.2 k (by simpa [KEnv.ask] using hk) S vs Y hy

theorem CZ_nil (η : TEnv) : CZ [] η :=
  ⟨fun k hk => by simp [KEnv.ask] at hk, fun k hk => by simp [KEnv.ask] at hk⟩

/-- Every `∀` reached in `t` (not under references) has a non-affine body, so
its values carry no resources (`VRR_copy_zero`), uniformly in the index. -/
def IallOK (ke : KEnv) : Ty → Bool
  | .prod a b => IallOK ke a && IallOK ke b
  | .sum a b => IallOK ke a && IallOK ke b
  | .iex b => IallOK ke b
  | .tex κ b => IallOK (some κ :: ke) b
  | .mu b => IallOK (none :: ke) b
  | .refine t _ => IallOK ke t
  | .iall b => !Ty.affineIn ke b && IallOK ke b
  | _ => true

/-! ## The resourceful mix -/

theorem iex_multi {ke : KEnv} {b : Ty} {us : List Acc} (hok : Ty.coupledOKIn ke (.iex b) = true)
    (hu : accs (.iex b) = some us) (hn : 2 ≤ us.length) : b.countI 0 < 2 ∧ accs b = some us := by
  by_cases hc : 2 ≤ b.countI 0
  · exfalso
    simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have hf : (Ty.iex b).fitsGranule = true := hok.2.resolve_left (by omega)
    have hf' : ((Ty.iex b).rawWords).any (· ≤ 2) = true := hf
    have hu' := hu
    simp only [accs] at hu'
    simp only [show 2 ≤ _ from hc, ↓reduceIte] at hu'
    cases hr : (Ty.iex b).rawWords with
    | none => rw [hr] at hf'; simp at hf'
    | some m =>
      rw [hr] at hf' hu'; simp at hf'
      have hl : us.length ≤ 1 := by
        rcases m with _ | _ | _ | m
        all_goals simp at hu'
        all_goals (try omega)
        all_goals (subst hu'; simp)
      omega
  · refine ⟨by omega, ?_⟩
    simp only [accs] at hu
    simp only [show ¬ 2 ≤ _ from hc, ↓reduceIte] at hu; exact hu

theorem tex_multi {ke : KEnv} {κ : Kind} {b : Ty} {us : List Acc}
    (hok : Ty.coupledOKIn ke (.tex κ b) = true)
    (hu : accs (.tex κ b) = some us) (hn : 2 ≤ us.length) : b.countT 0 < 2 ∧ accs b = some us := by
  by_cases hc : 2 ≤ b.countT 0
  · exfalso
    simp only [Ty.coupledOKIn, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
    have hf : (Ty.tex κ b).fitsGranule = true := hok.2.resolve_left (by omega)
    have hf' : ((Ty.tex κ b).rawWords).any (· ≤ 2) = true := hf
    have hu' := hu
    simp only [accs] at hu'
    simp only [show 2 ≤ _ from hc, ↓reduceIte] at hu'
    cases hr : (Ty.tex κ b).rawWords with
    | none => rw [hr] at hf'; simp at hf'
    | some m =>
      rw [hr] at hf' hu'; simp at hf'
      have hl : us.length ≤ 1 := by
        rcases m with _ | _ | _ | m
        all_goals simp at hu'
        all_goals (try omega)
        all_goals (subst hu'; simp)
      omega
  · refine ⟨by omega, ?_⟩
    simp only [accs] at hu
    simp only [show ¬ 2 ≤ _ from hc, ↓reduceIte] at hu; exact hu

theorem nU_of_accs {t : Ty} {us : List Acc} (hu : accs t = some us) : nU t = us.length := by
  simp [nU, hu]

/-- At most one unit: the mix is one side's value. -/
theorem mix_wrap {t : Ty} {us : List Acc} {sel : Nat → Bool} {ρ1 ρ2 ρ : Nat → Nat} {η1 η2 η : TEnv}
    {ws1 ws2 : List Word} {R1 R2 : Res} (hu : accs t = some us)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us)
    (hI1 : ∀ j, MI true sel t j = true → ρ j = ρ1 j) (hI2 : ∀ j, MI false sel t j = true → ρ j = ρ2 j)
    (hT1 : ∀ j, MT true sel t j = true → η.wit j = η1.wit j ∧ η.rrs j = η1.rrs j ∧ η.urrs j = η1.urrs j)
    (hT2 : ∀ j, MT false sel t j = true → η.wit j = η2.wit j ∧ η.rrs j = η2.rrs j ∧ η.urrs j = η2.urrs j)
    (hE1 : CE η = CE η1) (hE2 : CE η = CE η2)
    (h1 : VRR ρ1 η1 t (shp t) ws1 R1) (h2 : VRR ρ2 η2 t (shp t) ws2 R2)
    (hint : 2 ≤ us.length → ∃ R, VRR ρ η t (shp t) (mixU us sel ws1 ws2) R ∧ R ≤ R1 + R2) :
    ∃ R, VRR ρ η t (shp t) (mixU us sel ws1 ws2) R ∧ R ≤ R1 + R2 := by
  by_cases hn : us.length ≤ 1
  · have hnU : nU t ≤ 1 := by rw [nU_of_accs hu]; exact hn
    rw [mixU_small hn l1 l2]
    cases hs : sel 0
    · refine ⟨R2, ?_, Res_le_add_left _ _⟩
      simp only [Bool.false_eq_true, ite_false]
      exact VRR_congr t ρ2 ρ η2 η _ _ _ (fun j hj => (hI2 j (by rw [MI_small j hnU]; simp [hs, hj])).symm)
        (fun j hj => have h := hT2 j (by rw [MT_small j hnU]; simp [hs, hj]); ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
        hE2.symm h2
    · refine ⟨R1, ?_, Res.le_add_right _ _⟩
      simp only [ite_true]
      exact VRR_congr t ρ1 ρ η1 η _ _ _ (fun j hj => (hI1 j (by rw [MI_small j hnU]; simp [hs, hj])).symm)
        (fun j hj => have h := hT1 j (by rw [MT_small j hnU]; simp [hs, hj]); ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩)
        hE1.symm h1
  · exact hint (by omega)


theorem mixR_gen : ∀ (t : Ty) (ke : KEnv) (us : List Acc) (sel : Nat → Bool) (ρ1 ρ2 ρ : Nat → Nat)
    (η1 η2 η : TEnv) (ws1 ws2 : List Word) (R1 R2 : Res),
    Ty.coupledOKIn ke t = true → IallOK ke t = true → accs t = some us →
    ws1.length = nWords us → ws2.length = nWords us →
    (∀ j, MI true sel t j = true → ρ j = ρ1 j) → (∀ j, MI false sel t j = true → ρ j = ρ2 j) →
    (∀ j, MT true sel t j = true → η.wit j = η1.wit j ∧ η.rrs j = η1.rrs j ∧ η.urrs j = η1.urrs j) →
    (∀ j, MT false sel t j = true → η.wit j = η2.wit j ∧ η.rrs j = η2.rrs j ∧ η.urrs j = η2.urrs j) →
    CE η = CE η1 → CE η = CE η2 → CZ ke η1 → CZ ke η2 →
    VRR ρ1 η1 t (shp t) ws1 R1 → VRR ρ2 η2 t (shp t) ws2 R2 →
    ∃ R, VRR ρ η t (shp t) (mixU us sel ws1 ws2) R ∧ R ≤ R1 + R2 := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.prod a b) ≤ 1 := by rw [nU_of_accs hu]; omega
    simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok
    simp only [IallOK, Bool.and_eq_true] at hia
    cases ha : accs a with
    | none => simp [accs, ha] at hu
    | some ua =>
    cases hb' : accs b with
    | none => simp [accs, ha, hb'] at hu
    | some ub =>
    have hus : us = ua ++ ub := by simp [accs, ha, hb'] at hu; exact hu.symm
    subst hus
    have hna : nU a = ua.length := nU_of_accs ha
    have hMI : ∀ L j, MI L sel (.prod a b) j =
        (MI L sel a j || MI L (fun i => sel (i + ua.length)) b j) := by
      intro L j; simp only [MI, edgeU, hnU, ite_false, hna]
    have hMT : ∀ L j, MT L sel (.prod a b) j =
        (MT L sel a j || MT L (fun i => sel (i + ua.length)) b j) := by
      intro L j; simp only [MT, edgeU, hnU, ite_false, hna]
    have hlen1 := l1
    have hlen2 := l2
    rw [nWords_append] at hlen1 hlen2
    simp only [shp, VRR] at h1 h2
    obtain ⟨ra1, rb1, e1, Ra1, Rb1, hR1, -, h1⟩ := h1
    obtain ⟨ra2, rb2, e2, Ra2, Rb2, hR2, -, h2⟩ := h2
    cases e1; cases e2
    have hwa : (shp a).wc = some (nWords ua) := by rw [shp_wc]; simp [wc, ha]
    obtain ⟨_, h1a, h1b⟩ := h1 _ hwa
    obtain ⟨_, h2a, h2b⟩ := h2 _ hwa
    obtain ⟨Ra, hva, hla⟩ := iha ke ua sel ρ1 ρ2 ρ η1 η2 η _ _ Ra1 Ra2 hok.1 hia.1 ha
      (by simp; omega) (by simp; omega)
      (fun j hj => hI1 j (by rw [hMI]; simp [hj])) (fun j hj => hI2 j (by rw [hMI]; simp [hj]))
      (fun j hj => hT1 j (by rw [hMT]; simp [hj])) (fun j hj => hT2 j (by rw [hMT]; simp [hj]))
      hE1 hE2 hc1 hc2 h1a h2a
    obtain ⟨Rb, hvb, hlb⟩ := ihb ke ub (fun i => sel (i + ua.length)) ρ1 ρ2 ρ η1 η2 η _ _ Rb1 Rb2
      hok.2 hia.2 hb' (by simp; omega) (by simp; omega)
      (fun j hj => hI1 j (by rw [hMI]; simp [hj])) (fun j hj => hI2 j (by rw [hMI]; simp [hj]))
      (fun j hj => hT1 j (by rw [hMT]; simp [hj])) (fun j hj => hT2 j (by rw [hMT]; simp [hj]))
      hE1 hE2 hc1 hc2 h1b h2b
    have hm := mixU_append ua ub sel ws1 ws2 (by omega) (by omega)
    have hAl : (mixU ua sel (ws1.take (nWords ua)) (ws2.take (nWords ua))).length = nWords ua :=
      length_mixU _ _ _ _ (by simp; omega) (by simp; omega)
    refine ⟨Ra + Rb, ?_, by rw [hR1, hR2]; exact Res_add4 hla hlb⟩
    simp only [shp, VRR]
    refine ⟨shp a, shp b, rfl, Ra, Rb, rfl, ?_, ?_⟩
    · intro h; rw [hwa] at h; cases h
    intro n hn
    rw [hwa] at hn; cases hn
    rw [hm]
    refine ⟨by simp; omega, ?_, ?_⟩
    · rw [List.take_left' hAl]; exact hva
    · rw [List.drop_left' hAl]; exact hvb
  | iex b ih =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.iex b) ≤ 1 := by rw [nU_of_accs hu]; omega
    obtain ⟨hcI, hub⟩ := iex_multi hok hu hn
    have hokb : Ty.coupledOKIn ke b = true := by
      simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok; exact hok.1
    have hiab : IallOK ke b = true := by simpa [IallOK] using hia
    have hMI : ∀ L j, MI L sel (.iex b) j = MI L sel b (j + 1) := by
      intro L j; simp only [MI, edgeU, hnU, ite_false]
    have hMT : ∀ L j, MT L sel (.iex b) j = MT L sel b j := by
      intro L j; simp only [MT, edgeU, hnU, ite_false]
    simp only [shp, VRR] at h1 h2 ⊢
    obtain ⟨n1, rb1, w1, e1, h1⟩ := h1
    obtain ⟨n2, rb2, w2, e2, h2⟩ := h2
    cases e1; cases e2
    obtain ⟨R, hv, hle⟩ := ih ke us sel _ _ (vcons (if MI true sel b 0 then w1 else w2) ρ) η1 η2 η
      ws1 ws2 R1 R2 hokb hiab hub l1 l2
      (vcons_agree (P := fun j => MI true sel b j = true) (fun h => by simp [h])
        (fun j hj => hI1 j (by rw [hMI]; exact hj)))
      (vcons_agree (P := fun j => MI false sel b j = true)
        (fun h => by simp [MI_false_of_two hcI h])
        (fun j hj => hI2 j (by rw [hMI]; exact hj)))
      (fun j hj => hT1 j (by rw [hMT]; exact hj)) (fun j hj => hT2 j (by rw [hMT]; exact hj))
      hE1 hE2 hc1 hc2 h1 h2
    exact ⟨R, ⟨_, _, _, rfl, hv⟩, hle⟩
  | tex κ b ih =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.tex κ b) ≤ 1 := by rw [nU_of_accs hu]; omega
    obtain ⟨hcT, hub⟩ := tex_multi hok hu hn
    have hokb : Ty.coupledOKIn (some κ :: ke) b = true := by
      simp only [Ty.coupledOKIn, Bool.and_eq_true] at hok; exact hok.1
    have hiab : IallOK (some κ :: ke) b = true := by simpa [IallOK] using hia
    have hMI : ∀ L j, MI L sel (.tex κ b) j = MI L sel b j := by
      intro L j; simp only [MI, edgeU, hnU, ite_false]
    have hMT : ∀ L j, MT L sel (.tex κ b) j = MT L sel b (j + 1) := by
      intro L j; simp only [MT, edgeU, hnU, ite_false]
    simp only [shp, VRR] at h1 h2 ⊢
    obtain ⟨n1, rb1, s1, e1, hs1, ha1, h1⟩ := h1
    obtain ⟨n2, rb2, s2, e2, hs2, ha2, h2⟩ := h2
    cases e1; cases e2
    obtain ⟨R, hv, hle⟩ := ih (some κ :: ke) us sel ρ1 ρ2 ρ _ _
      (η.push0 (if MT true sel b 0 then s1 else s2)) ws1 ws2 R1 R2 hokb hiab hub l1 l2
      (fun j hj => hI1 j (by rw [hMI]; exact hj)) (fun j hj => hI2 j (by rw [hMI]; exact hj))
      (push0_agreeR (P := fun j => MT true sel b j = true) (fun h => by simp [h])
        (fun j hj => hT1 j (by rw [hMT]; exact hj)))
      (push0_agreeR (P := fun j => MT false sel b j = true)
        (fun h => by simp [MT_false_of_two hcT h])
        (fun j hj => hT2 j (by rw [hMT]; exact hj)))
      (by rw [CE_push0, CE_push0]; exact hE1) (by rw [CE_push0, CE_push0]; exact hE2)
      (CZ_push0 _ _ hc1) (CZ_push0 _ _ hc2) h1 h2
    exact ⟨R, ⟨_, _, _, rfl, by split <;> assumption, by split <;> assumption, hv⟩, hle⟩
  | mu b ih =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.mu b) ≤ 1 := by rw [nU_of_accs hu]; omega
    have hub : accs b = some us := by simpa [accs] using hu
    have hokb : Ty.coupledOKIn (none :: ke) b = true := by simpa [Ty.coupledOKIn] using hok
    have hiab : IallOK (none :: ke) b = true := by simpa [IallOK] using hia
    have hMI : ∀ L j, MI L sel (.mu b) j = (MI L sel b j || (b.idxMentions j && MT L sel b 0)) := by
      intro L j; simp only [MI, edgeU, hnU, ite_false]
    have hMT : ∀ L j, MT L sel (.mu b) j =
        (MT L sel b (j + 1) || (b.tyMentions (j + 1) && MT L sel b 0)) := by
      intro L j; simp only [MT, edgeU, hnU, ite_false]
    simp only [shp, VRR] at h1 h2 ⊢
    exact ih (none :: ke) us sel ρ1 ρ2 ρ _ _ _ ws1 ws2 R1 R2 hokb hiab hub l1 l2
      (fun j hj => hI1 j (by rw [hMI]; simp [hj])) (fun j hj => hI2 j (by rw [hMI]; simp [hj]))
      (push0_agreeR (P := fun j => MT true sel b j = true)
        (fun h0' => cl_congr _ 0 0 _ _ _ _
          (fun j hj => hI1 j (by
            simp only [Ty.idxMentions, Nat.add_zero] at hj; rw [hMI]; simp [hj, h0']))
          (fun j hj => (hT1 j (by
            simp only [Ty.tyMentions, Nat.add_zero] at hj; rw [hMT]; simp [hj, h0'])).1))
        (fun j hj => hT1 j (by rw [hMT]; simp [hj])))
      (push0_agreeR (P := fun j => MT false sel b j = true)
        (fun h0' => cl_congr _ 0 0 _ _ _ _
          (fun j hj => hI2 j (by
            simp only [Ty.idxMentions, Nat.add_zero] at hj; rw [hMI]; simp [hj, h0']))
          (fun j hj => (hT2 j (by
            simp only [Ty.tyMentions, Nat.add_zero] at hj; rw [hMT]; simp [hj, h0'])).1))
        (fun j hj => hT2 j (by rw [hMT]; simp [hj])))
      (by rw [CE_push0, CE_push0]; exact hE1) (by rw [CE_push0, CE_push0]; exact hE2)
      (CZ_push0 _ _ hc1) (CZ_push0 _ _ hc2) h1 h2
  | refine t ψ ih =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.refine t ψ) ≤ 1 := by rw [nU_of_accs hu]; omega
    have hub : accs t = some us := by simpa [accs] using hu
    have hokt : Ty.coupledOKIn ke t = true := by simpa [Ty.coupledOKIn] using hok
    have hiat : IallOK ke t = true := by simpa [IallOK] using hia
    have hMI : ∀ L j, MI L sel t j = true → MI L sel (.refine t ψ) j = true := by
      intro L j h; simp only [MI, edgeU, hnU, ite_false]; simp [h]
    have hMT : ∀ L j, MT L sel (.refine t ψ) j = MT L sel t j := by
      intro L j; simp only [MT, edgeU, hnU, ite_false]
    simp only [shp, VRR] at h1 h2 ⊢
    obtain ⟨R, hv, hle⟩ := ih ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hokt hiat hub l1 l2
      (fun j hj => hI1 j (hMI _ _ hj)) (fun j hj => hI2 j (hMI _ _ hj))
      (fun j hj => hT1 j (by rw [hMT]; exact hj)) (fun j hj => hT2 j (by rw [hMT]; exact hj))
      hE1 hE2 hc1 hc2 h1.1 h2.1
    refine ⟨R, ⟨hv, IniR_short ?_ ψ⟩, hle⟩
    rw [length_mixU _ _ _ _ l1 l2]; have := length_le_nWords us; omega
  | iall b ih =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    have hnU : ¬ nU (.iall b) ≤ 1 := by rw [nU_of_accs hu]; omega
    have hub : accs b = some us := by simpa [accs] using hu
    have hokb : Ty.coupledOKIn ke b = true := by simpa [Ty.coupledOKIn] using hok
    simp only [IallOK, Bool.and_eq_true, Bool.not_eq_true'] at hia
    have hMI : ∀ L j, MI L sel (.iall b) j = MI L sel b (j + 1) := by
      intro L j; simp only [MI, edgeU, hnU, ite_false]
    have hMT : ∀ L j, MT L sel (.iall b) j = MT L sel b j := by
      intro L j; simp only [MT, edgeU, hnU, ite_false]
    simp only [shp, VRR] at h1 h2 ⊢
    have z1 : R1 = Res.zero := VRR_copy_zero b ke _ η1 _ ws1 R1 hia.1 hc1.1 hc1.2 (h1 0)
    have z2 : R2 = Res.zero := VRR_copy_zero b ke _ η2 _ ws2 R2 hia.1 hc2.1 hc2.2 (h2 0)
    refine ⟨Res.zero, fun n => ?_, Res.zero_le _⟩
    obtain ⟨R, hv, hle⟩ := ih ke us sel _ _ (vcons n ρ) η1 η2 η ws1 ws2 R1 R2 hokb hia.2 hub l1 l2
      (vcons_agree (P := fun j => MI true sel b j = true) (fun _ => rfl)
        (fun j hj => hI1 j (by rw [hMI]; exact hj)))
      (vcons_agree (P := fun j => MI false sel b j = true) (fun _ => rfl)
        (fun j hj => hI2 j (by rw [hMI]; exact hj)))
      (fun j hj => hT1 j (by rw [hMT]; exact hj)) (fun j hj => hT2 j (by rw [hMT]; exact hj))
      hE1 hE2 hc1 hc2 (h1 n) (h2 n)
    rw [z1, z2, Res.zero_add] at hle
    rw [← Res_le_zero hle]; exact hv
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro ke us sel ρ1 ρ2 ρ η1 η2 η ws1 ws2 R1 R2 hok hia hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 hc1 hc2 h1 h2
    refine mix_wrap hu l1 l2 hI1 hI2 hT1 hT2 hE1 hE2 h1 h2 (fun hn => ?_)
    exfalso
    have hl : us.length ≤ 1 := by
      simp only [accs] at hu
      (try split at hu) <;> (first | (cases hu; simp) | simp at hu)
    omega

/-- **The resourceful mix.**  Taking each access unit of a `coupledOK` type
from either of two values gives a value carrying at most both values'
resources. -/
theorem VRR_mixIn {ke : KEnv} {ρ : Nat → Nat} {η : TEnv} {T : Ty} {us : List Acc} {sel : Nat → Bool}
    {ws1 ws2 : List Word} {R1 R2 : Res}
    (hc : Ty.coupledOKIn ke T = true) (hia : IallOK ke T = true) (hu : accs T = some us)
    (hz : CZ ke η)
    (h1 : VRR ρ η T (shp T) ws1 R1) (h2 : VRR ρ η T (shp T) ws2 R2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    ∃ R, VRR ρ η T (shp T) (mixU us sel ws1 ws2) R ∧ R ≤ R1 + R2 :=
  mixR_gen T ke us sel ρ ρ ρ η η η ws1 ws2 R1 R2 hc hia hu l1 l2 (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ => ⟨rfl, rfl, rfl⟩) rfl rfl hz hz h1 h2

/-- The closed case: no kind environment, no copy-zero hypotheses. -/
theorem VRR_mix {ρ : Nat → Nat} {η : TEnv} {T : Ty} {us : List Acc} {sel : Nat → Bool}
    {ws1 ws2 : List Word} {R1 R2 : Res}
    (hc : Ty.coupledOKIn [] T = true) (hia : IallOK [] T = true) (hu : accs T = some us)
    (h1 : VRR ρ η T (shp T) ws1 R1) (h2 : VRR ρ η T (shp T) ws2 R2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    ∃ R, VRR ρ η T (shp T) (mixU us sel ws1 ws2) R ∧ R ≤ R1 + R2 :=
  VRR_mixIn hc hia hu (CZ_nil η) h1 h2 l1 l2

/-! ## `Valid` mixes too -/

theorem Valid_mixGen : ∀ (t : Ty) (us : List Acc) (sel : Nat → Bool) (ws1 ws2 : List Word),
    accs t = some us → ws1.length = nWords us → ws2.length = nWords us →
    Valid t ws1 → Valid t ws2 → Valid t (mixU us sel ws1 ws2) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    cases ha : accs a with
    | none => simp [accs, ha] at hu
    | some ua =>
    cases hb' : accs b with
    | none => simp [accs, ha, hb'] at hu
    | some ub =>
    have hus : us = ua ++ ub := by simp [accs, ha, hb'] at hu; exact hu.symm
    subst hus
    have hlen1 := l1
    have hlen2 := l2
    rw [nWords_append] at hlen1 hlen2
    have hwa : wc a = some (nWords ua) := by simp [wc, ha]
    simp only [Valid] at h1 h2 ⊢
    obtain ⟨h1a, h1b⟩ := h1 _ hwa
    obtain ⟨h2a, h2b⟩ := h2 _ hwa
    intro n hn
    rw [hwa] at hn; cases hn
    have hm := mixU_append ua ub sel ws1 ws2 (by omega) (by omega)
    have hAl : (mixU ua sel (ws1.take (nWords ua)) (ws2.take (nWords ua))).length = nWords ua :=
      length_mixU _ _ _ _ (by simp; omega) (by simp; omega)
    rw [hm, List.take_left' hAl, List.drop_left' hAl]
    exact ⟨iha ua sel _ _ ha (by simp; omega) (by simp; omega) h1a h2a,
      ihb ub _ _ _ hb' (by simp; omega) (by simp; omega) h1b h2b⟩
  | iex b ih =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    rcases iex_accs hu with hl | hub
    · rw [mixU_small hl l1 l2]; split <;> assumption
    · exact ih us sel ws1 ws2 hub l1 l2 h1 h2
  | tex κ b ih =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    rcases tex_accs hu with hl | hub
    · rw [mixU_small hl l1 l2]; split <;> assumption
    · exact ih us sel ws1 ws2 hub l1 l2 h1 h2
  | mu b ih =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    exact ih us sel ws1 ws2 (by simpa [accs] using hu) l1 l2 h1 h2
  | iall b ih =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    exact ih us sel ws1 ws2 (by simpa [accs] using hu) l1 l2 h1 h2
  | refine b ψ ih =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    exact ih us sel ws1 ws2 (by simpa [accs] using hu) l1 l2 h1 h2
  | unit | void | int | tid | intS | fix | lanes | sum | code | array | ptr | ptrOpt | loc | share | cap
    | word | tok | word2 | tok2 | epair | tokE | tvar =>
    intro us sel ws1 ws2 hu l1 l2 h1 h2
    have hl : us.length ≤ 1 := by
      simp only [accs] at hu
      (try split at hu) <;> (first | (cases hu; simp) | simp at hu)
    rw [mixU_small hl l1 l2]; split <;> assumption

theorem Valid_mix {T : Ty} {us : List Acc} {sel : Nat → Bool} {ws1 ws2 : List Word}
    (hu : accs T = some us) (h1 : Valid T ws1) (h2 : Valid T ws2)
    (l1 : ws1.length = nWords us) (l2 : ws2.length = nWords us) :
    Valid T (mixU us sel ws1 ws2) :=
  Valid_mixGen T us sel ws1 ws2 hu l1 l2 h1 h2

end TermTear

#print axioms TermTear.VR_tear
#print axioms TermTear.selIni_CE
#print axioms TermTear.CErini
#print axioms TermTear.Valid_tear
#print axioms TermTear.VR_tearIn
#print axioms TermTear.assemble
