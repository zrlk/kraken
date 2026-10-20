/-
# TermClose — closing a static type (T3c-1)

`cl ρ W c d t` *closes* `t`, having crossed `c` type binders and `d` index
binders inside it: a free index variable `k ≥ d` becomes the literal
`ρ (k - d)`, and a free type variable `k ≥ c` becomes `W (k - c)`.  Index
subterms that end up variable-free are folded bottom-up, so at depth 0 every
index term is a literal and `TyEqS`'s semantic index equality (`IEq` at depth 0)
becomes syntactic equality of closures (`cl_tyEq`).

The store typing Σ records closed types,
`VR` at a reference *compares* `Σ a` with the closure of the static target, and
a code value's signature is compared with its block's declared types the same
way.  Everything here is syntax; `VR` is not mentioned.

Lemmas: index shift (`cl_shiftI`), type-variable insertion (`cl_shiftT`),
index instantiation (`cl_instT`), `TyEqS` (`cl_tyEq`), closing a term shifted
past the binders (`cl_shifted`), simultaneous type substitution (`cl_substTs`).
-/
import WeakCore.CoreTyping
import WeakCore.TermRun

namespace TermClose
open CoreLang CoreTerm CoreTyping

/-! ## §1 Definitions -/

/-- Folding constructors: variable-free operands are evaluated. -/
def addF : Idx → Idx → Idx
  | .lit a, .lit b => .lit (a + b)
  | i, j => .add i j

def subF : Idx → Idx → Idx
  | .lit a, .lit b => .lit (a - b)
  | i, j => .sub i j

def smulF (n : Nat) : Idx → Idx
  | .lit a => .lit (n * a)
  | i => .smul n i

/-- Close an index term at index depth `d`. -/
def clI (ρ : Nat → Nat) (d : Nat) : Idx → Idx
  | .lit n    => .lit n
  | .var k    => if k < d then .var k else .lit (ρ (k - d))
  | .add i j  => addF (clI ρ d i) (clI ρ d j)
  | .sub i j  => subF (clI ρ d i) (clI ρ d j)
  | .smul n i => smulF n (clI ρ d i)

def clM (ρ : Nat → Nat) (d : Nat) : Mode → Mode
  | .rgn r => .rgn (clI ρ d r)
  | μ      => μ

def clP (ρ : Nat → Nat) (d : Nat) : Pred → Pred
  | .tt      => .tt
  | .le i j  => .le (clI ρ d i) (clI ρ d j)
  | .eq i j  => .eq (clI ρ d i) (clI ρ d j)
  | .and p q => .and (clP ρ d p) (clP ρ d q)
  | .ini i   => .ini (clI ρ d i)

/-- Close a type, having crossed `c` type binders and `d` index binders. -/
def cl (ρ : Nat → Nat) (W : Nat → Ty) (c d : Nat) : Ty → Ty
  | .intS i      => .intS (clI ρ d i)
  | .prod a b    => .prod (cl ρ W c d a) (cl ρ W c d b)
  | .sum a b     => .sum (cl ρ W c d a) (cl ρ W c d b)
  | .code a b    => .code (cl ρ W c d a) (cl ρ W c d b)
  | .array i t   => .array (clI ρ d i) (cl ρ W c d t)
  | .ptr μ t     => .ptr (clM ρ d μ) (cl ρ W c d t)
  | .ptrOpt μ t  => .ptrOpt (clM ρ d μ) (cl ρ W c d t)
  | .loc μ t     => .loc (clM ρ d μ) (cl ρ W c d t)
  | .word r P    => .word (clI ρ d r) P
  | .tok r st    => .tok (clI ρ d r) (st.map fun (P, i) => (P, clI ρ d i))
  | .word2 r P   => .word2 (clI ρ d r) P
  | .tok2 r P i j => .tok2 (clI ρ d r) P (clI ρ d i) (clI ρ d j)
  | .epair r P   => .epair (clI ρ d r) P
  | .tokE r P e  => .tokE (clI ρ d r) P (clI ρ d e)
  | .share r     => .share (clI ρ d r)
  | .cap s r     => .cap s (clI ρ d r)
  | .tvar k      => if k < c then .tvar k else W (k - c)
  | .mu t        => .mu (cl ρ W (c + 1) d t)
  | .tex κ t     => .tex κ (cl ρ W (c + 1) d t)
  | .iall t      => .iall (cl ρ W c (d + 1) t)
  | .iex t       => .iex (cl ρ W c (d + 1) t)
  | .refine t ψ  => .refine (cl ρ W c d t) (clP ρ d ψ)
  | t            => t

/-! ## §2 Index terms -/

theorem clI_zero (ρ : Nat → Nat) : ∀ i : Idx, clI ρ 0 i = .lit (ev ρ i)
  | .lit n => rfl
  | .var k => by simp [clI, ev]
  | .add i j => by simp [clI, ev, clI_zero ρ i, clI_zero ρ j, addF]
  | .sub i j => by simp [clI, ev, clI_zero ρ i, clI_zero ρ j, subF]
  | .smul n i => by simp [clI, ev, clI_zero ρ i, smulF]

/-- An index shift at `c` (past `d` inner binders) is undone by the matching
valuation. -/
theorem clI_shift {ρ ρ' : Nat → Nat} {c : Nat} (h : ∀ k, ρ' (if c ≤ k then k + 1 else k) = ρ k)
    (d : Nat) : ∀ i : Idx, clI ρ' d (i.shift (c + d)) = clI ρ d i
  | .lit n => rfl
  | .var k => by
      simp only [Idx.shift, clI]
      by_cases h1 : k ≥ c + d
      · have e := h (k - d)
        have h2 : c ≤ k - d := by omega
        simp only [h2, ↓reduceIte] at e
        have h3 : ¬ k + 1 < d := by omega
        have h4 : ¬ k < d := by omega
        have h5 : k + 1 - d = k - d + 1 := by omega
        simp [clI, h1, h3, h4, h5, e]
      · by_cases h2 : k < d
        · simp [clI, h1, h2]
        · have e := h (k - d)
          have h3 : ¬ c ≤ k - d := by omega
          simp only [h3, ↓reduceIte] at e
          simp [clI, h1, h2, e]
  | .add i j => by simp only [Idx.shift, clI, clI_shift h d i, clI_shift h d j]
  | .sub i j => by simp only [Idx.shift, clI, clI_shift h d i, clI_shift h d j]
  | .smul n i => by simp only [Idx.shift, clI, clI_shift h d i]

theorem clM_shift {ρ ρ' : Nat → Nat} {c : Nat} (h : ∀ k, ρ' (if c ≤ k then k + 1 else k) = ρ k)
    (d : Nat) (μ : Mode) : clM ρ' d (μ.shift (c + d)) = clM ρ d μ := by
  cases μ <;> simp [Mode.shift, clM, clI_shift h d]

theorem clP_shift {ρ ρ' : Nat → Nat} {c : Nat} (h : ∀ k, ρ' (if c ≤ k then k + 1 else k) = ρ k)
    (d : Nat) : ∀ ψ : Pred, clP ρ' d (ψ.shift (c + d)) = clP ρ d ψ
  | .tt => rfl
  | .le i j => by simp [Pred.shift, clP, clI_shift h d]
  | .eq i j => by simp [Pred.shift, clP, clI_shift h d]
  | .and p q => by simp [Pred.shift, clP, clP_shift h d p, clP_shift h d q]
  | .ini i => by simp [Pred.shift, clP, clI_shift h d]

/-! ## §3 Types: index shift and type-variable insertion -/

theorem cl_shiftI {ρ ρ' : Nat → Nat} {c : Nat} (h : ∀ k, ρ' (if c ≤ k then k + 1 else k) = ρ k)
    (W : Nat → Ty) : ∀ (t : Ty) (e d : Nat), cl ρ' W e d (t.shiftI (c + d)) = cl ρ W e d t
  | .intS i, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .prod a b, e, d => by simp [Ty.shiftI, cl, cl_shiftI h W a e d, cl_shiftI h W b e d]
  | .sum a b, e, d => by simp [Ty.shiftI, cl, cl_shiftI h W a e d, cl_shiftI h W b e d]
  | .code a b, e, d => by simp [Ty.shiftI, cl, cl_shiftI h W a e d, cl_shiftI h W b e d]
  | .array i t, e, d => by simp [Ty.shiftI, cl, clI_shift h d, cl_shiftI h W t e d]
  | .ptr μ t, e, d => by simp [Ty.shiftI, cl, clM_shift h d, cl_shiftI h W t e d]
  | .ptrOpt μ t, e, d => by simp [Ty.shiftI, cl, clM_shift h d, cl_shiftI h W t e d]
  | .loc μ t, e, d => by simp [Ty.shiftI, cl, clM_shift h d, cl_shiftI h W t e d]
  | .word r P, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .tok r i, e, d => by
      rcases i with _ | ⟨_, _⟩ <;> simp [Ty.shiftI, cl, clI_shift h d]
  | .word2 r P, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .tok2 r P i j, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .epair r P, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .tokE r P i, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .share r, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .cap s r, e, d => by simp [Ty.shiftI, cl, clI_shift h d]
  | .tvar k, e, d => by simp [Ty.shiftI, cl]
  | .mu t, e, d => by simp [Ty.shiftI, cl, cl_shiftI h W t (e + 1) d]
  | .tex κ t, e, d => by simp [Ty.shiftI, cl, cl_shiftI h W t (e + 1) d]
  | .iall t, e, d => by
      have := cl_shiftI h W t e (d + 1)
      rw [← Nat.add_assoc] at this
      simp [Ty.shiftI, cl, this]
  | .iex t, e, d => by
      have := cl_shiftI h W t e (d + 1)
      rw [← Nat.add_assoc] at this
      simp [Ty.shiftI, cl, this]
  | .refine t ψ, e, d => by simp [Ty.shiftI, cl, clP_shift h d, cl_shiftI h W t e d]
  | .unit, _, _ => rfl
  | .void, _, _ => rfl
  | .int, _, _ => rfl
  | .fix _ _, _, _ => rfl
  | .lanes _ _, _, _ => rfl

/-- Inserting a type variable at `c` (past `e` inner binders) is undone by the
matching witness map. -/
theorem cl_shiftT {W W' : Nat → Ty} {c : Nat} (h : ∀ k, W' (if c ≤ k then k + 1 else k) = W k)
    (ρ : Nat → Nat) : ∀ (t : Ty) (e d : Nat), cl ρ W' e d (t.shiftT (c + e)) = cl ρ W e d t
  | .tvar k, e, d => by
      simp only [Ty.shiftT, cl]
      by_cases h1 : k ≥ c + e
      · have ee := h (k - e)
        have h2 : c ≤ k - e := by omega
        simp only [h2, ↓reduceIte] at ee
        have h3 : ¬ k + 1 < e := by omega
        have h4 : ¬ k < e := by omega
        have h5 : k + 1 - e = k - e + 1 := by omega
        simp [cl, h1, h3, h4, h5, ee]
      · by_cases h2 : k < e
        · simp [cl, h1, h2]
        · have ee := h (k - e)
          have h3 : ¬ c ≤ k - e := by omega
          simp only [h3, ↓reduceIte] at ee
          simp [cl, h1, h2, ee]
  | .prod a b, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ a e d, cl_shiftT h ρ b e d]
  | .sum a b, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ a e d, cl_shiftT h ρ b e d]
  | .code a b, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ a e d, cl_shiftT h ρ b e d]
  | .array i t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e d]
  | .ptr μ t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e d]
  | .ptrOpt μ t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e d]
  | .loc μ t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e d]
  | .mu t, e, d => by
      have := cl_shiftT h ρ t (e + 1) d
      rw [← Nat.add_assoc] at this
      simp [Ty.shiftT, cl, this]
  | .tex κ t, e, d => by
      have := cl_shiftT h ρ t (e + 1) d
      rw [← Nat.add_assoc] at this
      simp [Ty.shiftT, cl, this]
  | .iall t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e (d + 1)]
  | .iex t, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e (d + 1)]
  | .refine t ψ, e, d => by simp [Ty.shiftT, cl, cl_shiftT h ρ t e d]
  | .intS _, _, _ => rfl
  | .word _ _, _, _ => rfl
  | .tok _ _, _, _ => rfl
  | .word2 _ _, _, _ => rfl
  | .tok2 _ _ _ _, _, _ => rfl
  | .epair _ _, _, _ => rfl
  | .tokE _ _ _, _, _ => rfl
  | .share _, _, _ => rfl
  | .cap _ _, _, _ => rfl
  | .unit, _, _ => rfl
  | .void, _, _ => rfl
  | .int, _, _ => rfl
  | .fix _ _, _, _ => rfl
  | .lanes _ _, _, _ => rfl

/-! ## §4 Index instantiation -/

theorem shiftN_lit (a : Nat) : ∀ n, shiftN n (.lit a) = .lit a
  | 0 => rfl
  | n + 1 => by simp [shiftN, shiftN_lit a n, Idx.shift]

theorem shiftN_var (m : Nat) : ∀ n, shiftN n (.var m) = .var (m + n)
  | 0 => rfl
  | n + 1 => by simp [shiftN, shiftN_var m n, Idx.shift]; omega

theorem shiftN_add (i j : Idx) : ∀ n, shiftN n (.add i j) = .add (shiftN n i) (shiftN n j)
  | 0 => rfl
  | n + 1 => by simp [shiftN, shiftN_add i j n, Idx.shift]

theorem shiftN_sub (i j : Idx) : ∀ n, shiftN n (.sub i j) = .sub (shiftN n i) (shiftN n j)
  | 0 => rfl
  | n + 1 => by simp [shiftN, shiftN_sub i j n, Idx.shift]

theorem shiftN_smul (a : Nat) (i : Idx) : ∀ n, shiftN n (.smul a i) = .smul a (shiftN n i)
  | 0 => rfl
  | n + 1 => by simp [shiftN, shiftN_smul a i n, Idx.shift]

/-- A term shifted past the closing depth closes to its value. -/
theorem clI_shiftN (ρ : Nat → Nat) {f n : Nat} (hn : f ≤ n) :
    ∀ u : Idx, clI ρ f (shiftN n u) = .lit (ev (fun m => ρ (m + n - f)) u)
  | .lit a => by simp [shiftN_lit, clI, ev]
  | .var m => by
      have : ¬ m + n < f := by omega
      simp [shiftN_var, clI, ev, this]
  | .add i j => by simp [shiftN_add, clI, ev, clI_shiftN ρ hn i, clI_shiftN ρ hn j, addF]
  | .sub i j => by simp [shiftN_sub, clI, ev, clI_shiftN ρ hn i, clI_shiftN ρ hn j, subF]
  | .smul a i => by simp [shiftN_smul, clI, ev, clI_shiftN ρ hn i, smulF]

section inst
variable {us : List Idx} {d0 : Nat} {ρ ρ' : Nat → Nat}
  (h1 : ∀ k, k < d0 → ρ' k = ρ k)
  (h2 : ∀ j u, us[j]? = some u → ρ' (d0 + j) = ev (fun k => ρ (k + d0)) u)
  (h3 : ∀ k, ρ' (d0 + us.length + k) = ρ (d0 + k))
include h1 h2 h3

theorem clI_instI (f : Nat) : ∀ i : Idx, clI ρ f (instI us (d0 + f) i) = clI ρ' f i
  | .lit n => rfl
  | .var k => by
      simp only [instI]
      by_cases hk : k < d0 + f
      · by_cases hf : k < f
        · simp [hk, hf, clI]
        · have := h1 (k - f) (by omega)
          simp [hk, hf, clI, this]
      · have hf : ¬ k < f := by omega
        cases hu : us[k - (d0 + f)]? with
        | some u =>
            have e := h2 _ u hu
            have ek : d0 + (k - (d0 + f)) = k - f := by omega
            rw [ek] at e
            simp only [hk, ↓reduceIte, hu, clI, hf, e]
            rw [clI_shiftN ρ (by omega)]
            congr 2; funext m; congr 1; omega
        | none =>
            have hl : us.length ≤ k - (d0 + f) := by simpa using hu
            have e := h3 (k - f - d0 - us.length)
            have ek : d0 + us.length + (k - f - d0 - us.length) = k - f := by omega
            have ek2 : d0 + (k - f - d0 - us.length) = k - us.length - f := by omega
            rw [ek, ek2] at e
            have hf2 : ¬ k - us.length < f := by omega
            simp [hk, hu, clI, hf, hf2, e]
  | .add i j => by simp only [instI, clI, clI_instI f i, clI_instI f j]
  | .sub i j => by simp only [instI, clI, clI_instI f i, clI_instI f j]
  | .smul n i => by simp only [instI, clI, clI_instI f i]

theorem clM_instM (f : Nat) (μ : Mode) : clM ρ f (instM us (d0 + f) μ) = clM ρ' f μ := by
  cases μ <;> simp [instM, clM, clI_instI h1 h2 h3 f]

theorem clP_instP (f : Nat) : ∀ ψ : Pred, clP ρ f (instP us (d0 + f) ψ) = clP ρ' f ψ
  | .tt => rfl
  | .le i j => by simp [instP, clP, clI_instI h1 h2 h3 f]
  | .eq i j => by simp [instP, clP, clI_instI h1 h2 h3 f]
  | .and p q => by simp [instP, clP, clP_instP f p, clP_instP f q]
  | .ini i => by simp [instP, clP, clI_instI h1 h2 h3 f]

theorem cl_instT (W : Nat → Ty) : ∀ (t : Ty) (e f : Nat), cl ρ W e f (instT us (d0 + f) t) = cl ρ' W e f t
  | .intS i, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .prod a b, e, f => by simp [instT, cl, cl_instT W a e f, cl_instT W b e f]
  | .sum a b, e, f => by simp [instT, cl, cl_instT W a e f, cl_instT W b e f]
  | .code a b, e, f => by simp [instT, cl, cl_instT W a e f, cl_instT W b e f]
  | .array i t, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f, cl_instT W t e f]
  | .ptr μ t, e, f => by simp [instT, cl, clM_instM h1 h2 h3 f, cl_instT W t e f]
  | .ptrOpt μ t, e, f => by simp [instT, cl, clM_instM h1 h2 h3 f, cl_instT W t e f]
  | .loc μ t, e, f => by simp [instT, cl, clM_instM h1 h2 h3 f, cl_instT W t e f]
  | .word r P, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .tok r i, e, f => by rcases i with _ | ⟨_, _⟩ <;> simp [instT, cl, clI_instI h1 h2 h3 f]
  | .word2 r P, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .tok2 r P i j, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .epair r P, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .tokE r P i, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .share r, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .cap s r, e, f => by simp [instT, cl, clI_instI h1 h2 h3 f]
  | .tvar k, e, f => by simp [instT, cl]
  | .mu t, e, f => by simp [instT, cl, cl_instT W t (e + 1) f]
  | .tex κ t, e, f => by simp [instT, cl, cl_instT W t (e + 1) f]
  | .iall t, e, f => by
      have := cl_instT W t e (f + 1)
      rw [← Nat.add_assoc] at this
      simp [instT, cl, this]
  | .iex t, e, f => by
      have := cl_instT W t e (f + 1)
      rw [← Nat.add_assoc] at this
      simp [instT, cl, this]
  | .refine t ψ, e, f => by simp [instT, cl, clP_instP h1 h2 h3 f, cl_instT W t e f]
  | .unit, _, _ => rfl
  | .void, _, _ => rfl
  | .int, _, _ => rfl
  | .fix _ _, _, _ => rfl
  | .lanes _ _, _, _ => rfl

end inst

/-! ## §5 `TyEqS` closes to equal types -/

theorem clI_ieq {cx : Cx} {d : Nat} {i j : Idx} (h : IEq cx d i j) {ρ : Nat → Nat}
    (hs : d = 0 → Sat cx.facts ρ) : clI ρ d i = clI ρ d j := by
  rcases h with rfl | ⟨rfl, hq⟩
  · rfl
  · rw [clI_zero, clI_zero, hq ρ (hs rfl)]

theorem clM_meq {cx : Cx} {d : Nat} {μ ν : Mode} (h : MEq cx d μ ν) {ρ : Nat → Nat}
    (hs : d = 0 → Sat cx.facts ρ) : clM ρ d μ = clM ρ d ν := by
  cases h with
  | own => rfl
  | pub => rfl
  | rgn h => simp [clM, clI_ieq h hs]

theorem cl_tyEq {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) :
    ∀ {ρ : Nat → Nat} (W : Nat → Ty) (e : Nat), (d = 0 → Sat cx.facts ρ) → cl ρ W e d t = cl ρ W e d u := by
  induction h with
  | refl => intros; rfl
  | intS h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | prod _ _ iha ihb => intro ρ W e hs; simp [cl, iha W e hs, ihb W e hs]
  | sum _ _ iha ihb => intro ρ W e hs; simp [cl, iha W e hs, ihb W e hs]
  | code _ _ iha ihb => intro ρ W e hs; simp [cl, iha W e hs, ihb W e hs]
  | array h _ ih => intro ρ W e hs; simp [cl, clI_ieq h hs, ih W e hs]
  | ptr h _ ih => intro ρ W e hs; simp [cl, clM_meq h hs, ih W e hs]
  | ptrOpt h _ ih => intro ρ W e hs; simp [cl, clM_meq h hs, ih W e hs]
  | loc h _ ih => intro ρ W e hs; simp [cl, clM_meq h hs, ih W e hs]
  | word h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | word2 h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | tok2 h h1 h2 => intro ρ W e hs; simp [cl, clI_ieq h hs, clI_ieq h1 hs, clI_ieq h2 hs]
  | epair h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | tokE h h1 => intro ρ W e hs; simp [cl, clI_ieq h hs, clI_ieq h1 hs]
  | tokNone h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | tokSome h h' => intro ρ W e hs; simp [cl, clI_ieq h hs, clI_ieq h' hs]
  | share h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | cap h => intro ρ W e hs; simp [cl, clI_ieq h hs]
  | mu _ ih => intro ρ W e hs; simp [cl, ih W (e + 1) hs]
  | tex _ ih => intro ρ W e hs; simp [cl, ih W (e + 1) hs]
  | iall _ ih => intro ρ W e _; simp [cl, ih W e (fun h => absurd h (Nat.succ_ne_zero _))]
  | iex _ ih => intro ρ W e _; simp [cl, ih W e (fun h => absurd h (Nat.succ_ne_zero _))]
  | refine _ ih => intro ρ W e hs; simp [cl, ih W e hs]
  | refineIni h _ ih => intro ρ W e hs; simp [cl, clP, clI_ieq h hs, ih W e hs]

/-! ## §6 Shifting by `n`, and closing a term shifted past the binders -/

/-- Shift index variables at or above `c` by `n`. -/
def sbIdx (n c : Nat) : Idx → Idx
  | .lit a    => .lit a
  | .var k    => if c ≤ k then .var (k + n) else .var k
  | .add i j  => .add (sbIdx n c i) (sbIdx n c j)
  | .sub i j  => .sub (sbIdx n c i) (sbIdx n c j)
  | .smul a i => .smul a (sbIdx n c i)

def sbM (n c : Nat) : Mode → Mode
  | .rgn r => .rgn (sbIdx n c r)
  | μ      => μ

def sbP (n c : Nat) : Pred → Pred
  | .tt      => .tt
  | .le i j  => .le (sbIdx n c i) (sbIdx n c j)
  | .eq i j  => .eq (sbIdx n c i) (sbIdx n c j)
  | .and p q => .and (sbP n c p) (sbP n c q)
  | .ini i   => .ini (sbIdx n c i)

/-- `Ty.shiftI`, by `n`. -/
def sbI (n c : Nat) : Ty → Ty
  | .intS i      => .intS (sbIdx n c i)
  | .prod a b    => .prod (sbI n c a) (sbI n c b)
  | .sum a b     => .sum (sbI n c a) (sbI n c b)
  | .code a b    => .code (sbI n c a) (sbI n c b)
  | .array i t   => .array (sbIdx n c i) (sbI n c t)
  | .ptr μ t     => .ptr (sbM n c μ) (sbI n c t)
  | .ptrOpt μ t  => .ptrOpt (sbM n c μ) (sbI n c t)
  | .loc μ t     => .loc (sbM n c μ) (sbI n c t)
  | .word r P    => .word (sbIdx n c r) P
  | .tok r st    => .tok (sbIdx n c r) (st.map fun (P, i) => (P, sbIdx n c i))
  | .word2 r P   => .word2 (sbIdx n c r) P
  | .tok2 r P i j => .tok2 (sbIdx n c r) P (sbIdx n c i) (sbIdx n c j)
  | .epair r P   => .epair (sbIdx n c r) P
  | .tokE r P e  => .tokE (sbIdx n c r) P (sbIdx n c e)
  | .share r     => .share (sbIdx n c r)
  | .cap s r     => .cap s (sbIdx n c r)
  | .mu t        => .mu (sbI n c t)
  | .tex κ t     => .tex κ (sbI n c t)
  | .iall t      => .iall (sbI n (c + 1) t)
  | .iex t       => .iex (sbI n (c + 1) t)
  | .refine t ψ  => .refine (sbI n c t) (sbP n c ψ)
  | t            => t

/-- `Ty.shiftT`, by `n`. -/
def sbT (n c : Nat) : Ty → Ty
  | .tvar k      => if c ≤ k then .tvar (k + n) else .tvar k
  | .prod a b    => .prod (sbT n c a) (sbT n c b)
  | .sum a b     => .sum (sbT n c a) (sbT n c b)
  | .code a b    => .code (sbT n c a) (sbT n c b)
  | .array i t   => .array i (sbT n c t)
  | .ptr μ t     => .ptr μ (sbT n c t)
  | .ptrOpt μ t  => .ptrOpt μ (sbT n c t)
  | .loc μ t     => .loc μ (sbT n c t)
  | .mu t        => .mu (sbT n (c + 1) t)
  | .tex κ t     => .tex κ (sbT n (c + 1) t)
  | .iall t      => .iall (sbT n c t)
  | .iex t       => .iex (sbT n c t)
  | .refine t ψ  => .refine (sbT n c t) ψ
  | t            => t

theorem sbIdx_zero (c : Nat) (i : Idx) : sbIdx 0 c i = i := by
  induction i <;> simp_all [sbIdx]

theorem sbIdx_succ (n c : Nat) (i : Idx) : (sbIdx n c i).shift c = sbIdx (n + 1) c i := by
  induction i with
  | var k =>
      by_cases h : c ≤ k
      · have h' : c ≤ k + n := by omega
        simp [sbIdx, Idx.shift, h, h', Nat.add_assoc]
      · simp [sbIdx, Idx.shift, h]
  | _ => simp_all [sbIdx, Idx.shift]

theorem sbM_zero (c : Nat) (μ : Mode) : sbM 0 c μ = μ := by
  cases μ <;> simp [sbM, sbIdx_zero]

theorem sbM_succ (n c : Nat) (μ : Mode) : (sbM n c μ).shift c = sbM (n + 1) c μ := by
  cases μ <;> simp [sbM, Mode.shift, sbIdx_succ]

theorem sbP_zero (c : Nat) (ψ : Pred) : sbP 0 c ψ = ψ := by
  induction ψ <;> simp_all [sbP, sbIdx_zero]

theorem sbP_succ (n c : Nat) (ψ : Pred) : (sbP n c ψ).shift c = sbP (n + 1) c ψ := by
  induction ψ <;> simp_all [sbP, Pred.shift, sbIdx_succ]

theorem sbI_zero (t : Ty) : ∀ c, sbI 0 c t = t := by
  induction t with
  | tok r i => intro c; rcases i with _ | ⟨_, _⟩ <;> simp [sbI, sbIdx_zero]
  | _ => intro c; simp_all [sbI, sbIdx_zero, sbM_zero, sbP_zero]

theorem sbI_succ (n : Nat) (t : Ty) : ∀ c, (sbI n c t).shiftI c = sbI (n + 1) c t := by
  induction t with
  | tok r i => intro c; rcases i with _ | ⟨_, _⟩ <;> simp [sbI, Ty.shiftI, sbIdx_succ]
  | _ => intro c; simp_all [sbI, Ty.shiftI, sbIdx_succ, sbM_succ, sbP_succ]

theorem sbT_zero (t : Ty) : ∀ c, sbT 0 c t = t := by
  induction t with
  | tvar k => intro c; simp [sbT]
  | _ => intro c; simp_all [sbT]

theorem sbT_succ (n : Nat) (t : Ty) : ∀ c, (sbT n c t).shiftT c = sbT (n + 1) c t := by
  induction t with
  | tvar k =>
      intro c
      by_cases h : c ≤ k
      · have h' : c ≤ k + n := by omega
        simp [sbT, Ty.shiftT, h, h', Nat.add_assoc]
      · simp [sbT, Ty.shiftT, h]
  | _ => intro c; simp_all [sbT, Ty.shiftT]

theorem shiftIN_eq (t : Ty) : ∀ n, shiftIN n t = sbI n 0 t
  | 0 => (sbI_zero t 0).symm
  | n + 1 => by simp only [shiftIN, shiftIN_eq t n, sbI_succ]

theorem shiftTN_eq (t : Ty) : ∀ n, shiftTN n t = sbT n 0 t
  | 0 => (sbT_zero t 0).symm
  | n + 1 => by simp only [shiftTN, shiftTN_eq t n, sbT_succ]

section shifted
variable {ρ : Nat → Nat} {n f : Nat}

theorem clI_sb (hf : f ≤ n) (f0 : Nat) :
    ∀ i : Idx, clI ρ (f0 + f) (sbIdx n f0 i) = clI (fun k => ρ (k + n - f)) f0 i
  | .lit a => rfl
  | .var k => by
      by_cases h : f0 ≤ k
      · have h1 : ¬ k + n < f0 + f := by omega
        have h2 : ¬ k < f0 := by omega
        have h3 : k + n - (f0 + f) = k - f0 + n - f := by omega
        simp [sbIdx, clI, h, h1, h2, h3]
      · have h1 : k < f0 + f := by omega
        have h2 : k < f0 := by omega
        simp [sbIdx, clI, h, h1, h2]
  | .add i j => by simp only [sbIdx, clI, clI_sb hf f0 i, clI_sb hf f0 j]
  | .sub i j => by simp only [sbIdx, clI, clI_sb hf f0 i, clI_sb hf f0 j]
  | .smul a i => by simp only [sbIdx, clI, clI_sb hf f0 i]

theorem clM_sb (hf : f ≤ n) (f0 : Nat) (μ : Mode) :
    clM ρ (f0 + f) (sbM n f0 μ) = clM (fun k => ρ (k + n - f)) f0 μ := by
  cases μ <;> simp [sbM, clM, clI_sb hf]

theorem clP_sb (hf : f ≤ n) (f0 : Nat) (ψ : Pred) :
    clP ρ (f0 + f) (sbP n f0 ψ) = clP (fun k => ρ (k + n - f)) f0 ψ := by
  induction ψ <;> simp_all [sbP, clP, clI_sb hf]

theorem cl_sbI (hf : f ≤ n) (W : Nat → Ty) (t : Ty) :
    ∀ e f0, cl ρ W e (f0 + f) (sbI n f0 t) = cl (fun k => ρ (k + n - f)) W e f0 t := by
  induction t with
  | tok r i => intro e f0; rcases i with _ | ⟨_, _⟩ <;> simp [sbI, cl, clI_sb hf]
  | iall t ih =>
      intro e f0
      have := ih e (f0 + 1)
      rw [Nat.add_right_comm] at this
      simp [sbI, cl, this]
  | iex t ih =>
      intro e f0
      have := ih e (f0 + 1)
      rw [Nat.add_right_comm] at this
      simp [sbI, cl, this]
  | _ => intro e f0; simp_all [sbI, cl, clI_sb hf, clM_sb hf, clP_sb hf]

end shifted

theorem cl_sbT {e n : Nat} (he : e ≤ n) (ρ : Nat → Nat) (W : Nat → Ty) (t : Ty) :
    ∀ e0 f, cl ρ W (e0 + e) f (sbT n e0 t) = cl ρ (fun k => W (k + n - e)) e0 f t := by
  induction t with
  | tvar k =>
      intro e0 f
      by_cases h : e0 ≤ k
      · have h1 : ¬ k + n < e0 + e := by omega
        have h2 : ¬ k < e0 := by omega
        have h3 : k + n - (e0 + e) = k - e0 + n - e := by omega
        simp [sbT, cl, h, h1, h2, h3]
      · have h1 : k < e0 + e := by omega
        have h2 : k < e0 := by omega
        simp [sbT, cl, h, h1, h2]
  | mu t ih =>
      intro e0 f
      have := ih (e0 + 1) f
      rw [Nat.add_right_comm] at this
      simp [sbT, cl, this]
  | tex κ t ih =>
      intro e0 f
      have := ih (e0 + 1) f
      rw [Nat.add_right_comm] at this
      simp [sbT, cl, this]
  | _ => intro e0 f; simp_all [sbT, cl]

/-- A type shifted past `n` index and `m` type binders closes, under `f ≤ n`
index and `e ≤ m` type binders, as the unshifted type does at depth 0 with the
outer valuation and witnesses. -/
theorem cl_shifted {n m e f : Nat} (hf : f ≤ n) (he : e ≤ m) (ρ : Nat → Nat) (W : Nat → Ty)
    (σ : Ty) : cl ρ W e f (shiftIN n (shiftTN m σ)) =
      cl (fun k => ρ (k + n - f)) (fun k => W (k + m - e)) 0 0 σ := by
  rw [shiftIN_eq, shiftTN_eq]
  have h1 := cl_sbI (ρ := ρ) hf W (sbT m 0 σ) e 0
  rw [Nat.zero_add] at h1
  rw [h1]
  have h2 := cl_sbT he (fun k => ρ (k + n - f)) W σ 0 0
  rw [Nat.zero_add] at h2
  exact h2

/-- Simultaneous type substitution is absorbed into the witness map. -/
theorem cl_substTs (σs : List Ty) (c d : Nat) {ρ : Nat → Nat} {W₀ W₁ : Nat → Ty}
    (hpre : ∀ k, k < c → W₁ k = W₀ k)
    (hsub : ∀ j σ, σs[j]? = some σ → W₁ (c + j) = cl (fun k => ρ (k + d)) (fun k => W₀ (k + c)) 0 0 σ)
    (hrest : ∀ k, W₁ (c + σs.length + k) = W₀ (c + k)) (t : Ty) :
    ∀ e f, cl ρ W₀ e f (substTs σs (c + e) (d + f) t) = cl ρ W₁ e f t := by
  induction t with
  | tvar k =>
      intro e f
      by_cases h1 : k < c + e
      · by_cases h2 : k < e
        · simp [substTs, cl, h1, h2]
        · simp [substTs, cl, h1, h2, hpre (k - e) (by omega)]
      · have h2 : ¬ k < e := by omega
        cases hs : σs[k - (c + e)]? with
        | some σ =>
            have e1 := hsub _ _ hs
            have e2 : c + (k - (c + e)) = k - e := by omega
            rw [e2] at e1
            have e3 := cl_shifted (n := d + f) (m := c + e) (Nat.le_add_left f d)
              (Nat.le_add_left e c) ρ W₀ σ
            have e4 : (fun k => ρ (k + (d + f) - f)) = (fun k => ρ (k + d)) := by
              funext k; congr 1; omega
            have e5 : (fun k => W₀ (k + (c + e) - e)) = (fun k => W₀ (k + c)) := by
              funext k; congr 1; omega
            rw [e4, e5] at e3
            simp [substTs, cl, h1, h2, hs, e3, e1]
        | none =>
            have hl : σs.length ≤ k - (c + e) := by
              simpa [List.getElem?_eq_none_iff] using hs
            have h3 : ¬ k - σs.length < e := by omega
            have e1 := hrest (k - e - c - σs.length)
            have e2 : c + σs.length + (k - e - c - σs.length) = k - e := by omega
            have e3 : c + (k - e - c - σs.length) = k - σs.length - e := by omega
            rw [e2, e3] at e1
            simp [substTs, cl, h1, h2, hs, h3, e1]
  | mu t ih =>
      intro e f
      have := ih (e + 1) f
      rw [← Nat.add_assoc] at this
      simp [substTs, cl, this]
  | tex κ t ih =>
      intro e f
      have := ih (e + 1) f
      rw [← Nat.add_assoc] at this
      simp [substTs, cl, this]
  | iall t ih =>
      intro e f
      have := ih e (f + 1)
      rw [← Nat.add_assoc] at this
      simp [substTs, cl, this]
  | iex t ih =>
      intro e f
      have := ih e (f + 1)
      rw [← Nat.add_assoc] at this
      simp [substTs, cl, this]
  | _ => intro e f; simp_all [substTs, cl]


/-! ## §7 Folding commutes with closing; closed types; composition -/

theorem clI_addF (ρ : Nat → Nat) (d : Nat) (x y : Idx) :
    clI ρ d (addF x y) = addF (clI ρ d x) (clI ρ d y) := by
  cases x <;> cases y <;> simp [addF, clI]

theorem clI_subF (ρ : Nat → Nat) (d : Nat) (x y : Idx) :
    clI ρ d (subF x y) = subF (clI ρ d x) (clI ρ d y) := by
  cases x <;> cases y <;> simp [subF, clI]

theorem clI_smulF (ρ : Nat → Nat) (d n : Nat) (x : Idx) :
    clI ρ d (smulF n x) = smulF n (clI ρ d x) := by
  cases x <;> simp [smulF, clI]

theorem ev_addF (ρ : Nat → Nat) (x y : Idx) : ev ρ (addF x y) = ev ρ x + ev ρ y := by
  cases x <;> cases y <;> simp [addF, ev]

theorem ev_subF (ρ : Nat → Nat) (x y : Idx) : ev ρ (subF x y) = ev ρ x - ev ρ y := by
  cases x <;> cases y <;> simp [subF, ev]

theorem ev_smulF (ρ : Nat → Nat) (n : Nat) (x : Idx) : ev ρ (smulF n x) = n * ev ρ x := by
  cases x <;> simp [smulF, ev]

/-- Evaluating a closed-at-`d` index term under a valuation that agrees below `d`. -/
theorem ev_clI {ρ ρ₀ ρ' : Nat → Nat} {d : Nat} (hρ : ∀ k, ρ (k + d) = ρ₀ k)
    (hρ' : ∀ k, k < d → ρ' k = ρ k) : ∀ i : Idx, ev ρ' (clI ρ₀ d i) = ev ρ i
  | .lit n => rfl
  | .var k => by
      by_cases h : k < d
      · simp [clI, ev, h, hρ' k h]
      · have e := hρ (k - d)
        rw [Nat.sub_add_cancel (by omega)] at e
        simp [clI, ev, h, e]
  | .add i j => by simp only [clI, ev_addF, ev, ev_clI hρ hρ' i, ev_clI hρ hρ' j]
  | .sub i j => by simp only [clI, ev_subF, ev, ev_clI hρ hρ' i, ev_clI hρ hρ' j]
  | .smul n i => by simp only [clI, ev_smulF, ev, ev_clI hρ hρ' i]

theorem tb_mono (t : Ty) : ∀ {c c' : Nat}, tb c t = true → c ≤ c' → tb c' t = true := by
  induction t with
  | tvar k => intro c c' h hc; simp [tb] at h ⊢; omega
  | mu t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h (by omega)
  | tex κ t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h (by omega)
  | prod a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hc, ihb h.2 hc⟩
  | sum a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hc, ihb h.2 hc⟩
  | code a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h ⊢; exact ⟨iha h.1 hc, ihb h.2 hc⟩
  | array _ t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | ptr _ t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | ptrOpt _ t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | loc _ t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | iall t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | iex t ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | refine t _ ih => intro c c' h hc; simp only [tb] at h ⊢; exact ih h hc
  | _ => intro c c' h hc; simp_all [tb]

theorem tb_shiftT (t : Ty) : ∀ {c c' : Nat}, tb c t = true → c ≤ c' → t.shiftT c' = t := by
  induction t with
  | tvar k => intro c c' h hc; simp [tb] at h; simp [Ty.shiftT]; omega
  | mu t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h (by omega : c + 1 ≤ c' + 1)]
  | tex κ t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h (by omega : c + 1 ≤ c' + 1)]
  | prod a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h; simp [Ty.shiftT, iha h.1 hc, ihb h.2 hc]
  | sum a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h; simp [Ty.shiftT, iha h.1 hc, ihb h.2 hc]
  | code a b iha ihb => intro c c' h hc; simp only [tb, Bool.and_eq_true] at h; simp [Ty.shiftT, iha h.1 hc, ihb h.2 hc]
  | array _ t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | ptr _ t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | ptrOpt _ t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | loc _ t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | iall t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | iex t ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | refine t _ ih => intro c c' h hc; simp only [tb] at h; simp [Ty.shiftT, ih h hc]
  | _ => intro c c' h hc; simp_all [tb, Ty.shiftT]

/-- A closed type: no free type variables, and fixed by every closing. -/
def Clo (s : Ty) : Prop := tb 0 s = true ∧ ∀ (ρ : Nat → Nat) (W : Nat → Ty) (e f : Nat), cl ρ W e f s = s

theorem Clo_void : Clo .void := ⟨rfl, fun _ _ _ _ => rfl⟩

theorem clI_idem {ρ ρ' : Nat → Nat} : ∀ (i : Idx) {d d' : Nat}, d ≤ d' →
    clI ρ' d' (clI ρ d i) = clI ρ d i
  | .lit n, _, _, _ => rfl
  | .var k, d, d', hd => by
      by_cases h : k < d
      · have h' : k < d' := by omega
        simp [clI, h, h']
      · simp [clI, h]
  | .add i j, _, _, hd => by simp only [clI, clI_addF, clI_idem i hd, clI_idem j hd]
  | .sub i j, _, _, hd => by simp only [clI, clI_subF, clI_idem i hd, clI_idem j hd]
  | .smul n i, _, _, hd => by simp only [clI, clI_smulF, clI_idem i hd]

theorem clM_idem {ρ ρ' : Nat → Nat} (μ : Mode) {d d' : Nat} (hd : d ≤ d') :
    clM ρ' d' (clM ρ d μ) = clM ρ d μ := by
  cases μ <;> simp [clM, clI_idem _ hd]

theorem clP_idem {ρ ρ' : Nat → Nat} (ψ : Pred) {d d' : Nat} (hd : d ≤ d') :
    clP ρ' d' (clP ρ d ψ) = clP ρ d ψ := by
  induction ψ <;> simp_all [clP, clI_idem _ hd]

/-- Closing a closure again, no shallower, changes nothing. -/
theorem cl_idem {ρ ρ' : Nat → Nat} {W W' : Nat → Ty} (hW : ∀ k, Clo (W k)) (t : Ty) :
    ∀ {c d c' d' : Nat}, c ≤ c' → d ≤ d' → cl ρ' W' c' d' (cl ρ W c d t) = cl ρ W c d t := by
  induction t with
  | tvar k =>
      intro c d c' d' hc hd
      by_cases h : k < c
      · have h' : k < c' := by omega
        simp [cl, h, h']
      · simp only [cl, h, ↓reduceIte]; exact (hW _).2 _ _ _ _
  | tok r i => intro c d c' d' hc hd; rcases i with _ | ⟨_, _⟩ <;> simp [cl, clI_idem _ hd]
  | mu t ih => intro c d c' d' hc hd; simp [cl, ih (by omega : c + 1 ≤ c' + 1) hd]
  | tex κ t ih => intro c d c' d' hc hd; simp [cl, ih (by omega : c + 1 ≤ c' + 1) hd]
  | iall t ih => intro c d c' d' hc hd; simp [cl, ih hc (by omega : d + 1 ≤ d' + 1)]
  | iex t ih => intro c d c' d' hc hd; simp [cl, ih hc (by omega : d + 1 ≤ d' + 1)]
  | _ => intro c d c' d' hc hd; simp_all [cl, clI_idem _ hd, clM_idem _ hd, clP_idem _ hd]

theorem tb_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, tb 0 (W k) = true) (t : Ty) :
    ∀ c d, tb c (cl ρ W c d t) = true := by
  induction t with
  | tvar k =>
      intro c d
      by_cases h : k < c
      · simp [cl, h, tb]
      · simp only [cl, h, ↓reduceIte]; exact tb_mono _ (hW _) (Nat.zero_le _)
  | tok r i => intro c d; rcases i with _ | ⟨_, _⟩ <;> simp [cl, tb]
  | _ => intro c d; simp_all [cl, tb]

/-- (T3c-5a) Closing keeps a type free of by-value arrays (`Ty.arrFree`) when
the witnesses are. -/
theorem arrFree_cl {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, (W k).arrFree = true) (t : Ty) :
    ∀ c d, t.arrFree = true → (cl ρ W c d t).arrFree = true := by
  induction t with
  | tvar k =>
      intro c d _
      by_cases h : k < c
      · simp [cl, h, Ty.arrFree]
      · simp only [cl, h, ↓reduceIte]; exact hW _
  | tok r i => intro c d _; rcases i with _ | ⟨_, _⟩ <;> simp [cl, Ty.arrFree]
  | _ => intro c d h; simp_all [cl, Ty.arrFree]

theorem Clo_cl {W : Nat → Ty} (hW : ∀ k, Clo (W k)) (ρ : Nat → Nat) (t : Ty) : Clo (cl ρ W 0 0 t) :=
  ⟨tb_cl (fun k => (hW k).1) t 0 0,
   fun _ _ e f => cl_idem hW t (Nat.zero_le e) (Nat.zero_le f)⟩

theorem clI_comp {ρ ρ' : Nat → Nat} {d : Nat} : ∀ (i : Idx) (f : Nat),
    clI ρ' f (clI ρ (d + f) i) = clI (fun k => if k < d then ρ' k else ρ (k - d)) f i
  | .lit n, _ => rfl
  | .var k, f => by
      by_cases h1 : k < f
      · have h2 : k < d + f := by omega
        simp [clI, h1, h2]
      · by_cases h2 : k < d + f
        · have h3 : k - f < d := by omega
          simp [clI, h1, h2, h3]
        · have h3 : ¬ k - f < d := by omega
          have h4 : k - (d + f) = k - f - d := by omega
          simp [clI, h1, h2, h3, h4]
  | .add i j, f => by simp only [clI, clI_addF, clI_comp i f, clI_comp j f]
  | .sub i j, f => by simp only [clI, clI_subF, clI_comp i f, clI_comp j f]
  | .smul n i, f => by simp only [clI, clI_smulF, clI_comp i f]

theorem clM_comp {ρ ρ' : Nat → Nat} {d : Nat} (μ : Mode) (f : Nat) :
    clM ρ' f (clM ρ (d + f) μ) = clM (fun k => if k < d then ρ' k else ρ (k - d)) f μ := by
  cases μ <;> simp [clM, clI_comp]

theorem clP_comp {ρ ρ' : Nat → Nat} {d : Nat} (ψ : Pred) (f : Nat) :
    clP ρ' f (clP ρ (d + f) ψ) = clP (fun k => if k < d then ρ' k else ρ (k - d)) f ψ := by
  induction ψ <;> simp_all [clP, clI_comp]

/-- **Composition.**  Closing, at depth `(e, f)`, a closure taken `c` type and
`d` index binders deeper, is one closure with the outer maps below `c`/`d`. -/
theorem cl_comp {ρ ρ' : Nat → Nat} {W W' : Nat → Ty} {c d : Nat} (hW : ∀ k, Clo (W k)) (t : Ty) :
    ∀ e f, cl ρ' W' e f (cl ρ W (c + e) (d + f) t) =
      cl (fun k => if k < d then ρ' k else ρ (k - d)) (fun k => if k < c then W' k else W (k - c)) e f t := by
  induction t with
  | tvar k =>
      intro e f
      by_cases h1 : k < e
      · have h2 : k < c + e := by omega
        simp [cl, h1, h2]
      · by_cases h2 : k < c + e
        · have h3 : k - e < c := by omega
          simp [cl, h1, h2, h3]
        · have h3 : ¬ k - e < c := by omega
          have h4 : k - (c + e) = k - e - c := by omega
          simp only [cl, h1, h2, h3, h4, ↓reduceIte]
          exact (hW _).2 _ _ _ _
  | tok r i => intro e f; rcases i with _ | ⟨_, _⟩ <;> simp [cl, clI_comp]
  | mu t ih =>
      intro e f; have := ih (e + 1) f; rw [← Nat.add_assoc] at this; simp [cl, this]
  | tex κ t ih =>
      intro e f; have := ih (e + 1) f; rw [← Nat.add_assoc] at this; simp [cl, this]
  | iall t ih =>
      intro e f; have := ih e (f + 1); rw [← Nat.add_assoc] at this; simp [cl, this]
  | iex t ih =>
      intro e f; have := ih e (f + 1); rw [← Nat.add_assoc] at this; simp [cl, this]
  | _ => intro e f; simp_all [cl, clI_comp, clM_comp, clP_comp]

/-! ## §8 Odds and ends: positive-depth `TyEqS`, well-formed types, `substT` -/

theorem TyEqS_pos {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) : 0 < d → t = u := by
  have hi : ∀ {d i j}, 0 < d → IEq cx d i j → i = j := by
    intro d i j hd h; rcases h with h | ⟨h, _⟩
    · exact h
    · omega
  have hm : ∀ {d μ ν}, 0 < d → MEq cx d μ ν → μ = ν := by
    intro d μ ν hd h; cases h with
    | own => rfl
    | pub => rfl
    | rgn h => rw [hi hd h]
  induction h with
  | refl => intro _; rfl
  | intS h => intro hd; rw [hi hd h]
  | array h _ ih => intro hd; rw [hi hd h, ih hd]
  | ptr h _ ih => intro hd; rw [hm hd h, ih hd]
  | ptrOpt h _ ih => intro hd; rw [hm hd h, ih hd]
  | loc h _ ih => intro hd; rw [hm hd h, ih hd]
  | word h => intro hd; rw [hi hd h]
  | word2 h => intro hd; rw [hi hd h]
  | tok2 h1 h2 h3 => intro hd; rw [hi hd h1, hi hd h2, hi hd h3]
  | epair h => intro hd; rw [hi hd h]
  | tokE h1 h2 => intro hd; rw [hi hd h1, hi hd h2]
  | tokNone h => intro hd; rw [hi hd h]
  | tokSome h1 h2 => intro hd; rw [hi hd h1, hi hd h2]
  | share h => intro hd; rw [hi hd h]
  | cap h => intro hd; rw [hi hd h]
  | iall _ ih => intro _; rw [ih (by omega)]
  | iex _ ih => intro _; rw [ih (by omega)]
  | refineIni h _ ih => intro hd; rw [hi hd h, ih hd]
  | _ => intro hd; simp_all

/-- `TyEqS` at any depth gives equal closures at index depth 0. -/
theorem cl_tyEq0 {cx : Cx} {d : Nat} {t u : Ty} (h : TyEqS cx d t u) {ρ : Nat → Nat} (W : Nat → Ty) (e : Nat)
    (hs : d = 0 → Sat cx.facts ρ) : cl ρ W e 0 t = cl ρ W e 0 u := by
  by_cases hd : d = 0
  · subst hd; exact cl_tyEq h W e hs
  · rw [TyEqS_pos h (by omega)]

theorem clI_wf (ρ ρ' : Nat → Nat) {d : Nat} : ∀ i : Idx, i.inScope d = true → clI ρ d i = clI ρ' d i
  | .lit _, _ => rfl
  | .var k, h => by simp [Idx.inScope] at h; simp [clI, h]
  | .add i j, h => by
      simp only [Idx.inScope, Bool.and_eq_true] at h; simp only [clI, clI_wf ρ ρ' i h.1, clI_wf ρ ρ' j h.2]
  | .sub i j, h => by
      simp only [Idx.inScope, Bool.and_eq_true] at h; simp only [clI, clI_wf ρ ρ' i h.1, clI_wf ρ ρ' j h.2]
  | .smul _ i, h => by simp only [Idx.inScope] at h; simp only [clI, clI_wf ρ ρ' i h]

/-- A type well-formed at `(c, d)` has no free variables to close. -/
theorem cl_wf {ρ ρ' : Nat → Nat} {W W' : Nat → Ty} (t : Ty) :
    ∀ {c d : Nat}, t.wf c d = true → cl ρ W c d t = cl ρ' W' c d t := by
  induction t with
  | tvar k => intro c d h; simp [Ty.wf] at h; simp [cl, h]
  | intS i => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' i h]
  | array i t ih =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h; simp [cl, clI_wf ρ ρ' i h.1, ih h.2]
  | ptr μ t ih =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      cases μ <;> simp_all [cl, clM, Mode.inScope, clI_wf ρ ρ']
  | ptrOpt μ t ih =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      cases μ <;> simp_all [cl, clM, Mode.inScope, clI_wf ρ ρ']
  | loc μ t ih =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      cases μ <;> simp_all [cl, clM, Mode.inScope, clI_wf ρ ρ']
  | word r P => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' r h]
  | tok r i =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      rcases i with _ | ⟨_, _⟩ <;> simp_all [cl, clI_wf ρ ρ']
  | word2 r P => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' r h]
  | tok2 r P i j =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      simp_all [cl, clI_wf ρ ρ']
  | epair r P => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' r h]
  | tokE r P i =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      simp_all [cl, clI_wf ρ ρ']
  | share r => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' r h]
  | cap s r => intro c d h; simp only [Ty.wf] at h; simp [cl, clI_wf ρ ρ' r h]
  | mu t ih => intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h; simp [cl, ih h.2]
  | tex κ t ih => intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h; simp [cl, ih h.2]
  | iall t ih => intro c d h; simp only [Ty.wf] at h; simp [cl, ih h]
  | iex t ih => intro c d h; simp only [Ty.wf] at h; simp [cl, ih h]
  | refine t ψ ih =>
      intro c d h; simp only [Ty.wf, Bool.and_eq_true] at h
      have hp : ∀ ψ : Pred, ψ.inScope d = true → clP ρ d ψ = clP ρ' d ψ := by
        intro ψ; induction ψ <;> simp_all [clP, Pred.inScope, clI_wf ρ ρ']
      simp [cl, ih h.2, hp ψ h.1]
  | _ => intro c d h; simp_all [cl, Ty.wf]

theorem shiftT_shiftI : ∀ (t : Ty) (c c' : Nat), (t.shiftI c').shiftT c = (t.shiftT c).shiftI c' := by
  intro t
  induction t with
  | tvar k => intro c c'; simp only [Ty.shiftT, Ty.shiftI]; split <;> rfl
  | _ => intro c c'; simp [Ty.shiftT, Ty.shiftI, *]

theorem shiftT_shiftIN (X : Ty) (c : Nat) : ∀ d : Nat, (shiftIN d X).shiftT c = shiftIN d (X.shiftT c)
  | 0 => rfl
  | d + 1 => by simp only [shiftIN, shiftT_shiftI, shiftT_shiftIN X c d]

/-- Single substitution is the one-element simultaneous one (as KindSound's). -/
theorem substT_eq (σ : Ty) : ∀ (t : Ty) (j d : Nat),
    Ty.substT j (shiftIN d (shiftTN j σ)) t = substTs [σ] j d t := by
  intro t
  induction t with
  | tvar k =>
      intro j d
      simp only [Ty.substT, substTs]
      rcases Nat.lt_trichotomy k j with hk | hk | hk
      · have e1 : (k == j) = false := beq_false_of_ne (by omega)
        simp [e1, hk, show ¬ k > j by omega]
      · subst hk; simp
      · have e1 : (k == j) = false := beq_false_of_ne (by omega)
        have e2 : [σ][k - j]? = none := List.getElem?_eq_none_iff.mpr (by simp; omega)
        simp [e1, hk, e2, show ¬ k < j by omega]
  | mu t ih =>
      intro j d; simp only [Ty.substT, substTs, shiftT_shiftIN]; rw [← ih (j + 1) d]; rfl
  | tex κ t ih =>
      intro j d; simp only [Ty.substT, substTs, shiftT_shiftIN]; rw [← ih (j + 1) d]; rfl
  | iall t ih => intro j d; simp only [Ty.substT, substTs]; rw [← ih j (d + 1)]; rfl
  | iex t ih => intro j d; simp only [Ty.substT, substTs]; rw [← ih j (d + 1)]; rfl
  | _ => intro j d; simp [Ty.substT, substTs, *]


end TermClose

#print axioms TermClose.cl_shiftI
#print axioms TermClose.cl_shiftT
#print axioms TermClose.cl_instT
#print axioms TermClose.cl_tyEq
#print axioms TermClose.cl_shifted
#print axioms TermClose.cl_substTs
