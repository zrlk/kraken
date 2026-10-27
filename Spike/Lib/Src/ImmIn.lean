import Scc.Lower.Spec2
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.Form

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (B BState Env LitV shapeOf simpleTy litAt opLit litWalk2 lowerOp evalAt evalOne lookupV one
  needSome words prodOf)
open Spike.Lib.Form (WordPl)

/-! ## Results of builder steps -/

/-- Every successful run of `m` returns a value with `Q`. -/
def Post {α : Type} (m : B α) (Q : α → Prop) : Prop := ∀ s a s', m s = .ok (a, s') → Q a

theorem Post.bind {α β : Type} {m : B α} {f : α → B β} {P : α → Prop} {Q : β → Prop}
    (hm : Post m P) (hf : ∀ a, P a → Post (f a) Q) : Post (m >>= f) Q := by
  intro s b s'' h
  rcases hs : m s with e | ⟨a, s'⟩
  · rw [bind_error hs] at h; cases h
  · rw [Scc.Lower.Inv.bind_ok hs] at h; exact hf a (hm s a s' hs) s' b s'' h

theorem Post.bind' {α β : Type} {m : B α} {f : α → B β} {Q : β → Prop}
    (hf : ∀ a, Post (f a) Q) : Post (m >>= f) Q :=
  Post.bind (P := fun _ => True) (fun _ _ _ _ => trivial) fun a _ => hf a

theorem Post.pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Post (Pure.pure a : B α) Q := by
  intro s b s' hm
  have e : (Pure.pure a : B α) s = .ok (a, s) := rfl
  rw [e] at hm; cases hm; exact h

theorem Post.throw {α : Type} {e : String} {Q : α → Prop} : Post (MonadExcept.throw e : B α) Q := by
  intro s b s' hm
  have e' : (MonadExcept.throw e : B α) s = (Except.error e : Except String (α × BState)) := rfl
  rw [e'] at hm; cases hm

theorem Post.mono {α : Type} {m : B α} {P Q : α → Prop} (h : Post m P) (hPQ : ∀ a, P a → Q a) : Post m Q :=
  fun s a s' hm => hPQ a (h s a s' hm)

theorem Post.and {α : Type} {m : B α} {P Q : α → Prop} (hP : Post m P) (hQ : Post m Q) :
    Post m fun a => P a ∧ Q a :=
  fun s a s' hm => ⟨hP s a s' hm, hQ s a s' hm⟩

theorem Post.mapM {α β : Type} (xs : List α) {f : α → B β} {P : β → Prop} (hf : ∀ a, Post (f a) P) :
    Post (xs.mapM f) fun bs => bs.length = xs.length ∧ ∀ b ∈ bs, P b := by
  induction xs with
  | nil => exact Post.pure ⟨rfl, by simp⟩
  | cons x xs ih =>
    rw [List.mapM_cons]
    exact Post.bind (hf x) fun b hb => Post.bind ih fun bs ⟨h1, h2⟩ =>
      Post.pure ⟨by simp [h1], fun c hc => by
        rcases List.mem_cons.1 hc with rfl | hc
        · exact hb
        · exact h2 c hc⟩

/-- `runB` returns a result of a successful run. -/
theorem post_runB {α : Type} {m : B α} {Q : α → Prop} (h : Post m Q) {n : Nat} {a : α} {n' : Nat}
    (hr : runB m n = some (a, n')) : Q a := by
  unfold runB at hr
  split at hr
  · rename_i b s hm
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact h _ _ _ hm
  · cases hr

theorem post_needSome {α : Type} (o : Option α) (msg : String) : Post (needSome o msg) fun a => o = some a := by
  unfold needSome
  cases o
  · exact Post.throw
  · exact Post.pure rfl

theorem post_words (t : Ty) : Post (words t) fun k => Scc.Obj.valWords t = some k := by
  unfold words
  split
  · rename_i n h; exact Post.pure h
  · exact Post.throw

theorem post_lookupV (env : Env) (x : String) :
    Post (lookupV env x) fun r => ∃ b, env.find? (·.1 == x) = some b ∧ r = (b.2.1, b.2.2) := by
  unfold lookupV
  split
  · rename_i b t ws h; exact Post.pure ⟨_, h, rfl⟩
  · exact Post.throw

theorem post_one (ws : List Operand) (what : String) : Post (one ws what) fun o => ws = [o] := by
  unfold one
  split
  · exact Post.pure rfl
  · exact Post.throw

/-- A step that returns a register. -/
def IsReg (o : Operand) : Prop := ∃ r, o = .reg r

theorem post_loadAt (o : Order) (as : List Addr) (hint : String) :
    Post (Scc.Lower.loadAt o as hint) fun ws => ws.length = as.length ∧ ∀ w ∈ ws, IsReg w := by
  unfold Scc.Lower.loadAt
  exact Post.mapM (P := IsReg) as fun _ => Post.bind' fun _ => Post.bind' fun _ => Post.pure ⟨_, rfl⟩

theorem post_cellAddrs (o : Scc.ObjLayout) (base off : Operand) (u : Ty) :
    Post (Scc.Lower.cellAddrs o base off u) fun as => ∃ sl, Scc.Obj.slots u 0 0 = some sl ∧ as.length = sl.length := by
  unfold Scc.Lower.cellAddrs
  refine Post.bind (post_needSome _ _) fun sl hsl => Post.bind' fun b => ?_
  dsimp only
  repeat' first
    | exact Post.pure ⟨sl, hsl, by simp⟩
    | refine Post.bind' fun _ => ?_
    | split

/-! ## Layouts against the lowering's words -/

/-- Per runtime word of a value of layout `L`: `some o`, a one-word source
word with literal `o`; `none`, a word of a locative. -/
def flatL : LitV → List (Option (Option Nat))
  | .nil => []
  | .leaf o => [some o]
  | .loc => [none, none]
  | .node l r => flatL l ++ flatL r

/-- **Type `t`'s runtime layout has the shape of `L`** (as `Scc.Obj.slots`
and `Form.grp`: no word for `Unit`, one for a scalar or a pointer, two for a
locative). -/
def Compat : Ty → LitV → Bool
  | .unit, .nil | .void, .nil => true
  | .int, .leaf _ | .intS _, .leaf _ | .fix _ _, .leaf _ | .lanes _ _, .leaf _ | .ptr _ _, .leaf _ => true
  | .loc _ _, .loc => true
  | .prod a b, .node l r => Compat a l && Compat b r
  | .refine t _, L | .iall t, L | .mu t, L => Compat t L
  | .iex b, L => !Scc.Obj.coupledPair (.iex b) && Compat b L
  | .tex k b, L => !Scc.Obj.coupledPair (.tex k b) && Compat b L
  | _, _ => false

/-- The words agree with the layout's literals: a word that is an immediate
at a one-word source word with a literal is that literal. -/
def AgreeW : List Operand → List (Option (Option Nat)) → Prop
  | [], [] => True
  | w :: ws, f :: fs => (∀ v o, w = .imm v → f = some o → o = some v.toNat) ∧ AgreeW ws fs
  | _, _ => False

/-- **A binding of the lowering against the walk's layout**: type `t`,
words `ws`, layout `L`. -/
def Inv (t : Ty) (ws : List Operand) (L : LitV) : Prop := Compat t L = true ∧ AgreeW ws (flatL L)

theorem AgreeW.length : ∀ {ws : List Operand} {fs : List (Option (Option Nat))}, AgreeW ws fs →
    ws.length = fs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [h.2.length]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem AgreeW.append : ∀ {a c : List Operand} {b d : List (Option (Option Nat))}, AgreeW a b → AgreeW c d →
    AgreeW (a ++ c) (b ++ d)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, h.2.append h'⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

theorem AgreeW.take_drop : ∀ {ws : List Operand} {c d : List (Option (Option Nat))}, AgreeW ws (c ++ d) →
    AgreeW (ws.take c.length) c ∧ AgreeW (ws.drop c.length) d
  | ws, [], d, h => ⟨by cases ws <;> trivial, by simpa using h⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, _ :: _, _, h => by
    obtain ⟨h1, h2⟩ := AgreeW.take_drop h.2
    exact ⟨⟨h.1, h1⟩, h2⟩

theorem agreeW_regs : ∀ {ws : List Operand} {fs : List (Option (Option Nat))}, (∀ w ∈ ws, IsReg w) →
    ws.length = fs.length → AgreeW ws fs
  | [], [], _, _ => trivial
  | w :: ws, f :: fs, h, hl => by
    refine ⟨fun v o hw _ => ?_, agreeW_regs (fun w hw => h w (List.mem_cons_of_mem _ hw)) (by simpa using hl)⟩
    obtain ⟨r, hr⟩ := h w (List.mem_cons_self ..)
    rw [hr] at hw; cases hw
  | [], _ :: _, _, hl => by simp at hl
  | _ :: _, [], _, hl => by simp at hl

theorem compat_erase : ∀ (t : Ty) (L : LitV), Compat t L.erase = Compat t L := by
  intro t
  induction t with
  | prod a b iha ihb => intro L; cases L <;> simp [Compat, LitV.erase, iha, ihb]
  | refine t _ ih => intro L; simp [Compat, ih]
  | iall t ih => intro L; simp [Compat, ih]
  | mu t ih => intro L; simp [Compat, ih]
  | iex b ih => intro L; simp [Compat, ih]
  | tex k b ih => intro L; simp [Compat, ih]
  | _ => intro L; cases L <;> rfl

theorem compat_shapeOf : ∀ (t : Ty) (s r : Nat), simpleTy t = true → (Scc.Obj.slots t s r).isSome = true →
    Compat t (shapeOf t) = true := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro s r ht hs
    simp only [simpleTy, Bool.and_eq_true] at ht
    simp only [Scc.Obj.slots] at hs
    rcases ha : Scc.Obj.slots a s r with _ | la
    · simp [ha] at hs
    · rcases hb : Scc.Obj.slots b (s + la.countP (!·.1)) (r + la.countP (·.1)) with _ | lb
      · simp [ha, hb] at hs
      · simp [Compat, shapeOf, iha s r ht.1 (by simp [ha]),
          ihb (s + la.countP (!·.1)) (r + la.countP (·.1)) ht.2 (by simp [hb])]
  | refine t _ ih => intro s r ht hs; exact ih s r ht hs
  | iex b ih =>
    intro s r ht hs
    simp only [Scc.Obj.slots] at hs
    split at hs
    · simp at hs
    · rename_i hc
      simp only [Compat, shapeOf, Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨by simpa using hc, ih s r ht hs⟩
  | _ => intro s r ht hs; first | rfl | simp [simpleTy] at ht

theorem slots_compat : ∀ (t : Ty) (L : LitV), Compat t L = true → ∀ s r, ∃ sl, Scc.Obj.slots t s r = some sl ∧
    sl.length = (flatL L).length := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L hc s r
    cases L <;> simp only [Compat, Bool.and_eq_true, reduceCtorEq] at hc
    rename_i l rr
    obtain ⟨la, hla, hl⟩ := iha l hc.1 s r
    obtain ⟨lb, hlb, hl'⟩ := ihb rr hc.2 (s + la.countP (!·.1)) (r + la.countP (·.1))
    exact ⟨la ++ lb, by simp [Scc.Obj.slots, hla, hlb], by simp [flatL, hl, hl']⟩
  | refine t _ ih => intro L hc s r; exact ih L hc s r
  | iall t ih => intro L hc s r; exact ih L hc s r
  | mu t ih => intro L hc s r; exact ih L hc s r
  | iex b ih =>
    intro L hc s r
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨sl, h1, h2⟩ := ih L hc.2 s r
    exact ⟨sl, by simp [Scc.Obj.slots, hc.1, h1], h2⟩
  | tex k b ih =>
    intro L hc s r
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨sl, h1, h2⟩ := ih L hc.2 s r
    exact ⟨sl, by simp [Scc.Obj.slots, hc.1, h1], h2⟩
  | _ => intro L hc s r; cases L <;> simp [Compat] at hc <;> exact ⟨_, rfl, rfl⟩

theorem valWords_compat {t : Ty} {L : LitV} (hc : Compat t L = true) :
    Scc.Obj.valWords t = some (flatL L).length := by
  obtain ⟨sl, h1, h2⟩ := slots_compat t L hc 0 0
  simp [Scc.Obj.valWords, h1, h2]

theorem compat_prodOf : ∀ {t u w : Ty} {L : LitV}, prodOf t = some (u, w) → Compat t L = true →
    ∃ l r, L = .node l r ∧ Compat u l = true ∧ Compat w r = true := by
  intro t
  induction t with
  | prod a b _ _ =>
    intro u w L hp hc
    simp only [prodOf, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    cases L <;> simp only [Compat, Bool.and_eq_true, reduceCtorEq] at hc
    exact ⟨_, _, rfl, hc.1, hc.2⟩
  | refine t _ ih => intro u w L hp hc; exact ih hp hc
  | _ => intro u w L hp; simp [prodOf] at hp

/-- **The placements of a value against its layout**: where `Form.grp`
places a one-word immediate, the layout's word is that literal. -/
theorem grp_nil {t : Ty} (hg : ∀ rest, Spike.Lib.Form.grp t rest = some ([], rest)) {pre rest : List Operand}
    (hw : AgreeW pre (flatL .nil)) : ∃ pls : List WordPl,
      Spike.Lib.Form.grp t (pre ++ rest) = some (pls, rest) ∧ pls.length = LitV.nil.words.length ∧
      ∀ (k : Nat) (v : UInt64), pls[k]? = some (WordPl.one (.imm v)) →
        LitV.nil.words[k]? = some (some v.toNat) := by
  match pre, hw with
  | [], _ => exact ⟨[], hg rest, rfl, by simp⟩

theorem grp_leaf {t : Ty} (hg : ∀ w rest, Spike.Lib.Form.grp t (w :: rest) = some ([.one w], rest)) {o : Option Nat}
    {pre rest : List Operand} (hw : AgreeW pre (flatL (.leaf o))) : ∃ pls : List WordPl,
      Spike.Lib.Form.grp t (pre ++ rest) = some (pls, rest) ∧ pls.length = (LitV.leaf o).words.length ∧
      ∀ (k : Nat) (v : UInt64), pls[k]? = some (WordPl.one (.imm v)) →
        (LitV.leaf o).words[k]? = some (some v.toNat) := by
  match pre, hw with
  | [w], hw =>
    refine ⟨[.one w], hg w rest, rfl, ?_⟩
    intro k v hk
    match k, hk with
    | 0, hk =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Spike.Lib.Form.WordPl.one.injEq] at hk
      simp only [LitV.words, List.getElem?_cons_zero, Option.some.injEq]
      exact hw.1 v _ hk rfl

theorem grp_loc {t : Ty} (hg : ∀ b o rest, Spike.Lib.Form.grp t (b :: o :: rest) = some ([.loc b o], rest))
    {pre rest : List Operand} (hw : AgreeW pre (flatL .loc)) : ∃ pls : List WordPl,
      Spike.Lib.Form.grp t (pre ++ rest) = some (pls, rest) ∧ pls.length = LitV.loc.words.length ∧
      ∀ (k : Nat) (v : UInt64), pls[k]? = some (WordPl.one (.imm v)) →
        LitV.loc.words[k]? = some (some v.toNat) := by
  match pre, hw with
  | [b, o], _ =>
    refine ⟨[.loc b o], hg b o rest, rfl, ?_⟩
    intro k v hk
    match k, hk with
    | 0, hk => simp at hk

theorem grp_compat : ∀ (t : Ty) (L : LitV) (pre rest : List Operand), Compat t L = true → AgreeW pre (flatL L) →
    ∃ pls : List WordPl, Spike.Lib.Form.grp t (pre ++ rest) = some (pls, rest) ∧ pls.length = L.words.length ∧
      ∀ (k : Nat) (v : UInt64), pls[k]? = some (WordPl.one (.imm v)) →
        L.words[k]? = some (some v.toNat) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro L pre rest hc hw
    cases L <;> simp only [Compat, Bool.and_eq_true, reduceCtorEq] at hc
    rename_i l r
    obtain ⟨h1, h2⟩ := AgreeW.take_drop hw
    obtain ⟨p1, hp1, hl1, hk1⟩ := iha l (pre.take (flatL l).length) (pre.drop (flatL l).length ++ rest) hc.1 h1
    obtain ⟨p2, hp2, hl2, hk2⟩ := ihb r (pre.drop (flatL l).length) rest hc.2 h2
    refine ⟨p1 ++ p2, ?_, by simp [LitV.words, hl1, hl2], ?_⟩
    · have : pre ++ rest = pre.take (flatL l).length ++ (pre.drop (flatL l).length ++ rest) := by
        rw [← List.append_assoc, List.take_append_drop]
      rw [this]
      simp [Spike.Lib.Form.grp, hp1, hp2]
    · intro k v hk
      simp only [LitV.words]
      by_cases hlt : k < p1.length
      · rw [List.getElem?_append_left hlt] at hk
        rw [List.getElem?_append_left (by omega)]
        exact hk1 k v hk
      · rw [List.getElem?_append_right (by omega)] at hk
        rw [List.getElem?_append_right (by omega), ← hl1]
        exact hk2 _ v hk
  | refine t _ ih => intro L pre rest hc hw; simpa [Spike.Lib.Form.grp] using ih L pre rest hc hw
  | iall t ih => intro L pre rest hc hw; simpa [Spike.Lib.Form.grp] using ih L pre rest hc hw
  | mu t ih => intro L pre rest hc hw; simpa [Spike.Lib.Form.grp] using ih L pre rest hc hw
  | iex b ih =>
    intro L pre rest hc hw
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨pls, h1, h2, h3⟩ := ih L pre rest hc.2 hw
    exact ⟨pls, by simp [Spike.Lib.Form.grp, hc.1, h1], h2, h3⟩
  | tex k b ih =>
    intro L pre rest hc hw
    simp only [Compat, Bool.and_eq_true, Bool.not_eq_true'] at hc
    obtain ⟨pls, h1, h2, h3⟩ := ih L pre rest hc.2 hw
    exact ⟨pls, by simp [Spike.Lib.Form.grp, hc.1, h1], h2, h3⟩
  | _ =>
    intro L pre rest hc hw
    cases L <;> simp [Compat] at hc
    all_goals first
      | exact grp_nil (fun _ => rfl) hw
      | exact grp_leaf (fun _ _ => rfl) hw
      | exact grp_loc (fun _ _ _ => rfl) hw

/-- **`group`'s one-word immediates are the layout's literals.** -/
theorem group_inv {t : Ty} {ws : List Operand} {L : LitV} (h : Inv t ws L) {pls : List Spike.Lib.Form.WordPl}
    (hg : Spike.Lib.Form.group t ws = some pls) {k : Nat} {v : UInt64} (hk : pls[k]? = some (.one (.imm v))) :
    L.words[k]? = some (some v.toNat) := by
  obtain ⟨pls', h1, -, h3⟩ := grp_compat t L ws [] h.1 h.2
  simp only [List.append_nil] at h1
  simp only [Spike.Lib.Form.group, h1, Option.some.injEq] at hg
  subst hg
  exact h3 k v hk

end Spike.Lib.LowerNode
