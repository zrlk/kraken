import WeakCore.TermInterf
import WeakCore.TermOwnHeldQ
namespace TermBox
open CoreLang CoreTerm TermRun TermSound TermMem TermStep TermCut TermSys TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (E2) The global environment with the zero-word box at `l`: a published unit cell, no owner, frontier `0`. -/
def EgB (Eg : GEnv) (l : AllocLabel) : GEnv :=
  { Eg with
    sto := fun x => if x = l then some ⟨.unit, none⟩ else Eg.sto x
    pfr := fun x => if x = l then some 0 else Eg.pfr x
    pubd := fun x => x = l ∨ Eg.pubd x }

/-- The box label is fresh in `Eg` and unused in memory. -/
structure BoxFresh (Eg : GEnv) (mem : Memory) (l : AllocLabel) : Prop where
  sto : Eg.sto l = none
  box : Eg.box l = none
  pfr : Eg.pfr l = none
  ini : Eg.ini l = 0
  rini : Eg.rini l = 0
  msg : ∀ (t : Nat) (m : Msg), mem[t]? = some m → m.loc.label ≠ l

variable {Eg : GEnv} {mem : Memory} {l : AllocLabel}

@[simp] theorem EgB_sto_self : (EgB Eg l).sto l = some ⟨.unit, none⟩ := by simp [EgB]
@[simp] theorem EgB_pfr_self : (EgB Eg l).pfr l = some 0 := by simp [EgB]
theorem EgB_sto_ne {x : AllocLabel} (h : x ≠ l) : (EgB Eg l).sto x = Eg.sto x := by simp [EgB, h]
theorem EgB_pfr_ne {x : AllocLabel} (h : x ≠ l) : (EgB Eg l).pfr x = Eg.pfr x := by simp [EgB, h]

theorem cutSto_EgB_ne {j : Nat} {x : AllocLabel} (h : x ≠ l) : cutSto (EgB Eg l) j x = cutSto Eg j x := by
  unfold cutSto
  split <;> split <;> simp_all [GEnv.InCut, GEnv.Shared, EgB]
  all_goals
    rename_i h1 h2
    obtain ⟨c, hc, ho⟩ := h2
    rcases ho with ho | ⟨f, hf⟩
    · exact absurd ho (h1 c hc).1
    · exact absurd hf ((h1 c hc).2 f)

theorem cutSto_EgB_self {j : Nat} : cutSto (EgB Eg l) j l = some ⟨.unit, none⟩ := by
  unfold cutSto GEnv.InCut GEnv.Shared
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨_, EgB_sto_self, Or.inr ⟨0, EgB_pfr_self⟩⟩), EgB_sto_self]

theorem cutSto_fresh (hf : BoxFresh Eg mem l) {j : Nat} : cutSto Eg j l = none := by
  unfold cutSto
  split <;> simp [hf.sto]


/-- A thread environment with the box at `l` (a published unit cell, frontier `0`). -/
def boxE (E : TEnv) (l : AllocLabel) : TEnv :=
  { E with sto := fun x => if x = l then some ⟨.unit, none⟩ else E.sto x,
           pfr := fun x => if x = l then some 0 else E.pfr x }

theorem cut_EgB (j : Nat) (S : AllocLabel → Prop) : Cut (EgB Eg l) j S = boxE (Cut Eg j S) l := by
  unfold Cut boxE
  congr 1
  · funext x
    by_cases e : x = l
    · subst e; rw [cutSto_EgB_self]; simp
    · rw [cutSto_EgB_ne e]; simp [e]

theorem incl_box (hf : BoxFresh Eg mem l) (j : Nat) (S : AllocLabel → Prop) :
    Incl (Cut Eg j S) (Cut (EgB Eg l) j S) where
  prog := rfl
  sto := fun x c h => by
    by_cases e : x = l
    · subst e; rw [Cut_sto, cutSto_fresh hf] at h; cases h
    · rw [Cut_sto, cutSto_EgB_ne e]; exact h
  ini := fun _ => Nat.le_refl _
  pfr := fun x f h => by
    by_cases e : x = l
    · subst e; simp [hf.pfr] at h
    · simp only [Cut_pfr] at h ⊢; rw [EgB_pfr_ne e]; exact h
  box := fun _ _ h => h
  rini := fun _ => Nat.le_refl _

theorem thInvRE_box (hf : BoxFresh Eg mem l) {p : Prog} {j : Nat} {S : AllocLabel → Prop} {th : TTh} {T : Res}
    (h : ThInvRE p (Cut Eg j S) th T) : ThInvRE p (Cut (EgB Eg l) j S) th T :=
  ThInvRE_incl (E := Cut Eg j S) (CE_Cut _ _ _) rfl rfl (incl_box hf j S) (fun _ h => h) h

theorem thInvE_box (hf : BoxFresh Eg mem l) {p : Prog} {j : Nat} {S : AllocLabel → Prop} {th : TTh}
    (h : ThInvE p (Cut Eg j S) th) : ThInvE p (Cut (EgB Eg l) j S) th :=
  ThInvE_incl (E := Cut Eg j S) (CE_Cut _ _ _) rfl rfl (incl_box hf j S) (fun _ h => h) h

end TermBox

/-! (hygiene) axiom reports. -/
#print axioms TermBox.EgB_sto_ne
#print axioms TermBox.EgB_pfr_ne
#print axioms TermBox.cutSto_EgB_ne
#print axioms TermBox.cutSto_EgB_self
#print axioms TermBox.cutSto_fresh
#print axioms TermBox.cut_EgB
#print axioms TermBox.incl_box
#print axioms TermBox.thInvRE_box
#print axioms TermBox.thInvE_box
