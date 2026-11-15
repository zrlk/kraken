import WeakCore.CoreTyping
import WeakCore.TermCut
import WeakCore.TermScope
/-! # TermSpawnKidI — noOwnIn/noOR facts for the environment type of a thread started by `spawnI`. -/
open CoreLang CoreTerm CoreTyping

namespace TermSpawnI

theorem noOwnIn_tyEqS {cx : Cx} {d : Nat} {a b : Ty} (h : TyEqS cx d a b) :
    ∀ ke : KEnv, Ty.noOwnIn ke a = Ty.noOwnIn ke b := by
  induction h with
  | ptr hm _ ih => intro ke; cases hm <;> simp [Ty.noOwnIn, ih]
  | ptrOpt hm _ ih => intro ke; cases hm <;> simp [Ty.noOwnIn, ih]
  | loc hm _ ih => intro ke; cases hm <;> simp [Ty.noOwnIn, ih]
  | _ => intro ke; simp_all [Ty.noOwnIn]

theorem noOwnIn_subS {cx : Cx} {a b : Ty} (h : SubS cx a b) :
    ∀ ke : KEnv, Ty.noOwnIn ke a = true → Ty.noOwnIn ke b = true := by
  induction h with
  | eq h => intro ke ha; rw [← noOwnIn_tyEqS h ke]; exact ha
  | refine _ ih => intro ke ha; exact ih ke (by simpa [Ty.noOwnIn] using ha)
  | iniWeak h _ => intro ke ha; simpa [Ty.noOwnIn, noOwnIn_tyEqS h ke] using ha
  | nonNull hm h =>
      intro ke ha; cases hm <;> simp_all [Ty.noOwnIn, noOwnIn_tyEqS h ke]
  | prod _ _ iha ihb => intro ke ha; simp only [Ty.noOwnIn, Bool.and_eq_true] at ha ⊢; exact ⟨iha ke ha.1, ihb ke ha.2⟩
  | sum _ _ iha ihb => intro ke ha; simp only [Ty.noOwnIn, Bool.and_eq_true] at ha ⊢; exact ⟨iha ke ha.1, ihb ke ha.2⟩
  | _ => intro ke _; simp [Ty.noOwnIn]

theorem substTs_nil : ∀ (t : Ty) (c d : Nat), substTs [] c d t = t := by
  intro t
  induction t with
  | tvar k => intro c d; simp only [substTs]; split <;> simp
  | _ => intro c d; simp_all [substTs]

theorem noOwnIn_substTs_instT (σs : List Ty) (us : List Idx) :
    ∀ (A : Ty) (ke : KEnv) (c d e : Nat),
      Ty.noOwnIn ke (substTs σs c d (instT us e A)) = Ty.noOwnIn ke (substTs σs c d A) := by
  intro A
  induction A with
  | ptr μ t ih => intro ke c d e; cases μ <;> simp [instT, instM, substTs, Ty.noOwnIn, ih]
  | ptrOpt μ t ih => intro ke c d e; cases μ <;> simp [instT, instM, substTs, Ty.noOwnIn, ih]
  | loc μ t ih => intro ke c d e; cases μ <;> simp [instT, instM, substTs, Ty.noOwnIn, ih]
  | _ => intro ke c d e; simp_all [instT, substTs, Ty.noOwnIn]

end TermSpawnI
#print axioms TermSpawnI.noOwnIn_tyEqS
#print axioms TermSpawnI.noOwnIn_subS
#print axioms TermSpawnI.substTs_nil
#print axioms TermSpawnI.noOwnIn_substTs_instT


namespace TermSpawnI

theorem instantiate_fst {cx : Cx} {d : Decl} {is : List String} {ts : List Ty} {at_ rt : Ty}
    (h : instantiate cx d is ts = .ok (at_, rt)) :
    ∃ us : List Idx, at_ = substTs ts.reverse 0 0 (instT us 0 d.argTy) := by
  unfold instantiate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i _ _ _ _ heq
  split at h
  · cases h
  · rename_i us _
    cases h
    exact ⟨us.reverse, rfl⟩

theorem noOR_kidI {cx : Cx} {ke : KEnv} {T at_ A : Ty} {ts : List Ty} {us : List Idx}
    (hn : Ty.noOwnIn ke T = true) (hs : SubS cx T at_) (hat : at_ = substTs ts.reverse 0 0 (instT us 0 A))
    (hA : TermC1.drf1 A = true) (hts : ts.all TermC1.drf1 = true) :
    TermCut.noOR (TermRun.close (ts.map (TermRun.close [])).reverse A) = true := by
  have hmap : ts.map (TermRun.close []) = ts := by
    conv => rhs; rw [← List.map_id ts]
    exact List.map_congr_left (fun t _ => substTs_nil t 0 0)
  rw [hmap]
  have h1 : Ty.noOwnIn ke at_ = true := noOwnIn_subS hs ke hn
  rw [hat, noOwnIn_substTs_instT] at h1
  have hd : TermC1.drf1 (TermRun.close ts.reverse A) = true :=
    TermScope.drf1_close (fun σ hσ => List.all_eq_true.1 hts σ (List.mem_reverse.1 hσ)) hA
  exact TermCut.noOR_of _ ke h1 hd

end TermSpawnI
#print axioms TermSpawnI.instantiate_fst
#print axioms TermSpawnI.noOR_kidI
