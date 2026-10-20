import WeakCore.TermPlantE

/-!
# TermPredOne: planted multi-word slots are all `.one`

A planting promise that raises a buffer's count above `Eg.ini` holds every word of the first new
slot by an own outstanding promise (`PrefixHeld_NpZ`); by `PromNoTwoOK` none of these words lies
in a two-word unit, so every unit of the element type is `.one`.  (The argument of
`W2New.promWordNew_of`, factored out for R1 and for `TermPredHold`.)
-/

namespace TermPredOne

open CoreLang CoreTerm CoreTyping TermRun TermClose TermSound TermMem TermStep TermCut TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Held words are `.one`**: if word `jj * nWords us + x` of every `x < nWords us` of slot
`jj < N` of a buffer carries an outstanding promise of some thread, every unit of the element
is `.one`. -/
theorem allOne_of_held {Eg : GEnv} {c : Cfg} {j : Nat} {th : TTh} {l : AllocLabel} {cl : Cell}
    {N jj : Nat} {e : Ty} {us : List Acc} (hNT : PromNoTwoOK Eg c) (hth : c.ths[j]? = some th)
    (hcl : Eg.sto l = some cl) (hT : cl.ty = .array (.lit N) e) (hu : accs e = some us) (hjN : jj < N)
    (hheld : ∀ x, x < nWords us → ∃ t ∈ th.promises, ∃ m, c.mem[t]? = some m ∧
      m.loc = ⟨l, jj * nWords us + x⟩) :
    ∀ u ∈ us, u = .one := by
  intro u hmem
  cases u with
  | one => rfl
  | two =>
    obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hmem
    have hi' : us[i]? = some .two := by rw [List.getElem?_eq_getElem hi, hiu]
    have h2 : TwoAt us (nWords (us.take i)) := ⟨i, hi', rfl⟩
    have hlt := TwoAt_lt h2
    obtain ⟨t, ht, m, hm, hloc⟩ := hheld (nWords (us.take i)) (by omega)
    have hcm : Eg.sto m.loc.label = some cl := by rw [hloc]; exact hcl
    have hTT : TwoAtT cl.ty (jj * nWords us + nWords (us.take i)) :=
      ⟨jj * nWords us, e, us, _, Or.inr ⟨N, us, jj, hT, hu, hjN, rfl⟩, hu, h2, rfl⟩
    have := (hNT j th t m cl hth ht hm hcm _ hTT).1
    rw [hloc] at this
    exact absurd rfl this

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **(R1 / PredHold) A planting promise that raises a buffer's count plants only `.one`
units**: at a planting promise (`PCtx`), if `plantOf` plants `l` and the planted count exceeds
`Eg.ini l`, every unit of `l`'s element type is `.one`. -/
theorem plantNew_allOne {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {f : Ts} {cl : Cell} {N : Nat} {e : Ty} {us : List Acc}
    (hpl : TermPlantF.plantOf c Eg j a v w l = some f)
    (hgt : ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l)
    (hcl : Eg.sto l = some cl) (hT : cl.ty = .array (.lit N) e) (hu : accs e = some us) :
    ∀ u ∈ us, u = .one := by
  obtain ⟨hPL, -⟩ := TermPlantE.plantOf_some X hpl
  have hcP : (TermPlantF.cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t1, -, m1, -, -, -, a1, g1, -, hal, cl1, hc1, -, -⟩ := hPL
    subst hal
    have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl; cases hcl; rfl
    subst e1; exact hc1
  have hN : TermPlantF.plantN c Eg j a v w l = NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
    simp only [TermPlantF.plantN, X.hth]
  rw [hN] at hgt
  have hNp := NpZ_le (s := stOf c.mem c.pairs th) hcP hT
  refine allOne_of_held X.inv.promNoTwo X.hth hcl hT hu (jj := Eg.ini l) (by omega) ?_
  intro x hx
  have hoN : Eg.ini l * nWords us + x < NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l * nWords us := by
    have : (Eg.ini l + 1) * nWords us ≤ NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l * nWords us :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.succ_mul] at this; omega
  rcases PrefixHeld_NpZ hcP N e us hT hu _ hoN with hI | ⟨t, ht, m, hm, hloc⟩
  · have h5 : Eg.ini l * nWords us + x < Eg.ini l * nWords us := hI N e us hT hu
    omega
  · exact ⟨t, ht, m, hm, hloc⟩

end

end TermPredOne

#print axioms TermPredOne.allOne_of_held
#print axioms TermPredOne.plantNew_allOne
