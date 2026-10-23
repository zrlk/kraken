import WeakCore.TermBoxT
import WeakCore.TermSetTh
import WeakCore.TermSpawnRun
/-! # TermBoxO — (E2) the ghost box keeps the spawn side conditions `OwnLive` and `ObsAll`. -/
namespace TermBox
open CoreLang CoreTerm TermRun TermSound TermMem TermStep TermCut TermSys TermInterf TermSetTh TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem ownLive_box {Eg : GEnv} {c : Cfg} {i : Nat} {th' : TTh} {tr : List Event} {l : AllocLabel}
    (h : OwnLive Eg c) : OwnLive (EgB Eg l) (setC c i th' tr) := by
  refine ⟨fun x cl j hx ho => ?_, fun x B hB => by rw [setC_size]; exact h.2 x B hB⟩
  rw [setC_size]
  by_cases e : x = l
  · subst e; simp [EgB] at hx; subst hx; cases ho
  · rw [EgB_sto_ne e] at hx; exact h.1 x cl j hx ho

theorem obsAll_box {Eg : GEnv} {c : Cfg} {i : Nat} {th' : TTh} {tr : List Event} {l : AllocLabel}
    (hs : Eg.sto l = none) (hp : Eg.pfr l = none) (hm : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ l)
    (h : ObsAll Eg c) : ObsAll (EgB Eg l) (setC c i th' tr) := by
  intro j hj
  rw [setC_size] at hj
  obtain ⟨a, b, d⟩ := h j hj
  have hs' : (Cut Eg j (fun _ => False)).sto l = none := by rw [Cut_sto]; unfold cutSto; split <;> simp [hs]
  rw [cut_EgB]
  exact ⟨pubDefP_boxE hs' hp hm a, pubPair_boxE hs' hp hm b, pubLive_boxE d⟩

end TermBox

#print axioms TermBox.ownLive_box
#print axioms TermBox.obsAll_box
