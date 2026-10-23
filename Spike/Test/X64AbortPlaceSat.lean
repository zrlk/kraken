/-
**`Spike/Lib/X64AbortPlace.lean` on `overflow.w`'s addition** (`cOvf`,
`Spike/Test/OvfAbortSat.lean`): with `big` at an immediate (the layout's
`imms` naming it) or at a register's cell (loading `2^64 - 1`), `cOvf` is
placed (`placed_of_srepAb`'s hypotheses are satisfiable).
-/
import Spike.Lib.X64AbortPlace
import Spike.Lib.AbortSrc
import Spike.Test.OvfAbortSat

namespace Spike.Test.X64AbortPlaceSat

open CoreLang CoreTerm Spike.Lib Spike.Lib.X64Consumer Spike.Test.OvfAbortSat
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.Form (opdVal SEnv lookupS WordPl SRep)
open Spike.Lib.LowerNode (EnvNum)

/-- `big`'s word: `2^64 - 1`. -/
def big : UInt64 := UInt64.ofNat (2 ^ 64 - 1)

theorem cOvf_num : EnvNum cOvf.env := by
  intro b hb w hw
  simp [cOvf] at hb; subst hb
  simp at hw; subst hw
  exact ⟨2 ^ 64 - 1, rfl, by omega⟩

/-- `big` at an immediate. -/
def sImm : SEnv := [("big", .int, [.one (.imm big)])]

/-- The layout naming `big`'s immediate (at every term). -/
def ΛImm : Scc.Sem.Layout :=
  { trivLayout with imms := fun _ z k => if z = "big" ∧ k = 0 then some (2 ^ 64 - 1) else none }

theorem sImm_rep (lbl : Lbl) (sl : Int → BitVec 64) : SRep lbl (opdVal (fun _ => none) sl) sImm cOvf.env := by
  intro x t pls h
  simp only [sImm, lookupS, List.find?] at h
  by_cases hx : x = "big"
  · subst hx
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, rfl, ⟨_, rfl, by simp [ValRep, TermRun.cst, Promises.TVal.mk0, big]⟩, trivial⟩
  · have hb : ("big" == x) = false := by simpa using Ne.symm hx
    simp [hb] at h

example (lbl : Lbl) (s : State) : Placed ΛImm lbl s cOvf :=
  placed_of_srepAb (rs := fun _ => none) (sl := fun _ => 0) (addr := fun _ => 0) (sImm_rep lbl _) cOvf_num
    (by decide) (fun _ _ h => by cases h) fun x k v h => by
      by_cases hx : x = "big"
      · subst hx
        cases k with
        | zero => simp [sImm, lookupS] at h; subst h; simp [ΛImm, big]
        | succ k => simp [sImm, lookupS] at h
      · simp [sImm, lookupS, Ne.symm hx] at h

/-- `big` in register `r`'s cell `-8`. -/
def sReg : SEnv := [("big", .int, [.one (.reg "r")])]

example (lbl : Lbl) (s : State) (addr : Int → BitVec 64)
    (hc : privLoad s (addr (-8)) = some (BitVec.ofNat 64 (2 ^ 64 - 1))) : Placed trivLayout lbl s cOvf := by
  refine placed_of_srepAb (rs := fun _ => some (-8)) (sl := fun _ => BitVec.ofNat 64 (2 ^ 64 - 1)) (senv := sReg)
    (addr := addr) ?_ cOvf_num (by decide) (fun _ _ h => by cases h; exact hc) fun x k v h => ?_
  · intro x t pls h
    simp only [sReg, lookupS, List.find?] at h
    by_cases hx : x = "big"
    · subst hx
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨_, rfl, ⟨_, rfl, by simp [ValRep, TermRun.cst, Promises.TVal.mk0]⟩, trivial⟩
    · have hb : ("big" == x) = false := by simpa using Ne.symm hx
      simp [hb] at h
  · by_cases hx : x = "big"
    · subst hx
      cases k with
      | zero => simp [sReg, lookupS] at h
      | succ k => simp [sReg, lookupS] at h
    · simp [sReg, lookupS, Ne.symm hx] at h

end Spike.Test.X64AbortPlaceSat
