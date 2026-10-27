/-
**The start control's facts** (AArch64, the twin of
`LowerX64.Start2C0`): for an `Accepted2` program `p` with a setup block
(`setupOf p = some ty`), the start's control `C0` (the thread
`th02 p (meW2 (lay2 Λ p) o)`, `S0A`'s) is `setupTerm` with `me` the first
TCB's number and `u` the unit. The premises of `h0InA_setup_assembled` about
it:

- `th02_setupA`: the start's thread is `setupTerm`'s;
- `hp0_start2A`: the program is free of `ZBad` (`progNoS_zbad_of_accepted2`);
- `hf0_start2A`, `hov_start2A`: `C0` is free of `ZBad` and not at an overflow;
- `hC0_start2A`, `hpl0_start2A`: `C0`'s facts (`CFacts`) and its placement,
  `me` at the immediate `imms2Me` keys for it (`imms2Me_setup`), which `me`'s
  word represents (`valRep_meW2_of_placeOKAtA`);
- `hcall_start2A`: `C0` calls the setup block (`hcall_setupStart`);
- `x0_start2A`, `hme_start2A`: the first TCB's address `pinA lab + 8` is
  `me`'s number, so every word of `C0`'s environment represents it.
-/
import Spike.Lib.LowerA64.PinnedTcbA
import Spike.Lib.LowerA64.SetupHCall
import Spike.Lib.Src.RunOk2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open A9NoSpawn
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.LowerNode (FrOk2 ZBad)

section Start

variable {Λ : Scc.Sem.Layout} {p : Prog}

/-- **The start's thread with a setup block**: `setupTerm`, `me` the word
`meW`, `u` the unit. -/
theorem th02_setupA {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) (meW : TermRun.Word) :
    th02 p meW = { term := SrcSem.setupTerm, env := [("me", .ptr .pub .void, [meW]), ("u", .unit, [])] } := by
  unfold th02; rw [hty]

/-- **`hp0`**: an `Accepted2` program is free of `ZBad`. -/
theorem hp0_start2A (hp : Scc.Lower.Accepted2 p = true) : ProgNoS ZBad p :=
  Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp

/-- **`hf0`**: the start's control is free of `ZBad` (a call and a pair
before `main`'s tail call), at no frame. -/
theorem hf0_start2A {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) (meW : TermRun.Word) :
    FrOk2 ⟨(th02 p meW).term, (th02 p meW).env, none⟩ [] := by
  rw [th02_setupA hty]
  exact ⟨⟨fun h => h, fun h => h, trivial⟩, fun _ h => nomatch h⟩

/-- **`hov`**: the start's control is not at an overflow (its operation is
a call). -/
theorem hov_start2A {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) (meW : TermRun.Word) :
    ¬ OvfReady ⟨(th02 p meW).term, (th02 p meW).env, none⟩ := by
  rw [th02_setupA hty]
  rintro ⟨_, _, _, _, _, _, _, _, _, _, ht, -⟩
  cases ht

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out}

/-- **`hC0`**: the start's control's facts at the theorem's layout: not a
`ret`, no load, store or allocation; placed at every state, `me`'s word at
the immediate `imms2Me` keys for it (`Λ.pinned.lo + 8`, which `me`'s word
represents), `u` of no word. -/
theorem hC0_start2A (h : placeOKAt pcfg (lay2 Λ p) o = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (lbl : Lbl) :
    CFacts (lay2 Λ p) lbl ⟨(th02 p (meW2 (lay2 Λ p) o)).term, (th02 p (meW2 (lay2 Λ p) o)).env, none⟩ := by
  rw [th02_setupA hty]
  refine ⟨fun _ ht => (nomatch ht), fun _ _ _ _ _ ht => ?_, fun _ _ _ _ ht => (nomatch ht), fun s => ?_⟩
  · rcases ht with ht | ⟨_, ht⟩ <;> cases ht
  refine ⟨fun x k => if x = "me" ∧ k = 0 then some (.imm (Λ.pinned.lo + 8)) else none, ?_, ?_, ?_⟩
  · intro x t ws hx k wd wp hwd hwp
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq] at hwp
      subst hwp
      simp only [TermRun.lookupE, List.find?] at hx
      cases hx
      cases hwd
      exact valRep_meW2_of_placeOKAtA h lbl
    · simp only [hc, ite_false] at hwp
      cases hwp
  · intro x hx t ws hl k hk
    have hfv : exprFv SrcSem.setupTerm = ["u", "me"] := by decide
    rw [show (⟨SrcSem.setupTerm, _, none⟩ : Ctl).term = SrcSem.setupTerm from rfl, hfv] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · simp only [TermRun.lookupE, List.find?] at hl
      cases hl
      exact absurd hk (Nat.not_lt_zero _)
    · simp only [TermRun.lookupE, List.find?] at hl
      cases hl
      simp only [List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      exact ⟨.imm (Λ.pinned.lo + 8), by simp⟩
  · intro x k n hn
    by_cases hc : x = "me" ∧ k = 0
    · obtain ⟨rfl, rfl⟩ := hc
      simp only [and_self, ite_true, Option.some.injEq, WordPlace.imm.injEq] at hn
      subst hn
      exact Spike.Lib.LowerNode.imms2Me_setup hty
    · simp only [hc, ite_false] at hn
      cases hn

/-- **`hpl0`**: the start's control is placed at every state, at no
frame. -/
theorem hpl0_start2A (h : placeOKAt pcfg (lay2 Λ p) o = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (lbl : Lbl) (s : State) :
    PlacedS (lay2 Λ p) lbl s ⟨(th02 p (meW2 (lay2 Λ p) o)).term, (th02 p (meW2 (lay2 Λ p) o)).env, none⟩ [] :=
  PlacedS.ofNil ((hC0_start2A h hty lbl).place s)

/-- **`hcall`**: the start's control calls the setup block. -/
theorem hcall_start2A (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (meW : TermRun.Word) :
    ∃ cE fr, Spike.Lib.A64.Flow.CallTo p ⟨(th02 p meW).term, (th02 p meW).env, none⟩ cE fr := by
  rw [th02_setupA hty]
  exact hcall_setupStart hp hty meW

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64

/-- **The first TCB's address is `me`'s number**: `pinA lab + 8` at the
runtime's layout is `Λ.pinned.lo + 8` (`Ly.lab_pin`,
`rtA_pinned_of_placeOKAtA`). -/
theorem x0_start2A (h : placeOKAt pcfg (lay2 Λ p) o = true) : (X0).toNat = Λ.pinned.lo + 8 := by
  have hb := below32_of_placeOKAt h Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have hpin : Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab = BitVec.ofNat 64 Λ.pinned.lo :=
    (Ly).lab_pin.trans (rtA_pinned_of_placeOKAtA h)
  rw [hpin]
  simp only [BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- **`hme`**: every word of the start's environment represents the first
TCB (`me`'s word is its number; `u` has no word). -/
theorem hme_start2A (h : placeOKAt pcfg (lay2 Λ p) o = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (lbl : Lbl) :
    ∀ y t ws, TermRun.lookupE (th02 p (meW2 (lay2 Λ p) o)).env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep lbl ws[k].val (X0).toNat := by
  rw [th02_setupA hty, x0_start2A h]
  intro y t ws hy k hk
  by_cases hm : y = "me"
  · subst hm
    simp only [TermRun.lookupE, List.find?] at hy
    cases hy
    simp only [List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    exact valRep_meW2_of_placeOKAtA h lbl
  · by_cases hu : y = "u"
    · subst hu
      simp only [TermRun.lookupE, List.find?] at hy
      cases hy
      exact absurd hk (Nat.not_lt_zero _)
    · have hm' : ("me" == y) = false := by simpa using Ne.symm hm
      have hu' : ("u" == y) = false := by simpa using Ne.symm hu
      simp [TermRun.lookupE, List.find?, hm', hu'] at hy

end Start

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.th02_setupA' depends on axioms: [propext] -/
#guard_msgs in #print axioms th02_setupA

/-- info: 'Spike.Lib.LowerA64.hp0_start2A' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hp0_start2A

/-- info: 'Spike.Lib.LowerA64.hf0_start2A' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hf0_start2A

/-- info: 'Spike.Lib.LowerA64.hov_start2A' depends on axioms: [propext] -/
#guard_msgs in #print axioms hov_start2A

/-- info: 'Spike.Lib.LowerA64.hC0_start2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hC0_start2A

/-- info: 'Spike.Lib.LowerA64.hpl0_start2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hpl0_start2A

/-- info: 'Spike.Lib.LowerA64.hcall_start2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hcall_start2A

/-- info: 'Spike.Lib.LowerA64.x0_start2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms x0_start2A

/-- info: 'Spike.Lib.LowerA64.hme_start2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hme_start2A

end Spike.Lib.LowerA64
