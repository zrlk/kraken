/-
**Segments under `msOfS` as segments under the arena's memory side** on the
canonical AArch64 target (the twin of `Spike/Lib/X64OutSA.lean`;
`Spike/Lib/MemSideA.lean` at `msOfS` and `msOfAX … ab`): `msOfAX`, with or
without the output's byte step and the write abort phase, agrees with `msOfS` on every field but the arena's and
the allocation fragment, and `msOfS` has no byte step and no abort
justification. So a segment proved under `msOfS` (the start segment, the
prologue and epilogue, the call machinery) whose rows are taken at no
buffer allocation is one under `msOfAX … ab`.

- `msOfAX_rd`, `msOfAX_rt`, `msOfAX_K`, `msOfAX_G`, `msOfAX_own`,
  `msOfAX_mp`, `msOfAX_abortAt`, `msOfAX_pl`: the fields `msOfAX … ab`
  shares with `msOfS`; `msOfS_bo`, `msOfS_we`: `msOfS` has neither.
- `outS_toAX`, `segWS_toAX`: `OutS.toA`, `SegWS.toA` from `msOfS` to
  `msOfAX … ab`.
-/
import Spike.Lib.A64ConsumerA
import Spike.Lib.MemSideA

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Arena} {I : InvS} {ab : Option (State → Prop)} {lbl : Lbl} {lsize : Lsize}
  {fs : List TermRun.Frame}

@[simp] theorem msOfAX_rd :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).rd = (msOfS Λ μ rd G own lbl lsize fs).rd := by
  cases ab <;> rfl

@[simp] theorem msOfAX_rt :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).rt = (msOfS Λ μ rd G own lbl lsize fs).rt := by
  cases ab <;> rfl

@[simp] theorem msOfAX_K :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).K = (msOfS Λ μ rd G own lbl lsize fs).K := by
  cases ab <;> rfl

@[simp] theorem msOfAX_G :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).G = (msOfS Λ μ rd G own lbl lsize fs).G := by
  cases ab <;> rfl

@[simp] theorem msOfAX_own :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).own = (msOfS Λ μ rd G own lbl lsize fs).own := by
  cases ab <;> rfl

@[simp] theorem msOfAX_mp :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).mp = (msOfS Λ μ rd G own lbl lsize fs).mp := by
  cases ab <;> rfl

@[simp] theorem msOfAX_abortAt :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).abortAt = (msOfS Λ μ rd G own lbl lsize fs).abortAt := by
  cases ab <;> rfl

@[simp] theorem msOfAX_pl :
    (msOfAX Λ μ p rd G own ar I ab lbl lsize fs).pl = (msOfS Λ μ rd G own lbl lsize fs).pl := by
  cases ab <;> rfl

theorem msOfS_bo {s : State} {a : Nat} {c : Ctl} {Q : Ctl → Prop} :
    ¬ (msOfS Λ μ rd G own lbl lsize fs).bo s a c Q :=
  id

theorem msOfS_we {s : State} {c : Ctl} : ¬ (msOfS Λ μ rd G own lbl lsize fs).we s c :=
  id

/-- **An `OutS` row under `msOfS`** whose row control is no buffer
allocation is one under `msOfAX … ab` (`OutS.toA`). -/
theorem outS_toAX {X : FragS isaLSE2} {s : State} {c : Ctl} (h : OutS p lbl (msOfS Λ μ rd G own lbl lsize) X s c fs)
    (hnb : ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → NoNewBuf c₁) :
    OutS p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) X s c fs :=
  h.toA (fun _ => msOfAX_rd) (fun _ => msOfAX_rt) (fun _ => msOfAX_K) (fun _ => msOfAX_G) (fun _ => msOfAX_own)
    (fun _ => msOfAX_mp) (fun _ => msOfAX_abortAt) (fun _ => msOfAX_pl) (fun _ _ _ _ _ h => (msOfS_bo h).elim)
    (fun _ _ _ h => (msOfS_we h).elim) hnb

/-- **A segment at depth under `msOfS`** is one under `msOfAX … ab`
(`SegWS.toA`) when no control a frame run reaches from a pair of `W` is a
buffer allocation. -/
theorem segWS_toAX {W : FragS isaLSE2} {K : State → State → Prop} {P Q : FragS isaLSE2}
    (h : SegWS W K p lbl (msOfS Λ μ rd G own lbl lsize) P Q)
    (hnb : ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) → NoNewBuf c₁) :
    SegWS W K p lbl (msOfAX Λ μ p rd G own ar I ab lbl lsize) P Q :=
  h.toA (fun _ => msOfAX_rd) (fun _ => msOfAX_rt) (fun _ => msOfAX_K) (fun _ => msOfAX_G) (fun _ => msOfAX_own)
    (fun _ => msOfAX_mp) (fun _ => msOfAX_abortAt) (fun _ => msOfAX_pl) (fun _ _ _ _ _ h => (msOfS_bo h).elim)
    (fun _ _ _ h => (msOfS_we h).elim) hnb

/--
info: 'Spike.Lib.A64ConsumerA.segWS_toAX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms segWS_toAX

end Spike.Lib.A64ConsumerA
