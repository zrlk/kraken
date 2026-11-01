/-
**hello.w on AArch64: the witness after the spawn** (row 5j-wit;
`HelloRowsW.post_wit`, the hello twin of `WakePostWit.post_wit_of`):
`HelloPostWitG.post_wit_genSE` at hello's per-thread relations, wake's
`PT0` for main and `HelloEmitPh.PT1hE` for the worker.

- main (`PT0`, one frame): its invariant places its control (`hplM`;
  `PlacedS.ofNil`), or main has returned (`WakePostWit.placed_wlRet`). At
  `HelloMainInv.helloM` the invariant is inside `mainWRH`, whose
  `WakeInst.mainW` carries `Placed` (`hplM_helloM`).
- the worker at `PT1h`: its invariant places every frame (`hplW`, open:
  row 5j-wit-W).
- the worker mid-`write` (`EmitPh`): placed by `HelloPlE.hplE_of` from `hplW`
  and `print`'s call frame placed from a `D.Wi` control (`hcall`, open: row
  5j-wit-E-call).

- `post_wit_hello`: the row from `hplM`, `hplW`, `hcall`.
- `hplM_helloM`: `hplM` at `helloM`.
-/
import Spike.Lib.HelloPostWitG
import Spike.Lib.HelloEmitPh
import Spike.Lib.HelloMainInv
import Spike.Lib.HelloPlE

namespace Spike.Lib.HelloPostWit

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.A64Consumer (Placed)
open Spike.Lib.A64ConsumerS (PlacedSE PlacedS)
open Spike.Lib.HelloW1 (WSideH PT1h)
open Spike.Lib.HelloEmitPh (PT1hE EmitPh)
open Spike.Lib.WakePostWit (M2)

variable {Q : WakeRel} {D : WSideH Q.ι} {M : WakeM0.MSide Q.ι} {Λ : Scc.Sem.Layout}

/-- **`post_wit` at hello's per-thread relations** (row 5j-wit): main's
invariant places its control (`hplM`); the worker's invariant places every
frame (`hplW`, row 5j-wit-W), and so do the frames mid-`write`
(`HelloPlE.hplE_of`, from `hplW` and `print`'s call frame placed, `hcall`, row
5j-wit-E-call). -/
theorem post_wit_hello (hwf : Λ.WF) (hPT0 : Q.PT0 = WakeM0.PT0 M) (hpt1 : Q.PT1 = PT1hE D) {E : Entry}
    (hplM : ∀ w s c, M.Mi w s c → Placed Λ (Q.SR w).lbl s c)
    /- row: 5j-wit-W. The worker's invariant places every frame at the spawn's placement. -/
    (hplW : ∀ w s c fs, D.Wi w s c fs → PlacedSE Λ (Q.SR w).lbl s c fs)
    /- row: 5j-wit-E-call. From a `D.Wi` control on no frames, `print`'s call frame is placed. -/
    (hcall : ∀ w st c, D.Wi w st c [] → ∀ c', LocalRunS HelloSrc.helloSrc c c' → c'.term = HelloSplit.workerCallH →
      A64ConsumerS.FramesPlaced Λ (Q.SR w).lbl st [⟨"u", HelloSplit.workerRestH, c'.env, [], .unit⟩]) :
    ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components M2 Λ w t s :=
  fun _ _ h hr => HelloPostWitG.post_wit_genSE hwf
    (fun w _ _ _ st hp => by
      rw [hPT0] at hp
      obtain ⟨h1, h2, -⟩ := hp
      rw [h2]
      exact .inl (PlacedS.ofNil (h1.elim (hplM w _ _) fun h => WakePostWit.placed_wlRet h)))
    (fun w tm sm t1 s1 hp => by
      rw [hpt1] at hp
      rcases hp with hp | hp
      · exact hplW w _ _ _ hp.1
      · exact HelloPlE.hplE_of (L := fun w => (Q.SR w).lbl) hplW hcall w tm sm t1 s1 hp) h hr

/-- **`hplM` at `helloM`**: its invariant is inside `mainWRH`, whose `mainW`
places the control. -/
theorem hplM_helloM {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {lsize : ι → WeakMem.AllocLabel → Nat}
    {ms : ι → MemSide isaLSE2} {cw : ι → TermRun.Word} {lab : String → Int64} {exe : _root_.Executable}
    {μT : Marks} {hoff : ∀ s c, Spike.Lib.A64WakeOff.AbOffA lab s c → ∀ k a, μT.abortAt k = some a → pcOf s ≠ a} :
    ∀ w s c, (HelloMainInv.helloM lbl lsize ms cw lab exe Λ μT hoff).Mi w s c → Placed Λ (lbl w) s c :=
  fun _ s c h => (HelloMainInv.mainInvP_W s c h).1.2.2.2

/-- **Non-vacuity of `PlacedSE`'s extern disjunct with a suspended frame**:
a control returning a literal over one frame whose body returns a literal
is placed (the empty maps), at any layout, placement and state, for any
environments. -/
example (s : State) (lbl : WeakMem.AllocLabel → Option Nat) (env env' : TermRun.Env) (ty : Ty) :
    PlacedSE Λ lbl s ⟨.ret (.lit 0), env, none⟩
      [{ x := "r", body := .ret (.lit 1), env := env', σs := [], ty := ty }] := by
  refine .inr ⟨.inr rfl, fun _ _ _ => none, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ h; cases h
  · intro d f hf x hx
    rcases d with _ | d
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hf
      subst hf
      simp [exprFv, atVars] at hx
    · simp at hf
  · intro _ _ _ _ _ _ h; cases h

/-- info: 'Spike.Lib.HelloPostWit.post_wit_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms post_wit_hello

/-- info: 'Spike.Lib.HelloPostWit.hplM_helloM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hplM_helloM

end Spike.Lib.HelloPostWit
