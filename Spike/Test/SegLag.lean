/-
**`SegW.lag`'s premises are satisfiable** (`Spike/Lib/SegLag.lean`): the
controls of `ret0.w`'s `main` body are `Quiet` at each of its terms, a load
is not, and a segment held back at `main`'s entry control keeps its
obligation at that control; `SegWS.lag`'s `hown` holds for memory sides
whose owned words do not depend on the frames (`ownIncl_of_indep`).
-/
import Spike.Lib.SegLag
import Spike.Lib.SegLagS
import Spike.Lib.Ret0Src

namespace Spike.Lib.SegLagTest

open CoreLang CoreTerm
open Kraken.Promising
open Spike.Lib.Ret0Src (ret0Body)

/-- A control at a term with no event pending is `Quiet`. -/
theorem quiet_of {t : Expr} {env : TermRun.Env}
    (hl : ∀ x a e, t ≠ .let_ x (.load true a) e) (hs : ∀ x a b e, t ≠ .let_ x (.store true a b none) e)
    (hn : ∀ x a τ e, t ≠ .let_ x (.newBuf a τ) e) (hx : ∀ x a v e, t ≠ .let_ x (.xchg a v) e)
    (hxa : ∀ x b i v e, t ≠ .let_ x (.xchgAt b i v) e) : Quiet ⟨t, env, none⟩ := by
  refine ⟨rfl, hl, hs, hn, fun x sa u v e ⟨_, h⟩ => ?_⟩
  rcases h with ⟨a, _, _, _, ht, _⟩ | ⟨b, i, _, _, _, _, _, _, _, ht, _⟩
  · exact hx x a v e ht
  · exact hxa x b i v e ht

/-- **`ret0.w`'s `main` body is `Quiet` at each of its terms.** -/
example (env : TermRun.Env) : Quiet ⟨ret0Body, env, none⟩ ∧
    Quiet ⟨.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")), env, none⟩ ∧
    Quiet ⟨.ret (.var "y"), env, none⟩ := by
  refine ⟨quiet_of ?_ ?_ ?_ ?_ ?_, quiet_of ?_ ?_ ?_ ?_ ?_, quiet_of ?_ ?_ ?_ ?_ ?_⟩ <;>
    intros <;> simp [ret0Body]

/-- A control at a load is not `Quiet`. -/
example (env : TermRun.Env) (a : At) (e : Expr) : ¬ Quiet ⟨.let_ "x" (.load true a) e, env, none⟩ :=
  fun h => h.2.1 "x" a e rfl

/-- A control with a hold is not `Quiet`. -/
example (t : Expr) (env : TermRun.Env) (w : TermRun.Word) : ¬ Quiet ⟨t, env, some (0, w)⟩ :=
  fun h => by cases h.1

/-- **A segment held back at a fixed control**: the obligation is asked
at the held-back control only (here with no kernel, so no `write`). -/
example {I : ISA} {K : I.State → I.State → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide I} {P Q : Frag I} {W' : Frag I} (c0 : Ctl) (hK : ms.K = none)
    (h : SegW (fun _ c => Quiet c) K p lbl ms P Q) (hW : ∀ s, W' s c0) :
    SegW W' K p lbl ms (Lag p (· = c0) P) (Lag p (· = c0) Q) :=
  h.lag (fun _ _ h => h) (fun _ _ _ _ hK' => nomatch hK.symm.trans hK')
    fun s _ _ _ _ hc => hc ▸ hW s

/-- `LagJ` is satisfiable: a control of `J` held back at itself. -/
example {p : Prog} {J : Nat → Ctl → Prop} {σ : Nat} {c : Ctl} (h : J σ c) : LagJ p (· = c) J σ c :=
  ⟨c, h, .refl c, rfl⟩

/-- With no control allowed (`C := fun _ => False`) `LagJ` holds nowhere. -/
example {p : Prog} {J : Nat → Ctl → Prop} {σ : Nat} {c : Ctl} : ¬ LagJ p (fun _ => False) J σ c :=
  fun ⟨_, _, _, h⟩ => h

/-- **`SegWS.lag`'s `hown` for memory sides not depending on the frames**
(`ownIncl_of_indep`). -/
example {I : ISA} {W : FragS I} {p : Prog} (m : MemSide I) :
    ∀ s c fs, W s c fs → ∀ c₁ fs₁, FrameRun p (c, fs) (c₁, fs₁) →
      ∀ L, RtReads s L → ∀ w, (L, w) ∈ m.own s → (L, w) ∈ m.own s :=
  ownIncl_of_indep (ms := fun _ => m) fun _ => rfl

/-- A state at a load of the runtime's memory at `L` reads it (`RtReads`). -/
example {I : ISA} {s : I.State} {L : Loc} {kl : Kraken.LoadKind} {g : Val → I.State}
    (he : I.exec s = some (.load kl false L fun v => .done (g v))) : RtReads s L :=
  .inl ⟨kl, g, he⟩

end Spike.Lib.SegLagTest
