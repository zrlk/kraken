import WeakCore.TermK2aRet

/-!
# K-2a: the `ret` frame link (staged per-step premise `hRL`)

`TermK2a.stepB_ret` takes the frame link `hlink`: the counted words of the returned value at the
frame's type are counted words at the returned atom's runtime type.  It follows from the staged
per-step premise `hRL` (a `ThInvE` witness of this thread whose closed return type has the top frame type's signature): the
returned atom's type is a subtype of the return type (`pubWords_subS`), laid out at its runtime
type (`sig_of_eskel`), and counted words read only the signature (`pubWords_sig`).
-/

namespace TermK2aLinkPw

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermPtrRts
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- **`stepB_ret`'s frame link** from the staged per-step witness `hRL`. -/
theorem hlink_of {p : Prog} {E : TEnv} {th : TTh} {a : At}
    (hRL : ∃ ρ η cx, CE η = E ∧ EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧
      FInv ρ η th.σs (Resume p th.stack) cx th.env ∧
      ∀ (f : Frame) (rest : List Frame), th.stack = f :: rest → ∀ ws, pubWords f.ty ws = pubWords (close th.σs cx.ret) ws)
    (hterm : th.term = .ret a) :
    ∀ (f : Frame) (rest : List Frame) (rt : Ty) (ws : List Word), th.stack = f :: rest →
      evalAt th.env a = some (rt, ws) →
      ∀ w ∈ pubWords f.ty ws, ∃ w0 ∈ pubWords rt ws, w0.val = w.val ∧ w0.rts ≤ w.rts := by
  intro f rest rt ws hst hea w hw
  obtain ⟨ρ, η, cx, -, -, hTy, -, hi, hsf0⟩ := hRL
  have hsf := hsf0 f rest hst
  rw [hterm] at hTy
  cases hTy with
  | ret hu _ hsub =>
    obtain ⟨-, -, hr, -⟩ := use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu
    obtain ⟨-, rt0, ws0, hea0, -, hl⟩ := use_FInv hu hi
    rw [hea, Option.some.injEq, Prod.mk.injEq] at hea0
    obtain ⟨rfl, rfl⟩ := hea0
    have e1 : pubWords (close th.σs _) ws = pubWords (close th.σs _) ws :=
      (TermK2a.pubWords_subS hsub th.σs 0 0).2.1 ws
    rw [hr] at e1
    have e2 : pubWords f.ty ws = pubWords rt ws := by
      rw [hsf, ← e1, ← TermK2a.pubWords_sig rt, sig_of_eskel hl.2.1, TermK2a.pubWords_sig]
    exact ⟨w, e2 ▸ hw, rfl, Nat.le_refl _⟩

/-- **`ret`'s binding contract**, the frame link discharged from the staged per-step witness `hRL`. -/
theorem stepB_retK {p : Prog} {E : TEnv} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At}
    (hRL : ∃ ρ η cx, CE η = E ∧ EnvOK p η ∧ Typed p cx th.term ∧ TvOK cx ∧
      FInv ρ η th.σs (Resume p th.stack) cx th.env ∧
      ∀ (f : Frame) (rest : List Frame), th.stack = f :: rest → ∀ ws, pubWords f.ty ws = pubWords (close th.σs cx.ret) ws)
    (hterm : th.term = .ret a)
    (hr : r ∈ tstep g mem pairs th) : TermK2a.StepB sto mem pairs lb N th r.2.2 :=
  TermK2a.stepB_ret hterm (hlink_of hRL hterm) hr

end TermK2aLinkPw

#print axioms TermK2aLinkPw.hlink_of
#print axioms TermK2aLinkPw.stepB_retK
