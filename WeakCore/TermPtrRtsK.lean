import WeakCore.TermGranW
import WeakCore.TermInterf

/-!
# TermPtrRtsK: the D-B lemmas for the `ptrRts` / `granW` clauses

* `granuleW_prom` — the global `granW` clause across a main-machine promise step (the
  certification facts `PromNoTwoPF` / `PromLocF` are used here only, cert whitelist
  "cellOwn + granW preservation only").  The new promise is pushed at `a`; no pair store starts at
  `a`:
  (i) at a cell of `Eg` (`GranuleW`'s third conjunct would make `a` a `TwoAtT` start, against
      `PromNoTwoPF`);
  (ii) at no cell, `PromLocF` makes `a.label` a fresh label of the promiser `j`, so (`SysInvN.fresh`,
      `GFreshL`) every message there is a promise of `j`; a pair start is no promise of `j`:
      **source**: `PromOK` (`TermStep.PromOK`, second conjunct `t ∈ s.promises → t ∉ s.pairs`), the last
      conjunct of `MemInv (gOf ..) (Cut Eg j S) (stOf c.mem c.pairs th)` from `SysInvN.thr j th` (`ThSys`),
      at the pre-state `c`.
* `ptrRtsGL_init` — the staging package at an initial configuration (no frontiers), given `LblSto`
  (`LblSto` at init pending the live-binding decision).
-/

namespace TermPtrRtsK
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermCut TermSys TermMain TermInterf TermPtrRts TermGranW
open WeakMem (Msg Memory Address Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`granW` across a promise step** (main machine, stage A; cert facts confined here). -/
theorem granuleW_prom (hnt : PromNoTwoPF p k arch Sp Init MintOK c0) (hpl : PromLocF p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hG : GranuleW Eg.sto c.mem c.pairs) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (n : Nat) :
    GranuleW (EgP Eg P N j n).sto (promise c j a v w).mem (promise c j a v w).pairs := by
  rw [(promise_inv (a := a) (v := v) (w := w) X.hth).1]
  refine granuleW_pushOne hG (fun q hq m0 h0 e => ?_)
    (fun cl o hc ho hT _ _ _ => absurd ho (hnt X cl hc o hT).2)
  have e' : m0.loc = a := e
  cases hs : Eg.sto a.label with
  | some cl =>
    have hT : TwoAtT cl.ty m0.loc.offset := hG.2.2.1 q hq m0 cl h0 (by rw [e']; exact hs)
    rw [e'] at hT
    exact (hnt X cl hs a.offset hT).1 rfl
  | none =>
    rcases hpl X with ⟨cl, hc⟩ | ⟨m, hm, hl⟩
    · rw [(cutSto_some.1 hc).1] at hs; cases hs
    · have hqp : q ∈ th.promises :=
        (X.inv.fresh j th X.hth m hm).2.2.2.2 q m0 h0 (by rw [e', hl])
      obtain ⟨S, -, -, hM, -⟩ := X.inv.thr j th X.hth
      exact hM.2.2.2.2.2.2.2.2.2.2.2.1 q hqp hq

end

/-- **`PtrRtsGL` at an initial configuration**: with no frontiers, `PtrRtsG`, `GateTmin` and `MemRtsCG`
are vacuous (each is gated on `Eg.pfr a = some f`); `LblSto` is the hypothesis. -/
theorem ptrRtsGL_init {Eg : GEnv} {c : Cfg} {Tot HP : Nat → Res} (hpf : ∀ l, Eg.pfr l = none)
    (hL : LblSto Eg c) : PtrRtsGL Eg Tot HP c := by
  refine ⟨fun j th a cl f _ _ _ hf => ?_, hL, fun j a cl f _ _ hf => ?_, fun j th a cl f _ _ _ hf => ?_⟩
  · rw [hpf a] at hf; cases hf
  · rw [hpf a] at hf; cases hf
  · rw [hpf a] at hf; cases hf

/-! ## `stoLay` (v3c `hLay`; GO): every cell type of `Eg` is laid out -/

/-- **`stoLay` across a thread step** (copy of `TermMain`'s `case stoNI`): an old cell keeps its
type; a fresh cell's type carries `NewAtT`'s layout. -/
theorem stoLay_thread {Eg : GEnv} {g : G} {i : Nat} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St}
    {n n' : Nat} {c' : Cfg} (hF : EFoot g (Cut Eg i S) E' s s')
    (h : ∀ l cl, Eg.sto l = some cl → LayT cl.ty) :
    ∀ l cl, (EgT Eg g n n' E' c').sto l = some cl → LayT cl.ty := by
  intro l cl hl
  simp only [EgT, GEnv.withFp, GEnv.post] at hl
  split at hl
  · rcases hF.2.2.1 l with e | ⟨-, T, hT', hcT⟩
    · rw [e] at hl; exact h l cl (cutSto_sub hl)
    · rw [hT'] at hl; cases hl
      rcases hcT.2.2.1 with ⟨L, hL, -⟩ | ⟨K, e, L, hT, hL, -⟩
      · exact .inl (by rw [hL]; simp)
      · exact .inr ⟨K, e, hT, by rw [hL]; simp⟩
  · exact h l cl hl

/-- **`stoLay` across a promise step**: `EgP` keeps `sto`. -/
theorem stoLay_egP {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat}
    (h : ∀ l cl, Eg.sto l = some cl → LayT cl.ty) :
    ∀ l cl, (EgP Eg P N j n).sto l = some cl → LayT cl.ty := h

/-- **`stoLay` at an environment with no cells** (the initial `Eg0`). -/
theorem stoLay_empty {Eg : GEnv} (h0 : ∀ l, Eg.sto l = none) : ∀ l cl, Eg.sto l = some cl → LayT cl.ty :=
  fun l _ h => by rw [h0 l] at h; cases h

end TermPtrRtsK

#print axioms TermPtrRtsK.granuleW_prom
#print axioms TermPtrRtsK.ptrRtsGL_init
#print axioms TermPtrRtsK.stoLay_thread
#print axioms TermPtrRtsK.stoLay_egP
#print axioms TermPtrRtsK.stoLay_empty
