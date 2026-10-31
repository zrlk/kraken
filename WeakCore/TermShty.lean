import WeakCore.TermInterf

/-! # TermShty: `shtyT` (T13, S10) discharged

After a thread step every shared cell of `EgT` is in the stepper's new environment `E'` with its
frontier (`tctx_shared`, via `tctx_cut`), where `PubCpl E'` (in `TOut`'s `MemInv`) gives `noOwnIn` and
`rgnFree`, hence `noOR` (`noOR_of`). -/

namespace TermShty
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermCut TermSys TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **T13 `shtyT`**: shared cell types stay `noOR` across a thread step. -/
theorem shtyT_holds {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    SharedTyOK (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') :=
  fun _ _ ⟨_, hf⟩ hc => (tctx_shared X Y Z hc hf).2.2

end TermShty

#print axioms TermShty.shtyT_holds
