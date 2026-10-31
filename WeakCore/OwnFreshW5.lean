import WeakCore.TermPromClos
import WeakCore.TermPtrStab

/-!
# OwnFreshW5: the single `ownProm_sto_keep` site

`ownProm_sto_keep`: across a thread step of `i`, the global store at the location of any promise `i`
still has outstanding after the step is unchanged.  The only fresh-label case (a promise of `i` at a
label `i` just allocated) is ruled out by `PromAllocF` (`hA`, the hypothesis already supplied to
`TermFgnClos.fgnClos_thread`; admitted for this single use in `ptrRtsGL_thread`).
-/

namespace TermPtrRtsK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem ownProm_sto_keep {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hA : PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {u : Ts} {m : Msg} (hu : u ∈ r.2.2.promises) (hm : c'.mem[u]? = some m) :
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = Eg.sto m.loc.label := by
  by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label
  · exact absurd rfl (hA X Y Z hS hPfr m.loc.label hF u m hu hm).1
  · exact TermPtrStab.EgT_sto_old hF

end TermPtrRtsK

#print axioms TermPtrRtsK.ownProm_sto_keep
