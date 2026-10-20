import WeakCore.TermPtrRtsThr
import WeakCore.OwnFreshW5

/-!
# OwnFreshW5b: the W5b site

`oldMsg_not_fresh`: after a thread step of `i`, no message below the old memory size lies at a
label the step allocated.  Such a message would be an outstanding promise of `i` (`GFreshL`), kept
across the allocating step (`alloc_noFulfil`), at the step's fresh label, which `PromAllocF` (`hA`)
rules out.  Allowed as W5b for the single use in `boxPlantSep_thread`.
-/

namespace TermPtrRtsK
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem oldMsg_not_fresh {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hA : PromAllocF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {u : Ts} {m : Msg} (hu : u < c.mem.size) (hm : c'.mem[u]? = some m) :
    ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label := by
  intro hF
  have hm0 : c.mem[u]? = some m := (tctx_pre X u hu).symm.trans hm
  obtain ⟨q, hq1, hq2, hl⟩ := hF
  have hG : GFreshL Eg c th m.loc.label := by
    rw [hl]
    exact X.inv.fresh i th X.hth q hq1
  have hin := hG.2.2.2.2 u m hm0 rfl
  have hin' := TermPtrRtsThr.alloc_noFulfil X.hr (Nat.lt_of_le_of_lt hq1 hq2) u hin hu
  exact (hA X Y Z hS hPfr m.loc.label ⟨q, hq1, hq2, hl⟩ u m hin' hm).1 rfl

end TermPtrRtsK

#print axioms TermPtrRtsK.oldMsg_not_fresh
